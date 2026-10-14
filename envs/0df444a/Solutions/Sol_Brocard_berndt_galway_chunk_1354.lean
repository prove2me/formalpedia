-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1354
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:32:18.984359+00:00
-- url     : https://prove2.me/submissions/b7bb2983-e220-4bd2-9d69-db7460c11ff9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 243345323 ≤ n < 243525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 243346573 1250 243345323 243345353
    0x215040503030a0e16060f02010e070f0302030c1f0302070c05220b0303040b1e09060301030f2001020c01030b2d0307052202030a06090603030206040b0c0406140313 72
    0x3000795903901e0841804030546640e00724403004e0f03a01130031030140e182003c0c100003000d5030380a1a241c10f403c07003040342c00c0f40502403419400105004800340445c440400f00e46030415607000b42c04032204c8100c0d00040c40904c131084803040d40f02610f503403070b940100d80c880d400610507070b8041c40e014201151508002041e40310083c3c4200760301e40b02e00c42c10a15840701030003200500301c002c402450400780340594070903091082e002e04500c46009440c000c028454050261407281034081d00103601c0750f17183d24000109510510042d40c5013801c0d04048491000d00b9440b001c504075069000c0d0207032134034500044d0302800028406a41c0281c80e01000101001020001030400c0400452041030300d0030030045c1410000b490b00240d003d0f545984540500178240060301084020800005913250345055402c001400160080c40a03141005400002d05600007040780c09039025001540c515140e0f401c2e2503815201c0c6104e140c012844c8201060070100e58100519400a001e00c04a141200c40c2c5d40c0b003455842401d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 243347823 1250 243346573 243346583
    0x2181003090c09180f080d0519151211010c1b030b010f0e010b0a020f030409271101030e010b041b020d08041703220b070e0306010f0b070201021504 65
    0x500c125041c4910141c46000402e603509040148a050300c040982c41542200094588003408981d02c00700f0944008176040c1c1e6411703107c204520705007101d01079100c071200c0c0707228100d42e400e24a1a042c0188007c104070102d031005062050b00040d03079610050791140a820107814056640c440b031020904110503000d18900140009481c1030440ca044841c038141a0003c05801030400000d0154499000c0c8950554260070089611100c00600c1289010422505c0c103c2d01d0001040019084980c3c0d0003040c000412200d1304210b642e00c00d4403041d400455a0030103808502a4002e0491950091b44010341c1150402e0010526144200208081c3c0ba8101000202c86651902401c0390302c0c2e06001314001366010b807400360860f0605843d10300c10b08914441c0203400001c00000700d00e50b8140300d1011849141d24298801e00740ca00ca051400804101716099004240030103240e01581ca004a007860685a804850142250924191500c40e421001d0100e05601c15020745c420051240001540f20314814 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 243349073 1250 243347823 243347831
    0x1203011e05090a050405120a0302040e01090903021e070905010311010206011703271002010c02010e0705030709090f0c0305030316030c1b0320011a0a0609030602181003 74
    0x1425031a240d521100c0200095008010144038075907840110a800008122000c6100c1c0c6450a02c1c50505180080c40c0712010030002c1c0c09403e09070541c018100b15052010908078a0782c3e2858068251212200d0041c01a008481015103801160519491140c101001c6030501900c509404088500c01c1e08142e40e049000356481006690403c5003078003501d0014449103030061102c080513030301c1c000c041c20b0400380c24200700d8800c410303e1551030f41030300d0240041ca03121120070100d0000c4d009003400c00f4554019401c2100c0329003100400030b28030301121030180040038101d02d080080e000510312154200c8aa1080d1010440801c1e0710b03460541c080d60082000d140d507800c00306600d0400c2c2c0b00d1180d403031040c18101003401032540c0c1c0100030604000741164506102e04447d207001c68a007440c400c41480810790040304581011015031200520403a001121103228242104000c0c2044062041c003000a054080500004103260050a2078040204030010700d501c546c00050301000c14070310310380002661 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 243350323 1250 243349073 243349079
    0x3030d09051b010912050309150a080c0301060f180b120901060f0e060d1505181501080607210216020f0a081e0307060c0504080f06060a090c11120301 66
    0x400c0c00011001030080b41c1d19040c0c00d4003080081d04512851060b0b4a0b00316180f011042881020b204403138000400402d1102200b40100300030601d03402a03207150000030608130005205605220850b4103803030703107610344000e88113100c03504955a6040c0500c818071981c80107400034003403400c400505840700030070a0803a0b40d4502a00c0c0c0c01d086401c50743c8880d4022028403410840503c000340529000300301640d410101c1d00c001d0400c1903080001c100c440785504d15047c104034071941c078816090500418030082c3c07111005090500c048006082c0943c003101d40041c008100101d00800032803245e40805d4501040c8a4000000803080b600129120107840d1116898103045103010311444e000203008035103e8000500301804550344074035581c01060300078070043c48202034400400079500c88550000301030020405600b00148a6007042c03107085998403c0c9140700503003000100c1c603e8072500024118001d1545080b8100000d40119019401404181c4406042044041c403820380200402c4c50942d0392545 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 243351573 1250 243350323 243350333
    0xb031f091403270d11010e1201021902030c060a0e15090607030b01020114010501051305040e0a020102061e1302060f03090601061209080306061318050a0516050712050903030d09 78
    0x14464410f0f0382c20100808070340c0f00307598036806010250380040c2d812401503101e4006880705810094000e0340000300403109030051205400501082c0305224200c42e282c00d04640c140c5e43c0380118138640001d038110740001068501b4540c05881c00d039020000300c1d9420047e007101c0708241d00d8160b410400c0e5030002d400f00200c5517014094929a5a8280300070000c25500c0b80780070501c2c5d00103024890402c4800070301405514101d0f8100c1014200c001c0c010020300d07a450004070740c0d4071b0615104902500448000803500c80c4440040c0300b440041303c0900e0859a42d09040150482a150b404c0b130f400602031110b54550301c1d80c00f01862054842c1030041c121941401c1014001ea1308114900d0051401c0014410020f8544401e0b42e0304804140c0d5401d032500114030481c089290350340c1003090821404101130221001e0780d080301d03000c2e52250808120700e4440e191000c9101da800425640401c508004c2d0350300182d0a081c0005111220745030160030f210b000d000203821548102ca000918a031071700d5082041c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 243352823 1250 243351573 243351607
    0x3120809070e07080a0e0708010606030608010513020a0312120f14010e011d0a0b030f030304060e010204051c0f0204050c091306050a0b0d02070b040309180b031f091403 74
    0x202c00324410049141c2190001c110640041480e540700d5280d500c41e018000381007108002401146009200241e1a48002801071403d4030482c0401e608050201e004086403208400c3c146d03402816000b40c850035a19140440c048040614003000080c0041e0942108644120285110410300101d00004004d055007084031042c1c01000008902100400c000044400c825203401020710b103502d0b141d5505600d4000905003150300681500a5450380345c10080c021000318804c6100301703020421a881074030440c0c02c0b0b0045020b4103030440c4484c04107840a02d4001802c407156842888407802d251903950203d01030341c8054a03500040705000c9030048403490218140e149208048804100040c82c0c140000d821300c066101d203a4240000181d1100234407030f01d0b0104d9404641120b500c15450400381f80007801c0083d41e02c58810002540e00369040010310780d0050179a901c400400030310212841e0a002d003d80241d14000a070415a560b00840c001903907134624507447d01c1750784003854035800c000e4002c107884 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 243354073 1250 243352823 243352829
    0xb0712050a0207140f030405040b120105010609060f0f1704150e0f100b0f010f090f0b0403020f0315010902031909122a08070c120f030f0504032006040312080907 71
    0x9178100c4060b42440c400d000080e14200c6070300300c50202d01000c1c43c50200305042100b000b610869400d01c00003054082e007000c980021541107690f0132080d441408000c441204580103c1c40c00110492001c0e40c0d500304000c549500180640401262404c81d00c400304121a60448010401e8201b05c019003c90300007480100030b1011a00320034000b248031100000c0d9540d000b107400364144604c0600180ca85489000d142020341103280d00f801c004d81d220080c0c000190480d1104a205001220034034269040200310320852202e5446100140c0c3d00b41940b860107500010880c0819400070980000da1309280c0c081d0381e14550094144850625a0b010010400c3c2444040b0b0121010300306600c03c0102c40791020120400d410220054036003200e8500828490165440140c034805c0036008441407040c00501c0790120f40c880c4c0c0310100084004901510903004074400980505c0b400b5202e0304a501c05400c41015400005014507d411b40b41d41d600e020304080c200c021303800108a0010032141c924104210000307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 243355323 1250 243354073 243354113
    0xc0108071b120212041d010f0e070e120d080411030c01120c020c0d0b070306081c0507050109051204030b07031e0e010923060c03040f0b0712050a0207 66
    0x30401414070048000070340030030001c10102103100c0d201107a0303100340032000c120b0300f000c000c255555079102c03500c0700d003030b1600f03000601104410400000c4400c00c42c010340d8201c41184882114664620006440c605071002032036030410818102e00b05410403d008910100c4100c0e215003a6500303060424840f42d00c1d002c10040e010794001450b009150f0380054141d5281c540741500030906010136501241042c00b9110500d411840000c03c1e10700304144000ca46104401035603081003c03d0781c03000b500da0340d510390300c4803035007400c11688202020500c180c0c001c0c10001d0042c40041007450032581c825140c0069500c0b0350003c0e04010500307004201c501100641c01003994542440040c500030661380c07030301d18a04044014140e4403081c2e224445000e400030070070280c010b124442d842c3c02c1404c85083c03500b100003400d1054010480011000c407280780a80e4029900003000044614050f6641d692080f00070303100d482072101e1000301c121840303a1800340030702c074528040300541c590b072840c580310b440b420401100e064 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 243356573 1250 243355323 243355337
    0x20318060a0e0303040b0c041203031b03270807141612030e010305060d0203010606030506040c1d2806030b0a0501050a081911030c1902060108030d1e0903020c010807 73
    0x214002d000090720b4005c0d030840a80d6459880c0c413003002d105441160b01144082e591090311006054241c1e00680d000100b001070410a28001c0b00118100c03a00000701910300d54824591020031040025080324861044010704d2815900b91a1050140d00448602c3c00071b500800f092038103040099005401403150001e07807019000103540c085d00da01c0701ea1040c01d04055950000400719542d13026800c0c40030b40c0240080002c6519641d0050190000f19003030346c0034030b00304040c45c016248541e46450f41200411004c10090702c440081019852810545420a00103004518544042a01110001c01550301e000600c82240c0c010b00546140a0f4090343c10300c5801e0205c0c5403030542008125601c21102c64100301003c08000c11031005003400344031154081008010460301c91401c10041403401040104400c00114070a0101c0c0c1c3d8141c2402401115003051180e80034803a407540241d03450402c0e5828007210413180c41e10f5081201c07069082540141c6c007501404109580205001d50000844c1c07030300b11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 243357823 1250 243356573 243356591
    0x1090b010807062c0112110307090906050f0105070b060a081608010507080108060a09020301021c202107020c22050901020a02030708160c0305030403031710050d0510020318060a 78
    0x6903241c582080e1242c140801241b154654400c191b000080074140c40c88070340d880c1d0400a00c0140540c1c101c3c0143d82c51513107003032808100d520b0160100440140b050756076502d01802d95a0703446040707002426403070f040000044d011400240c180190401102c0a045000c0054680704c4000d01751900500307a44244401000107202c1480c01081140c0d10070a0310740c010460820610203e0700901c01d081c010345480c2d0701a03000000098554103c1c0d0034100400342c03480503a05c054442d480051042c90344109150310a0b030003080c0714144820b541d5611041c03170300503525500c0c1d400b00410b2040508960010810460b4101194034450610400b9005240c01008509000d52520003070740e030744226130000c0c0852802044100782028109400c08140340d0158101c0ca8181e030764039045540340c0050101310049a0040f00400042ca03801c1411846203591942c019015480d28081c050040d0b030035101a144d50007181000340323000d10036000650060160309003011300c141030b40701120f0138240c01503d411040c2e0300b0070001e4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 243359073 1250 243357823 243357887
    0x412030b01030b1008090703050706020307020102010b0a0e06130f020d09021234180e120f18010e031b0f06040e010303030506061b03070c1d01031401090b01080706 72
    0x38481248145c1000b0200d070f21755404131894070615504c010103a10403550080364055000c00901600342c400e03002441000e02c2031080000f9206540501c001c0d51400000041e40e501d040d0030903c00d241c42d020400540b400100c1e01200503a480ba14000545079200d03046e0404500304950480312801d103200140c4000d25660f281140001c000703520703001042c0300e4150010b8114155000302c4004100040050040c0d40011030640054001036002d50344a00800407609502080d50701254006840030792054504080c122002c2c0c803040a01c0109410010740c034a0402c15902c1c104242103a0b2103e6820b1104642040d02c10000d20201c80b0401d24020700080c0020081d8a42249540f03041d260703d400c01181c81e40c0d4400200c1c019010f1044034050380c0101900034181b112004c401801414011024a0401c1d40c565210814400c0c038a4000789014801c0c0004101088a818541013843c110780c00100e054007084e2240104074200380c11000007600892002c014407500500c0d10302c1a42158899441140c05140304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 243360323 1250 243359073 243359089
    0xe011a0a0212030915090706020609030f0301051915030905160506090d0516060503010e1602030d0f200c070602010b01051206012102030601300908120412030b01030b 73
    0x110070b062000c00f10209510210034040540320303a103040203280f0f40b0b141c2000b246031354001902c45c040141c01020007080e804e14010084441074000f0510302d07883c43c2d2030042030013400c6450682109a400c3c0c4084080307985010b020515059140c0fa94000c1624411070070000d04000310481004004e8000315401c001079110356050303400043c4119201564240181000c1e8148008a201c406040317140040114078560880c000c0c50580c0c200c48080e07002a526045e1403508620040ca0800150388180f200240c2d05003d50003c0009802d1141c0124031110014240c880d20103192198210f030f403002044001c69040b040110384001d010b04e00c000e001d20140000003a0051181e0610110010300c0100082c101ea4003610400c000d820984507450f03105147c114404c3e00940084e01c0c0741e8000307070402e90000701c02c010030500c1e10105a84407400003581d407881140302000385000c950450f1400404d202c065101600160310a12407401580d00c44008440305000030101c40328036100605040c0f901100030703103079210001c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 243361573 1250 243360323 243360343
    0xe011202040f0603020d0204170a11010305040206040302090417040f0504050a0c090e1815040b06090105030601060302180307030302010608070b12010506090f030a0c05010905010c05190201180e011a0a02 89
    0x400503906c11b14554090080d10558000d001c184a141c10344e05082c100008039501c9030303401a5425038620510000445c00c1d114182d42c060740c060700500003440949413071001180c0080c81410310780c00348080416a544150010792080d00601d00380d0b01e04025505183c00340703a602c402d014400b0040d0110584001d00040c440d409000009001d41000074844230611002000e44c3c0d110030304803082001000250060420210381c200c54882500700481c0d002d00340702c039269044c0c42005002d02000d81c20028114001d4000801d0000d841d58140c04190b07040c0c50910000012f103010740e00224200d401e0040052030312001d0752240710102c1040200d5010048448220740c190359080310b6081d41e5903102000070700040c003800c940a6050081c0b01c809402c0003000e0280d401101d50130b881d441250741c0c1d6900151110000c688000c1d05641104013480d91b04041c0b01d20306540d4a2050401040642c0380e0990280c2811954014440c42e240140041c00700c41d41078450910243c00c4081ca076841d00e20f1607507009440c0c4901ca8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 243362823 1250 243361573 243361577
    0xf150108100908070c03110406061706012703080705010506010c080d020906210106080601020102070209010306150b04290a0c0b06130e061608013b070e011202040f06 73
    0x80102c2c820000b042e800c584101d80c00c0000c01c503400e07440741080e6003021600c0a5040c8a98030306030f0700143c981e000d02090090219092058200c039550a0015601c1c40800102c80001c00780903180309402e0611010490081c50040780c41c0d030744502840c03900a08480001d8800d0f814003801c064800001401c10084803104942c10a0150b161801403008c80e110f80107410106203070248589202d41d40b1082429024102c0d06248c1e100e652503100c0500680c200e100c2c101000c3e41003607075000144007003940c54000c20088200380c0e4004604980e208550f411342c1c2c000da080303002c540d18420744190f402c2171b0403015182c0384403602124514003a0544006000e00c849000000c211550341c900189441c1e4501000201c42c14003210141704125800311426154174046580b600c0344144039810f9111940b00300c0c07220b41a60002c80343d01806103516030038040d0100b04000d418103030312040c0038140f02d5000308500303450040030942c5807440c8880b503010014100180e44071460540900c10701c001c12144064070a1002101c4083c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 243364073 1250 243362823 243362831
    0x708060703150e01030303021903021c1104030206030903030403080610171906080d170609040b0405030c1b10080705030c071a040b07110604050a1101021507020f15010810 75
    0x90305140e0149102c41e406481240e1955000105060700b58004081d1054000002000489613441c2a400ca0003015684500ca0340d518900034800360040e80500b140803200401c0504040e643e80c0010110b601c110740001440d007020003880101a04403480302d802546c12107422103a055414030080c8056195004c10310303140c0040c0041a8501034007003540040c5400d4080511400b0388846d8626a9441d4010071080026282000c1c611940307075081c0c1c0c29010300f200070300078102030316a610703007100981c00a40f059965000400040001c02c1d001c00810440d04000c01c0780722801810001086040d803440c0305c0c0441840800c408001c6c3c100d5101c400c0303079404600811540d49644450030000002d102c50200310070048038060520090010300d4a01d2445079441e96100601190040022a202c0b40155401441a444003c504c000604075131603c10840034180b04584500c248441d44021681050303a1003005600156a400c02e500c0040c48a0242c03c1d00d0f501c80d809071942740c0040541e444543e03450310301c40190340f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 243365323 1250 243364073 243364091
    0x13090b06131503060c11030319050405070b0415090b0a0c03030e0a02040204090b030105060607030e010f03022511060a090510030e030d02091306060c0201110102090402160b06030708060703 83
    0x1d154004140d200a811040b40001d840c0c1c90800010325180c501c240200f0360307012940300c174120000708072031150880300c41c21031008102d0004c68000c0c00000e0001c5409005480b80403920b411a81c0203440100381c41e05e0500c08039040700a005d411000342ea00106141e034020492580d00c1500300c00e56080c0c4903814a80060070320050740c0554105410b00170025881800003e0014942d18036400840380d45200324006c0003152107020402050b84134151000b0049120f00c4030981566008007040d00c0d0303068040c1005450301c09003008400d544c50019402503400d80a8403844400d1140c1e030310360510036102c1540c5062030303c5e08601d400f8005401d14810385201d07103094102410018481d8001c030759008400b008403500d90b803402207a03802031b42023945040c0c010411200e40c0c1c0c1804c8074034041d41045501c680c45100401086070011504c240321800312100b159000c010100c1075494a20003800c001119040310403d005e443c0c9000305400b48040c025600c26480000f0500c121f6001081581e0041c000b420700050300b080e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 243366573 1250 243365323 243365359
    0x1509090c26073006060504050102070b0310053105010812030c19020a1b0303050313031710051201020405030319020f061815070503061203040308031513090b06 70
    0x100e41c02040c000f4214081d410880488000c1050340c2a4240035001c1c000c00d500c0362802c4803a8002c40c85606d00581c081d01003000200c48840003982c10040410001890030740f52004201040580d000403070802e251030780718200015002c541307880601c4049400780b0107035160811280e96011512442e400351030000001c6030755645018110380c100307201c60020f004e07501d10b045000303521000e503c1e07003c1d035508840601007185581a01c108500342c85c2d05441c2c150a6848044d03806c00007201c0c2c800d00b2401c0c03042440344110902c05080a0502c5401c00005080c106405d01c41031003003a4208260002c00d036070051000340142d0381c0110650725604d510010b940c030071411040b0201c0c81d240b4403111443e501d005180c1170082816207044242e034089008802c9442599272402c240c00f4000084403840700048003480890903528202c0c070fa4014411a4031300300e0f420591642c650083c558819a600503e0840310950800203017845400360440e00c660a404021038046500da50450410061080c0d116500c00700440f10310036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 243367823 1250 243366573 243366587
    0x1005090112060b1b010c0c0311030d0f020901020c0a03050c04050c0f0403150c050909041e05060a09020f010c150207061407030b0915031002070c1509090c2607 70
    0x40c1100c1072240650380c00a50300326911241304a00c80c1c0004884542940c1e005006074100c4503e51741d1091640e00080d14115041c0c1d00240c1e0b262440c1c0410410040d40c00300300c3c003a0641c882d010f00300050b03075800c044001a182007001d032050340c007502240e842000030400114040a00b0142600e01050603030380d40b0701c2c220407846004401e44d146000400c0100a000c1101d100c10031a18140c207040203001070416040c1e681d40180201c2c40e034406012400100064201c0d124400700090010f40480032655542e0f40f9420b01400310750f19002030b9504c4a0704015454140d607441103252080c2001340d030600c203d48500106410817445000e403250002843c2c0c082102c1c0ba40300410b403030440c000c0d102060a0000c0028080c0c00074018845c03082041101103100c020a00089501240c8014010801a561100700c0c00180d0081e030020b840c40b900306c1000085c5903400c4a0000030401c0ca640e2814425030500c00b07148100d440488810041041c2c440014400c1d003074490002d040c41d090b00c01807410365903507810115812 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 243369073 1250 243367823 243367847
    0x6030f03090503010f0b130c050d181511040605090f0a121709010c06090204060e01030b040303051506091905041a03010605030307031403040615120302010b030c10050901 75
    0x290502180281455842405082500c0d0100c009021110711224103106441294400c0703035001301c0111000009092561007514842210b00f00b0710304085040071494112114000c1e84074840d115041484d04120405100e44580610f40c1010440d50008070410002c80c090b078018141444030002d0861441c1c0e85103003020700d04a01c0189a851010380304d1001c000304040880301143e1040180e50000d42e0525050156001d42c00180d6a04282c15001e450303550103406400c0f401c1e40c02560340c0c04082003000b11082000e01940c014140c40c00c603820b0a140080c2203c1009210b0001092a08102c0700c50740c2d0399000700d40d2560800c540096101041e503a0100c8120301c0d6500507a4000d03d0a540d500c56800f50a00c00c54019208074001c01984c1c1d600e0003071503101d00c20707100020000389000e018070601c01da44002550700a4017402c80058140b01510346100180820f0300143c644204070900c04081681c24041c40403c01000e4026020910000f030118071040c445078440d1080c03003404174016038a0b034848c034201014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 243370323 1250 243369073 243369083
    0xe1510170a08130801150602030f0913050a02030f100317031f0603150b12010905090f0f0c100c0203060c1b0a080415050f030a0b12010c08070201150302220603 70
    0x81c1d480541ca0f1003404410f144a034030344650038081c4c0c0030f84020a81d03140c0c8084549503005180350521108080d19294007160010758040c4c4141880c0304851518441d0743e215000b00840182c0ea401c080c00a000701c9080107044200d4030320360040c00d03c0052078054110030301105603041c460b12600c9a008080c030f184642400c5100b0850103820000301c6036032542000f90311104105000403c40d0721807806203081d106138171005408041d400f004205402d038a13403150794800b010800390384034507140908403420052518040445680f1550b03820000d450304d85540341c0078032946c0c20304100e0b980c2d0f154080b03034440100411092030140045003041d0f001a0107010340c2c3c80181d008050711b049078800d2828280c01c0d0068002d248168450002c00b1503420f0260003218100012404c0c900c0c20340d60b8001034080942528801c05401040c102e02000c04140240a1004440030030b8036103c1c010b02d040a03009084400410b42c81500401c03100c0f0410160312004002003180241407001d0075218101d1710b012011b81a03951000382 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 243371573 1250 243370323 243370327
    0x21903151e1802190e0f040201032405010e040507120c051b03120a27052d1b010509011b0b1f1509060f170a0e1510170a08 54
    0x21032191071502d040e294600c02c8035400c01c01503032801c0114000090f8000d90301c0d24200d85012640c1c6080e80c1c2401c5510501c1413402080325502854408059181d8131889410301031301103014011580c014a84d1a0301190641d41005185840c0c41e0080520b03440490044000c4c2d40d50b208540c14074400d1003110710805040f00c00701088658424219503990101040700100d640c18008240f41c01c40d08c1c080c0d084200c2d05507a102a64003c10701c01080303030f0030000c08100c0d024860500148002562460211080c0750b01c8648955130115111203141003000b042c01c924584a000303810030079240e8000080c2c0780c0b040003e1905007440301204a42c2c1009400510020389545041e800301b00d050328032240030f00850b29102201c00f85003030f9591400111040b6a490507004500ba543c406d00c881c070301c00d030030100c200c00c00d500d007055000d07170000030912075030030140c0700d81c00101e0703c842152240f52130800041a848001901e448502d20700765821480b0502c0501401c541d1302d155002840c012103081190043c44c50300882015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 243372823 1250 243371573 243371591
    0x408090117011211030313180f050f150909100209060d020c030c16050105040308221404061d060402131d041127060102030c070b0403021903151e 64
    0x3414450081c008954025a42c42c0c080560708022007910b60300b00005c0f45047c51541024030003801b521515072241c20b400d41d1060025030b41409030141901401c0d5450118030681440200f24910050a441943c0111010014050003a00019042040038000030005850f03660400c00100944504082d019240c0e00201c0d00440c40c0c070011004111203144502140c48203070216511010200562045c240441c0042c00200f0105000d20000c102c1c0124400f4011160303242e01a501c2c4c82100290840d0407184044495076003203080c0f6114000180a44981231600d0703012200042c000282d0040c49030b03003d281c01261080140d5655803c01000c2c00d50b64240100500054400c01d00c100c10458040c0d032807100c10429415142000c560540e500500100110f07201483c0c40c8100c8c0b02c1076005440141140700c10080346150030404c1c01401c2c050016003100380d96451440c01080f840d600349905540c0403c0c1805000c00c0001d0280040084003803601e280420120124010a6a15038503240442046801e150502e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 243374073 1250 243372823 243372839
    0x207080301090b0a0b0703081e041202010c0219020d03090302030d05030906100303080a0903141201030c050402090303040e0a0f021b010606112a0301060b1306020c0108040809011701 80
    0x51816140c08090422500c003e490400085881c948941010f02004010800c0420301c01d40c2110350180004007a100500c900403840240170404448c2518801007507051180c2032075084c060740c190003c6900c01003030450b88100d0703058403002e40f0060003481600040c8248c010507000300b403028000c0d03400806039201014550409042681708403980401030054100241e4042607900c2c8540c142c80d0143e82c0c2c1c5100343d0f100b00d129401003a805000390300788405100410b4074500c228004101c3c9540c02c007a040c13103951440c41c1a036108002500098441c81c0141b00c4224162000820754040303e003010144079054440805010007007048801030400180001414002c8042a036240340729000702034003c02429541d01d83c203c2e0740c076041591800064000d80d14100051303102900c1441781c0109210540400070381d000000342150310b00d900c0f0b00da001c080481d840510f82c1440d0703207400043c2051b0010707003503d0340f00d031000a02d40c140c000c100809802006c0b0700481540d100e00c451b001000002c0460048658480c161 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 243375323 1250 243374073 243374077
    0x101403100216031b0b1801140901090606140f090712020409021801090608060d150c020d0f02070b1b0a150b030d03060b040e060d0f11130504111201060801020708 71
    0x1c180c0c0428456205070b03113480c0d01410030709500b0350803201e80c1403540c86070342035092809200314a202c1c99640320308040c0308180802119a005010140c00040c032400240b801c0c0c401d645265100c40070030180c100c20344150352520401e4001d80c9508682d41c0c0c02c140e450786400c0d182c6c2c000355000320740080d2001c41c0c04640003c1c1c580c01414580005100f42c5801c01c0440011101402c080c02420000b50281000c00c4482c146464040305481c40740f0b9460a00020a03980e0000b1240d03046404401a40045100c03039003150071003e00500001c00744080c0500f0b90a140e6841018450510180300d41e1840300304500c003122091041100213980101c080d0402104080f02c0c070040d010500c16140700340251021848228086d00c00c000440320b1510080c1d04103882c3c041c6c00c00240030002c008940240420b8102070014402022840545200741100c00040300d030003080c4642040410894400d240c038003000e12000c10010300c680000c104048903003001c442042805079014101c9940040311560010031240c00300311f88100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 243376573 1250 243375323 243375367
    0x29010b030f0906090a020f06090319140a0b040209060103090f1b05010504050a0911121305060c0909041205132301020312040f17070f15051014031002 66
    0x71408400303440b00203459885120648191080c0d40c80310b08030000500706940e08043c414002801d46003000f0b402c03404a410b184440b4100340c0d401c029941000c040211841140c241d410501c8010108a9000d0b5250605601d018101a20401a040008034181c0c031035000400201d5001c588403034240f04500c1d11903001c0402c00410850390390701a002080c0341d445001030740d0031641e00410318210540b400c2d82c44001003140c01c0d803850840f441081040d11413140100703c10b0003803000d4510352042203141d0070f00790b0600e800504078118000d0100488655a510a101140c2142d00104d810041408a803400d80b014480e0302107021140c070481c44001507030400c10800002100202504550019030302004a0b00c070710400301080c01034504200401c01064054094002c180d10803081e000b614005003800199a40100303004840b0300d10600c0e841001c008111003168403000249100b807219060080c000c465040c120b01900b2500940b8500c407440c269010800302c2040c000d0182d04640d0380785682c20544140c1010300c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 243377823 1250 243376573 243376591
    0x3030c140606060406080a06051207031e0206191101110c010614060712020c030a11030c0a08100b0f04050a05091e0613080c2e050103050a29010b03 65
    0xd001451424030114016108000080c1030030319190401e038050ba03481c1000f038500c060300307691400045242d803200381e000350441c84950014400c1a145241001c0d030300060300780340840c0044070b40740b901c011388a610030355410b285442c02000e0724812080c8210b56180b071144041c0e07015802e2078031155035114082d0040c1b05511005000b4055552961002d40b088072503082c200745c20000030002c420100704800c4c0507982c02c52841c41501c6400c04074000203481c100c80d40c601500e001412070303d2145503103010045066810b400740d4010788500e10307009400e42c69010020a0f510310a0b00e8030b41900fa036a81e05c0c2c0f035070080c8800c010000c102e01e080038103080c2c1c0148000c984aa141e441008208400d40b00d10301e00c481d02e40c650a0000703103e070365500901410541c41d1010201d03011103061000f03a40f00300f405e02680c8010b04185601074140040c240f0160f800001c04040b80311283d142c0300043c40481d4000c0352a50003a50400c240c0d00320614841e614140f540700507949030101c078910500101d5041544401180210168 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 243379073 1250 243377823 243377843
    0x150a05030f1e0f070807090501151706030102090603040f02041404081806310501030e0c1912030206010303020115050906010e03120406020f010e070b1806070c03030c 73
    0xa609050303072000c06450721401c0e07910030380014060107011481c0c0d00000d8201c1c2d080c0c0d1211421101d0003860501c06070401c10881e00492000e1210f43c0d110b1107090700500f4220010101c0245003030019210345054161044003444001c00101162425012651400d00161032140e03a4902030038580c410032200e440c128480d41c103000b8480485003884096a0050b0740203003820781391450300d6001002c42070109942e070303800c600c0038071418285d51760248007594401f0071404100075111608002400c6240150046410315107010050346d2600c170005402034994400703651085d01c030b40b901c0311400b4030404264001040254a14008002c140e80032400c14101d80c401d4009110003190188a41c280304030900446030092551400101250310603840100700d408090160303080341e4030500c071006556009070040d80140e401490b04c2860f405003441980c0307618444101410469091000c1d28103281b04911030124200d01555001e5801d640c1d00b021200815801301c00a90216581d00d401b6220007100e44058070b00202c0c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 243380323 1250 243379073 243379079
    0x5030610053c0a080c09040612050606091f0b13090e3d05060d02040c02010c090e09061906080604030c02040e060601021f020c0607021507030b03030306041a09150a 72
    0x2940c01a0b401000d010b89131800140d4404440013859000011842c1c0c1c001d889800016174191b0510880842c14060000380074223140038007d1149010019204051820382200403460340d0301100041000d41e0000301c0171603510140306902006440081d044905003614042251b402401c0010320565070b41d110850380b00d999016105a08442030780c8005950310b400303111404c80140c2000f81d10256000d8401880309120175125004201114840160540580e66039403c03402c1050300300c4091350007485250803550701454010200c50710381e80040d0004644805802d12084c1280003034000c10090540f44046404914090400404044031120240e01503440c0445215030304078049007084c07043d0300c1a001805a542200880b409001c502056000f086509021003000b10a013440180c0c0120f01c160b006045140c1c0d5841e039500da1fa00091318440605217071100e2170866450100136250321620450b4002051551089082e4040789800e041950008a82082001c0000a10030b451034006040c6d07402c20105c0d031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 243381573 1250 243380323 243380437
    0x718090c0f1d0601020a140c0111191e140606040b0f0a21021302041a04031205030403140a02060702010b040605030705060f090d080307120b010503061005 68
    0x20203004801d42000070003003040100049403140e0f904400180704a0b003010f00d15450f0b6281c0d08005034582c0300c3e2038002244c3c6140a41e40060800503101c0000c000e06080360007070341c00d001c04040609008052021090f244424840c403c03000303640707040d0480e29040344071000c003035560b4880c42c007296420300c141d2508004411a08042c0d6000c14042c0000c0d00c520852810500810b084244450340d03100f014001500b0300c80180c071208120f200070f84150b1000b680352404d0440d03088a03c10340b07100001103008244010400300c0c208035000b0b1412280d134201103680351550b090440341c1c02c030f202c000c40c0003c5500003520356149500080030761080d01142e00800c0041252810081a20120300c240b80d4558028102800b05151400081c61210303903d5902c58a03010710b105c0440c140c403840c200d090ba0007140210400024640020b01044150800b007010818201100000b070864000546002d01401e98616010350241c001d070b0484620150b00b400c0b140780b4040e40025040c8030300b078145600034503000000003164568 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 243382823 1250 243381573 243381599
    0x612100f12080a12021905040518040f111f020a02030c240306060c060403080f0901060e010303030915060803040602151b0708093007180e0718090c 65
    0x2d52008401e841e000604000300c601c1d41070f4111401e0415401c01080131001c0104e00403000d6030310759850340e41d242d80c5400c4c01c12103008110750341c0e41441c004e210100000a4a85070030201c1c515442407500d0360709030749007010524480c04c00c1c1e1403072031148103245241a489e40008007807400c00c1c8210100c860381154a418820f007900c40e00d2f0001e0082c20f01d10000c020005040f030240d544200040c21081c1071106141960345401015141a0301094161040c0300c40707500000c40865000c5074420003071048a02c0d040c0a01c02c3e0201c1480081c04141c1d440c6091000c000308140141015010035000f0300c941d9490740421034807030f4130a21540703016202e030b062010030509100e80c0017031040d05000300080c4c07040c1c0445802052940110000c4601c1c840c2002440c0e80c660390500968485c01102c0c0401850340ca00d841030304050b498074010300e1195804000c0801540721020240c128180340c409011450701d0304100e00a160000e0380d080024000480f05031000e1074103d03a0700409289000b403012444540da540f4140c4110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 243384073 1250 243382823 243382859
    0x209120f0606101211030601110705010f1202090301110415020c030a030e12010501060c03030606030213031103010b030a050307060507180501081503060a14010f0506040e060612100f 80
    0x1075000580000e1039450700101105030b2411908107080c402c0c20008243d011900c40a204030400383c80442401000d59106418444062030103004011a9003014006130200344104202e00400600241e4060310746201e4054a20710310018000340f0604205510340704041e0014054502c2c000c2c00101912410742c4009200404114050007501040c0c243d903d00702c0303103a045140220b42004440f0a011602d420902c24180204115030799031941c0d003898a03001702602c001c1c0d4041010540184002c0d06401801045101140d5010814645480151012901500040d04469498020319960300c0511201000800c0400d1003850200720951761250309842142050b4009484910044801d001e41c0d401202c070284c01410008a1402008070705001070314002c0b085400d03c10f070700c1c1c607982120f5a40542085e0b05003d000303248081c4000354284030100d1458040c610030780b4109a140c0f0003050362500e6a00441d15100000d12402d0341a140c500310304403401e001407065030060103013108001121096240c4150758 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 243385323 1250 243384073 243384103
    0x6280e040603080d090809130501080d210b120321100f030609150c0216140f130b0307031412031b0904060e0108010903030f050402061c0204030b0a020912 68
    0x90140301d801c44d600621600c0d000b22842c1d003007004480b10941c1c480016a4080351040706c00308a546c10401503e0030501180003240a01078216080101c000480c2191014031031544000624402d444000580180b190a00380c4d01c80e020003d4010343d03100d5100810032031075410030440c40d8030340c50352108024419490b2044410010000c4070500c00101c403600142102401001c4041e002c07203103154401c08450921010701e000da0300c03100500d8814480302c40090001e000305032020200307031001d0022503091000c5000039440f810202038003844400e21940104030035070707028045035009078607860602403024018016140e02c4c4181c0e07165032050124030080360305c11991040a2444080191210030f0a170b004480e540f540991903000c003203420259098814000d00e0134a0001c40d40c1c4005003009000c480e0420007108059043c407040002684400040710314444040d14400c8590001c482000024022600001d00c614840e03000d0208940407600500704940b400c4411680c21542c0c51941d07661043d0315904820 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 243386573 1250 243385323 243385327
    0x204020d0c092103050708070803070306170a0215090a1d04050f010203090a080903150703020a0e010206010f06050307020f01090c031109060d0b07030e1911060f03041106280e04060308 81
    0xf00081c400c5c4013402c1603030321030401c4a042210a1b0f80e0b001058100300e550900190380c0e85c800f0403002e4094410007480306110001744c0a4402c20b500411580850343d40c5080285000041c04030352525092101ba0040541500c80303400f19040185c010b840a0713040d04e050b03c0c64450601c1c1d91004240601c2264001c82c401801410441c0e8555142d440d5500080d50140c0c0c18044d02a17902c40802c42a00d8052007511580d400694502c2c4014014043c2120340454a04543c0310000607c000c0c000c20300450140c0d415814055241d0341d543c4d504a00d003011006800001d5424141d20900b0040e4404050007543e1203511030f0790341d690500c01801b405400c21129998001040d03c02c81011494040890350407840629001c2090000e21090703614002e02c0111602130701200300c0960060218440805540e00400c4031aa46481140307201c0c90428040584043c1c441c40407010201407275615a402c4a0310690240381141c0000d504060307000001d54901c1030800400c600f220148006d01d1b00b8800c15007038a0344199094 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 243387823 1250 243386573 243386639
    0x60a0e040b010903080a2007030506010512010204050d1202010c030c0e130f02210a0603080706020a0314010b03150108090d03090f02060c100605040b090609040507030204020d0c09 79
    0x80040c018100c0080c0c14070001c1c40c008404250844010300709042e0079290001007d0080381e451021845180c12646e6641100605200096021491504507482215088900e51108103064024416544843d0b8030040c41400074040002c21044080c140785141c000308142d601c1d002080e029954a080c100300018017404865101d1300d0241824418059800030014044506180320002c9900c6500802d10300811003010040c56101032000c0c90b48000014400c0c48070b00d16551f210000c80c0a01c0000030141600415011802c62180d03006110101d003901e2005d546580d00d8032000d816600c240c0740303902030a08c0c020014842d54007500c14640210346803401080c150a45034011802401a94070440f000c0d10080d61800250340c44001400e4181e406502400a05032010b0000088032120783c0020302583c02c0194101e00e6a803540350180d4404400d0341c00d44500c0d88c4502c0e005051000b2504001d50103440490a200b65080651104045800e65100e0b407006540f03600003000d6000e40d06940d20201d0034801401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 243389073 1250 243387823 243387829
    0xe030a11101701260d2c06030106050702030f010c02030d23010602010b010801060e0a03080304020105120403020c030706050304080711190e0f0a1401140d020307081605060a0e 77
    0x4810380070b880c00ea1005400b4501c0010280001c0e401548400d003522113039809828a80c00900184d0441801002d641d48214406400e100426070540e1540000c48140402052100707021891150028005070340e1f982c50348005001e03074004038403e901070300c00c001f0100804041449031381d25585080e00210304204da004510400703011035482e1207003028003c95100c1504400388003041d0182c00d081e00003064580440e0001807005e44164846c804004400703c4401c040c1d10340280c44400e50360000d441a03030f00d80e12800141c485216842a294034030202204010900d0350125503628001c404505480040c1e507111000c61b102d0005031000340c4001030410401d0005144010030004518001d08903000d0010b40070f10100140010b540060b0f05041d54200300640c044902d014681d01a600c8241001716404200c0c4408550205028019104160101c1800941d071540ba40d0071406034010211110304e510380d0900c54403025100340703e00f030010203850b011505180c008143c98400c0a20354074414022286810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 243390323 1250 243389073 243389089
    0x3100e031b0f0d0219030e040204120b040506010626040512040906090f0204080c010c0204111308010b01081303141b0c0102060901020a0e0d0c080f0d0e030a11 70
    0x1009400d10040201a01e1044040074090394101d400014142c0c68156000503400c1106820003d0110740041d054180850100c190406115802d49000d03d43d208441d00440d0091284c1d8000c01e40018030a40340204102a03820507520940c416419101035903070300e03070003560001140c50074600d2500700c00c888103240c407240c40d80385941f2a0080044a48442070b001c0098841d500503000b04610b03035100c502c10302c03100320755000c0d400341c003490704404510706407415151513182c401420301d26042080860400040d95900c4d00240d1104c040c84c650240d4030b5a520302d080540b41068031565a003542001007a103125801020060312030443c01080c0e030542000b5a404542103601481e180303030540d0091164820071b0f00800f99040312100600010010074aa40e000685007040040041c001c0741e0040003006080c5521407021209084140c031040c501000c0d0f0b24011400d000d454000214174402c80c013640c4e00000703000500340b00c910103985400c112550004141610344170740d54800350003000e100822040608201d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 243391573 1250 243390323 243390341
    0x30c07020910050d080a0806031501150e0402030705070c050f1f02011107080703020f07052404030203031801080f010e0c0a171017030327070306050703090b0c07020310 74
    0x203002c024850300d07800050500f01c00b031441070354601c03804103d03000b406070407503907107a0050000c600a040701170304840e46240a01e01400b9881025500c02c040300520341c040c4a0300d052110005205545034904040000c011703030022942501c0310303c1000000205e500f0114152604030b01c010f0503008445006480e03e410488504089804540d03075225201c0b290f100000c0505840e9201d641c050f540c1d00c0e40340c1002441c1c4061050262941d80100104100325582d00680c00c3c2c0c1038011458942c121004a08450b1305030003940d001940502001520b0031030f15080b41c40414102600740c0700c2c5407080e00c810b410509580405d000d886014500b0740c011580700305002d4064a04010030780b03016442071200d011500d0f5030181c10f0703803502c0003166030842c1030040801400d481075a81d546000150301310701e482c140c0b9250b4420b02c02c120b140c1c20f8030f03803030003603002040e0a0041002440e00320300c0500140c100844018018a8118815034514070f4890101c0e5181807104210f0307080b260018020042001088100401002c00780 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 243392823 1250 243391573 243391591
    0x1e04030503042304020315040c1115090f0d0c020904062d0c030c09050405090a08030115080a0c020c010806130f02090f09010f0308030403050f121803030c070209 71
    0x4000080040d808200030006400190208000103850f03464141c68400581c600c2ca00c158014802c101c0d81c10307001154603801c10004c48020514040060b0242c036452101c1d0000707161b43c040c1c8240541d01126000c917640c0541590001c07181c5180000c07031010744403040c2c0c2c160403000071406600307100549002d150280c0c2144c001c2900082d1500039030007203003030800d00d400c8034003820001003601a00f041a600c40c0d80800e400d0303801c05000b8101030b80380c01088078a40b401000d2049640d10041002d4610402c02c4236021984200c2c1d0543e20350f1a651020164101100e2060000d40c0c0350002440e1900c26018206c4190201d800520000d041d20005540040700107000d107802200e02c02440541c01001d0040c0c95403104101c1c001a6039840c1030007403000302c0782d00c880b02c50301034000c1d04e004004484d03038a012101140e41200c07540340c6035122071404407014130618000f201d00c00b10114103890015a408005401441c0e00d03000c81d07040242e07103542c0d5901c80c00216031007551940e00b88518405800c050041c2c07940a0401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 243394073 1250 243392823 243392827
    0x15070c03080907052106090705060405091504020a05040f05060f0d05090a080d090507050607050c01050c03071b061b170a02010204050a030501020a2706030c02100507080702010609111e 81
    0x1342d40401e4203052081c40722080c121200141c442e41c00c10070b10229800c102d5410103000c48600b0003011421501c00c6129460040312003000040031720305406000c0360b042500600555030389000002c0186560802c0c0140e00080402c03180c0014070b46041412a25900e4401c03801a050513401c0610300020300700140800d0860180322503170000603010b10700800e001c411055001940b5041418118601f010603040380340141020407a0b04041180003d51243c1c403102481e10720340d25011002c0c21400c60044580040940c000c7d2a2a603c41014210242040d02d0140da1145800d0085074400322000c1000c0030003406114921415854482c1010000c04684d00180005031070305036624040303604503429078001c6d1016540440c01d081c403a58841600400381007505a03050480111a0300c928078001c0610849013455a80c0d050000b00c00d000740b080000d201d1410b10100164505114043e11556003100e5210055182100101d2240c0c035038424000c0810104903454100541890010b0f00c400e24081501058001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 243395323 1250 243394073 243394079
    0xe06090a0911030f24010828150f0f1a040b0f03030408060121030e10030f1802031002070f020603060105041a19050304030c23010609050915070c03080907 68
    0x410404c51486000c4000148031004001d4400000320b500300e481306146140320070040100c080300260320410382c0c26001e808180c80b102c01c000d00850251030140184070840090b0085544e00301c55011600382a007002c000d01810400b00d42420449807500001150034140c8180d0031910b0030258042c0d0100d5002505c007210350f0200200091560700140c1c4507002980c8008014828468450f42203034078a185003030321900c01303d4030b079401402450420722402d0082109142c443c0c4868803d030400c0041e15500f5608011640c25580c658960940380c40069000c0c2c811002c207040f80c80782620803145a41e40012817030b6224480c50b400c1040c036520160116040003010300c00841c0005810241003000000008004d6035171003007a42e010350b10001c2031188400e2000a104000100340c0100d000c824044d03118001d03111103e442e0401121045202d007078207000350728040c2e0216190b2450b500c0f8074061105d8404407580307103600481c9540d03004011127481c00005e5a48840c00b001a004500d10703030b08107001205850b45651 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 243396573 1250 243395323 243395329
    0x310091e240f090507030515040f2a06020606100809031608091c1502070803010605070c03061802150901090510030e0a0c05090f060303090d020a030609110a0e06090a0911 75
    0xf144001501c0c83c0c0c020900c10410044100716042c05000300c3d00c040c0546103000d8558441c4004082d0340a0014a001018106404a201943d1580d82040c20030241c07030589400b0025601c00d81201c110b4041e10b5400e00043c41c0c1e40c000d281c03203442100c0c124000c40c6480455082c0c0403940c0203140003103807102014082003202d1b580d0011414462404a1440180061a400c1c48950008200e0643d010030348100311810228001808a0341580d200c2d0401507620205803402546185550340045c1c84507241c40000c802040400e14445281402160001803040801409030003500c09c16140380e01040c81e06008200905001e100c80402203000d050004006147d00078060412030114000c40c2c01500c503030b5007403102d0b1802440c2c65030070a906d602a0212440c2c400701196491140d429040c1c40307550401c0d052411541c070f222144010310340c850f9050060309031519244582c6031070152082e21540c3e002c0b038003007031100c4c1c9003e200303100b0100180b0740354450315042c207268020110b503481030f11002000c561100b80c0d91 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 243397823 1250 243396573 243396581
    0x18030804050d020303120a020a09091a01030e0a020d06060f0609080d030507090905132001080c13030c091a060703020c06070c1508040c1a190504050310091e240f 71
    0x107d0701043c05a644c6601942c01001c4017100c2c1c120606031450004c801e4204a81c0b00110141c03400300382000211a0b5440b000c1c2803401c610004001e50243c4500c0c80038007006000c1d0800b00485070403441e4903002984030341c41038412101e0b5002d980b5a0741d00007420103070064480d420240e04524030341464440c0940301c5200e101603078422159803501280c080d02060810403100003c403141050201d001d48a0700c9208002801c9a2000d410f0199018000c580b0005400e04a0000401560b209034001c0d01940c2d2542c1c1000600480f0030718449035000030300c1c9100f140c201740007120b225942c96800f518071954510300b0001250071810042d0385160446038041030349203100d0807440c0c112070b45440303495244c50b203440c08030018411500204910a5403e4803121517482c03a20955000a0810717054240c0200c039600121094003a6500c181e0f4184030301030b0711001e28005540301c0155035014228000128050603188080f1801c001001030030250907010440c4070799003440d2415040081d482001c1000f010650540b0161 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 243399073 1250 243397823 243397831
    0x90c06020a080f1b120c0601050f0609010c03270e0714030708220b040b09241807181104050a180b0406060905130506010516030c050601090c18030804050d02030312 72
    0x45c00b000521600b180808024043c0144001c40390030301500c080101050f110b0190340306241c144500c41e10381404050040480c4001e030f1084139125180b00e41c080c441c00c036000d0102e124042407100c066021811407481a0700461034030203444149407441e00e0383c14007120081c030000e02c03111b18801002285001c410f0722055854050380100110103050070701e410800c41e404005030500c07506901c000084982da1841a2010003850400d45407540d55941d010010007080c00c0c003044c2000207018400b40426034008140f43d6228401c08040c1c2000000c100d10400c0c84284900d0260903444000c7c204200101c1400e4418644500e00d60308000c070301c0c8031100000c5400d940d055005100400c0400724140032504004a40e4051200c1d6030100b0320840c1840300c000f80032071040c8041500c14514820a0101f8140601c40241c083c41e40b080c121046503a4a000c0440100030b40e0310808006100803205a80b8401d24070680b02c11f680d00720340039030300c0e10340390504000d603041c45aa000c07038050000380b00102c0143d42544c0a50b00c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 243400323 1250 243399073 243399103
    0x1060e07031b210e01020408010203011a07170903031908090c0603100306021b07090b120f0c130b04090615120b0f0703020c0a06090c06020a080f1b 65
    0x22a0400490140c1503840ca03001ca65400b602c4803540082c0c6a83c02050381030142144040c03503003000343c03000002001c0c10036800842c43d690b00000d000203003084150300450403a001016607044110042c85602000c0c4550140500305e0035406116102119910f001010b07d075100400b00ca14124030360220450410282f66250302241081040180d078035000d001c1480864000c44002d4558946003403000380034406808060502a8040b031a45c00034400081e49101a21410381103a0707040e80e07140240c001500000300707402c1c00b1f002c01c0600303a1009000080c0d45c01c180c0465601074204002404207000e0601e40a9204071300085e141c3d081012551600d105404509001d07200c081002d0b01110003036850508141e00428040042808520210344441140390f0824040384480d241030325541c070110003a00030040300340254080c150360f0342c0c10440301e41e105079282403248650305401a607442080c2d0f200d103281700d4003500521040043d5603008900138010950345503140c6101140102c20460545002030003944412 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 243401573 1250 243400323 243400349
    0xa05010b09010909030504090e0f1920030c040b0102100e030903010606051204110d0b01060509040b0a0501020a0b04051510060e030a080d1a1906170402010f0c0809030106 75
    0x61907081404800340900700c040d109001e040881d940041081c842d6101d20039955a0319101c12030202402e0080c1da10494440303003210304616000f4000803400d061104201e490281c0c035140449002004442084a800010301a1001c08486010700010b4460f5422a6045005405d44051511072078850a44070a0000c07004580b20b1103010185800c407521504000309110302800b10b40e41c0d041200c18030980c420b92001001e1000003001001c5646079000c0c0c00c000740305008800c00441c40303541c410003500f0480703411142030242c1d1040700180803400a05005050060304100c038408080340300c0780d46442c6c02034810000c41d911001c48400285124400b43c901444482300c207401044901d45c02000c04c00c0080c0b04502806228000356560382081c8030304908203041c03581303c10300c0c000c840c027140302c1c04c072022000030740310001101d200c1504402e11100c80c0100f03004102c0350064482640040e000f850701c1254181c403800141c0080c0c1000341c45106444108546500c1e04001c0d840c065142070195000600801010075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 243402823 1250 243401573 243401591
    0x6020d1b150e030a11060f090a14011b120c031413020a0302030106080c1201050601171801052508010e0a02030c070501141e0f0f07111c030b060301120204050601110a0501 75
    0xd401d282d005480c47c0d00c0c80c0284c01c00d008501c18045485a0001d41c0710520303000c450408600030f0b0141c5248442d600c0c03065201c0c5981e800103508050300c0d5001e1000c0d0b50f01000615440c040641c11242e0030b141c3c46d62030b016210300003000044400344a00c04180001c0030103d00551320340c000f80c00c2d10081d420002d41d58100c001003e540c0d06000c0e0368150410080f000030301051900380002050551380e0081e040e0b00010050106103030880c100041c90803010448028032081c584507a010030500400c8000c1c10158000001103482ca03440b075488241a80d404c007005140c184c2b81c060502029400141c81b0021303003c401c100325800541c6c01d01c20082d89801c030b021501020314100c1000800038460300c280044440191081004617041d003035200b907018802c0941071031030340c41d5035408403145c05e410119141c480c4643e0844030303807130307400e0304080c0509041503601845444a21000d1019900081c803c151000c115098110300518080e044154001c0f410f1404004280c0c819090514007100d03142d054807a81d40d120041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 243404073 1250 243402823 243402857
    0x20114011d10060509090c04230108011d1306021201030c03110f10111c0c060f0207031d062b0f0213090515120706020d1b150e030a 58
    0x1c5680300840b8440b01904030b00d0040b000d043d500c035001d03885204030203900000d03250341200d8042d01c003e8035440102c0346000c145040301010011001c3c003518045180c55000003040250741e0760190719104032140c40c5125842d140c0061550340c2c0010310807245281c00340a00b4190901c81d6007010b000310302900c1541038151440c24400072124980f03d120b4042c2d400079001c00101d484004941d0704014981c034012200c090004045400e00b11381019032005a810002903040795a40003010060b1240114010841a4144000d2208030b12035080e0081c0450241c5154280750351010020269624015003114a810102050072500038803c00000d01d540c40c81d003080c00c4d140b510710700c14403078003000322141103203402c2114450500012545c41202507441e1140c0000300c1e00b0340051070f014100c1d500a081010f042c14040f0301c0d1030f1200500e0064a00500c601780144406610803444107200803059840c0c1d840c1c80d00b254590303103458011070240c6400d07103440f42801c0d2032845003000101000310250351245100e00085500b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 243405323 1250 243404073 243404129
    0xe0111040303110c09060f12011118030c01020d0f0212030c1b0105010308160804030f0b0702160e1816080705130b060313030c0c090c0f0305160f02011401 68
    0x50440e050b840b82400d0249170303c0c0c0304901a01300c1801c8508030102e52040001925450700780800c10025403c1c882007102e8144454003a00884d140c1c4880965142000d00506640b540c1a54911b40180e010b1405211094011b00b140e01c140f6078248140d60710605003803110f1202d0351066543d240f08100000781004001500742440d007100c4e801c00002c3c0306070b5240d03856112460183c940c03800786a00d0358450680c100603428048400559011000801c101460f0800c0d000c8494110b4840c80035006d603e18120080c481310b00403c00b9142035030f204440d683c07203070710a0424508041c549901603114038000701081d001c86000e14001014081d004100080c1480184140c0c1a08840c0011078030341410811034051b1b8400058940c008449410042208064202218500f08051006e0810100660080340c08a1070744c01500d1040f1303460b282c400c0840d24102d021003c07640100c1d01015144040f0300da00428a00c91500c0c6d40c44803080340f0010641d1100c4440790003035804280c1c009100c4c503185c10380440780201c0c0d00c24 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 243406573 1250 243405323 243405347
    0x15080108030c0703150e100203060a0e1e150d050f100207020303070807020102250f0b030403020d0c14030c3304080304020406030807030507110922060e0111040303 72
    0x9142011800b46034695202c0701c9000c000e000a882d00c560f2030700c00340e1039131005440300f0f10b2204403034a4020159400009520603102c11b17000360b286100105500fa0317801e0900303005104249a4201c0d0001d00d110507103441d070740603102c555210600119844c1a80d20600f110110074050000b9207006410032181b141380101c441500d030031a40c010300000025a50200c00d9803007140d0007510302ca544401c2440100c0c05d0002d6a007050f4403c85406440c42c0c01c90b41d00100ca00151030202081114050700c035a4160183d010441d801801a03010b03100e9842120305c108046a2058404c41c0308002c298080c02e4240c0c150703000004190364036404464170903031540048440030b0018800440c80b00c08000c1c0ea81c1d03189602c00c0b008101420a41c00000440e0442d01e81d540400c0045400041c0b880e101d541c1890014400d50210400303603120702d00c1c03100f0140c0c549400070f4003901640c3c1e41840340c401901000d58110910702401000d9854990b5280090b0328000c081c09103090315a0070340040c5031b54900354a00540405d410403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 243407823 1250 243406573 243406589
    0xa14120d0905010302130b0a110712150f1d01020d051303080f0c0903011406090f010f05010c08090a0e040201020f030c121c110a120e06040201031e06150801 69
    0x14a140d54481e03000048001a0703075081c07a001da034071510700b041d10104500c00d40c042800c0342c000107040c06c0301982c04050011b240450609a880c4960340e030701d168032401c1100d9005002a015122040c8810b01d40d5482660400740010b40429204089038409844042241e20041a42d400140b442100c150500c1182d81c404103a59a880c9040c000391000ae200e04001815240d543c12b810740466050b107041020380b074525000400030f2240c620905a1840b02200c1070320f5007406904610041520404004603040c143ca510403e03007100316285c030004580da8000a6400d0310005400c0140080c96110038080c8406068903d10007136990409100080c0703010005104c0700215041402420b4411101207440c840e4803070b07401d141903101c04187d501700c4031403070244000702c158514155002d90240183c9020380545d02d400e0b02d681c50401d20159800c0705582c50b9000040301c68124200040044d0701030361124040c0a20201c618003440143da00090444015400181c95020200601d030300d0140d0240e607081c094021a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243409073 1250 243407823 243407833
    0x603011401031502031806071707020d0f080c04030204060305010522030503070c030909020c060a050105060901050306090a023013120c0201050d0216060c09050604170c0a1412 77
    0x1510b031680d860f454503c0501506400001041e02c121054407000d030388070380d00c00a132011420814000f038030050f01c948501c0b80d0f400341c600002721403034004a1525489880e907111984100f49003102264084002000c02c40f001e5000e01002c0007603180d900c110b00180d1b218000000c2c080c288030f5012074480c0000ca000301500610380710f1007030010f03a000c1c0075039401c680281018140c2a04928040e507101c980c5400a120a5102103401805c0f500c0c0040c5030b07030180b5003000d820806a42c03a6003d20006105006040e40404c0042010404034109044d0480d404075032404010f003040910032480e40300c5845036100c201c1a60f0340c41c01d80ca0f8501d00c3d0143c6281c0010b042d250038080380c1d40b20307614080241e0214080d103041c40810903551055902600440708504443c0c070b030031560790540300b494000e030880d1800180c404500e84290108520f0081b1a4481038590060511b82002d1501868a415003440c100c060241d0103031006040194440003802030141c00207089402c00d41450005015a50701070126131440340c0d04c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 243410323 1250 243409073 243409079
    0x9090102091e0d0b0405010c1d210111070c0e071803060b030c0909070f09060b0418060504050705120a050f011e030f0503030f0106031406060a031b05030603011401 72
    0x3182e0315503040c6072003400d4950300c0b2149800003a02502c006600a800b02400d80200810003606600941c2034102940ba03800081d040460b031000c1822075902c0e2550080f402d160780c802d24280308040314000845480c0040307201c00c010398031300e0790715080000708485c0002d0440061000404040701d0507488800c07860b0801000348400001111084a031101810080d55019412182e80301403050709a003610140c100d07481801d00c20102550750040e0700c100064560051780c040b61920040c081c0c4001c40e49403a01450825045c07081801c40207007500300a40c02241e8550700000c40780c44a019003841140a07440309501c1e00041004c00311142402442c03c10b50500d03000802014055800f02641034170b0341003210880c3d41d0605200c026450a19400c0681000100c00e41582003000c000700840c402d440c0054090616680d07003c0a805407080948005d00428511000490609000e406011904041e10303020581100e85011b00701039104000001d400540c2c004100141c90400f4000e0740218440790843d440d007989 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 243411573 1250 243410323 243410329
    0x30219050f0409051f083007060506130603080909010902090a3005010203150117130201050d02031f050f06160807080c0102090102060a05071e051b0c0909010209 71
    0x1c42c40c003541e01074070703951804a250382c0c42500544004820390b00c004100981c480c0320b81a83c0c1c042d21000b2010840b8044410030701d0640c2c08141ca034018841c9102c036030030079404e82d45850242c00002d02c0260820302040324600218600d0203480e00942c01803c1c059030b2003129a007071125070340e0141c000b81c1200f4010469101c1136110010107108440d295180c0340200701d075803403c1030142d03618000c0700105410403a0b00c800501a040d0300860003009a10b022581d159401d40040d68402c9000580c00048190240040c02040620901801c03843c814074006103401d8800d10f14200300d82056072004181086040da080d290703100c004411010b0b21080740c00380880300700c0c000003039042d00c80c4114034040c04900c050030038100141c00741554019948074401036101c40310b0707040c0503000390032140754140188155000301d44013030306034400d45000c0c165031341c0c6080d0908001050544103040c191140010004100103264600b0784683d807400c0c0d101011009841041c1e480c000b00211150003408283c601d0f4410803e8803600c0d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 243412823 1250 243411573 243411577
    0x20a08070e03061519090f060906080706450b0c1906060f08030310140f0103090f0215040306060b0901050a0c05100c1707020a020603070c050a02060406030219050f 72
    0x24004c14001c01110400c0c0011420000030b0403030040c145c2e07059107804581c00d180c9400617890307148001c0c0c08000013a507940304113050303034154850080240c000d0f2a0520030644205c440071940440900c60515500000c480400c071088810142d88400c518824140640500320f10312a000380901303d645824032102d010401d13154002a4130728082d11079059204400c020641d0040c400500e00c075a444c0e1401641e89003150340fa98421616003110002000000c100340c080514101400c08024200e0509079580790019802010540000d94140c50307807030030070801651040080c0e092800c00c680c07059203542c95840c001040e544140c100e155900c000b400405800d903171003016900000ca0a28007000011107a003400c5080c007114180c00100d05041c041c2c100b02190300b250740101d0112580c0c43e004807035500d24800f03d89030282e03c8002944014100045480c1900c10040c0c403c0c0c4a01540640b401c1c0a010f600003109079100354003040210703402062a0910007442030b5105108405800d025207000c42d00f1010104078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 243414073 1250 243412823 243412831
    0x6080f09101a1203040614130303050d09020d031d01031a01080601111204050f010c030f0e0a09050f09011803050d051b220801060f03020603091f020a08070e0306 71
    0x810b41d02c0416041901e051450300c110401c010f0b02c214482160250669140c1e8068001d000100d464900d0304500144250304444201c5842c80c200016641142d4040307540f6804482429160380d2941540009a640c00c20007440061013074995032640301840c07020000070380000d11aa41410302d0b1040c00010300450020350a0070310802d01e01010696241001684c01b0780c90111151128811032111100c41c0404000a0081e9441222200002d20041004440011074044020000341741e0f075040d19882d41c06501410441035000704054921512003d2100480d0022034600c00c44451103002d0140f2000288694a02d044000c2c501c40c604c88070340d0310082c20520800620f150791941e42c1000a0301c1003242014a291403216140055644000d4656848101c00301e0380341000d103500d201e1002810050500c60300c02240c811441c0807105c9882c42d005c010140d00002c0c1540e605006003d442d02040c0c8c61120800d0240301c00e0b03000140c40701a600300040c250000240550140f0103050801805683c2c00221682c0c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 243415323 1250 243414073 243414103
    0x90a180204090218010303180506040602030d05040302010608160f0e2413140609240d0204020405040603030c0b0708040f110321070b10030f02060d180b0106080f09 72
    0x407030a0703d20101d140c26200d07560b145840582e00c0b0010042680c800301c1c1e0040614101e4020400944071001c0011900c928070820025070300c108002e0400e800035030406a0302c24041e0000081e00c40e030340c13103070181462650451a400c3c40790508080c40115042001c2d0030142c1031020742c140091401c046c80e01445c440d0360f5031200301c40710183d80030a241c1c0d40e031003070280314003044403803d003d02100d015a0903219036050751141c1c41076400c84002001160542040340310110400e40e180c189658450600c1651041900140d802039020400032541c3d480c0c40c01541c008521036613440f00c8054150030b00660350880030f03107100d0030008900140300200b01201c4100d0140c1c3e03086810740201038851000246042c2c00143c6520510203010b0702c820413102c0c060080c0c01c5080c000c01034250036594650b12918420700e1800014103480c03d0b224001c016090010207042c00c0c801e00e480002d00010b480d500300e2030034403042c1030459215500b000107000da00e030300c16102034010390380c000880b0b8a400c01d2803815480d8542842070700d01d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 243416573 1250 243415323 243415331
    0x4050306010303051e120f070f0e190806070c02010224010603020f0c060103050c0f040e03030705030c04180b0103060b0702090613020f13031101020d02030d150312030b090a180204 79
    0x10b803900c081049202c2c0042900348059139101c0d16141984030000c00c64001c44080c3c0e40b00001001c950281c4190300b202c0c1250390321007070036405000030440c000d5030643c00352f00c044031130300d00c0490b90503010030206000c4c113241e482e03104000910f0300c0024905030000341d02107011140001c0d4034541440407075240e419607d041c01d0260300e442e41035420031900e005408000c0d020307201d200000020b000c40414a81e003088010740c2e50761034104101e424002075821210103d80d03580e0040000644103882100a15041452000441c0c5416503482402000070b40c01d2405255031070351400070200f1980c2500c5444001c080401e0140d040c040e15400190080c6802030890b0702854400d220071400550740d81c12507802081131507141e522810606c888a4004400b4001265151300c8400645c03036940c0000f540c01c3c0b042129600031840d0041040c00100507141d021500308521205000100000705107004c02540792106603400552405c025040003844600500281e801c949000318510140c2840349100c0c440035015a004a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 243417823 1250 243416573 243416587
    0xa1a0303040f270212040c0816050607051504050319030e03183118080304140a0c060302030718050f01211409060a020a050706051b0a030b0a0b0405030601030305 71
    0xc09007209a02910f82d0b02e44001050b89011030701e01540da0250740075240c1221956265441c0300c1d580e260201e02030101054070801001a49018002001120b20583c151824511260081c00c111174090304c0840da59000401d100280c003c0340c0e183d1a016000c140383c14415480000f4100d910b910607401f02c1d002451a6980c02c501e81d444e00100800720b200e403201c2c0e2085000380f036820130008180440b65948628201405d40c0c0303010f40890904403159400503401407840d22180d45d180e814810300f0b01c0c1141c0601441d680340d80490046d85861000303211640b0096600d10b07002d40010000103001c10303203003034002d1046800c1c0708544400d403451560000c02c2c2804580c0307049401001c110b084000c5d44c0c01d9003050503c520800c44041c4c01070174070300540c4030808461a80c0c545411607000c0e1300600d00e003040040c00c1071003501e01140158111940100c1082c03140b01461422582314035041c3d001c5402c84021035151410300c030f890304040e8410001009050049800c150820001070b848240601c009020003030041655 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 243419073 1250 243417823 243417869
    0xa030212011d0102070203160f0b030411040f09110102070e190b0a12020114030c0f070303020c0a030503090d05040b120c0c01020a020a121b0303020f0705060a1a0303040f 75
    0x14403606440301c030044414402c4007400e14081d40c4411000c034000d0080c2d0401101c1c4c021204540420354113003000f40c15a41c3c0c03c00000103450303000104180c403d00b0701e08180300d4507a100d52280910a50500c94041110136903030800213101000107010a04540c40108100b140d84030081041d074104c0b0200000702508996200440040c01d0110a0b03154442014200002e800b4410b11699402e5071007a02e50541016481d0341d003803000d010480b84444601c43c208510030200b0840c100034505188642001030800324a030030214034000c0e500c1c0c411400324030300005003d101c01040040e03011140303440c9000340c40c00b0300301030100c0180d005604540210702c84a0b03001c1440e614280080e0303180342e00c40f04000c540320151070400030f5640260600c191002c070b203e0030440c2e9140e0701c151410f4810020901405c50712004030340d400c500940c4190280d03200190f041c4990710005c0e0301070100d00d00601148401003455000c44045000710041c103003103140303c0d510802c070400c040c40c80800031074201c031007003c4442d5000b1000500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 243420323 1250 243419073 243419081
    0x5041a030709031205040509091c02060f1303120f0902041a22200a1b08120a06090e030301080c03030304021014040b0f1b010c120b0607140d1404050a03021201 70
    0x447c40d40710041e10100142010000303500c912440c0d803c2180ca0210652290983c0c450f031f01920880c07260290000029211164003c002503400d20074070b4a01c044502c2544106c003110700a0103555982030700c450740d51b019071400d4003500d420000c210380744040c002d9500c00061561001076084400c10801c0d01401552000c03954044a00c8507500355109198803401541c0c00803680c00b40040700c0201d41c100076a400d8040340f0100601499030300805051074182459480c141c8048000c0150070381d2a1200c4021542c036200e0f01aa01c4c0c200e108000a6447c2d50401d140d190500740c0710400d89000c1c3c2e1050040202507030350101c0704840c07410f447c24550414010000214054402c6800044c0d11280c0000c01065414101c0f00428140d031720b80421050410315580c81c1401d0300c1d214124000092541c141580c40c0c000070f40c1c421507030003000030100c902e0140c840e542c4101c0d600d107191082459411021384010080d07006110100c100c3c00e0094010302e03040c141400030b500303200c8a02003c0d01401c81200e91485c01082580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 243421573 1250 243420323 243420329
    0x106051207030f0221060a0f200310090606020a050c0409031b05071203170603060412030e0102090d06050712090b0403030203361510120305120705041a03070903120504 74
    0x2c2800100444441842c0c0e565000d48800a05a10344239512200f0040307882081c1d2038106401442c9401070001228500b107800182503207151f0900b01000003504102881140c004110030f8000c2c140e14503040c240f10b41001d0084031a0b41c006e50070031440c00b0000ba408030308400d005040f880021440c3d48203003017003450001c268105410440350700c140b0b04c0502da000000420150102c546c0000300b0b61350360040c99240c2d44140c4000304000c003c000004100c9019030420380e91103d101d4001800c04e100540001c0300d0302014202500e407250b8850a00410a0340300c94101100302c0d18540c1400030b582c65603112018a00001e00240030540e011022900040740c4283c6800a010f180388000000c1c00b802554084203018180c03900d1789880381c10190f440c00000104c003a4801d00d8256107040415203005208242c4902c104021001c11104001e204800345c0c400102034002d01c1140d0f90143c449050140e2040001c0c4882c00041000c10140100429503911007041c0060343e030b021000750f0136011034032030075640742c00b99030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 243422823 1250 243421573 243421609
    0x50d03050d0f0911100806010807020c09131406152704050c040606030b0d140a05030d06140609031f0e0304060521160c05070e01090e0106051207030f02 67
    0x15202c100c100025000f150515014034400840c001d400000c001d032408541c14100042030000b00002d940398000c143c815441242c0b4016034101e80308030400100c071a10b0803103403010309000b02e890020030300140f40100034800f440c010041115040410440004071600074030a0311074540d060340000789d0012130051040b84c200201031400c207401d0a1070b0041c0c868070b0004807a03004c0d0b483c003000082d5091080c0204030347e0b601c01410138141a0259207422503514048580300600f44507a070744000000d4001c0004100703144a07080006452801e03c031003240031980c060a0f05200d01002c0c8088125964081001256030240001040e083c0c1c49401000d0094413441c0c0b2605a2808041400a03495030420300500309024180d0313aa9810744403a040016200c00d0541c2d221a0003050780d4a034144e41805805200403481c00b4400b1141c0080e91804005e1b80e04400340c02c5030301603640b610044070002100740a0308000c0c2c2030442c4c5051100066031170380d955841c51840701420300803c80d00400190f40302c000e01d41c9090a41d00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 243424073 1250 243422823 243422831
    0x2030108011a0f0a1406070b161803020916030f020f090a0b0f161a010909021f2a06050403051b0604050a12020c09102c01050d03050d 59
    0x10340c25050090002000a4030101450b0580308002d10f000c20005400c07140c000c0480100700d050001c00e1000c0c2101c03020039038210600300030740400b14024400281c40b60b114042d040c41e003420f280c60000e003142d044101d43c50320410681818001a613504103513a078060001c00440d0140c480d14213048000d80200e02d01c10480d14800a041030400315220f00801d01414196130804c84580d48002115043c41929503400c409002400b860710b9960f001c11018030f10034001d034020b05690310011141c01e403140003a400307042001c0e9607101c260114104130440400e803140c0d001c2d04442c070004249002d4400c2d1009050846c2044a0300644112149007404e80d0b02881e400c41410096031510345005400c1c0d50010b1300310250300c88401080a001100020541e10032035021000c0c00420300150780345024101d0b8000b100b420b6004415810b505c40d20307000c0001c0c1c418180f41d210042d45516200c1c03001c00844220450746030003603460000c2d455180701842d2003811180c0c15201c0d05031103d00d0b410115914001c5c1d1048408141c20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 243425323 1250 243424073 243424079
    0x50601032a030b190306050705130f090e03070309050907050408011b030e1606030203060105070213090b0c070c181d0f01060b0703080a1d010e2a1c15020301 69
    0x884940188666000d8508005800d070a00030050203000603004c0e000010012181480010502d41003107070800e1560500b01d04042c0c1c05c200940007504203400c8103000250300343c020420301e50f150149414141d2000051482c08900d40c80c001c001d10218020140641840004103401d00c0c4200f08850081c02c0b810002c00c9203281c1503171581a002804200280042c0c18400c502e40302410114104140c41c1d01c00c1618828645440c10690107500014101e6060010520110300562248a0441d40e10541700b00005040c1e4a00d240c841d00e45100039040211808040c06424005200c8080c0c11040d07558500088080560300007003200503010030b01084038801f000180c207103041e020003d09801440040350080c0b0041da100c0358800c4e864018024040d0004d00c00c200030826514999000c3d0100146201e056000084155580350030f4403d50780021905502c03800d207000c40594202041000c0e02942d9040311440320a1078001020007243c404e4400e00c05178450303c0c2d0003c1014070080400d890380100750640d180d41e9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 243426573 1250 243425323 243425381
    0x1c020d080f2106090709031506051201141008030a1d120d0e04111603110f0d08010803040501080705030a06050a030b0402011e02190c0e0406020c120301080c0405060103 74
    0x46003022901d00b10605004103009160000c1518800c0380c2990f034900f0781c2451138590709081c44100c01008007295030350b40080354036241c2070064420000e03920b0010405c10340c0400c079542e10003402017291250302609501444254070100841c1d51030152841d05280340f000e1000030801d603920a80300958020742d80609890881c1c00400c40c10b2090407a03403100c150103906031302031100f070312544199040954020130024860304860081303512030034080d00e0310400ca0320101540d41e1a2080104800c1842c1d4429130000e44e10742d50020b0340078003401c100310140d070400d80342070b001801100c0003901481c248100440000d20002c1c09602003c02003100403c0b103d00b150752401d02c4109003c0503101a8000f6a003210340c401c11070701c0c10540808a200e0b0364010050f011480e1300408645649a40483c1c1014401d080041c04e036000070300044c0141e004640c0107994002180b00c1c0d500e81070b080900d0b008076000500c010046060f0215068514a0080d140412556075010049008000c0000c8ac9061207203c2581241840c3e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 243427823 1250 243426573 243426607
    0xe01050d05090f06011a0405040e0f15090c040204080706030518030a0f030c2c2202031012080418020714011e06030809060a030e0717010b1c020d080f 66
    0x300502041d43c4e83d0366210b0101c1e0171400c01d103020081024604010421841c10030781c1c00340388583c80c2d582c00d4403003140c9100c1d4003d041c08032000b4540c00d401c0808003444081c01e81480321010692007200e0862400d407520b0405074070341c14284501014140d64000040c0d10010ba0360f00b400d04441e043c0c095075580c903c07248002e401c0c12201c6507220002464407000041180c0200e284950014420305842d400c070980340d50542e80007010386501d90300a6000800f96446550010780b0b5142241400301c0503880746051282110030068a510800f444421400d240c5c000c21540e00c100c0b0300b81d5a03283e0310422010003d41a540291041c128010880180302c0c00100c020700c019804241d907480b00200014103a144980c40c4e2023a6281400041e00d104000c002a00040c501a001056646a681008142400506244d5090000e254070601c0f400010200104003103400b1f206481c0101411a5000c400301c3c01308648640315042e104000b80520b401c0d55010080c401000140d80c02844600b4015646c0c0b080394000070785103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 243429073 1250 243427823 243427843
    0x303040b0a030f1802130f1404050d08101502030f030a09140c0109090902030c1012061a030a0c2c1302070308040305031b210709060f0e01050d0509 65
    0x80c1c030b0039118032aa843c0310b001c1c40050181c0025500c0715003800f0b80800c2000321011140c02e10701595a885207007050020701490908450080080d5020f00e0700b42803a50410100504d203d04125144041040c01405212072a0955900018500c4401c52241c4103a01c0c504c45c412010051481c04420040300501d99008010440d100d03800c1c01d425203c03600d02441e6140100300b213080c0410b100c042c0611080005901c241c00c0c40d07000504856000d0390358004540c0800d18107200341c00050326221100e56580860281000821500b030030a00720114201000350b060101500500b070443d110350048200e9842004080c070f2102041d17401c0100e8440312003001510900d1058414000c81c41590080c2c1428007074420780398142d405840d140110380d00c1e6502141c25038802801e640760050507401c030541c0404980090440f40c09001c00303401020042a000030280c2d5070040c400420010741c1c500030321003d17910100302c0e0644e403081d040c10700f1038480d5032005a03058080c800030b003441c1e1450301c000c006145000041001807 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 243430323 1250 243429073 243429077
    0xc01090c080d0e010f03020a030207080705010b18060901030321060b130b12012702071113051b0d0e0303040807020f100503010308070206160309060206011508010e150303040b0a 78
    0xc600c9420042c3d942002100d500b81c00b0131204034500028034002d40045c40f55900c10f250062408100d5522144541c0007074505580c0c036955200450750a04101000410105007445070810178038010000a00303a41c41400002c2c10042080400c0c0c44421220040c029240360840007402140d8a4840c4141980c03c48000c002d1020150f030790005070321311414201e5003000c141229000d2580e0030103500c4407181201190300300011000b1440452002d0701440500489031160403074841c5250010104a182c008540400c044607161009000700f080000c12941d62030700c0c03140c4486441e8410b10484000504051400082c240800000c00c020846110014010f25108980c0082100030309002d101070101c004803220040b41d020801400890b070402d01800c40148014002450b0081740207800041c2d40d84914200c0100310302400512030181c040c000f0300d01608180c0b16030300c01e51f40e0340c0c000140b60f250184100014a821613005c924034038a200d51440904e40080c007242d1387c9595030245685681c0c494141640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 243431573 1250 243430323 243430333
    0x130609150203151903050c0402130305070803090108010e090a061d0118020a09020c0607050d150b19050c030f090a03020a060807030501050a03021e0d1b081905060117030c01090c08 79
    0xa540c09552814040d25007113070003082c032601c26800b404001e52000460400d022b0343c070100000042e604104107005019000081c40e1a0031340103001401c92041a0001302c00c00090004002d4600c07400100b800300c0c6604120f01040002c104602130304011403c03a4242800c0d4204461440c80310581d44002c1c064500c00d0743e100c60341c0303030340c80745503900b20700410001c500c071034020b400030400302803003240034061350b00c4e13003000015460305440f00d03c468901e07254ac0701e0440280302040441002c02d4011a03441000d0311418031070310707003824154142d440344900398821803401d10204812070161641c1201c400a51350140040c0740003a10354002400c044802c85801002030b080c000045040d0825a103403000303d0f9030190100c0d5248110361b161654030070303480f413190360402249090180403075110301c0030a82c569405451400c4042c104501d4905002d0300c4040a003d40c209a1404800900300140f9039044403d803050a4845d0401d00300c0307050075841501c801c5900c941c2800c4141d0140080007038800e04603484041191 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 243432823 1250 243431573 243431599
    0x503032a070506070804032a030e040c0f0518030a0515090c011209140105070f090f031a040302030d020c0c0108130507060807020a050f0109170313060915020315 71
    0x203405200d8150002c000e0780200d030228800a00604500360828402c1c2808a0320b08044182c1d03402c1042c079010080048130407450020203068214803140c1800070300380c60500000c215080d01421503102c401e1a2070400100041100d1403002c6400001685140142560b49005240c10402d523540c01d024005002b44c1004000f09080840020316048403100c1a111000345d030075218404030040542c0c040c00d03280c0c14060a00c10095031820700ca0a4401c904648a036625182407860050804d902900310401e00303161410107101044805140303015084500c10801455511072808038107601810202035411400826004001180824500191a13080e46c80043c1561040810f0982d000c0c00000500705410491042c40042d1003640955406000ca0040325440c10040c5d0303400749000d18007242d6450b00c3e5512403010341004640200034120b4030070240c0c43d6046050034000401031400090b40200510741d201c04140401c0700a090500e501c24861008548030f24084840b60302c070700b007440001441041c21a681b9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 243434073 1250 243432823 243432901
    0x2303070e101d1314040c031103031305060706230a05150303190201020913060915060c0f05010b030f07090b010509012109080c0a06050901050907030b0603070b04080318012d0903050303 81
    0xd00c198102f14000404c10500d00410300c85644e001942c00e9540c291205c48907c0f1030600080b1901043c51b50740d000e80f81b00d203410f90000080b6900a418016416150030901200c0e544c000140c6e0240030043c60304c00c13240341d0030030380031b034024403465001503004410403411801c00c094079071140b0220750003100d0521080c81085000748600800e8024000460045400800494058500c52184074813071000090003000075000689000101a80103909034000d040500c2510b1050081e4404d400e401c2c2042c41c01c01043c0000600500c1c492080c02409801c0c2c1c6190301941181a00720380100d64204500c190340d488002650754981e8200d04007569814101408158400c0d030510945110b101e002d800f40038503e0456503403000903000501070a40c1841000000300f084104100140004d1842030025540c490329071448402601e2540c076464140110200d0340c100038101c04105500c44500d90484440034150304100b600c101e60781c1d40010f4024030001c010003003241f50001600d0031442054190304200c940302c40342 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 243435323 1250 243434073 243434077
    0x812030106080f04151e0e070605040e220606030209071403060402090109030b0a2405060717071a0603071205030a2303070e101d1314040c03110303 65
    0x801e00050040d40008800207144842c258026208032240140c210700034488a080d5550441c040c594403180702c0710100c442940b40301d01c4c0315400c90100a055000c0c60200301504d0380c001c91054200010b00e48000505118241c12185401609821500400360940c1440c000800050104a00a400d41c034042294180188400e0324500d100b031783ca081c60360395100d062102a4014070102810300c410300c01c0c0800010380c085001489071460000008102ca4594918103025070030641c1c910750340c5403900091000da10307404110b400c1207410414201120508551840c20751040300e00113009c00700314068850415400350a5103001c0c003010bc2c102c540e66500e6282d59542540328000c000e01170b500400c60803015038001c000a03000044440c00c00903034414214100091503000f01c80c0030780000c450480c8502c807860202150b5034042185c0c0f400b08507140070800410300d10315445c401a031007030320702ca801c103030026180350482110704584030610340c014146880c002c01041e84500040b00c4004601907803c0c600d00300041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 243436573 1250 243435323 243435329
    0xa140c0703060b0102011e0b03070e090a0b04020109120b04030909060602070510030b06130602070b180103110c0109050c1c0f08090609061b0607030204080a080f0c0f0708120301 78
    0x58099940786540e504014012079000c039055540300c014207901d25605401c03c2d00c0d803c1d600d14000c034104180000301030a0424070780141400400301003c0c0095060002000f01d00d846c0c0c004007102c126140c5000580c2c840354a40e00c082c1d03030b801240c88050108034584041e42c0c0168400d8070f806402580381c0200c0001c0c0c1c3c003503015000c016130044104105610b09944400802803446c00c00040f40701011000c02d41581c45010052500b40980f00c041040d550b0401c40440100140407640c0d08000b00805101d0003a000c07d080d2a0416446440d41c1d00c4041d58181211030560308580204180006454060388a0b41c04510700c5100318050026040c6030901501c20800c2641d025140d4980f80100755100c800d2601b0805003190070180030b1000d403149890b5100103241d401b1420046074034010b412a4454501a130003800d8004250041c4401c01c5a0349002654110081d84190520b454900f005000d042d10f00030141d100c4494402d840040140c041c000c40e14406407024041540c0500e101e0f0003030440c030f51000784 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 243437823 1250 243436573 243436597
    0x2030a0927090c09091b080d050f130905070903020103150510140708070804030b060103060f1a0c0d110607030e060a050703090512041701060302090c0c150c0a14 71
    0x1866850345001030782d00220075a0302c00e00b401d83d10307075840b42100000c4611003981100c001800701111103c12804000150040c0715000007801c00c0c200b050f00c01070286c0103c4118041c00c00022425600c50000d00981e00c01502c40700f0b900b00464a00050000c10003c61032005a022a03c0d0010082c42160b010180f00280c6c3c1002d80070602139920404100c82d0164450107544c05404213100040015014400406855004500740b54483d401c50601c1601103401620750781c1070515200081082c94054005003045416109400c04400702c5a0300507241442101c0e10703501e45000300703080c07114610b41000c00e0744401000c0d882117404a0783c4508007602100c840c011092600e074001c10000d0400c1c1584e0701f04030b51050480c6000303c2d20f4462a51800c1c50b010f030798180c02c1c10008007c035040c810082054200d41d84512068020701c18103140d034001c142c0401c80900a441d08400004044c40d4400c0200124207120010034003144445c038040c10031030440c0e0030181d90140003030102c1141514a95070101500c070320110725 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 243439073 1250 243437823 243437879
    0xc0222060b0304050303070c1b08060f06030a050706080a06090f09140a0305090910181b020a03051e090a06020f0c0105031e09121c14040507060c0501060f030302030a09 74
    0x2d80c000e482310302c00d031402101e180002d5005070244050402c0458002c0040c0b00042101c0c0c10480c08500c5071800c01000e1070b00a0f48400c00b2007010400008161080f00c91906119185407076009032000a441503030000c0c2015030030aa5112000051513002341803290051510303104002001005540f20080d00d40041e0014400780300c460311500e802c100243d00710704004038602c1d007590303104001e03401520912120b1003026070701c0c1c410300003400030200080f68003c0c0d1440501480c0c03486990180c014000c0400510070b0107580c80c3d1b090940140c03c0c04444a290004200c46002503844000035507405400c41d220342c0300e00410f01d4107419540100e0941c0c0c099620221080b5210021140001b41c2c11001442c0c04800d1251301c030a040d401c01d01d02c00034400c105c88826034000034942c083c101410345400e01522a00f010b40c1c078080102107000481e030318003513a2480c60150601d0700c00342026400b4000302c3c0c00018071026203140020405400000500c00c0c100e0381d4480740a01303070350360151001494069140485420003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 243440323 1250 243439073 243439081
    0x340c050f061204060527010c110c03030d0203060a0308040320010c170d090c060c0b2401080a0f0c09030b0610080114030a05010c050c12030106090302100c0222060b0304050303 77
    0x900c4e008540e200706440368a825519a00481b100c0300d9007100b035003407680d946d030300c40c0d100f005580b0800032013200548000810000d05c5200200756207101c0e44c010700c00c10542c08000b240560359200866001103400c560016120358403420650740c0903031200380006802e070341458071029950040c03458040b4103401506848400c0080706851901c1e9100389440d0a03001e07a07400d1050000303204c00f540d490261400d135440c1c0481d9032003450041603074040a080b822000386c101c4001984003c00c94046c0c610400f00f803a202c0003680318201018007030070314500c212400030b080c0100c982000f50f11030806d40840f401450000310b55190101440083e4080d0802d64001800210041c0300d0350720361101104907024080d04407840d1010580b261400c68140026220004600160440c10342000300f02c1809a811070244461840d4503000000e08042914800280140525130110805c40d018200780c0313100603005403500541803103010001140d10100008103200c40d1500402151071310884090741d00c2181c3c840015851600c0e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 243441573 1250 243440323 243440333
    0x90602070b070311150a020a1704020603060d0f0f031817060604110723010e070602060f0a0e0303190c03060302031b0a030213020a030b090705340c050f061204 70
    0x42d203144044d01445400140180d22010990031482128114001a182c40d8076920060254088183c00c1c071072001b410046c4405642d0340021a900160200d80504148213070303181c10340d109083c10710050142c400e0215424103068000c01003c080f084502d088400b034584410240c810f5903520001c400095003d00c001072002d0400d540420405a001c1c501181010071580d5410188020051200e21072405c8450010321842c0074081c1054a01d11080901492030030032600039541d60000740501e00c07141c420713004104030708030a501803d900101c000c152589c91406a000c00389445860004404503450084002e145910911602c41507070f80c0200138100c40703940641007031070b44201451001e0f03000da00740c1400001039403504170502c4c004482c01c5000da142d011b407000250484d6100500c51f0b02661081e01005040c1d03a011003150154100c4580d00848540000d0300b2030104900c1610511759261060320032001e02c0002042802220f60844d1181144103242084c0b20844c051880c916109000a10100f80050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 243442823 1250 243441573 243441587
    0xa030506040609020406020f07050108160c020d150b030d02011109061e0c061b04050a031407090507200115120501090204020301060c06050f0c0a0e0a080706030c090602070b0703 78
    0x280c005202061280d140c400440072a40154055000b40e44103440d05d0091103803d04c40a00204002d007820780e0907107010408044111500e41407e0100310701c00c1020011940c8440e0760071011a008003203c60038800680d000b0004000f5048204e11038170a003528819410700c14040c0382200842551010704001c0c5040034000150060a241d0074290704865035110300520100180503200700f0440102078508107101c481d80c0d000c6807900d10fa4022901000309000e10303124040f03502c040341da0100d00f821402c0005501d550401c802c642040041d18240f00c01c2c800499800728805000c0c600b04034410103004c14240005003220301c84044801ca12030600d0381049010b8203000040e0503a0301440004c00d07089503e5000900300c2c1c0c426004a004103203a41c803c0c0341481014416154429502d850b1003042e814050f46034085401003400f240701b0000600d004078201d442d403403943c8000b000340c50304540c40c403038940344042c0240403035004140004404810008400348002600c004603054035005600e00000c64804417804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 243444073 1250 243442823 243442831
    0x181a042003071d060109060e09010e0606070506010303020c0411190507020a080613030f030b0a03150207020301110a1b1a04061805010603060e0c0a0e1b070515010e0c0a0305 76
    0x50042c85000101d0014120104609500489007010989043c1c0005400a50b01d50000c804100031f1a40d00e1405480b0b080f403031415100d41c4101002e440d96a500065214803519400401303e00524000108140c0c0008080c0e41c0440100c1e414004001e80c640045d4060082c0f8418207482c500071500300b0308c00c40c02800100b18640c0080c04400100e41c85031244d925144040e140c140c00340ea1b40020300000c1c50b500581526403144c0c180380901c0f40280000014a160950f804081d06401034180490904140e40e811180300e00e5020f40288a02c20f0030506607a0380f074104020400c0031a92a03034040d2110000095a40001c0340d015500e482c0f072509520b10f1035841e0500500848110ba69106c101c103c400d9082c1d400a04248100004a0b02c1825480c2c078205542c01e1856040c000c0d4080450174240d0350b211680e680580e504040003d500780d0310b80c05101c2502141c505c4146d1442400070301c4105106001c55240b21120001402c601c1d641d982e80181d40c10078004541d880c0b400c84061040d500c0c0d081c4030360802a00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 243445323 1250 243444073 243444079
    0x40b031b01020f0a030206160306060203090f030106050d03030b04050109020901090e060f0a0e100b04150c05030f041206060f03020907260a09060b031207021c06181a0420 75
    0xa0b412071220f402d19154201e6425005a03002c10108102c071190111090f0041100f440c0c18842680303060b00280d0341c0e00403c012544610101c00140f0070390f031000d60140e0002c001c02407203088000340505015000b404101c01c4103001d1b42c20200089002051030080b103010803c103a54030f1801c40d10302098207010748006818a036001c075145003803440a40c0c2d41401c01000e000000100001030801030800560a10103a00c00da500c0710b07003031204004405c0c02c0d80101080040c1828890f1100103035190590941c031607002c3d0240e160b90041000714041040047c1441c001e442010100078041e212045078100b2025480025401003004001500980c401c011070300d10001055481020b03994400d02c2102c20301e6085601482883d40c48444800303000c01c1d80a0345041c644183c020b021944452006100c0500c83e08102a0140e00c40c0c0c0040c940403000d600103d00419080310042080300e00d0070000c045010702c1150160b6484802c1075079076041c405080b01d4503000343d61146060303609686c0600f0164080b080315000d00d0b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 243446573 1250 243445323 243445333
    0x40e151807050f0301060905041b1d0a090c0806180103082a010e010e19020901270519050903091f030603060203100501020706141c061206090b06040b031b0102 70
    0x340d40c001c20005076020342441d1f2a01207040c0c1c04c00040c04100c0f18240e030054510b038031281041102907000014122a01481c4014855032450000810180041540040a00d42c13510144141880e44990f12501422040b90884903038a80e058100c03c91100a003c09000510b0400111901c11440e901c3c40705402002c4e40304400f07071400090004d0840c0d04050703020220340d448411540750b0300c08c05d208440000c0c40b5031502c0300c0035050030740100b1803a10301409100c980c42d52450301481c0d00c6c116000360001000d000c04051000d803400c00c00700c0368030500d5924080d094078140004030341c0070000402652044400507120300b40c415200c02007800b01c4264003034410140750343c800c4040003050703241c001148901d61507181142c2e1140b070300380024500703d045c2e80088104002d4460280e00c1c0c11503401198080704000a50a5103040c0404801006164030780c000203004070624212010040103070080c1d401e050080d0b2002c112940c4080501054945412800e075058100c0302c0354000c9940306400e40395258a061040b14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 243447823 1250 243446573 243446587
    0x201030b030f1005010b040609030f03021c020c090705090f04150503070b091003111602041103091006050108060a0501031808040e040b0603011802010e130203010b040e15180705 78
    0x81d0500e440c00b8a1078415402018400350041480d02a040c01041c0004407645014903140c4c005040780f059000091401a11450100a052080007030050b0240046001d1580166910019507201500c4a070f1500031141c00000038001c9004409480c849074000d49810307160000c2c04104001081e036908042c03015010140d01044c5074904001d0b50000c0c10303200603041c0d0740307003080340c02c01c091b402405509404240c10402012114528070701610303031808105c40d0001ca041c28903c000b8024102882107404448004010415201e00014040c030444001c480104021500d503001110012000c45806400110f0342c0c100b0042548a5072010b07218200361640680c512030b05030780f00741e510b9020764800071079403410703100344002e002816417a80d811200450080111440a0342500b8011034441800717818003400c454544103d84900100c404c41c00030242085580350784958003003050390414000d098001d040f240c0092418060082c00700751070100207020315851801c01d03200582c0d07590020600d40c2040010700c451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 243449073 1250 243447823 243447829
    0x110103060906090204080712050703150209040207080307030c021203010b071703040f0510050f0a0b1f020f191a1f0315050703020313020603090309030610060807050f04120201030b 79
    0x1010140c40c40203c09a0340b6890810000d10300034080d0440040b030b0b081c210080c1c0020341e0010b520802c4a41c440003500c000c00005c030141d030003406900d0710319030003900022b01d180401210f64003e620810343c0d43c80030000413010107000c03130b641d0750321300a28042203000300010b0024205810207081c44521070108078510860700d07e05002c040d00160703812200c1416400307039101040000e22000400752007641d8100318034030308400381203078100e0041e2005008c0707503862031400056141d4818480f0540d030422080c1d19408000c20000703541d01500b100c0c011540c01040100d181741d6031414a000703074070390b00211100c030b040d004801c80348001c88000d0140601112034030a002415040125010002c2d130044041c0c10184041003c80d01c1510401460402007510420030000d0041861504814450701920700d50348a03035600c02d0345071540c890b141c400d6506201e05010407903035040240700c01090b11000e9607042856101d04030251400d0080d0b0707a8000c2c1c00241888188104002001e070f082c2e81d01d00514010a82d407802d4004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 243450323 1250 243449073 243449081
    0x9160b090a21140309041a0414070f030c12021c0e0a02010c060c020705180109060b04060f030b21010f0e0f060a0504170a0201020a140901020d080606130f03150501030f1101030609 79
    0x82081f480010001c0510b882c0ba00713204a0b2a82c0c02020100704e00c0e03182429001385500300b828849800c0c1556581903d43c3c5611540c203003a040481c02104541d200c0d000c81003508503075108890340a1150516103414064440400c0c01c4a070242c1c1a160001800600d660f400d000d0133084810303800718030401000190319940e4007408030910282e1703440082c0950404500d002580d601d42c000c02a110130400040141a61000c00310201028a00d03000540b90713202000119296003442c885101c0101181c081c120241040d405041c0043c0c19560030020b44480c00c5159444601540082480d40c001ca000121050825000310390b006124650280380308400d5810b171203541c0c008a21410050b98042003104c1d0044d0401d0114506d656030400741c41c01c0c0b0100d200001d50315101c02c0c50303030001c11108070b0108076141c41d00410303908840da026101d00d1340c0366140d140301d180c900440d1105440e002140000390442e41240c0c8103250507650061480e030b908403038640754010341c4c2d040725202504041e52450001125101841 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 243451573 1250 243450323 243450341
    0x180b0d0f081206010e01050409021b030f0d140103230c0405040b0601030b0906130e031c09050d030b0603040b0402010c0b090619140f09160b090a2114030904 69
    0x410580c94801030b4030940311036140200090b040c007010f0710070142140e82240035242140c4c2c0c030803409691003000c0b80340000071140c00101044580b001180841100103000c0103401d944075503110801c0380381c9602c400e4a071505801c1c40043d04128142c900203e070b540744c500550680003800801c96030000c0303c0c0c00105003110740440d815149140e580040c41300710740e03041c0150941b421040381d900b0380c0ca08181000a10600420816180c5140d032220301d8400d000b030034015241801642c0c801030b0609500342210001405100c0c0c400c071654015604000c40c002d001e0310030725040c4040581b445d82917998135600c0803864580a40103030b06010048410b0000152000d0707009104401800107010b075410000c141320892001d1030b0380081c1e05801c04100040490000032103a60028000e8102201a01c45003011410701c140080c03080900f0301800000300f00005088000d1607a01810750b1502c16140c0d940d80d0000c000c0c01d82c3c2460880001e1b1201394040483c0914070001c0704111700d4000d030f9161050f5400005e080701e921351 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 243452823 1250 243451573 243451583
    0xd0803010617010503240601020a0c030503042103020c040f0b060705010b01030507020a022b05060901052a0304020d08090d0b1b0c2e1811040204180b0d0f 68
    0x85803000c038541079110b4540103040c00d40080ca41a10450f0191014030500303d15103810008010020384943c0c800c03c00204860b80080345070b100310b03450382841600c0f50320900803040e40c0c0d003400c20b203183d0000b0280d0480892a03003590103800309107040c6082202420441e448890300c03030340343c2c2a40c03034059803050004c2c510035100d000006071142840f400034042c0c0790024a03000a41d004100300a0140e1541d600001040d42002203201c0f0210150702000166031094402500b5440f90104124900805600043c051110000a0800040d800a00e004d0740c45031260004d40c011401c0c4041001801c0021071020f11030700c118000d9081917810b00100b440a50103240a44041054005000030100d040320f10010f510384a06a542c904003124118a5840440300c401e403044001c40c42d83c450490400340700800300d000f8110720034424030703400d200e0000c4a01d0403040b00f59906007490f00070000c80d01c0e00703100b19422166801620305842c0102e031403403030007402e00304030494200c0c00c40916400019056080d04100501c19 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 243454073 1250 243452823 243452837
    0x203190c1106030112060504020a0b030f090105060a050a090c0c06020f070c0504051501050a020c030a0614100311150c0106030b010e161d0607060903020d030e011a0f0d08030106 78
    0x604114404a0301c0140550141c281040140301004000d940c0c4440c007904000f022485450f28400308d82e014400764404401035401100b817000000007001a140034140b220000d00039915600100134621119100310307076114041110402008806402c2154144011305101d0031540300c64542d0001d90f8030a1629a524045c0000c1150800104141920140905a80802144c0380401c4c0c040218039007110300c01d041c4800440c03a0b8460b1442005040b91400300541038070714a11840c54220064a050210058061800d00c000382c201400500c2110841c1d412007504614185e00e0401c0c400c07941030700c01d42034440040800400d90004001d0181e40000d600c101901882d0b5890154061b66541c0c0c081d0429904a010350101840305610081d0030002a8144684049400c402000a000c900c00c8000003040d5070f0802024006061300031070019580c1d00300340c4007413003004003200545080360382103418240c0b0124901004005414000b101c0355805401900450420a803a12604001c1d0401d0b840800010b0340c3c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 243455323 1250 243454073 243454097
    0xc09070908010f09080909042301020901030e01020a021e150f1b0f070b070c02030d0e01020f07030b040f050102040e09010f0b04050c0a0e030102190804050d110307060507020319 78
    0x70910480c4019104007004000c41507090340c81404902c0b900319101d01c02c07104c0c20041024001003400c90101c407000c60303042d02c1210801083c0e09003c0d420007503061b40403d1410f9520b00e100d01041c000c55800b049c090f0302034245075000c4000540c481c405440e07006824402d0f800084003040c0600701003070040d481d10164841905d0b0003240c0180f841046201d11400d00e10910503210100c01c204142d41c400f690000150145548240701143c81e0307491030b81c0107581031040300c942c1c51201da002000c101204d00300b079017a81c01b4502640b42c6940c0d103010b02e100003081c02c11031000060100c0c007030000f100420b0344540005458196035031080c019114003900d50b00e075103075914411402c1e40d4045219215030a6015a0140244c0c5087d081404003402454981c2082c4084002c020b0003d950072340c11544442d01c5091070309841e040707203240200104070440d42126148134000b015903419016815001400300c15000951404a0750380e01d01c1c0c090b003405041c020940c44203116403c0390380700c0013130040c0c00d0756000da03114030854803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 243456573 1250 243455323 243455339
    0x405180609090705090103060b0613030f020f121005130501091a010e0c0d0c020c090916091406011121030601020d18090207030c0602160210030b01020316050c090709 73
    0x2070003070241119540250000c001c1070301e076001410b0440b608400c3c001f40301f03102003002c01d490348241804c43c624409034083c04410086090100d5100310300944401150204440c140408640500000307600340c0d0040c004441d2400f207541080740e121154055040c50007500c1d6403402d0a59003441411661182c1c0892208414105803075407500500904c2c0101d4118100315088540d98400c5800c810b81c640d4841c05100170444c02080006040200a0b04400c1c1c20b142c040130454860b0b040c1424112100c44091000a140c03150703026440008602006c443c8468503844011340e211503e0000410103400b5011131140d44c80b040710305004c240b840c20007206640c1c1c50943c00090500455059501c02c1c0020001003100d00e085a01e40c28082e543c52130001a55802d40e0f060035641c4801d1504004c210500024003141c0240804200c0300307060b80f00707a91a01100091820940036241c0142c0614010307131080c000d0440003040d003180010117501a4099826440942020408241080fa40d12001c99030050080000702 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 243457823 1250 243456573 243456589
    0x6120b030c1804051203060d020d02031606050c0706050c0714010909150e0c282003090f03060f0a1503061406011107031a10050a12030f08061305040804051806 70
    0x5c41c1d0b500c0d155151600c0054081034003664068002d0550000440071900d0410a0355041c4982481d2810f01c035136078100052180d40842d0f0080900d004d4950001075090003034040d662400d40340d4014182c644d0a0400302c5680c0e14a034581103040001c0680001103a00443c491260b0309501140e00042c1c1c01d08140303c840c4006c3c405050b801504030208055240003500b165029042c0303102e059098150342c0c21010465940c0001c0c0b48041c0090341090701c0e5401050008001c00d80c0160540308080c0310302c0c1003401c064442a0403500c070043d4400307050005400c1901648a4104801391044444170fa60b00c036210401100c80ba4030010345441001d500744406036810030951b40902c1d41a2004020f942d0a40d03556140101c0c80c408000404461035011034084910850701c070010300000b81074915020756030f0224903500e1022030426000305034005054059140324400d250b1181d030001e480101a09086943c0600406008009407244802484040307032681c0da900d9120707044075a807401c1051505002040282070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 243459073 1250 243457823 243457843
    0xa050627061804020f0d080f040e01050901060c050d050310031406071d06370513152010020a03060302090630011107060c020f010606120b030c180405 66
    0x10503000b00400005076142520b1004c5c0c00c0c4151a05200c030f095500e00324085010311451b04e00621004030b008142a44003807003442c102c80040b85c505419036a41d034015506500c40c501d0140540d00205c6100980c140a90011a042481c0060146107a0b60b20340301c0306400a4903100902c090b400450901461950049001401c4100c1c0040ca01007040c006001606522898010100300b40018a101241c03ca80c0d101490050015154058070030788180b00080c81507000c400c884140b4481e0040c00300307072034940451401031040c5039190381c404101104075401d140c41e600e0390054400c1c0718810110400a05a0002c1d000947c06a00c02090759030842c410803e01c1c0c400140024004c044000002c03002c4140c0324000c441d080040c92420b11680a506007032b601601101041c110040ea0004400c0c00700041c951000300c240784e0940c01c1d00c8600118807a0a0700b0f8590038480c044c0000c2c0c1ca1000c51036000e02603070140b0138a1034001c080350072110181d000300c0d10032400c0070000d1006c004030700104014408280922844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 243460323 1250 243459073 243459109
    0xd0812010315051b03010909060204050a03030c030212070f150905010f0e100e0d0e0d061a040501060f0905060a18030c1d0708220510090201020d020708060a05062706 73
    0xb03503d40c0c1c41142244d50205100d0364814544030341d8400280540765048401401e00505142138058603401e02404003d590901100188030b00301417400c0c84454541940c4d0000c0d4489810f408010060b2a07a081d10320402b040c840c481c65031441c003078001030024480d5842a49501c4404110710032540213417410702c600304800c86803035401c041d40302074071000225001c0321044d0350741421000080d010010518034076482d03030014102440d2040c069400f80086042007a0711030100c406103c540e032181e8085440340d034000c100401003002042c0c00d00135442c221029200646607841c103094511401400c50249480799130085d82d03101018030040c0304000c4007085181c51803120102491850814407130040c4a0100103019520980c0740345608071100e40c1c0c0e40302c03201860b80c0010403560302c0c0038010342072001807009500032405803140d40030040c0510300100308401160ba205000d4100380ea00e00700228050140100b143ea072101d104601d080d08030a4105c0c00e510540e9524402044901c5c054051092210051842041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 243461573 1250 243460323 243460351
    0x106030c080f100504060902030a15051b03060d03050c01091b17030403080901050d02070303020d0c0806010e01030203060f0303030705070c0503060105060a0302070201090b041403070b070807020d081201031505 92
    0xc2000d10000f00c0071181001c80c8000141d980c3c441c1030000003400d40c03020003035142c06228014010f0003403840c15206a911038010400c61611100040c01c40c0508241c0800c0c840b0005000150b010304c0e241040604c001c4c001d0034154644041208401c1c01c403491032204540183c00500c002c0022004500e01102404080f4810280c9030050710089640303000b0b070720000b000074900141e0041e10741d01c118250f076a03a001020055403036003074a14016000c2d402181e000203ca52812402e241d9943c0314241c0345004040607154050f03000b820800442c040c3d0310052203142c01000040c080304160301d0410065106010319910203450b8042403804d85404101a07000e9482940000010b01240c2e845d00704079030084609040060392000503100588500c1d07002e9110a80c08180490002402198030343c8240075000c0071010b4805082e00c2d1040304240b4000e12201910402090100a00505007501030300b0859000d00b1040b403d02280e400c01a000c81d01c26001102c44000d1003052070b2600450b8098941c0111030040c03580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 243462823 1250 243461573 243461593
    0x10807090503060910180f0b1f1512110307031104120b040302070e040506070f030b0406030c0f1a19020a1203200c1b0604080f03030717090706120e0109050106030c08 73
    0x24003c0d01403610050310654420000c15044a41511485449101801c040261341e0f070340c252a100000414201001103032f04140d004603026000d1103401e001c040400c459600319203130310004400801c0450b2040c20b15460800011070855101c10031040c07c540708455032412440d20b0700e802403d00400b030340070004058032a001e00002aa01103a01075000c0d4507440e02e0b2181d00c680000032000380041c20b10070b80d0800d01d012804070610000f11017040c180e4420340c100c000c4061761084004000b01d81001c0c560784c411807d024170010550303078a420700411950352044546120311502d5251910711240c0355200820340d40c200c04003603040c490340081c0364900c0c140c00c06410200d60514682d11108100a41f26004540807003080e51035940703c0555003d0700304d58089841d41b007019610b2565950081d900003002c9403c240303115449940c0c502c2c0d00e0b80304405040c050598079140040545044c1e22440c4040c4e07169032074440040d00500240710700d405603030203a0b0000c9002483d504103100f1042c01c079048103d103600b10310305103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 243464073 1250 243462823 243462833
    0xc0e04110105090a03020405040b010302040c1d060c15011e06030b060901110f1504050c091603090602070816020f0103020a05040e091c0906080901060e040201080709050306091018 79
    0x29400e2002e0030300c1580e44000030300098a0342c4039600f000754400d10f0031081c40b050164064049040e00d1003503d080068000881081d034030104000c40c01b030120700180031154441d04041002e4141e4402c0b6804540003c042c6940d402c1200c00243c002c0911344032403054003c0e400d100703200c10304024201070030b040000c01c84500216480348101c040d070a0610080d05052040000104280401565010240c88801d800c00d80d000851013000e44068440c0c4c13144100d01d560034500b4001d02802140101c0d09900002110300c2e00750080c021840041d00da01c2e41c21310502c404940018020030440c1d541c4085101e01420b54030401c0a4880c0001c4042d042610602c0346ea55500d810400300c0b41540c1070420f20003199603690010301d03d040e915041000c410751040800110441e00015800c0555000d034072844429640c14510500301c0315548994055a902540498099400b8007040d64000031186881c2517402c1d180e10200b40f42c9101030756002804c1e4004040c21100381c00d684100f40568024030300c40e5001c8034203a194 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 243465323 1250 243464073 243464093
    0x7030b2505030f070503181c080a0506011b05030408030a11010e1605060d061a09090c0702031002181504090b0603040221100c030c080f190b0415120c0e04 68
    0x144d00140480040407440c0301a00d08104154011107900b1a14011444910300c5100300070461640d001c2486c6002180000f04140a894072a0301d0607968400c80045041c0710045090440600341c5440c0010400416081d03010700060031402e950703848031500e0640c000c50f1701e400c481c00b007410240c054000a04003442d80701039500700411602c0454031152980000c0709140028000c13a4401c07040103003030400d059904044c05000c1c3c0030801003140c00b076910382c0e960000d0038000d11801c04000d500d5080302d040c0d40b5014000f5405400d0306290007002944402e000750210715a0070204040d241c58074408142003116840900a84207e201d00740c62580c04c50034142c0c0842c809080ca82c881d4004035050141020a03c0001c0041400103000180240a24000d115002e001030840d11003900002c0c0301580050305c00c0c0b5926134020300800040c951401c00007000d85c0c00c17400030510410300ca9409900d40a034043d18403000c0c440c2c84041e14031585945070300180f80c03500403c00c0e0319641c0850f214508190800001c01c204440e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 243466573 1250 243465323 243465331
    0x11802060d0b06030a0e010506120604021e03060432102004032004090302031204030e0a031a130b041713060f1701050a1707030b2505030f 61
    0x341103500d03094254403840241a8694060783c00010200402916511980101041034844002040940c4440003480045540900d1080c503a9125402260050600004560307036081c030321000101d022a114000780c20400181c8003500e0a81c103014600080c0d040c14406a20007070031005e00e038042510042d41e11520703102901007003150a82d0756241051501d01550b20f0710490308000c000035965903180e20300840400c0301820b200641c106161101500c50030180318100f02c003505a00118100341c0d02e0720654a201200910840c10000841d10a00081d11000c44110107184610420342802100040300300c2040c0d00146001c0a9415004200b40800e1441346000d40040c4c01c07807080c410b40070b0b01c00311013100c901c18400d0111420b0f00b9500001519944007480b10361409441d0340d0452610f600300c2510842d800280140c40d4400ea20420070030201c002c1940c2801c1c4560f4400c141e03486195030b515403903444002111203940d000200000000070800b824a1a4803401d420f04100e4114144107883e18420003000f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 243467823 1250 243466573 243466579
    0x5100f08090f010c050712030603030503040f030903050d0507030212030f010b03100f09020a03051803250f0b06190e01060507030c020d0c090609050103020d030e120615010908011802 80
    0x1c128031600501098040e10300e0b120007880b10700000034000b41540d00213071095600541c0101c41d00d911510a010f00021240c05039202825919262a07441c840340304180100c09100c0e0000000000410900041c002c242d11038544640310703080c034100642000c0d04901c1c060407e1700208108032517902e400021505443c0041e088907100c0c0d840c040e895a042810b600003003034203000103100158180c166001040b84110750b50701481349440300d421540800710114208201a041480082d140e10303400344401c0610240c62400f220074200300c0e143c106c0f1101d00ca000990f03030006210200314041c2406100203000c1d08024010103005450803503041c0480d541801490200706000a5800606103d0701c820041240c0060200450b1440e9107801c070f03580c15030351103450002820000002007401451140904894029001842c4200c25940445088013040c1d4826441210165080c0c44150708000c0184904070b4103500400200808001502403542c0b03500510040c2c3c100480d120300588600c42050b00a6419 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 243469073 1250 243467823 243467837
    0x70608131101020a080c010f11180f010201020909010909030f1106070804022206090e01020c061501031803050324010e010c031218021f0215040609080408030304050705100f 76
    0x841c0100d0402489071030107002e4000108031269055010760041c03590300c108503030400007000b8043c10301d200350140c81d076015080100c8040860960510400d01e45411505100042c9440c12241c00105940c07001e03040100602c0c0c3e501c1c120001c0640201c280180d10381a400e0200d10506180d5a079552610001c00c210b081100d05c00114086440d407404000801690021041000c1d001d0020400200b03483d11810014504004081214010600c00c864051015101030b00140e901d406811600d001c4c0303803107003a04265440a60001c1801142c1001195910a03507a4980e6414a590220301c07904071063b402d00d444010356910b09c50350313070401e5108240130420b0a005e00f8240342410259680e01e00c010720f906185040117040031450240c0c0401400b014402c91baa440365403c5802c104c048100007111080140c0c1c04812034090404880280541c828860100807608120711741da101d00c80e400c50746c0f05280030392003c070071300041281c01e000302805004103075070311281e1003541c0c20002e14480c450b0740550203100c9a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 243470323 1250 243469073 243469103
    0x712051608070816050c0301050106050301120803190c0816052811060106020d0908030f22050d03080402040e01050903090105070309030501050c030619050f120a05160807060813 78
    0x2c01044d6042200d5010b070505405103d420030341c2d280d030b01644c01175209510304000440d00c0c0d4003410640381a603c1040009616014543d01d545456001070b004c151200c100c4410321200c0307a0680235000003010683d031040300c1c42c01d10701100c103003a07040c00f141c88041c00000d1000f001e8190300086403508210b81034003c13600c1101d040b502a241c0200755a0700701c0300c0e40501c0340007280f2240c001401440201041c2e6919400c0c650f2104815141e010741510f20001032030800c0103415141c420309186400c264260743d0a400c0030fa4960000c0d40c000c55000c4110080341600c001c2005615240c400c0001405004000f0b00c42d41c40c0c6200d1268a900c80c004005d4184070000c80c0601c1403520940c01d0700091503120740200b0013400c05960411403030f0405ca410920400754a00c82c2c1c035061182491080803254084c01c000c1480c1d41c5036081140c2e00e01e4010b131841c8541710701000900410020401c2c0c104540f6109200306c902420034240794100529070b00524244401802403007850810200394081c030740c0c0c00c89210904104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 243471573 1250 243470323 243470333
    0xd360c300305072307080c0a03062d060e060103020a0215071218060b3a1a01060e0109030206090405090f030d05160c02011704060609060605071205160807 68
    0x240040c080c2106156032620000c0244411030041c182d2021360440313000560f180c40c4903940302d5090900c0d580105161504200140b00d68111141c5071180c1514414002881c00c0d03100c0c461186a51984806074a4600802111506011440d04240d00303290a61070850107110203540d0710340f4005542c08107040300b00040c00e0b2510920569054107910003091006c040c04200408115442080584d101c502d0a5000009441c055031074480141090643c6480c03014140e042c5104c0b456258030001d0f044074032a024100041402c82041c0700e01000714185800765040c400c000b401441004801030501204402c14005130b51080196012100304543c08a41965210601420700c5005408580c40d844081840c0e4403002d2076400c014414140507420b05081129440100c40c050b8002c10b01a0119040c2d42c601c0c1d0401804001103540300740101070100d000740d0f5420401048030ac8940c0000700040c00400d000041040d4402d018004000c9841c00508001c010704030840c55600c0c5a40082482c0300009940c3c0c1044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 243472823 1250 243471573 243471577
    0x1e05031c0e04060e240901140d06020307180e0108030d09050111030709031725030c21021c0e10030b18060907090b0d360c300305 57
    0x8002e0024807140d0366541040940000a03a0740510105198040619856060300e02502417100201070640607407814502c01120724103d40000d1f04909410040004a001c03800254081d00c0355903950840404401c4112301c0c0b41c0a01d03045040c654401a0040245c44030000c1a901c0080100b0000a01c0400e01d00d099401014a01021502d900c80841008081600f111000044a0160b0024412002400e00c0c00c2041c1c030031000030419030100307481c480159070200c200300c0d40d0b85807003428010107030941d030380b50150407801e08540c61507898200b1b4a6404425418460041c00c0f410072188502003c50401c3c014101e82c05241d401c6008503110031030245413034803d4000d401f5540f800b0304940f241e1401d99145134480641203600c14041c9c02458045000c81c1c1c4900c00d142c044a4105050906100190302d41c07401401c0708103e800b922894081d1104807542540340ba000030448429030002c4c2c401842d14210710802c01c280e0202821071080c43c1400d072800f010310303800c0b80b600c02c218110308030034a050f1900340c801e8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 243474073 1250 243472823 243472847
    0x3091903021207240807030504080c0109080a020f0c0d0b0601021524011704060b0a08031c1404080412060e0102030405070801050c07020f040b01031d0105011e05031c 73
    0x40e9141180042052000c103030401904c08207580507030304400070705130416403200482c005000941c40030f0009441910a5101c1ea40003071040429910300411070038003034207442441d6020341d403070800041c02401039501000741440c0313045968090698480c486001990f5512100401b03810303403c0386000500c00742c1c4284909100f280d02c00942d2807840c01c25858041101910314541000314011b031507003403000d6019451194032012203092600355680d8554801c1d024013841103010340c0244801001044603c820b201030603542c00050301d0381000300c0300080749000351540d0000e06001440003c3c14003010507241c1d0b040703c05558000d020a02e4840c03044c80d1040041c2261541c082440d4408020301003000404a4010211800c4200901c03041e00d5901c18603c0354800c0704c400a52018042d0019009810240c0021441c0e407814100080c00c8480303040256020340340240a20560795684006014950020074442200c100c242c0c500c008079414103000c40e983e01c065074284500000102c2920101074400d050300d000b1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 243475323 1250 243474073 243474079
    0x21207020106050f06070b07210f0b090c03010302010912081b06040302070602030408030427140a0e010c0c1104110408030a03060b070f0b07020a230d02010e0309190302 74
    0x14a40844001d00070701d00b0b4003d00340704400c001000b0a00f4640b21055800f0940c00c1550008141c48182095441a00740d4941505480749051441554490b0b40700d01181c01c0390500010030114000030400500850003000801c050400b8001400980da1104d085400e880300c40951120800c41410181c61a0042400345500148983d5010f40c0615010031030314000c5100b6001c942d400c0780c40703400c1a07031280201c0c0a0f0030410362050100b04001c04085c40e01f024a01d010140b1403c41c0207480140200381d6182039403042040e8100d1081c010120020321039200c0c210300c124020003100341e4a0700f00500300202100054426046136480149990329175200f0003c201c0c018402540d616654010f0ba6100d80040c01060b01082c9000b40000700a0005411a074419900428100c1e002d0466640c01c192800090590741c118411441e00e0f9000900009600f43e14100b040e2041441d0300680942e545086111000c130320869050401c60081400008142c84400801b1600321100d42031900010f14685034030b07400654 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 243476573 1250 243475323 243475357
    0xe1c050717040306182001030f020c07171614120105151e0904020607031b060614010e1305130b0a09020103060b0f07110604030807060606080105041802040f02 70
    0x100203003200002c108403403141d4018030004100c03404203003c60103800c0c0d0140c080010308156402e03900c01c2c0f0407407001e070003014100000c07101e0001000c18101d8100200011707561340006000e01800a00300c1079100c01890200041210303c60000b80001c0d20580e9125803440c9804004203c03245a07511030702000007003001c400800161a14584408002819488041c042d0010005002000f514248542103c603c09040e5808035125a42030000b964403c840c1501049110a031a4100e07101112481c0400c500502000c01d1041c00d00e0840e4110402c513550040c18420000c251507110346645405280c15646071100043c1641e909000e070855030880c2ca4010701003000c0c0710421003d8400c42d40b1a11205000b039804000d541e8076256421003c0c8a204411608050305000200000740000a04000140701230000e03801c103070350303030783c0b10400744c1c015800484074103807210001d00030340380d01c01e820f2401450111818003003d46c0d800c001f0071146c0c2180c64003070302441d140c0c102d003a00d1505a404550340c0e00c0705803007105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 243477823 1250 243476573 243476603
    0x14040305060f0129070b060103061505070501110a020c01030c02011e051f1215090c03030804031106070c1104200310080a02090708090c060414010201060503010e1c0507 74
    0x402110b80c00d000310f0b182849501c4590101c07805040d070314901360080d80d203103034940b66081d11141600d001c014601070402d500c1d5003000c0f40c88242d00c451882c4c14039241d203c65881c0c40c0a844d100303096500c440c5246542e008144256440075074001494080d2110a080008241220601c102d003d403000340a20f102da5040311000c5456030500c1d9110900ca0340800348407a04e50b03c030711400da24a40c1c1152090030401020b801c581e401064000640d58901c00e849000010a00c0d41507985280007400d642c000d80200b800b01041000707140c0c1090a218144050170b000d084580340904024146d4031081801030303c6030351107880200950700c45900c400440841c10030361440c95000042040d00300d610450b0844103516141600066298002804648890b8010000002d641d610601100e010340001c00380030040c842c501c21406541c035004010005001a040b0800828200034006800d590325588504d000b03a1501c51040c0d40464041a4841034810600c803030b00c044407001000b00c41500503c4005450014500200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 243479073 1250 243477823 243477841
    0x1f020d0c0309031e21090f0602032a0703391205010209041506260609190e0105061503010305030a0807121406040c0c020a0308032d06030c0a030309061404030506 71
    0x15603031740b015a590360b0038030760300c0e144005c1010085118100150b4020310199140b5201d42e90741103000d01155522280c0e00d40ca0b100d1040c030380451a80305450005042714055200c02d140340c0310340c421030103103103a8007490719003a508004412450320510b0150240c01c1d003d031007000000e404036405414014130900000d8150700090f9201006031203101c010807802505040005a0500c88034070b916018000905541e86060901164000042403a000280c2c10325a0148080251041d0801c0c200854000245440c11405104e03051040c4480a0304400041c801040054000030071942511540c0c50545080c0d210100d0550380400030404500000d401e144807a880c904007104010303c5140b0840302440f12001e0300744151005400c40102079040840da040900118025000070364204c0d0391180c10b41201c03901500705d81070084c0d0210300511001d80310000d10040d0300c0d00300242411884101d43c00c000d854078660700504204510b115000c1807000c0540f28040349803804098400854010068841514180801c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 243480323 1250 243479073 243479123
    0x601030c03060f08100c02060f070c080706140103140a02030604110118271b030b0f040f14090c13110706020a020f060c090102100b0a051f020d0c0309031e 68
    0x5017185507403901040e0311100e803002444038003418031486081d24540b00c5d510100e80d0480c1141c2d060351074802c100071946c00030701c0c20710440300c0300f41c0e00705082031103541103161104680000302d00c0e15142c1da005040c1240540e4004ca80c1d03540040d4800d0183d82c3d0040443c0c0140c40302d15000d00910072a05034040b00190f0001901c1c4c07156209014003111650160000708000102c1e421400380c9001428200300380a01c45000303a01c22030000c01d00074032080142e1940d00025040d40e40d109243c0050079200c1740e14103c0c218007107540c1034205443c0d501518030141ca683c00b01f450201c600000501013034903000c0032119005102c00300c48030746400c444299540c455410019685101c1b880b81e01c0700a00c2803034000b8005660400c20340e454034005034040d0540701ca085113054080c14048582c0343d170206081c2c500140d0703036554942c1031a41c461480e00300013038501c00c2c0c0300c00303810204c1281003407090245c41726040f40000c0d031241d0321109681d0b01c042104c54895072041110f1071001c0d0684d00174030304440c1104d2004070b240d201107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 243481573 1250 243480323 243480343
    0x1002041212030c080a2f0702031005070e060d0612080306031c090b0c1207121409090105010804030c02041a030c06040b0d0203190c12180b0601030c03060f08 69
    0x10800c60035040d1004404070fa203d80d0200002944042c04a8034040710f0b60421001505d00038407407030720140070b801541d00210045505881940b40020101d0850405008044002940d10030070041c900c2c1001d40948400750440400e44540c01c00110860940240d50000026140303a211001c0d014031140341c9507641d94001e0350014030a119512a48041d802e02da440c2604005241e5140c02485240c00c3e194207070741d0410900d49804c0d0041680301308003c0c003048040c1c01d40c0da028030300c260b240d6104090301500c00c9102c1498402c01794410828418141c59010342d050440d003003842c0824180d602c90030210369812004400030f510900781141d54182c254066820450f0300800c42c181d81082d028034007001101e100e40e214080e0000014400d1401d2521070754007440c0c1c031021104860309050300900401c012680458101004205070074402907080b11a031140780202e1a803040006510100c2d61a404503500008141504040e11611500005403007500001d00402e201004600210349440c100c81c1c840c00041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 243482823 1250 243481573 243481583
    0x2130819061109100503060d0b10030b06010804031d0f04090507080106150e1c0503030c18060a0c0b100902070609050c03011b0e190b03090f030f0a05070510020412 72
    0x5404414454002c1c00c0700e031690b80040c98070b0b0310b0000c211000d66146c0c000504a640c4405051844030201d1041b407441d40c403032540300d165000d45906514054a0704c0310050882030400400c1020000025000004000e50040074561140980f0541d4002046024144c40080e00f0a0819211404029001034400309880c03802001f40b145689581c0c3e1861290035201204d000550409061400e81c107120040d2000d45405080030103064040b600c810340395900c140c418800041c030004281c0c41c00080403c0d803c2c00c181c0202d4007117151495040e00101420040b01d00a0590211400810405550503440600810303141c5002d54440446040110040c190360302d00307a4481c041d461078600701c0c2c0f4040c03145550500600650001c03800002c042210042174154131180c2082e203030300c04441b151085801c102c000300440e50074039650745850f05500742002286540800d90742e00501400b14103070140c80560326200460318005480b0089400c002e4945099000c3e80360a583c40041c2c046000306100007880c0001d8010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 243484073 1250 243482823 243482831
    0x3110307090209180411150408070506040b030c0306030f1209040b090f04081c060e01140a06020d030e0102070605070e120f03030105010f030b090118150e0403030213081906 76
    0x22a6114103911510f40c0642c0d000542c424400e8610380040440360704280141c52000403521b010000c80d000c00885261402e103607002103010808100100980005040c0a441c0b42d4141840c10044034001e010262030700007080c00110001e081c1d51020054000701600190481303a032800c020921201c107034440900a80110b007410b94070038550402100f0715000d9540c1c0c610745801c503583c0751501402d5401c92014403001d0f5200080c0c219403840c1a018480c05400002c0d0707000510351409182400007104054064020041408200400c0350041a82c0206007a14200880c3c001d2401c00040c4c024882c4003c0141440d00c3c01041c0708600768000541e25a4000a6030a07020001d04403c505940711062031410305151710800060000d54856015804034007602d040c0814910040c00004110100c03d8112031440c075003032200403c000e1400e02a040200001c80c0500030101d04240028407000ea0060016040c1134000070f100d041d03055140c259800500c0e0380410307110202c00b81e103c444907030160000300307131251030038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 243485323 1250 243484073 243484079
    0x50318150925030206030c04090e030a0e030a030206060906130609060e01050a0e06062b0524030a1b0e0106051e0306090402130b0d0308090601090b030304030b0a020f0403110307 78
    0xa110302c190038a1207100d00c8592410b2840d400c009040d07200134040c0441040c02d22000641880350300552400d070f034440c0c000e151109403968000f8460f800c5800300034400d5104494020205c0e0300410481e80140e000e5034400c08560f034281c00304400d5130041940b481402e140c001e000039141d40c1607010605441458008940741d23680c4d14204054800b50713004801c210250b403c0401e00c00e240104c010446000c0490b20040015061050741c8040c000c00042c03011110748a408016814400a030110481c610201000d0703059208880030a584540c0300744d0050800310000f0070b84a60a0600302400000c00850300d0b9103115603100d4800404c5504148840c4d42e403103484001c603417030700a049020b480c07207004090700700341c083e5540740c00304407000450b4411003100690319500d1f00310586410034420232481c0a5220007015060001444e03103040c10503030002c0342480c038240d551a240d03079020045804583e08500e00359002c0c1c40710303a000e80080c450041e1440751000005400010010b0003a030b00742407000101c080d40d40c0301d99 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 243486573 1250 243485323 243485353
    0xd0315050907050a120b1008090c04111b0307022710180c11030301080705011e0c080a1e0f4a030106090902130e0d0503181509 56
    0x1041d034402c000704905000d0600050300c2000380c10801c0000450100d500019030010032510000e41c4002c2002900d01000c10258031000c00c004c949403242a181048010b05c1c00c4100d50580c0a80e180807001c0055001c5507080d10601001625841d980040a14001c3c2c528009410f00031990301107840031100c0e5a000007002d000c0c1c0003211204031911109044800380c503008030b800c01042200140380502c91501c03d030204201c0f007003010354003030300d580d8000388100c0703003014000352901c1420740e0034a071440705541e21204030f1f540c006660540e003944550203a840703016a600aa4901002d12110b2500d03190203c4952780b480d0344003003000c594902c10f8662030020320303110340c1c00c0c00d1103800b90609802e40071114510341d6030101d160310b110700304200c42508280720702882d000081c29136542e51301c010100c1c3c1d100c4058406601e004208050440c900d07010810030682c218083d15120b010407401e40d414010003000058441013025100ca0380100f8035425203050a00408444042200c266070f01e01083c4103054250100003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 243487823 1250 243486573 243486589
    0xe07090c02100902011e020303090f1222030602030403020312070305041a0a0f0203130c1706040f11030118060c020d0801150e1002030406030c0c080d050402040e0d031505 75
    0x5000e58081c1081c882060406806403401030001c0b410840030a40311401100c3c5940d041d00e203403455502465490520700503140c6004002c04070300f020354200c010b840000c01300c9030040b0307107580c1d1903158001e0401d5800010003010400d9548042c08a1303000000f0001010743c08401481c0030b001c07115511300b440e264800c0441c100c40003240d0003403030040c8000132031052051031120b040d84090828804a81103c1c0c03400e1080584c1c000361240b6042c442c0c118200010003007521910000390055005003000c107182140940c1d40c551010300080c00041054243d10309211400c00c5408810300050020301041c801d02c55100c0b420840d49406481c240d103400000c09000e8404640119900c88070740d564240360f402d201c14003000710b14600800d03003800000e116640c111703140e0700c1c41d2245804450b0041c5407501c5c640080034050700d0501a0300303000c0101300501e03040080d00600a444180d055000c0000b4255243d02c00f0070000d05584808095504c42d041d81012202c0c2c8c16041040b540808401c42651395580324213010002c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 243489073 1250 243487823 243487841
    0x30f100b030a0b06091306080c180a020304020f060f070b06030d140f0403050a030c0b09010c090303050c0736090807020105070c180501060305071d06090102070506030a0e0709 77
    0x50004001080c482d0b986a0044140b40300c0042c0a41e180031000d1000641030301d91206450b000e01c0c1c880340300b08290001030101c015851401d6034410300040e0900c1d0b1700c02840500500307818032141e0101c0420b0a544a0348110401004043c100c41d903119500100c2c403103660418441102c01001c01400500c031402d01150080c4611030700e07220380405620001e00e500080d08548800c02c01541e051000202107407003007050100050103a11007140d0a00c20741808007220a005080c01d41607811321400c00c14041d40b1105c29412642c0516025403150b001c921500d041039055440003015081c2000f90501a02148001d074007404540da200b232103010300805100040e1854898080e041200c01e1240c54003650182c40240702c640d105101d060106900e44420400340c0d4001e00094115642c6c0d5001800303590b804d845a250800740c0340c101100640300361618000402c81c10442c0034018200840d05003010f0b40200484405800e00401c12510792500b01c20300c0d4014585018001100e1103903807000204204548079040f11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 243490323 1250 243489073 243489089
    0x2030a0e0f0304050d02011215030b1510300e1e060a0e03040806010b0d060806060f010f0201060f090b1008010f090504030c080307020708060115051e040f0605030f10 73
    0x41900d00b034204103048500143c280e0500581008c44402a0110f200300c41d0030f07160085200a0550071400c001d184260001d114040800c07003448905060b07503511250140d51883c500d040210b284024018000341e002107404441c081d020a071440480721310a410161011031454110f592303920b03200080008070640c0c40c1c159809030f040300d40070408120194200500d00140a02243d107041d17034031310350795290040903402100007241c0443c3c525212650b602421000b01a028002c0c940c038100100000c3c1218044c01800741880035808040c40d17818002e400103402410b00c10600d1a9055071840c0c10300241a80c5d030030582c410341449138029003e502404110341a01c425502100c0d050f4240203c1b00c00608002d8000e609000880c4810400100e81800541c8507061590251042c280703001d18481c80c028060300018004c2408100034142140c0c0901915010152611403207400c641d901a80c03080c510450308007202d00c004403600410b00d030790041c004600a4113a1005040c0d569035241c810110914103004a1340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 243491573 1250 243490323 243490327
    0x6090102120c030405011401060819050106080f151905041508030412050a02091e0108010204060e010525081902011a04090c0f08070303032a080903040b030a02030a0e0f03 75
    0x60030400b220203180d21511880000401508103100c034004004268060400a2400410860144409000014003442c020420710640d410b103c80509480c100821442d02410b404000072106041e0f03034079144000c50003501c41e00f15800010010030741070b4240d0250500030350403c1200c4919500b0a6071140458001401540c14a801c0c50582c1c002115140c1041d1800d20a0030340c100c0159480f440b60038000c480700c0b000c1e0301d001444480084081801680010b1450f48140400c000440c1c0002d8121307142d881c2443c010ba070b156540b14a40f1081c03201500c0c540041c403040b01e000c0c0100460f00004200621807403a013048000e0410408909840e07032031145598035030441520110900701504171584142c443c503000c01c42c0c40c0e12040304c07000c0c40703038554800399080d48807440c108245501442250103071000101c0080c00042e41e0303010803040c040c01080403010086e12200207044d944050040c0d4000e840326100d01da030340c1e050032841c400294005030340045281d031520380c58281d00040003401240425a51010354 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 243492823 1250 243491573 243491581
    0x5190303091206060b0a0e1009060207090b130906091e030e060f0909190e030f04050f010c05010507050a0f020a0b0a02030a020c0a060e011811060901030914010b030609010212 77
    0x5403109000030b801c562094460304040303150949030028080d06422580e41001103c0f004e401c0003203145200c882d980c1800000a0140506580402d1441c10b0f90600c4001140400e07240c0c02180e040c4029580d8100320070f140018030f030704202664101c0064180911462802507100601751000c151404c0c400501041c800d60011800e4144080503041d11141200c10904211411010807903150044605150710720700f020405201400c0e0303100f900302e40c0840c1002181031460702e04400310244681e0280900c51140d103000065103a03c162100c01a00c0e90000c0280101d040480010b440c3e031300240359000100d03122456001c20144001182a240e68010b08400d10030b44130201004000d41c405001844595020003485410150400c50030310420f00c2100001042900d0f00c17512400c691a0440740400c0071039011004021603d00744031209c403041c080750800d070703965040130040c0d0083c0403c0e00d000342400c04080c151803085070f041d44030844600d415030540c3c0c40d954401d245103080f4442e10581c0c0c14207201c01004a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 243494073 1250 243492823 243492839
    0x602030706051323010518031b0a1b0f0611060a0c090b04080f0705100909020306010c0b0a020d05010b090109090e03210a060501090302010c02100c0c0803040519030309 74
    0x10b80e03042802c0d91900b10b9290140c2d251001000c0d103840c5140d10904803107441c1211031009100703803076121a0199030100c01d407010040c0c0036201c4c403460841104102400d2940c0b1488001409003803045540000f102d5040860346510281040c0c16201d410520b0380c484c400001c1c094041c4203000c0c41140004003410880e92a451800e0003065842036141c1040b070f10300004540a880744c002003000d055100003e040c8143d2010202c1e1402034030340c001901500f0b030f00d9a48a4407036008413030103050b2000d44d000543c4039075a03400129616441c00f00081c05001051081c0001a40309074010412140b42101c01d20660381c0f00e070180c540c0792203146901c80c0014441c610820402a80780e00c0f0403041d140e082c0591f4600302103035001c40442d5001e142d54a071099054403e200e41180c1a2080f84000c10302070a11400007895500003908214007110041c0c06100c03c40203402410f445100703c4a86607502160030143d05885404841e62a041801000c2c05189d480c81e200c2c0c0c960000414450443e13915580300c40c041401c001c09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 243495323 1250 243494073 243494081
    0x1f090314030405120a0e0415060203030f1506030103031706030c2d0d060c02150402151602030f06161b0809060d050f0601120504030801060e12011e0b09010602030706 73
    0x10a03103c42c002c030f0101c180c04440c0c050081981910320754440e6a88004c0108000440b200d440c40700d560311089100c10490290044207507a4000140f45025410380d84400400300c003003481000700365000b40000008010550460100303040481c06002c40074150b59043c040c141d0b645000e04d001d03075008000c00092841101d4100360080c0705020140d20390790b542c90130808522251409502100c40c2c41e1203030584e001c2290b04100010044000031031b007400600f440d40101ea42100030f0400d000200400161301d6002014403000f0310382c0320341e0240c2103c1095500200003915840c00390703000c200040078000c6402d1614410300201d00b4980b03c044a00509080580d03c0c1400c6502c2042004d0300164203210070402d201084c440e0341d100760110040c80100d031500c0800144624001400d981d802e500d440180404a135000c2505419104d44e07040194129403040009043c61046000f00103140d8200031001111480840d601c3c000c4c01840365050003224040401c0108400d402d015a41c01607109112400100c5d5003500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 243496573 1250 243495323 243495331
    0x306010801091a030703140c0a0303081f0503100903030e010c02070902071b0b070201021009081e16050304091104061d0a090f020913051003110a0f06021f09031403 72
    0x100f014001d04401003c6424803841e40e10603a0303014204680c04410348024030a80303001140481e040c10445046690103050700b03001030643c01102c41c1a030071000c1c050600d81c020302c000e01401003c465078042090300e030030064200040110000303420000841e001e605c05000d07100c844034254010300826030400602100a400c1542d0640795132004800382c207210001c0c0c42c0c0c0321000c1c3c9079894006503105043d0002902e4008a8000d070600ba43c5004120804140a201039601c17a25145050402d104203220169005009403911495440403240161003000700002c000c1045440f0000203004034002070080305ca140c042d510691000c9480b400c013440e00321303003802c40307200f55984000c00c00146292101c0c41402206c10050554258550011b980d1180d8a4006080b01101c0064071051140d442d001010421080c21071000034108201d0f010154400e641e40c1940701d01401e801b950050480b80c0d25a40259a00c9991054502c0b40e500c50000b001181884d006820460b9096140d5508011022403503042c190310040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 243497823 1250 243496573 243496601
    0x1051003020d0602090405010f030512030c040e04050106030203060a0b03010b0a05030a081605010f240f090902040e060405060105130e060612031309020406030f090f140304080106060f03060b030601080109 90
    0xb94045c1e0780d164402d140c080c00344020811462821807505900d0322a0708000c04003002030500c200240700c3c044000322000e480d50303104d41080a4a9914049001d070240c2d403c000d600d40101030030002d0005232684820340d00c0e10105c00900c5070102400610440050600030517030035401004e106c00203d41d401c0c0c0149444c800510f141c0310316042c140c50b41800c565021f60007840030380d151081022400003070075040040700f1614100000c0c607032410885054024030f61050030f081e1603d80304003005550311035010024144c5080c054620354502490181d88400d024011688940611600c07017007104450f12858240716000402840180c40d040100b02c4402c04070f07026504588010807410b10140e009140201c0105008000943c441d81003c501600740c1d000451412041841c08101501281141540312035064102c055220030318420141607095203d0350300406420340c20082c0010303500b80d1040f805119241039036820000035491311010f40030741c070054070710a001540c8140180724444090344604030451803c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 243499073 1250 243497823 243497827
    0x1b0c1509020d0c06020303151c1401110d050601020105130507120f12021c26060a17060a0b0a06230c07060509100302040302030312060a180b01030e01051003020d0602 73
    0x980e40c1074030f007181d140c02030f2006800100a1041c42450801c031020482d0007242c04124644498012043c8508100300103402001c40c4044401408020340c0407a0180e000035030381661798003114003020054a820307920680158680350010344074010b090600201b00d030f400b201418ac41840e201680d940b242c0f60a0040e00d04110f4a018030000400c035180c080c02d03001c2c154015041c02007100f0414034084000b00340384c400b4840e1003406407414040c1344030f02d00c04542ca0903201a401d51203510229005000a8000c001e400c441c0c01540000c90400069551046040001c184903c0f1030340418020b02800911584c00400c20b00c403480c510900c4111010000c1d480408040c500300001d43c246d207468240c83d0341c00b40e000715000281900346030606403401e82d0201034a040c02d47c94a0320390381c0404d07030340c5c4a1050b4060070082c1d00c00c080340e0381d55200c1c0d030341000412044400d01c0354400c140300c010005100f0a20110f012915115104c0c91039241800303680d1003541c1c0c003030442c29020310315001e101c40c1c0385036064100c80d21582 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 243500323 1250 243499073 243499099
    0x10b040b091c03080405010b030c01020a230d020708070b07020906040c121506080109060b04051002030c060a02210708071206030c0e07110304080d200d031b0c150902 73
    0x7548602d29450196859080078201420302a003150369120596000360041d08600340e01d07980000300440d50a1303104050108420b03c1c0380d07801c034510074000082d012071f00445640b8241c03151700050003400d42e108001074500d4603641d40d404500c10711801c00001e40100007400040c8031840c1581c028020120b103820011148180402031400300c07031a0701400c010261800c54280141540108601d0140c80c0300b220402c80faa060030080c42e200c1c001d030710405109209a80306150010710a00503940807140e900300311200c60410342181000780d0081040041c84140d402111141030030701c8020303503004017801e4130b403203003552a441c1084800707800c803803d140100c9807a21000000a5070070010007008042e280b100390480d0134a83c41c002c00c9a0314030065070405600601044c458900c011809072002c00c1141005446942103510841070350189151680d000e0089141e0042120f4054001000c203060205407085e0700618804140e03640800700030080c04004005000d1a69601244d000010850005100e8101040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 243501573 1250 243500323 243500359
    0xc010e0405040201021005040c1d0606090d1a07020d08060607030e010e0a0e1302181012030908031306032706020f04210201080a090302101e150806060603010b040b09 73
    0x47c040d901204c016407204400c0180d07400d104d207044400c2c001e0702c24900ca0f6081c0400000d056001d8040824420891000040f08104e8420804241200402031203180d40c030b8815000303516a034400f4881c40c003244007200060598a400411603400365419201e186100c030101e0011559092240580f90b0441c07194074001c104500101d400c944503503a40b2441ca8034104080c418005414400700b800c00d101c90f040d00a002010048160079010760f1020b002d41d00c0700c6a11800d003100c518000742c3c01600c5501002410215156038404904c007600c2c4241c074240101c00c03000c2e41c000444038020654640b005060305080340014800c1e001040c001d43d00d00101410562109030b450301d07010350720704180c5c0c1281500c17031080c045503002101503038481c101c0001041544019200651a1950b0040c0d40c0103c80c0da81003003130b85c1c3c0401c0501d10141224241d80c200b2032041c9011040c0000c1025001d800800d100f0f24001801c02c0c80c046c2d04403030598400d105540c1c20149401c200e00b43c140c01800303c040d400701e5a0450b00d00809 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 243502823 1250 243501573 243501581
    0x30c020111070b04050706180603020309030702060d090c050a210204090212031b160302120a0b180105010f052209050d0801051009060f0f020a080a0c030807020c010e04050402010210 80
    0x79000d40f030160401d082034034007a8984113580d4040d00070b0110004840e01c5c200b00c04510304080326440d003005a52560b0b51500b0b40d045201d43c603030083d03101030082446184503030b080d0310111130032344100c03c40380c00385490360104080c11915206402d0700e05d00340d00802d040d03419200040500d491010300003140b802c410707070b00203154100b01140d1080143e01c081051612000141c401030058100c04019000b00d41041075011000c01240c000640a41c07d49100501c25640400001543c0c0f40c101403601c0060401d10081e281d00c1c040c0880190441d8200000407c100701d4440000f01114402080c444040b80c2244105007010b41d40c2c46c1070058269030780500340101e4814065451035112607503a40807190705150400100350000b81c00740b0b0401c1842c0e4403e000313103a0004100710100200341400045192440d01c00c92a250b0307a400001c005260100d0100c030382035000b80310350303012a01c01c0c3c581e420503550700c801c100d80d40d1590560107800180fa4013403102c001d08007907001d590014018811784000b152080c030403005030703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 243504073 1250 243502823 243502837
    0x50a0b060a0902160f11040509010b1905030601060c0203030d0e010b0406090912120e010f0905210306060315040507090e070c02210a17042105060403030c020111 71
    0x440914041010340e2800e203009901400c0080d400f14107004846400d808500c185078002040c1d001a0700803c400d024240c0000034004400400900c5540f40c60642e060180650300101d03406500e5140c0403c1180c5905c460100654101130028556030f0700c1c0040c111490000202c0c00e07601800104100e0500e07051030700441040000701400400c0442011080c8021500e280d0300909000e803800c0955030005600b940751250059003460500c2d8007014415010b8004d02c480c0b58404519032030320000b085003001c550040341000f0b01407419500194881b60204510300c8603280860280300b400c20000b100c5140610203950044000000102d4800002d808202162000e40f80c1e10007041c02e004d4100602400070410380e6020311940b4042c4030660b2075602040c8501421b414046d881401c0c807400344412441040344500e46500b081903240310401e031881343c9240e030307000340244081072070783c920481c40140304c281c030010920746d01c000103164941d1103442c2200180b51200405045540340c950700400040703428064a28 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 243505323 1250 243504073 243504083
    0x206010305240609040611180f030105040209040f0609060c020610060216060e0303210103060b0312030a0c020f030c1b040c02030a050a02010213090f0b0316050d020d050a 75
    0x25411400c016160844076821a803071031203046080380d084468604401d400400aa40c0700c141d5449510300a030103400700d00000103c050000c10450403502d041c071000d42126209484a2010101002c18035003618002ca4010b50085503120200700061103080d40040b8550040c1d40c0020b081c0001d688000a48150002140c01640441e041c801400d60180c0040028411030000f1b1240303910f00031500d030902200d445603809010025807c800d554a081c0201c0d455805150a05000c1d4210200c14070606034003070205541a605d0400742d040e843c140010020ac0905282c600c03a030455840c2601d800140442c165810214014804101c003251000c01c060701590180a01605458410f142250005840c80304660302c59428668144d003e15000b10407500c50303029600c0e048c1d568401040b0706a02907c0b500c8520034003e9095140092400c606030f01080c140781d4840824000f42884030105652901840c100760700750340405000f08114902041810f48062015080c10504135540d1907560900207600c1c000c2d21 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 243506573 1250 243505323 243505333
    0xb0907140d020a110105070309030807050c070b0301060918050103030e09060301021c020903150105060a080c16033614011b0f0317010b07080a0e030a0f060f020f0d2a02 74
    0x4104c0c0085c001c0a902104a10b003c1080500d542c81c02442e01c0405003040e030070f000001400000444003808035801404500841c40d03507039691884002e0000340244a02000100f04503800c6208551a016a80c103ea41655841c026031440c5010070070040c0300501a030764550b60800800601100401c107190591008541c01a255074400b000d050610181b10110345000c1140c0c2c0061101e540c481e0180d4010540e04d15003010b282c0c1d240012070540744110040302004100921209041503071048000080007203481d03c0218880300004060302c00100008110030b030b10b00380103052111507000348a28a101205140c0480300280d01d011100740e581002c4d400341c40030b02061030400141a000310075081c000d80d851903804619071610030380c03401500600324010800c4000080b0450200c0c0304542029420000806440351030700e5519101c900300030802e00c01c03240107041403011200c02079244240c806281e80a8000c5142c803000c5503000c402410700c600f034604921111840d0a203001180b94414a01c0040b9070000c1c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 243507823 1250 243506573 243506597
    0xa05030a06231e180915010b0307023d0b060d060e070c02090c18060a050a02070807060905010e030a0c030b0106090509040804050d140f030406120b0907140d020a 71
    0x800c07200f05032480c030100000740142c1d00b01192606580940c07404100b80c81c440b43d68407182452030030700c80c00d26541a04121100000b0036004070110045028200135000c03101d044403891f81043d8426480754000c2003c02c03480302c90481c003002d41c0000684416000c02e000a031507502500246981d0401000c0d14501541c3d21814402c000c40c03602d2141c1c2258143c2014456000d05130300107021888002c040d4081c0038008180c620701c3c0d05010304501c001c0c242c010061a03c034004010020016017201003500018070a100000424183c082441403d42e05e0558038a400782c1e041c40015030b882d4410f4140d6035014480c3c0b00c0180041003544c00114042c5200719151070031545400e1004001c119640c01c80c9118440d074000b401300159101e42102c0407241c080c1c4a00d031001200b81071420500e000c2204203821801040b20700c047c503d03002300080040e41d41d19240c400014015060820807600c0040c1e800790041119808111450302800e01c4d42520702a9541091400300c4030040e400c1a038200c00c2d0408040340e0140d11075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 243509073 1250 243507823 243507829
    0x702160503070b044a100302150a050c01050a020a0801090b130e0f060910060e090d0e0604080102120402010824060a0c0c0f0305060108030307050a05030a0623 70
    0x548010181100200800343c280300001c2154803951052a1000c010703105405183d64030802100d50411610400200c480781c09200101c86080d4016012004c5c00d203d400528a8442030600303405494010700f00146d03501c40c011190410f540074151240030f06c10280406c0c6a4448240101c512401c00048090389800d002007000e002c0c1e00040c1c02c82150281088400304030758562100907510707610041c0011860403590a012814070f2410302c00030703100303001e018204980c0c1c401c00181568044200c2c1030812a4071355030b452905001e1001c0d100381e21075801c101445044580311f801d043c0c0d801400101464507181c2d03500081c50880c1c2c0035610062501c28010100300c29585c120303180342c1d40013003812050400400c4058504805004460341e86103e41c00c046254104288620034818a1a92285150103115100c08001c0000d60092100300c03400d1040740000310f03e555022051b28000c1e080b43d01c0701070501d0010310059400b07401c01440000c405a0f2a000040c82d40c010100c1c9111400c2021040500354000d003080c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 243510323 1250 243509073 243509113
    0x7050c1603231911040207020d0b060a0b0c03181f0306080c0406080307060c0e060706020429030106080603030d1a03010c090602190606080d08070f09031a040204060b030702 76
    0x454511900a81c421544504440fa5820707400c03503200c40e262002030360f40400030f03000707005211010790400c00384485401040390a80026010319001c5030b038608000d5890080d62190b100d68075844c4440c0e0800c1c8040f120300c0c0c110a80d6a1440d0030018918094030b06c20410944a107000000c40d000081c0d00c0d590100400d0380b0920680020590603a824801a810081c603680e4900c160103005060550742d50b1120707a158803500c00c00c0c003803c40040c02241e4800c55824600c0c00fa412a0050f240702420200200c81c2c0e03100a80508150b0105911041b8110380c40e20342e041d611410001d1002e50140020495001ea00e2a10b1007815001d25500180a03030203103080b0180360031108032200450510034200c0c1c0901002d070b00002c1d0781c401c0140130400440d0224062070264058105540020350b00d201351031108141d690011035a5200301240e507079008085c110003400b02ea8110044c44003500c403805000c0303081c94090030381e808142e00900182011460555500003c2e0040d130003255030000580004000982403400001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 243511573 1250 243510323 243510383
    0x60903010e0604050d03050f0601090303051b030313030e03010203040314030c0c0102190e03060105061812030a03020421020f040c05070c080c0a0e0f0a051b0d0203010509010e0f07050c1603 83
    0x4400f5200c1d140210010b410b03800350f4003014061041c0880d410fd49040b88040d03060500c05408240d0b52282400540c1069624018400b20089406034101c40c160b07040520079203126a4055581c1d2040e810304a6429181d40d0000e03040d10450b01c1c0800000e51450800d0008051400d00f0160030801c0450041e0020600c0380c2154115203e608140010801d0396a078009176003c0d01c40d14183e005a001102002940404182d02e440c24180004a0103010080e0580d0251080720742d40ca826848504030944078508122100b04000e5110b60000d92461035405c180d03002c1480d16100b424038070710340741d000d480d83c842c0c840d0b8035400b0154590140c9c2c442d6800d0708106241300d00071301c2d81c00d0301d42c3c030107017070441d422200c616004000c12600340d55180001c4109400d03c0b072038030201100d645802c0c0c0d500000013155020b540700340100da003d0703400c2d113000040c4d90920030240c0c0d2050908415148103500e030344008440d5a4080300c607201c0c2902c240e03e040084600072807d91802140b10340a51400381004109190304210005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 243512823 1250 243511573 243511591
    0x12070809010923090f0702060406051003050a0c0333020703200a0618030e0f01050f04030b010504110c030a031d120705161511010f0e06040c090614060903010e0604050d0305 76
    0x3170280801c294000030601e4010741d001202042c40e0f07551411050740d14201e40e00142840c40b030200004144009800301e0340a9a001d0104c052140c032150711400d800b082543c1c02e040c1d80d10860300840100000c0d035406800514846c3c94600100c1c8030700da00c078164220118010004982001c0f5425042110f0b0b880b441c840600c050307694600c0700442d610003a1007100c500c5003250048603003400800080e84200304861551070008803131903d8640700d08014034000c2e82400b43d98011842c02c00004440c40c2100161500224034900a62401440c40022000341941c3c4400403080300c0c070300e0380c04c90000c142444210300c6503540150050301c42002d414441d10f49100780c038088040a50040e400e1014020145200280160034100402401e4540040078010144000c0b8031032018a080a0320712900710108440b40264010056450307919110101581112014850380a5645201e80d0003030050520700090500403170001c000056521007440c072075040c40c0d41100c040350b076600300040e0a6441ea40511407550404155 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 243514073 1250 243512823 243512851
    0x6050406120206091f08161803080c070f1d01050d17300103020f0a08030306010e040f110306280501051605010c050408010e1207080901092309 63
    0x104040301d8034880024040d0041d080010141c0e026100d003080c0102d0048025030304c2d2101d55911030014110380c4191500c01d2440700c01480d140c0d40d248030380d88030b00d0300c21541070039055543e156648240003503010340700580c1e29003c0c010000a00544e8403ca000c0240002c550384000441302407444150000160002485030400c43e01c1580820004001010b4900c00a0400d9540300e0015440040800c01c2103501c008680301c840b00000c503c001e00003020b0490348203840c081e8400d450b44042040080260159803565481840010300541c815400c400b06440b01400c0012165904c80b8000151138051600c0c48011800005102043c204507a0a031a00840c0b0340b1003160075a022008061412601c1c401e0604001002c01c0700c406519040d14203d031110390110080200404001020b48036030081d21034200d0365480e060140500d15004543c0040d44004c0700101c5240208613a5040e000b500f0a0180c40e0400c03640090204000701030351b41c0e01101ca811100000c0202008504004044400904518001d000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 243515323 1250 243514073 243514079
    0x1c0801080d05130608040206040b0304050307020a062613020303071214160f060b030a060b010305070905150307110304080105091c0c0b040203100908070b09060408120702190501020d06050406 84
    0x10907200d9005a92003403411405d2074403280000741a80c003464210101e80240001800100f280000003400401e100740c804c41515540d6031802e807103024000441390032500103d2060340d4100c0f000c003c913a603c0a40142210285103164002ca461504400c00858940441a00c000724140d003203041c99601c90030a10b190f525240749407280042119140000070041c0d0340c602407d4040000c00d801c214485c4902030708172000d40145040c140080c01c02000032501082ca08400301d00b13554810401d8105841d0040d201303040f44010b1020804c50366100904250030003004d00c03c020540c9100340010700c000e0411500100707150404c4502541800b1450840c00c60310401c00b591498940c4d0040300703162000340c0050b03030f1010390381e15800031074140402c08240c200154a812141010012807070090001c0d6406107203050404d581d112406c41da944820398010302216002d00100a8807018681c4a6600a10f14410f0383c040c0014070b484000403a400e20421580c594011851800c100094807039000204000c640c14005185 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 243516573 1250 243515323 243515347
    0x3030207060e031c0f0306360e15160c0c090203180d050423060f030703200307300b04061809050d03050609181c0801080d05 55
    0x120301e1081809000d4101c05840c259503040c000503480715000e4542c00d884071400303000146840f0403038a5181c003003440e101011880c038104204001041e40308c04028904400044c4c0414520030005052604458560a004062807010302142c010884200300142083c02e00c001c0480c4420b498081d2501004540341204001c82d00021a81085410000e070042c1c0e80d441d042000e00d84040c0c1d905082002e40b00703020360021503c0e8000010011168140c21170745003044201070106a5820034100d0030740c004414013440b4011005140195048235981c18000b0b44000ca192041d1801024040820501e14010042010841d081100c030000060040004640c040c5030440008003500e04944251107030f40e603007820780a02d0320346501c403a016280c1003101130b00001e00501c0c498003808107244111100d02038a005c1031340c0380c2d01074010540201d100402c500f8040e500c85c0c06400216100800009081c46400b1255110b4136441c0060321101c241c981d02c405917503050a000c20f151101c4c20301d041003040410446400380003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 243517823 1250 243516573 243516583
    0x506010504150203090307080616090806040b0c120106031a0301022113140a06060b0a050f090409080a0c0210170103020405040c05060408030903060105010c030804020906010909110306040e07030302 87
    0x446000b85020071603a0712038124a507018030903c080c0c141c8184040801c1c0c40d100064024070441c021016208414159a4103c80303003a034910400d880c03070303012601040c00203608901c00341d130107120600d400381005078074403c0c21801e0070203034015404265140c022015401c1800c40d40806048154025441d20b04240c02c0b0200700c50020081890100501300400c049611400070054640c3d00020b4440b210011071110700d4550000040480340140b510100040c0f501c03007242522404002503d807213003882c0c10b56040040a5101d41c1c1031692241e544d6030083c00040e060740290041d00d1103036658016001907441031010b01401c418000051000054121604250119010741942d43c11766021a041d241c518082d82c10a00c650866607100340042004240b40c0b90000c05406500801c8040702c0c3c0d117036030324001558400e101a601030001401c10f0001000360030210300c040c0e0413a0043c0740211a00765035040203000c40d5050701340f00000340c100005102c0140340c40c0c021900781c0c2e8140b0300a0b02c6103500e10780c0c01a56078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 243519073 1250 243517823 243517829
    0x41d010b0705210d0c0207051003140a05090304050a14041d1902040b03071502100b0105180a0b0a030204080114090309120718021b0a03210f0f0b12010506010504 71
    0x440303181c8043c812072402c850207407002ca045102050160f40030307040d0065100c4000e8007a0390b00400c443c41791048d20502c81d0041c122a454842050602902d880d03c01d000681002401011648001c0200180a4403481110389c02065400702104d440f40a5204000542e20000e17682c01c00445e41a5549804020220343d6130f074086c25680b1b01e8110b00c0d229102041c0030f0007010207016414044c042c0300141020072100046a400000e60a98a81550341482602143c00000107180010003d0004526031403200c0b9103607a6280c001000c2d04101540ca03400354035654421540c0f2800a600810100301343d40007405140c8049002030840c03c034500d0980d64960352070096250042c4900c0e21044550003c800a1092402404101c804016240340300b00444010b90b00003404258440d120100140c01d1100104000390010b40c9581ca034000102c01403440b91510701c00d00800d18403aa078501c01c1d65040c078141c0c402c5061070345009002068840c810070820100d200c1030040042a40d040404000031a81d01000b26829 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 243520323 1250 243519073 243519103
    0x10212130e040507060f0f0801050105160c0b340f02060714010504110d0c0506030702030909090c01030b030d2c03010f06050a0b07020a170f03041d010b0705 69
    0x990441203540e03003609440740c1c0a214a80d50303030414001031041c00b0034200166041c9440d030019124151030122000c0c1251300d4458002001c220051169601c04c01c01807420a00001181041c0301c095103c00550b201107612000d51200001211440c00c5400f1000c100822000020000040d1100e15284490700c1707030042c0140407420103102c600866171a40140d0b02119088400c8011064945036124001d08050b20300b5110280482407074010b41c80c150001c1343c190341e445098005514503002c2030101c1c6030000351201041d80020702080000c0e442700312410748160440342c002c00080d5007138070015040300c070181200340c081d801111b11030280c690025440c00d07a5110520400300e51000108455104a400d000100d0341942484160b0740c040d5000d40200040d907c0c201c2e41400030b80d0f545c5004a00621555000940181880030b0404c1003042909101c21080005425621f0740b0b5070540742241103502ca0b4004400c80d04802c00004800e602c459651400b41c40b1b01110180750180649684d65034200b07040c0d56101d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 243521573 1250 243520323 243520327
    0x20f0d0c03091203141201050a0b16030c060f0c020c0901090e062809080d0b03011a04051302150307020607030204030c0e07030609020f120f06090115020312040305030114040902010212 81
    0x4101413143c1000d13045800c9a60b80203880c2c018203001b00045e41402c0c03044511801c1c541d00f02080340591401110001c00e030130300f00076051001e140e50582d50050010819911296070b4004800a00418001c80e855980d40f07a011b86080065071082140381c00041e048022441d02e00f00440d4940103002a40c1a00f0040000f810824803648000700840800840010310460382003101d028100141c01c0041c020050a149050004100c21400d044c22614080110300c1180f80c02c002d0380300c46040c103600540d080020061100c6408520750081b4108052999021130440d20020400809550500c0483c1e007008080c0b505610341031030343d12011000d038a80c4c01070600c966095004104898000c1d440306004010302c040540d02c0c0c03019140243c450340c01003010040c44510308800940082404452244151001001c03c5a03990070308003069002c4c40c801940c030301540310804c44001e0390041e0030407152296100e80c0e50183d13603606011f24464030914803034505015030700305102e040040c0c0c1c01142c440311440740201032075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 243522823 1250 243521573 243521609
    0x1014031306140f011e260f12030114030309031b030712080703050a120603030201020a0207050604380c0a060e060405100c030902040f050718030c0905061f020f0d0c0309 74
    0x11003d404958040d0040040d003000080e40c03030120421007101c0b4101d02007900c1f00e01c2d1042501c01c1c0c5075801c10701c1d881c0904208200520000130010104620f950000d002c480c00d0012a401081c5066611081405c03144a401008041441c0c00c005ea10042c043c0e072440041d82a00030b07030b100004e5002d2610000c0a0040201e0580015440b81100c00c01c906042c66050103000e550b400c0180c004d5101003041c01c010302950f1408521410000e0840d4112681c1e000120946401c1c0c850381000b0b00d03525416260b0850300c2a00786408903da200c0038058000054024122141e994503102c010bc5821364031180702038205004001c08107401141d08a804c5150030000f2480d0348148004800810f0b40c0100254400d1501140304a200c1580d80702c28428069500c13904081201e5075100c8441000ca44801040c61503540b10901c040050394100070b42101f00501200030103885603244c0c12100780c1c00601300c1d00581c010b0320052585407041000300942103031800c1c80492020700d500d0040018605000781100540341503000c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 243524073 1250 243522823 243522869
    0x70e0703090b070e091f03060c0905030312090129011d0a0303050d050f04021e0a03080f0c0c060f0d050907030503040303020708070518061014031306140f01 69
    0x1840d05a01400e03040b01032800f40400b401d802240c642c600e00404103203000840124020395003400c64482c4a041d80d00d01c0349541c0c0da0380090301c1c0303080c201c0080060200002a46e510104081d002072f4083c1007007004140f41658045d403c4840305115003030305041c284110b100d4520701400ba030803100380c2883c2030807541705105c3c8941c46400c8851006134000050b05000402d140c0d01c035000c0c1182da070403104107000300d8941e016500030f000700598000c0d603c0080741c48400c001c207480c000d08070541e20002d030901c0e02c40c0c0d68a4451454580050f4440311009034000b42100010f0313403e000c44440c128040310143c2c00c082c46005d100c1c905000c2c1c49207086807103a803480443c006041c100f08101c0215031100c112507a89440389002500d540d036034481d0b011940305500c0049864500781003903001c0e8041c0c1d05e07031000b029601c0d281005180201c00250000b404014004031140d01100c00c0110301c107a070075864109621b41645040002c03504840300401d030802603242800b8201412030f403840d04451034040864400f0700c0712040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 243525179 1106 243524073 243524081
    0xf02070510201c0504030203010b041e0b01030204030f0c050a0e070228060903081611060106050f1b070e060d0302060703151a03010e18070e0703 64
    0x4006500705442090000c1040907000f16619851203951222481034080008000240300107001c2c03007542801d00039284407400a0713800b0486961306001a034840c1c6403090b04409810348582040c4070580c800d0f01070b2005103400080a03407900c10180b509400c112050300c00d9038080c4031105000904a96100c4070240700305041d8000d05440754804100c0084071007038880d0b02d5504000c003510360340824460721030b49072124808d490328482410b2a1415408803000c1c4c0034904100448081c140c07000d00b4020030b103a41101c009082113038440806400309101c501581c041c00e80d1001412015035280a000075584003142c1c0c8030020307003420b03444483c14002e0201240202034050707030000020444040c8640d0003860642000071800b136010340c940140c01800341444d4080707007081d640800140f10340640401c0d816003005605800c5103801460300c8500e41c40d0f28040c4102c0100d00c1000c000294100d0207500 = true := by decide +kernel

theorem cover : BRFrame.Cov 243345323 243525179 := by
  have h0 := BRFrame.cov_init 243345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 243345323 ≤ n) (h2 : n < 243525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
