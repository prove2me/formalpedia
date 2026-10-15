-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5554
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:15:01.12048+00:00
-- url     : https://prove2.me/submissions/2b0b501b-d8b4-4edb-9b3f-f8f0056631c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 998741007 ≤ n < 998920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 998742257 1250 998741007 998741011
    0x201020c03071e0b0a0b0a06030b030613030c080a0504060809010b03060103110406031e0201020d210213180c260c071403130e070c0305120a180c03020f0306010b040608 74
    0x1c10784054100f681500e555100240031201d6070382c85900d84001c2e1801d481c0c03000004001c1d00c07540c20704100e844041d0700440d42d64480100115400c10b03643c8038200c00d05004450317040e05240d020041070b5446012000081045c2c200b4401d02e4007041494010030380c540018010680b420b1005402400303141e1854440c505002503240c050340d003140d030320080030012808050101c0404803104013000e8482c08944002407a284803000000d0401c1061100744140618000b084140345440c40f0004d40c5884401103404a0f416243d40700000c0801c52908007100065250084c1e8007038034894903580307805e4581c00c07125100c40c01d400040508200d12000002c1152807090040c00600d4080d02c40c903080e0340351540481e46160721a00d00da001141c00c28008009003d10440800d90160141c600000e4005003590084c00c10300401c01c400502410074000074500c284150300c8040e9252200801c0d206450041c14010688000c44c081680610001c071001c2c0401d0030000f42140c100c03017000c109c05142a1400c1c0e82240c2850300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 998743507 1250 998742257 998742293
    0x315021920011a0a1a120613061806140303040603021606060e01091a150702032a03101a060d0b090a0204150305041101120204090203040c060f0201020c0307 69
    0x11078240301078010000d105a507503c0700800c0d990848100e80b0020040b02011036030001e03030801a0340d10203500b04526141a55480c1a04030f10140d140e446080c0060303250f00295040c024560b140c20400200c9502e10740c02d2a11b11241c1702001c020f0b440e2030710411650740a22051302a0180c1c41080104440e074400d600900e9402000301b07444a03590700c5652a041595a940d1141d0500c500a00041c84140c42c0c0d44291034440408408d0109075a030568085000407207000b901d10501d105c0030980005540341804869085501e01c2003601d008141c0c0c240f041e19507140700040c18000c2c805d0a4080d41c0c1000b1502c1900f2801d4240c4d4481c0600300c1021307003001a19402582e0541c10a0384454100c0f42a80f40e180e401405006454000b503107890030300051000c03d000d03c1142a0425040c41d05010100f0241c003d80d4031200b0f02860400c01e0200489206c0e8040c1c880ca601c040030306480082040180a09035581e00c013528440e50780c40c014441b10741e104030f00380d0060b0859110160410001580012164020f004600da0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 998744757 1250 998743507 998743547
    0x100905012a142a01050307110f060108011401030b0a05040f0c0308030a0e06070c0b07030e0a0c06080c030f010905101d0a0507051309110912010603150219 68
    0x8a0581d8400d0381c90603008003140c00206041c40c820042e4000d003c811900000c120011580f24001c10f5129002e14691642506000b40000440c101c0c03440780100c10814003554040380c103030450002645949100034840c0700204d5290034100e4818000243c00b140c101c0b074205402c9245926600c0500000303010250044881e490500704450000e030f811000a0f000394003c550f180e0f140c5c070b812001c0078252210300354801c0d56034002208201c0d01d01d0b08140d80850842e00f03d28210740980e140442074000b001322071400c58007403107881c000c4003c11040c10304103030035180d07250350381d502e9515030421450303080c00b0503501641400d01d40001403000d10416400305038050f07007198822554036600d50040c994119550801c0e05940b00142c20850860f1060180582142e05031516510b45805c0400c6980354141c10b00030001481e880e0207c0f603c02e0901d0b10269000011300504000e1074031030103101540280414441141d0910344d4000b008045c4041380709039a9000300021380c03c944009213803401c5410340d107207030b1400e0300701c030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 998746007 1250 998744757 998744807
    0x2b090b0a0c200604020a0f0e0f09070f080a0210030c080711101103092802090a0e030c0a06050105030715121113090f0506030a0f0515160e10090501 65
    0x84800d140c51102c40d060805800e07682800d0051102800703003038020b0011049202070420682180c542ea2030f40c000001803111925444100c0072504202c62039002028003d22a24042800d180100750ba040d81c074800c03641c0646150031441b0030b509480b48141c070080450b4510300011486800344588a9108020509a4020f03001d0300d0064811200d0482d82d610450f40044100080c0c80380400211115200350000841039000602400480301d070004002802443c1c4000803501160f0982c0040303802451241c192034491001003121a81d5541d400d00c1078603100e040c4400000d0303500380824044152400d080c0800e110b010345000a1f5a501ca40c180070142e02c0d6554a501c018850500018090080407055031140151603c1e402009840c0350b10009a111854001800752650b4000b50411341e6641c420ba01220b003000c581456400d11a40103c0958110900c4c010441006004070741d00c007103402581c94180c0103140c1481804481c54116010b980403c81c450410f009a600894041c0341030300300718504680007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 998747257 1250 998746007 998746037
    0x609021911010e030a050f07080706050f070f0e0103020307020c04110d0605090609010302041d03030f101203080403080a150306090201091a120613022b090b0a0c 71
    0x903801940c104008080844904803034a510540d0a00c0d080a110000d00c0b460403035421154030380c4a510034a6090110010f4070111559510055882094101288d01c1d100ea80d642480d40141204840207503400d481400060f082c103001e40c1d0401d142440940da03068032900540010740003584050b281d0b030203512916407911404d40d5540106040c0c62284e84880b80c17a0b0560044040581d840350704050300c40d40c0180108491a19445840c81c112a011100460b02c012403450b18201d1040407411040540000000c000d0b501c40d4846c5100d0150340c0072040c0c00c1005540b00b01040b5015902c00005001441d9a4041008240b01e210a10b4015144040000d183c103c0241a01c0c800115580129481303511542e00000355038115049400400010a00100c100180300011059100f104944e85140307880c00c0119880c0d49540c104010100d500107411540c031000c00e0354440034000302c501c0d407110451000960380a044030030700070103006982c000000c41e0541ca5071790318040a00301c009200c2007045078410b04a482 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 998748507 1250 998747257 998747261
    0xb1c021f0f030203070c0f11090c1e0f040e10031205030c09040c1b030314060f0d0f030201020d140901060816030308041b06080117010603030c060207150501090c1e020a02130609 78
    0x2e5240301d010205404800c0300c1c18070140040041220103d02414001c0030140c2c0c00bd070140400310308000e1003a60b50340000a024100030f000c2c2d03801820141282c02d042060a890f412803940681e40164200c000b01a90384004461520040703400521148007402582c03038604150b041106c0500c402e04005125264000380540c2c003202c0d1090680000c0d44070941e0020008105401c6504040290340c0b9242e580c8a1002083d181c0007000d10092182c6001d01e00d02003031610030b6041d103040030441e5200703001d240b02e00e0540140c0c1e10800d0300c02a01d6946000c00001b4240d0b000980c02c3c5292583d100c0036040c90703255803030079140c00c0c0000788140c800f07140d4407680c1551084da404800340948129141c5a4440d41488034002815414407404d450b140e2503c001071001c02c1d004020003001c1c980c80032016079101258603014803440905040001d54904010020408060700c3c0c02580d0040511365820401d84002d403800e0034100341026465000d80c20808100b00581007000100001c040214404284184ea640034001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 998749757 1250 998748507 998748533
    0xa030204110901170c091e04020301030c080c0108070e060a030f0908030412020f07090216050d110c0613091d0a060606080105120705130b1c021f0f030203070c 70
    0x31100034002001031080d0381000c008840308004c1c0c0c40c0384201d840c01c526200014416100898402d910440059020005031084508607080140c42952296501c0c46c0c200ca44c503195019592490060174020520383d403203003031018810f901036a42d030b080d5000100f082c04110780c400341c599000c25454404803240d90314240a403030b8459101d03010b10b40e501d1030681005003403c10120406411900b0030303941407007207600c0040d100084e14903c01c0010f0703444042c0780f0b901c6c541482501e0001e140f030046441801519802079846120581280c05403540501d9640c20441184a60060040d1110fa125000e000042595100102080e4040551091281100c4685182601e0303207104a0b02c207a210502400344582c883c080341c3c0106400e40700f600c000031074210501d48030981c60250b071b0b00a03120101050841c40641c1c10003900545d010380024a0214841c1c02c01510302132119090f070240c000305004c2d100040710041000204c000035035580d0340010b050a800c0b00a03520151580003000825241c0401003180c1e40d00c144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 998751007 1250 998749757 998749781
    0xd08010323160302101412100e040f05010c09050604290f03060a0918030305041e11040c09120b060103111801080f070f12140c030406110313020f0a030204 68
    0x480283c9984100714200c048109074004001045072908400780c0e080c0141c4051b145004261550380d5202c140c2034081090603800698100054410320040c4412444038a410f2401030f8000d100445900800f07a44d00b910500c503154010408110420125801010300722056080402e441740c5035413000b441c4500c81e08040c60034003038243c00000703010540c80c100304000010440d12501380007200c444103a00307002003d59100a400e250300d0b00002820401d000940e602d0030600c2100420201105040155020401c484100e00892070301080a1005000703000d0f0b030049841c0c843e42841d6203d61951103c030300300d6001c1c140c0760506031112581d900c4002240094218038603480007800c00d1070788074400180150000b5100444100c4c641e0103000c1c0b03140e8001e01c00b40003610315060503100394400190364401840c28012061448103103005002d2a840c0d403100545c0624002c00b0244054000444c00c0001444252080c24581311102d26034001070501002e0074110f564010803074811950789401040580380804120 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 998752257 1250 998751007 998751043
    0xb040b04090b01020c0d1407231c050d11011812030506240715020417150f191d07090e01140c090d050d0905010807020d08010323 57
    0xa01400541d84682c109070282440101002c6034088080344168012a2000e4100000400842002d0a04200e144010000c4c0784c10150040340c1c1ca25000020211210010f104041030041140540c01c030402c0110310a411070f01400d5002211801500e60302016402c040342552107080070f0b1148814480f00c1c107a070700e0044e04604a0303030101c01401000c0300c1c40100124401d604030b0b0305194086845280600c440381c1c605042613a40c002c24104421451004c1d402c00840e640001408244075044901d0703451846285011150f8040a0401503401184201c0300012401170010024030740038400b1062610b003100d0000700141280084220050079031100352686910380c0020000c2042c010f0340d201ea0103040241c50b00800c4a000c41c059480d240c03030340142c40c02e40784484c0880d20300c8881e52005813040400c1c0e4420300302c8228100c0800050100384041c4142c03404200b140c000901c900d800855821644100b503035171031501c1d030b0955990503004080a8000d08286d0384c600c9503410030755030070450720074000311403518 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 998753507 1250 998752257 998752259
    0x2150a03140601020a0c030b071205040c0503010b090c091504091a10020c0319031701030506040627020d05030f04060201020715060506032410080402030706080c040603150b040b04 79
    0x3500444801c00341c03880741150310881c03a6101140f0482070840540751b0010342800d880e250148101c40560000c420041c40710f1402d001c0c8400c010b00f0703041030b000b2200180c00a00190013110200710b0030900031640045605010040c1205925200b50105800400f1000321405d298841260b031f412100c0f0100c0120400c00f0200402c031103840c181d05049071050b054030007400f9402c0c0800120341c9841008040b400051410120503007058010b0400d00d441c6464020803290381d41e1740c0d003884c0d80d4840040e6000c0e50140c0c42c01041c80030412000b106107601c0c3c808240d003411415859820700140e00141d0388240d882e8041030260154086c8103000030f0000f00a40d900150b00c402c0c103820180c1450100c252284481c907e0300004000c0760701c48201b62a44058031800c0510341c0031165030140030480e03102d8400c07a44141c2d500e140c000b80340e0b080000d4030301642c002d9084610864480d9026910102c05465440800e60705000070444140f282d0015002d9404c003043d1214850703591001c50009800581115141c02c0e40420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 998754757 1250 998753507 998753531
    0x12150909061505091603181e03180302060f03090c1009030c0f0e01060807020307151a090c0d0e010e0d0c020306101a0c15010e0612010608061302150a03 67
    0xb1040010708422a446960703400c01100c650001908200d240060603181c20f002100202c3c070034511202c20381c22402801241c020f500c91801c48030382050301100883d12120746050b90407411300001050300d44c003130040e6107002c565a05124154000610b480c0c001e1180c40107400082d20b500c031501000c0142c0e62220000c480c11490041d4001c0d07081e4000a201d48201d00b010004d00c00b8004001c0d044a206080c40c402c5a00c41d08012421481528400707410702c3e255050101030b864071a030060411038118400e02640d078a440d0100000c004041d035501c1802c00085c882d046884c9115844580000740da24000034042c00139810290420380076402c0385011920030241075041d8101489102c1d4451201092203900700c0c101401c40c11004601003c00c4050080442d42c0d2020250801c442c0410a200340e100e2a480d41e03403859001030351030085401034000c407800c000c20088003405020f85001e80d1883c0c40609002d5465043e0b00344040c0407aa800e83c0c1c4141c6d850741c40514000707028000c040c2c16507555400304a4024041c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 998756007 1250 998754757 998754791
    0x5030d140a110c0705010f09091a012006150d0c08010b040b03030a020a172101090b1509040207060b06030a05040204060e01050d06110d0f06050306010f05011215090906 74
    0x400548080c81c0e04101c090f0003810049601c0f810344009080102c03140c1401e5000300c400000079004804524503000003110708108019075040c81c11030983e19440320708140341d0305808142070388150000a92110000c0752840c001e1111100b110304c03018104929041c0b4a840d1314840c50390390b602406440c0d5482c0361940007418540601e50518100b60010361a081e03103060000d42c0c407280602d000d015041e03420740d80c107040d0314680c00321410503070030b25500d1007010400d41980311589820b1241415061424502900c1424000044010b680b01241070a00f030200c2c507020300000e13510403041203c019540305080312a07640c4010156004500c036140019040c941481800200c91140d0003034040e21081c04010025941c40c2d0300410046588800082901e22a00942070414003a10004800c00c43c20042100344490b90f941c8030408443c4102c0c21540d031643d1f9401c28230304003006030080d6800951005c1024444088641000b042e4801a15400c0c1c1c85a507102c42800440d0750400d0100d410340d441d503949030f415000746 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 998757257 1250 998756007 998756021
    0x603070f050d03120b0405070f081f0e27060106110705060a0c1401060b1c020f19090b120105130536030a231303020d05030d140a 57
    0x2250808219420580059620b18020300300408002081564084050107a0400d00b140c12010340b060026040080002e4820710400c200d0307100041020b03000402c20504410b40d103104246103000340e901d8034107148921580c614014000c204203208210980420400b004070303a8941c02410014003134550400324000c258401110245160368400c0009001315502d80b4201e84407581141046410b403041803810840f0b040b0030f5001d41c01c4070752902100040407040d0600810950344101c0d503d002c0c01c0104001c0100300e0286401000c00c0c0c0c107080c000010072001101c58080b00e10010308042c004607030349449891056115269440e0100f83c1c1c60300401050a01518010f00c9401240c028130803850095003c9000d0101c1c40121503c8902110281c004104040c142010780d00803001601d41d81c0d0144400034005911400c00121044407140c41080181c50310002d9814007103026402029041c0383d03408010070540c0300102664240002c103c4c0d65203c584510490120480c11502890f039480d081050364200d90b10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 998758507 1250 998757257 998757269
    0x70609090902060a2001060312032403110d12090312030c080f0c040506030f060306010f030507051005040b0313030206060d150c0203090607050a0c17030703122003060307 75
    0x1840071140040ea508030a4854100382440c0940f02292564100351100c003003641e07044655440e000000c01805003d241c10103e28046881c14041d6071620303a84200c908004403039103840e210407410180000f48607014100f00000f8014240070460380540c8658070b12055240c104404120400800c10030442c0d16034025030800345070301341000111502603015120403401403441d0100c0306254001040c080002c01034801605000c1c081545928110100416940c01600d10520901c41e1000000b160707a800c01006041c3e84d4004090712425240c9400d01c04991061511081484002c1c003000c00d66003104406180301c1c98408880b00300040352800c029061180c0605050700504003035000c4800700c0c46440b20002001a18040050104030014089066000d24480640d000100080c072006200d030010304482c40500910904010654400c50170482c5400a9034040c00d07504148501d601113809100110341c00c1c000e017400490641c4000c64a80f5100c07840c11800b0500c44400700030b0004074201003001030302900c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 998759757 1250 998758507 998758511
    0x1c0c02070608091005101a0d0608012007030207120302100f0b1005071e030c0611090f0103020c01140a090c050301060b0f0d06051f1704020906040b060f03070207060909 74
    0xc141d501140c85003000900d0b16481c5031200d020802e8040e09010400041c98800e6402c021604d805071f5801d101d070302441c45d0080050a0080109000406100e05e190200f9400e2400c2801d42100c10b2044982d00a010305400703600030202c00242c140902e183c8100e91030b110b6800b8000719840dc000c54400c80b03101b41d0709690300710b150440d4101701d5244c8000c20020f036a0759040c1243c03155a5450700d4060340c0314140300080000b00784200c0408040c1c0110300200706030b1081005020341c024050840d9403902801c4110b6510005884095090354082d0b0b0007000e080480c2c0002007a40107680d8210511040c00303540e070b404041c0e52031000a05100a048100c006030104600a10219140141c00171341130090620003104040e00251803003c102c2140d0207070b0010b10300a070140c081c11080d12204095109600c1d0311501144030380c512503103131841400a80384110f80c010041102622540c06110040c520b01c583d054102404001869034021540b01035441402e4560081c0101401d2904c0100100055440303e04224 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 998761007 1250 998759757 998759761
    0xc06090b01090c03050103110d023f030306090c0c0c090711071d04301e0302070228091401030201030e030a021230060906331c0c02070608 61
    0x1400d02d140007000c0681101c002c580880b160001501c080400b03007010f40194101344010203916206101071201980b100b030be00d5041c4881341e0070f49480e4402140c0441e802071402e03000401e040d00003406000b001a03480115000c0b9421000031801079542640c0400104585449900048208012032005400c00c592038402039014090002004403003e04003c010030303040c06510403451034504811600d802d00700a0b119090000d45000b6203c1101c50060340c2240032180600c45400d4000d000b12060300d07502900d9846c41180784041c0070000240740c404540300001c0c001001901d018203000c1d05003907540003d00c1c1011940f542c80054100c071401c07603900045800030710007070001c00d0300412003102d106c3c20004c0d466961000c215007022003040d5283e81000da080c10380c079260000002c00010b10310596003580e2444a07615040200180160701003e18801030584041c400b448003510349203100c8601daa00701950804142909100c003141c000f1b400c806100342d451400f02280e0740d04201080042c04103040503003080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 998762257 1250 998761007 998761013
    0x61d0307020d020d1e08030f0c0f0a030c020c0604180b03010618020702010215180c09061c050c1f030605060f03011e03050607020c03070503010c050a0f0c06090b01090c03050103 78
    0x2050340b014060300c100720840c00e030350a0200004090f820208501303502c1d0014040d41c5403c03d2250002d0b586138820310141d0300020380e038910182c200da4400030256505406e0007a070b054114007404403880c070b0804500a501c0d0101c00b40d141d99000d800134107100200084102c1441100b141200c808000d500e01c0390317040c91400c0121410403003d12104607101100581e4910403800140c0c07928903600d4030018003064400400c104134055208240c100b5841130150351200d5106030400100c0c5006440c03e5900905404d5516541c061004642103694031800944007810290000900ba422007a400b94441c0d5841d9003d55820a03413601c10480941802c41d1898202070441c80400c2581c00305010708141d0204034040486030b0301c48602d10764000c40d4444211010380c503214500075150740300301e01c0003800f07031180c144085030b00e2506016120503004d840d03680c142404480300c000c5070382c034100740d00e08818494240d440501041403030145101c424040d1403401d50300e52401028408480d081c01c82c0d1303810145040014400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 998763507 1250 998762257 998762269
    0x114130f180b04020940020d05060910062006041209091107080a17090106080706021f05100f120c0905060a0501030b01020c03031204050c010816030522061d030702 72
    0x1b020460030040400360307461a00002030b40c2e4100310a503c01d1110684078180d040c9150000d213000c003155038062020352621000e0004201c0d0660720340490006840f42440f101313104040d034049000001080c1c60b0419502c402d0070f41840001d8078152502e8011288a40000740c002e100315006012281081142c000b1000c0341aa050155407001454143d0015446134242e114940340f4052040044400100c6d0800d01e14041c002d003990700c200f507071034042c21000040c00d5001061140e100d43e4080c1c00002040720000400004200003858400100e106100215456403500c1520b0090404070394100d031200043d042c00c83c1190010341c8402d030242d0a207001c22a950b229441d8040440c6c400b821302281078040d0724010f03401c1035000c0000701c1d0144000b00d0031400080c1090010350060b4003034810783c3c46103000f50004685070314084843c0c500d50342d42d0880d824260303482548030580c0504083c1d90b00e13001003903503a0000741070450640b040e910162501d04c0c60701030701e0a0020b030940c002107041c000c44c07070203a03a42c1c08180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 998764757 1250 998763507 998763529
    0x503120f0106120b180712060f06020c061312080a020601150203090f04060909080d0e01020a170403050d0615021e0d08040f12080a0b03030304020114130f180b040209 73
    0x144a54440c00f244c01103403038401c40d4600004000503401c0351841d040350002c281041c00303049908810304110380000e001c199a010217003500c40e198043c0c52480e101c0030511585500c8596010314100038540c0028050401310316000d01948551034541e82c030f00692500914100d0107030041c00590700540300590300b20750008120f50f50b240d0107440d0150401c001400080c01050154001c6a1450401c400601000003500c020101280c44050800416a815100341d080380208070403203011a04480340e0400c811410b03004203621a220707281c00c81c1f518001410002c00d0316200e60002c2c0c0514556510f0500b501e8051001d0a500700c0a400b141413041e001c404490342d6030034082070b03100500100304082028009210440403440b904a9006401030301c201400a0031404201c619000300c07464001a40a0381c60702104990185405948000341003528046822940d03014100f11600342100000005048000c0e60180c1c00600550070050004c0204459078400c0d070700d103100d5261140e8810050740d0025078548002c52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 998766007 1250 998764757 998764787
    0x4061e09061e090f0f0302042301030b19140406051e160201150303051c050c190e030d020f0f030c1b0303070605042409210504120503120f0106 63
    0x4040340500c9009503100f00c00e035000801e9400b01c0f2003010400b6030f400307403e43c0c0840b4030030ba504100c101d1812140180800040040f41c945c00b400500400c003040c00b8840742e07900425400080d07003600e25000f00703140c1221050000c110402c0c0e0000c00b00410300c1858403909078800110b40e0a071b40841d4042c2d501d4252114010418000015014a074681c258401d6100e416400441c0d400383c91020b46034203010703001c1e8100308404810b48041603000c0a41482502401d40103c40102c800317828800100c062030742c0c4111280d107010030042441030205065030200000d41e5854000d0300a0000714040f0f0810300d09240e004100d0305aa43e108019541050034001039000130401810310308000d01410704002421032040000203001e543c10641800140180201082e402003020507011f40900c401d81503103130580703041c04009081d400c0c98039070710b40589032038220700445603100d482e01c01c0c40c0584038050941400070294041d1082d9001280c0380c0302541d01c108196411011586140801e0340c5004001080540c28516030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 998767257 1250 998766007 998766047
    0xc06180b070807090302090903031b180f0609091305100209060d091103060702010b01020105220f03051b1b37150f09060f05090f060d0204061e0906 65
    0x3c405510469610340035650080800b240e0303007004403004c0d03171303d410075103050111240035054000300700741c01e0040b1074400c40840258034800200c0420045807001c3c1c500f849404c00b44c200900d043c07030b0395480c0b0410303c142ca103142064103400343d5091241c981003a40600e00030042c8104801c045a9491806032a00c2042685021483c21104d2424a03001c2e40c104038803641620400702400f408a0f01900075908680083c0d008002035596440050384002c03401c8490116200c0440402001c6140b42c641d0240d160f01034104240361101010f00c1c0e0b121065002000603c2c1c5d0014141504070410f02b10511903203c00c11140309455034080c4614042c0c0d2551051503850400f41c40f9041d086410100d01800028004414056124001c0030800380007a0011800180015402ea1740458803c0c000c0020803003141d01c540d1a00d040440003014880c1000a04100d10380c459800d00c45004801d2041c0024000381c82c4035605c0e50441c9540c00d003840e10340c0072955070720014401c884a0900800f9406400590322517400d10714 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 998768507 1250 998767257 998767261
    0x50f0909090a1b0e1e0711070308040b071104020309060f0a090203010c0e1c0b06060c0f0706030903080c07021c14010504082a030f07140601060c06180b0708 69
    0x8401c0c9090b0841000801e0400080d0350305480f405400c05520456203a180b403640c42c0d95401400c13040344008103071541c104003201c05c04203e5084c401c1c0703c41082400703001c0480701c20ba0313181d0f10303410405d80060f8000c090790100058110100800e0024485407d4410791702913043d0b041443d00642c560324010301c0702800042150026141d0b100941140c402213401030003c000d003194088000704074484844103240a142c0c202c807800300c00380301400030f6806107400c41070116030341c0c8031a001c014107030344070000300002ea03c41c5008290300c80c4814048880205a0380d140040c2d0007985150140c011040284440c0121748140010805030700d900340718803a10004807144404480262038003000100b2104140f5240c0d620f4070782000700700301606000b460300141b60084008150a80074543d00c500101c0410098190418801000f41c0d40ca003101030280180b244c01c068070080c03101c10215150140981c032480008021364050b2040c0305c034601c40e261480a5922101e10b800b2415254041c1079400030f4901010042c03c800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 998769757 1250 998768507 998768521
    0x20303041a090a170a0f11250b04080d08090307030c1e2f040204031a060411161502032a0903010612060b01080105101409042901050f0909 61
    0x4111440f4030b0b40703c0345030340342019043c40f2a025500a841441d0100c0c3c0200c43c60550140240c0e501c00300c0308209402080c04c6e40020151914104c00110508940c140c00c2070081001140d1001078400782254000401a003c00c2e5180141a1400601340b0407954000708a84008268406421403255400c0480c80d1940780c003140e80324481000c912000f41a1030030099a10304120030304002282482c4404262117805141c0504200c204d106510004014040c240507140c43e0f1040180b010740d001d07900910020703100001260800e0281e00c0040141c2400d80020711420030041000a070701071004480b41d0442c02c41c42c003810b0001c44121401060740034540d02d0307003081807150344000c220f40c030b90743c0c1c041c1c001d105096441c41e40040e01180c80c00119281421725040c0040b03544036000341030403078000601d000340200d00c0b01e03015107006000c1ea85074040404100100091604c0d1806201080401c108061028002c400032240c01104e09099107810003100b0040400c0041c0c00f4010f48070013207400c035030001c0d907616001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 998771007 1250 998769757 998769763
    0x6280e0702190818220504021c051c0f0503060409050a080c070f0803070b040f060e0a24060810110d11091005030915090a1b060e01020303041a09 64
    0x1c15190507040000345660030403d100014180224102402e88000d00180c020490300c40000c21542c10300c189420341c200c0304004940c204076046070014102201c2201a00071450315101103440664060748612046107104000d00501e076084407843c43d04900710505004003d18600c00509043d00c1251211031440c1071001c140519070b412680824056a190702c0c103e14039481c2d200a105080110100700800542c222000c012981d003c0c1e03203c010b09407596600d0782c40801100c030003241a1103403070340e49201c1103904c4420820040d10034040c1154400301c00411010100d42c0404400f448c0c0520f0410504000150000a0008502d070100780003003980c074200d42420106001f40704007003134040d0400282e03422004c0c1c200b00804070306805844200d0007c04e41c0320156450f10066880ca5001c2c0d00007401400c48460f92250190000c05480a40c0e1108040b5141d048418155400c0030181924a4400300718003038009110f040100804c2c00614114a0a51030360030040d0b0039031916403d175a072401c0c0012040003040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 998772257 1250 998771007 998771023
    0x103090213090b10080a0206070620072f01020c010e031f0608010605060a0801140a030506070e01090f0807150201140114032a19080d020606280e0702 66
    0x495810000e16042d810b08014204007a511415207070b4807403030081000d141c0401c800a403550040c4c00d40d072402190f66211001445550f800724224006000701c040c1140000b0700034080f03030380114100040d074880f0094489540910b244100c0c07104041d150b00002d1030343c0100b0068046d41090038084403800c500804241007948032004003090784400b103a0340d441c0176110740c843d20555094100030003c0710740b41c03402d00100c4d03c10000d460010031001d40041240a04065002405035405440c0945403562652800e14041081d00c2d08400300d095100c0c00c10a9517441046107009112950751000f225141c4135206484a0f41d6000740c5c81d00610b60418401028004d40004002152400400100b580e40f00c429480300340210351304070700c81c0c003030f1414050048295103418803e4850300c4003181c0505502034200032803802e0016030641540c0200c600042d0480003801840140c150715000307000e652801d001004084140400010703070a512444480c1e10303070a00c85540034150b071b00306030390075503140c0750441c00b0f9180c4444 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 998773507 1250 998772257 998772289
    0x1b05030d0e211f090b0c0307020102090a0605030613110a120e0a030908010c02061b09010215100e011203140304170a052101080d0c03121406030d03020309060601030902 74
    0x1c900d403410080d00009264140c010f000160b1210110b802005101a80c400c83e102030b01006000001c03a8540c0e40c48401180c00c101c15000041c90300c1e1520002c902c80607565440703500824000700400c8618117014000c0ca01a460890003000f40380032403640400c26000365613040080020b1944a4081c50078039071f1128440005000c110b543c81c4c0024a001040400c05018004540d4202242c2290190001800900550180c070145d842401035075508801030b04280c24250440c030581800c50b50310f000c900a1140103c00030075500100d1410030316886040b007410380c81400580c00306507036a0301080d4890600200404a8480302d580d80c0c0700d600b400259107078040300d01c40ba4080005030418041d03411400400308901d00e1340203400740621140c1120f110755001d10822a2039046420382c20041445032070842084c1d4031074101078241104000b06081184c064400140017101c1c58001e20565150802c04030420400c00d01e000e500d985003850180f42c68040280429050541b00c010737003401c40d1382d0380308003c0030464 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 998774757 1250 998773507 998773549
    0xc070206040314011d0303070801053309031209030a0b060303040e01090f0605100e01110f010216140712060917030a090c08030c1f060305070b071b05030d0e 69
    0x641c0710464000c102c601410b00da24130400b00c03100d1105c8004401c1c2c0784070300300d039440350700c0c075a840d0509204120160858110014040e403c3c0c81482407100225021001107541d155a1103503100d0061520302a101c0a603d26844018401348419550000c0c080503425030022480009840b50030100b071031406070b03401031030f00c004d800400442e000703084d9402070311800f025607801d03c50349a9420902610400c402203540020b1030b1403007036100950148203403003401306502c0e00300c400c03480f004c100c05400c98001c016404100080d00030b0000500c40891448218405188084d00181d4601700004820700c1034900010092500c1d111074406000804040f41640d01c400940c0540c4d034581050100000d0401c030008840c03c030f600c0c0c1070100f1140b5000040e074496001e4400108507c00360180d450302c2c030b583e420342580340c00c41d00d0b510040001402801840028003840d5101a2520030701c1c541505190181c07004d5448800407280c0401050b58000f07a10000c0e04009d0615208410100e004504c014103d034001c1000c50b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 998776007 1250 998774757 998774783
    0x51e0709020c1609140a05010612050c0d0c080f0702070b030412090b030103060b1206090c1e0d0b0412050f07060f060509100807090504020604150e0405010e0f1501080c0702060403 79
    0x151107074000c1d19842d00c001c107030684142c1e129803114041f00c07000c1c0500f100060f03050608a056400030b42c0f1a0b500500c0f00f01143d400d182025079100240c44400030280000381c001028040075060020003590480d04900103001e125041111036902400300510140c6078800300110b101a180c01800c141d00540707074064100d07680c0c3d81c5130305220014003c6070883c1400340d05410355581154001241c00c1d805000580040c12406400008000c5241000d8a00c0b01c0650f00310202440950f440d005131014482c880c0344823514501d01400e165032004009030854040c0310080001c01c070300c45050021035108940c172a6000940307a10b400510001406290005030f042802c9000744000d07072820000340000c0f81d00d440200c849154a8401603401e6401c26a402500400309000a12694400c1c0c56030b42008001840c12007908080000064143d450a92004640d11022000d00040041110115a010b4524644020f5840c00900000c0481000400c6c08403039120106a5104655034401180c000715040840f6000003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 998777257 1250 998776007 998776019
    0x30f150302030f0d0917011103040317090f19050f0129030a0c0e3120100e0d0501020d15050d0c0b070f051504051e0709020c16 56
    0x92140c00164401d1081038180090302c03800103000800c24280c1d690307508050313150801c400b10b0348018041c40046c554039002400c00100d44171001c0d5219a009a40700c02d064040790110810b020f0024180040340c1e000391810003034601d40010042c0c032001802511000300c00341c3d0b05042d400c021014862074029402c09503003455460040c2b543c4c40c140d41403104415650341800d02016659403003c48005c1801c011958208201031403001c065502100485d072080210380800b0980c0b409640343c2c0c40b50f540301d0010004110902642c0d1102c40c1030030702101c1f41c0660614003c00002c00b80d0b801110220100003040701c56506a4803101e540220a582c0000217540352034a50f0403510142114002d01d01401204801c0051540381411003228000d410080400807141454441f0a4541c09480190b60099240d422000010001c12101e58400c071f0b0700311440c4250805d0b10300b05003024400903c0384124424048599200c0601180407002c4500c1c4a4005035a1403980c181d05003080e40c4031403050042109c0745400142c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 998778507 1250 998777257 998777291
    0x130605130c080f1002070f080a030e0d09080303061e060705030403120306030314030705040f0306050601030506033706020301170c0109060e0904150c120e0318010c03030f 75
    0x1031a210340e01c14100c1d15102d1240c036a42d11100012040c0550120040302c82d004c54660050034068040e528609a1130903903210031140340e00440c854000a9501d058103c1ca02000b4000625a0f40c0c041c03600640d114604942281d99020140c400d0b481003000c40d45613035100c1e0440c1a0a003c0220107054075469400600348a602d90700544800d5500c0c6100780500300701c40b40b04c0c1c1700c0c1c481035a03827544400f200e52200c400c210703409400082c210703401d2080c20000454102c0803220000021403050070040317030743d103000c00c00141580c41c081e012030b0296105200c40c5c0420b5802c903080f4489500c402c0002906220003140203084c00d0000100545441d1001001187c4003041554002d0300f07a21020444900b81040380044444254a204440c00207400203910140b0303107070880000d600f20f40503201c24504180c00c414080e04840d80780ca28100407501c40782c52082003400b2801444a1851001c0203941011000031070400e014000c0c2c02800d042000c40c07032540741003500984c00501000303804107041207288110341540b22 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 998779757 1250 998778507 998778541
    0x60d06030606092403050d0f1206090c021c0503150303120906160f02030a030b010c1202010501050a060e03060601030905120301031b0b0a0e011110140604060e01030b06010503130605 80
    0x411944100c0e40c13101290401640203003100e501400402d8201d0b003405c0c0440b05040060303106801c005407091050110401401840e010304040180003178404d500c184081d1414900360355045050440c1c03041c0c9040550481d090720ba114a20700a1001850b80c034200003800c52203421005c1859585c484180414a07200080e41e510540d600070b61703010012100d00007520400700302d411410060b40104415400c0903c0f039004050394200c1810440114407541d5a20005110036000c051f0042c1c0d5100010412891300c000b06078014455800c005c40840202d00c0483d4860400400701c50526840d913070303020100541005883d07862081000c442e0740b039584a1034645c00c05207a20b6070400c15481d110710081903e948280854204c10503d89484078040040030064554105025805449000707650020b1043c00450003440300c40301191101903c01e240c000100800c136481d540003007400e2a001c400600c000b074280b1036469048030003403c10750307200e54a05100d520031401d8480003c01c0c16082c4000d000c410518020800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 998781007 1250 998779757 998779781
    0x111190b01030611120604020721020d08010f0807090c0c0c09050103050c060c0c1e06070c0e0718030b0421120c050c0a020d02060f221d06060d0603060609 68
    0x12186481404c03204040d400303a85501c0b2220611880414028640f0b9170080440714452003a280e1805152181c0485441600350514056007140078a082e11562081030706000d450f6a0b0069407105013480d2000399900b4080c054048500d60f14164482800d026051101606901c900596440340d01c2d41e4501d0064403080c4411900c41c0f042600002c401d1174042c040e1040c450750320004140d21880b40c0d080110400103902c00003000c00e40f002d07844a46403526001001e8445c015100b05a034680313000120382e0820001030210042140c1c2515454a040148240000f00c0703401c41e590310015140e0781004824030740114010f40211182c0c0030040c80140d00299400b080100208040002d07680c0c600f0b09403080c1c400c42542d058540c00403900c600043c07a0110b11010901c1c0090a00703800d1150001e404050344d401110001c030b40c051944004001101951795000240c04c0201059480c0c000e44020512400001b4041382c0c461200810072544107011a030004009640100003400403554500b0020000c290030ba07105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 998782257 1250 998781007 998781011
    0x1204081006120305090d11030f2d0307200d03270e180a050105090f161d04050a0b0c222301261e06030703020111190b010306 55
    0x28002611510b1200043e40545035549480c80c6002002402c21070a0011110202646408009a20b0812406500700183da004000300090318002c0c002684084181c440f00103822041d03081500ba000c0280c0300c855521282c03848281302d031403010b0440961002601500a2120049542403591180d40c2141600c507002000c03a00f035107910b000441c04035041c02440b240c0b15101c000b03d070045c8080342c0100340301103a260940c0c6481040e03a0f609030950340d0650b00c544a6034804030842ca14500d00744600e1000c004c004888105ca5440c101640090500c590340c580c06c030f038001000180900c03c00b0f1014294035079028900166a20b0100c410000c69042001e202d09260848446010342d101e051107080306a9801144035690740700c0c0040250050143e00c032000f410070a1016442c01c0c2d11241622b480c40101d1100d00740001481d0100d0340911104070510100750518000080c0407c40d18046000001d5940a20380041319802e0b00170318910308803800103004800b00f0004c451105100390342c44110b050324890002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 998783507 1250 998782257 998782259
    0x27190b07120b0f06090a0f030515070f021b0d05161503020c0c0405360d0e0f10030e0d0216060806060a0509030c040203040822140409051204081006 65
    0x1841044641c0c2040d450b4003c2d40c1000ca0a07402d1400c50050020000f000340028502a1140d2913402c0c10f00065000304d0351031340a050340d80e00350b03010f40d81010760000040c642941301c0c0c1d411010003551074030070a2243c0710021100d02c0c0000246c640c440c1613040c058100b8200d07000302d41806c4849040c0c0906209001060344800d0080403450701c00e00845102400c2c0740c0081035030b102d02ca4100001803601a0030019040030a1031041002d628044000c1205074840c8981e6503126582403105060045034900c840401c5418803815030030b591007a031385c003000074015111881503580000c0150024003252542030352902c075414444402c07d500003090043c400008c200034001030b1380c504003960003401c02d468866008030140070403652213100d2401740c0b4913464000e0449540704000c50110701260300540e41540c03101c2c4001519115010440715240d89492010380c00344640380380030007415081040c1401c2c1c0e4455502c0f01d00c10b005024042281880703203600c916040707950780d03a00d01c20282e888100b2030f1040802428400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 998784757 1250 998783507 998783537
    0x50f1503071a0304050f03031303030e032107140319020304051002031602071a03010b03131a0403200712030c0c0b0306120d09050625030e150327190b07 67
    0xc1564020900144509c803840c22650b0190080c043c07450040056100138003900c06103030600e0640110b040d032210007629060805140050030180b07a808580d0014804000740103401d00b0a100c90700c1010a106801622512103240040c1041c0070041c8203881c250011050001440d800a54042e1494081d002c8818443c0e55105070101240e0100001840c4c4405000400640300c0c01402180c1c006503c600410900303d042e03880620103150454948803400c8000e0400080507040744540b40d04038049280340c0f49000c4031061490351243c1e00e016000e0505c62000a03082014040d6060001490340120300403c0c05403120000440c0350001c5500074415104400c1d02c107041c100100308021100510356030380e9246420842403013010751040d1803034507801d5504232150f12041c15183c9043c1c210b80c440d684005620300300c3c8017005000e1456115508103c03408205029268048001c03200200601e0820182c6080c040201c0da820000100d0040341c1d10f803000f482510801455011311403240c007043d2566460251025 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 998786007 1250 998784757 998784763
    0x1080102092404050409030207030b04030e01110a0c18140901020c16210c030615060e1005040509090c030604050a0203100c020d11250e0703050f1503071a0304050f 72
    0x10b811030b4001010001031106081c83c2e0005007030280a40112108142da0f40c0d00c2c00c0e20100c04807010340000d41d60600b188590360340200200c00d000c903100000c001006440d2203100c410101c45c07203403020f8041c0801400c500b01c03826030000049880c40510302c000514110290754044e5000c682510102d0041009103c811000b500001c0151782100d0382c4811003048004082241010500060762134203400c1030000006105070082a414480300d4a00100c05c51400038041c2179161142101271061440c203810041d042c0c1c0c040b06880032594121004500c83e1168407010741003012050100e074060080c0d2007080f00340040041c891a0941c03007034084400306c0012003c402c0848030030b030304100010b0300304032510800d461090411000441c0402c2c00e6880103290070001c801e21001c20680800d2020620038100410302100c4d100a901240c542000d0056151600698228001c0205000101d85114100003c26101007000402414240e00a010300ca4104074180107940c00c126400c90b031f24801c3e1044040000004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 998787257 1250 998786007 998786059
    0x60301061e120614010303021e01200310031a010e100b040e10090e0f160506090607050106030204050703050429061309082a010c0504031113050108010209 68
    0x11028030714099061115440301c10640c0072040d03554035269045041c5090201400c0307030003903200f03400030000c0d64200c0c2203524126030407034190f4071180d01d0081b54a0729a90b40b141005480141100520380d00d50381c0b0002d003695120150000f42c01e1264250703005181000d10340500d8107841110701041ba45603103002c21440354001c24081c1545040c01403000300002e40450880c3c40d0443c04005106074500c0d29200034508844440328854031582c4400206000810280310301446a4000401d52800ba800c050101d1194440c9843d074130b001d40000100361061140c02e51181028541c010818401424605001000307040f05171001c2e1440c01c0c0d401c5690b400010010107512682d10107900013609075460314104240701405841401e83c1c0d60711018041d0000c0d5545005042900e4450a20712449250250840c60b03810300500a11180c2e140086500007203800506860441c5d902080050000c58620040b80501d0f1101d107820b21107504080010402c0c45040d000b400401c1810b40fa000c1c1500d40c00f400d445201d00c0c01d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 998788507 1250 998787257 998787299
    0x1201f020a120c0c14060109110c0a02010f1707050d1406090c0c120c100c020f0a0818030a060606020d0c0c031103150a1a0f01210e031206030106 64
    0x95070781c02c10320010340e07400c040c0c0c4020460030141c4841c02c44d91034051200300390111100980d04013000510076001c280c807502804603c0c0c004800e00301001c03290000d82e150080d8138081d0510600542c9a8030580c4600c500e815545c00c0030505c14454200440e01a140d50000c4061100160030300300a5444c8041e5010701612840c802881100706481d14940788416500c4825201214040c1c000703180500d108000040080c82d14900c000c002d004e1402d146c0b80c08444012003c00c0443d00030042c0250b6500000404030300c05a04001d0f00b650341c3c10450f020340c00c0e0200c0c95140d6601402900c020030240825a0710000450f0180c0c1c081e9030a1a000359000c80c3d0003040084010004600140e0600c0880d02d9100481200b89018045614120f49241c1d10781e41c192080300d42d40a21601e803d0b100030000000030b105000306405030b070701d22070621400001074400300c494144410000b403091505450b0b2081078000c5c8050200d4141504d81e9401c41c403100c9034141c50300300d80c8240650300780b40d000101107902200105101003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 998789757 1250 998788507 998788517
    0x60b1e0c240603060a380a06080619153209030105090601060c03051602031504060c0309030e061809070c1e031403090307020a0e0f090c1e01201f020a 66
    0x25010581514a421018802062004000c1144000d807680640c0c01c0c00390141c0c9c0c80d00d080520f02070003007002440f2503020343d007480e101d19a82007150064101d0320f0032490701c646c00e003092080682c500007842c0300c1802d1180039502c01c91741c0c89074003c0d490000c0100003e02d001c0e8028080d5035075401200d81d4481007845030900082480c55a0008240310790040d11040500949420440c81c00d60002442c14403440c80400b071000041c01844104030b80b0344243c45100308242802d10401c1030a4078042d1105200c035040f140a40c07000584c120000364030307001403e0b804100506c0624070b402d14100042c00390210741c004840b00c00d501c1c0039408d6210b4480300300740d11003981a5980c0c00c00d041d002c4800000380c0c0014004448612080c0302c940010790395900302c0406807040c10f001199038a040215403190290141c1100035617041581e8103d1a500e80301c8005540304a010101c40e1074042620048502c120f01c40280494801380300f0b025580781c440428514108089810034031a80c88480c10b42c0c4040348105210300001c16 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 998791007 1250 998789757 998789801
    0x20d0b0a2a0c020102070f0906050a080a0c06080c07020306010602012304020f01051308070914070f080a020c07050415080618062206020a0f03060b1e0c240603060a 72
    0x500c01c000c80c2c1d41a42c07041c0f05445980d50b80314030010900710b0a80243c5120b50715002c0601c03050420340c0c841402024050000c00b1445e099407035498076000300c0e014040c10844583c000515102d0050204c614141e4090115090396071343d140024001c00074414403c00b2000310701c2070720b800244460801809107400070841c460341502d0400644444e4820030203510302c65080711300000d0b0030b9001d000410041103680000314100c8181c1d03401248814009103060300b444501450004030540c44080c070f0340c1c041480c5900582d0780c2801001d0a1615456a2205500c00c5c189004a84260615190310044a0781001111600d88482e0403d0318801c900c02c03020081e90f0f10480028a45201c01a030821113030190076190652010242c80341c90a0b60700c03140000c004602ea05103c94806a8144103601c0244413001e2590b05002581c04501c200045003000d4070b82828008c5030003003200c5402c0c40760314008030300002c0c6000300401d0405041b20403201111000d100b4007851000803d403d01c03034081c040061070286d010500764 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 998792257 1250 998791007 998791091
    0x6030215071b080a060609020c060406090201050904110c100506030a0609030c12050705060a020c030403061112090d0e040209100c21020106080c030f0d1b020d0b0a 72
    0x16044408150782044200490b0084280d501e0091000b600c600d1015100164007400d0000c16910541e0103840702d28030420807091403000100741c4940043e446440130401c1da00600040741d99001d140711032a030103480c241c5800e201a0a02c0d0040c12490801070580303100d040020114421540210385003a055048481540000f84643c0d11030030103180b00e0b0a06040700c4607103843e0540c11851070348454001c0380e4005000d2003031020410003580c0c070424550045d482e101c850301c06240c0b0b030f01a6110090144c0c7e01d03100d19141c1c20100d01e06980d60804400c06120f02441d0040c8a070740e40b9021005244081100c051000c2114113180c006c5955080c1e0207090411540050b410440d864004034200340c603140c003072412004001c190051610010141640041030303003801c05030403e0900c1c10002c2418425030200c80080c1d0062804512403056100c581403402c1e2a40621142b01010401400c00030b40c4042c0c5903009204000104625a0180382d111004001e20100c1c1000c1882c10940c04c1240110180401d803084c81c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 998793507 1250 998792257 998792299
    0xf080a08030705221401171611030c0f03040e07030606050f09060c0d20030313111f05070605070806130b011103180f010810061d091501080a060302 65
    0x7035001c1603601c20380030308103181310801841420742103a98072103244803401e0b03802d681c407171500c02904800d0070030750748141801c04c00050214a640b91010a1015220407a4905403040c419607502400490030389098640c68001d50340c41c1d5106020b60030502c2c40c0302011a110768400d11a4405031111900c0301454001c952130101080d42002d914140d00440c20003101c0100e01040c4440d8000094985410240c41d02c0c0304482d0480200694041c07001c1d078414001c12015945005080c0c03407854005075804617141400d000716203419090340c10f503050f91914401040300580d200c0020407000340208005c0005458500301200d642000340d960a0384009000300c040c0319a80242d00c8940c020105040c62a40400c0d4814402d0564219950f54121100e60b0304c6911258208445d0588046400346450b001c1c0d0b00d00303030000d1081c01819009080400805114802e4a001841d414620040008281460750714021104a0300301c01d040216a00041011011506c03085050041e0303410349a006041055640c0c4036004181c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 998794757 1250 998793507 998793517
    0xf0f0d1103090f0604031a0f07020c011205040c0f0e040b06011e080a02090a0305030d0b040209011d0303090a1511030c030d2408030408010e032a010914070f080a08030705 75
    0x191004d4204400000074040240c9401541c1240d06a0411031504106e004c0e0707603c00040c8401d080d90480000c900b2140e900806800710042e103410001160740740ca00f846245080300340c020300c80001c1000f00124110001c01062445144a4881e060b9070f139568900442c0e80e0b000703900102c01c1c900018116003444038014038926a01c17030b288603001410005c01c040020000e1240e90b01c01c1d10305d80c100165039004c414103401038a0004405507070039031502c1c0c68003000910300ca442c0348214000f4400306c401c040044c1d500b4012224180c500501d820032081d140c079400170b2603102c1941e01c0d901144d6603441e032070750310780000c403e0700c03211285000a103085c82c1044524402901e503000c000356055010041240c1d461000100103c098a01d03500115180c0e424001860300b10707070102000c05c2c1140c0c81030119a150f11030401c1041880c5025050520801c072442001c01d003d0091042c2c0140b0800b80004039074600400000c00c08110784000c40301c00410390b40c442000b9101c1e64440c0000d410b007501000090241402400240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 998796007 1250 998794757 998794759
    0x3080c07140a0522110903060609060d12030e0a0c061701030210030216020a0602070e010e151e0d03030b4603050118020909030a090e07030204080f0f0d1103090f 71
    0x604544007007854542181c4441110700034102c07010421b01d05038201007045da544020190f03901082810901d0004034002107000380141032030500c101200420b4829040544260303400402c484a036440352800c24040002c900a030800a00071443c100c5484c070103011414100ca8010380310105100741d62004501170740c0000c40302058404020a00c0c401a00ca2022400051009901a11903a81404242c0d01d8034141a44800e203038012100601c283c0e480d06000007681d4040c11504504102044003d0300c0864101c003003106c1d40041450004002d054154001c603011000850b03e824500d260f1f51614050b4191601003015001030f00170301c2501c1c0c1d424a1305541001d003070301141a000c0569039078545003551112080c0e111100e40c48000700c0b0440c104880d0940c1c01000e2034018504140c10190001c0c0340300618454039181040c04004211a00c2c0241e0454001d400d204054440d0303000c1079035040c1d5540a0706943c1c002c80d44034442e00d0307403401c51140307240104c02c8528001031460011810104000002c51240f55 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 998797257 1250 998796007 998796049
    0x1080603070f0906150c05070506030a091401091e05100903020f2418060402011202040f0806160e010801030305030702010609020307120f05010803092803080c07140a05 74
    0x10400d01455115a0000c0100080208020782007002c100a404000f8290034180000c6e070120030000390300404c00c4400d650068a81a44960320107484c1c1d000382044113000f51411030a0751030320f00000019001041414003604980c0001ca80030b469400081d07818502c0500507410920885412000030f03004004540e000b0b104444250b00658201418a004065a4040380072043c002426014200c200254054401060348100d00451840c6135141d0800620090402c1010071010300d10900c2c0350305590140250300c1035050000c0e110f500c0b4581d551000da0360f00d4921045292807480c420f1081081450306041070f56400364030b034a0b540e002d403007642002d40704200790354803900003180b84031581c03019521407615a9281642040345404260440d40d060310029480c13410b02c00140440c000c00412a401c01c5000e1b5002e04001c94511619010a241c613507082c1010041c0303035000400c2c802d5810182140c4001c0d82c040c0c7d861159242000c03081c036030f43d440c089a0000340ba42c80410491501083c9111885201186 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 998798507 1250 998797257 998797259
    0x415200d1b050124140f090c09150f04030308100b0702010c03031e1a01080f060d031119020112020301030c0b16050f030c370510110d0e0a0f020108060307 68
    0x4c00301d00080801c0304090a0a2200003c1000700301074000c10110301401e440000702c074009400400c50104000304641c09003800051007071526200c031280f400325400c0d00308102d52503500d030780c9000349030303034000d210680c0081c0e007007808542c42e0813540004a04541c810703443c0078079184645d80103640c004900e0200303030207240d40c0e0f030964601c900e4403414002203800d0b1400009211242c031441005540c602611290400150a040115076005441c549030802c40c21994804c0ca0601c0b450103c5610f9084402c861140c0181601c10a100e14036103030481e40540f00362144600b41503403812207012404240700180c00c89401031010464211980c004144030441e24041c83d4032084561110761415a07243d10215040e440000c0e06845000140300025440792041c017600c42141007842d01b081a5403485066070300c1805422940d4040140802080140754140901030020040881a602154004000c0b000001c1c0c18504404104000818450300c1180e21548124404038250011104064020325803034042c030078004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 998799757 1250 998798507 998798531
    0x1060f050d291f0b090a0911090301061403120c0309010e042a030e010b1509010c0c06180605030c0a031d0a0503030402040b010c02090c0c030415200d1b0501 69
    0x100d19204003050428052442c8020300e841c800c3c101c050307110312502c55081c030441c005a43d07680c030810708994410901040d81c001c903400520180c412081d03295850341c07901d0000034a51045045640081d2380460648040b80c0d040d580362003040c850903061200c0ca800403c034015040d0b000380c0344400c00d41e0018000003030b50141405408039030030b0381c01c0390200d0072840c520700c0704507503a85030041c0303142070000200074048102148045007282000350984400307410081460074081c1d120f8200d075003015401c0b0300d510669540d85c1d030b00580303a4200402c4004007003401d0140401e030503000744c00301c071300600100e80010b142030413500c0e0803401017612880c02c010904003400341c0d09200e2030400500c01d03106c0c0103102551341da061038810081119004800c450511014108007405a42c2d98078145034840e03200d0001c15611492031b140c0c0d50441c46550000b40f08458032409000382e441e40144004510100c0c545c9407005c004814510070340c1c0f0111a0000c500140040d0030800e030760110b80c89002c401a00c07600002c258044480d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 998801007 1250 998799757 998799833
    0x11a0f0f1605060402090606160f050a0c0f0f05010504240c060203012706060228051f0f0506090a0b130c052221211101060f050d 57
    0x103072064560b030f032206007404254a80720140a4200300212138440c501018200c41418100d04948082c1120070101030860600a040c03040d4030240e80c0c80004010b18645400080320703102100e018101e2204040200810594000c0b4200d5041d15000d00f08500c002c480b1002414040da4800d80c0e0700d00f00301401c11a00001544c0d4000345000e085199100d0255800c00c2ca220104034100841c0c0d4081c0d2410b11000b00140c603004681c040c00007040e900d041c1c9446003c0c03910a8181444048000c00714401d038800006032030186c00e44215580e40e4502c00384403911580c4420720907920f003600c02c20381c480c000c43d010981c5406541d215605031240600800050a48042940304440310708032030b0000704500184517400c0346501000c5000c518807100c013894106c1e0070700b16484040d6407003401c603641c43e9000c2c1d5490024048081a071094120f400c034426214681e949200514000d5080c900c1c0ea515070a0032000f00d4520810f10f00d0380180d40340074290031001d200d80d850b038403484013039010300b040c2101c115052a80c2002d410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 998802257 1250 998801007 998801047
    0x90b0f04090c0512011514060c06130209180c1c050304141504080a0605104e0b0a1b03020702130501060c14071814011a0f0f 55
    0x604500600300d1514043c0038a00894042c1340c041c6900d0036414551008048561704280c403107018030034009071008000b044091151001c2c0c001c0c2031142d901000400e1007500201f00e46640309860030f0f030f099100c00003c1715440101300d0410000d42c00400002e111414040030301e10260000348074080d811031141d110b0b2030a43d031080d001410081c1c1c542103000500c2c18203100005c102041c2e040c146103040d1038808010f8440c0c1e6400e0000f000107132580c0c0420702c004a54200d50780a4194074408103404200d030a4402c0b1450300e00f98064110344407040b42942c141a012080c100054a10016141c80030300c07507078030810380130380c0106000201c039034411580c5030741c482440b0b07040b0104085860041c0d030340a650042104c1d610b00c80c0c0019107042e091100600106a00c641c1100029500c460410b50001c031020a40c1e0508980b41c1146440003901c105070340d80714a060300940661907500390b9841d05640c984071040117000700741e015562140400c102c920b1b02e1010703402c02002c0e243c0c549891607040c810071600c0308002600c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 998803507 1250 998802257 998802263
    0x30501150f1407060b1c03050301120809040203071805090603030906030a020403170a1202040b070f0302071e05041b0203090d0318060f0806101b030210050901061d0907090b0f0409 79
    0x380d181000c440d800e181c5403011b241d40c800c4440c0e2001c0d4032203541c000e01ea44014060312003520041c64071001004030b0001030b94003240c0010019510f03440c007001300410002c54103888400703d1080500001d914201020600e01034000507020b14a0081600188241c0e0350000d011882d0f2a03600308030010200d2020310142e05094484404955034204d00c0d40014000c241480e401200c552040000f040070010030811960707c40d5008031060300000340c9007802e03414101036920941801c1461201c140d400304140c440303901602c0c41180e040054030070740c0060050721084414003030003690080042c090540381c9450300c20440340c460715040e19074048aa01003c0c04481c07623442940401c0180b03688101c2c464002c10041d078001030946290001c1001020010544880303610700842c0c41d00d000c0650010f140c400c0c482d10f80382104a441c2848542890748401d80244000d100d5001e480c0310176401090350515070808a400362101100525199042800c050020003002310f0302541b01c81e00c101ca10b0001e0312180038041d05140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 998804757 1250 998803507 998803511
    0xc0e100309051212060111030d0615020d0305010b030f091905010b091f06030e0f0618060601080c0d0b130914010b24030a020705120c0d030501150f140706 68
    0x1c40e860843e18004640404003200441480034103845560240c1c1107500c40ea00b480c0c5015144001d01c0c400c0d040d44114405400c24a08040d40800d24614418400c80125002e900300c0380b4028094404034115002030062443c000001c0000c0b5113515130407000303140c0140420090780d61440003038a8181001c042103204070b649075125105102c151030000d005541c0403c0e80d60746c0e0010700c8816a0300c11460707005406a0000d05a440c3e042c1d208201081180304940414841128035504001003240900d480c0710605940b144038110004025520a60f1124042c3d1581c00c80241081949440d030300c0600b903445a0190006105c42070348440c10f64501035880f1440c05168140b4406d1134407141582941c6100407440d0240701c81c40100c0310380704030700301151072900c0701c480d0f81e10307142c3e169218868080c2c810041e014020380301d1640c140c41120130840c0144040d140300c80849980102c41700082d01a248248210008807490880c40d400c1ca034090481c20454035010f14201e504058128612422500001c4d802d440c440d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 998806007 1250 998804757 998804771
    0x109020403152a030917072406080f0a0b01140603070507020328020406081902010c1703070801140409080910030b15040f0b092d0301090b060108060a0e0601030c0e1003 74
    0x41b40340c1008055011035402c0042c0360044946451100760400303900411082d089101800d003803402d0354881ea005d030005100769070f030540c01c1c4800259140d0010300c06540c02a8442d00014400a000001d0a46048007804003825659601401c2d00c5a41068105031381602629043c006070004800c07540394041d541d24141c41d880003041c010b010803920290070050441d4045040e00a883c18100c01d600c00f85a030900c2d044120180515091401a0034903610702000303c804014414440d4000b1000760584000c000c0118510400900f00320540e10599000b03490141c3c00c012287d40c1d8108020180350800f800d050101d280104000803845001e10030b10100b412000c00314080c00580f07014000c140051021864250600501c94005031301402042036260002d40032010324405860004203075000c9001c01070003017003801524100400d115204503050340c0040d00325000038280b8501a07240358262a61484200300c0390795402c005400a081c0760400300d0610095003208140c0d652006074041d41c0020941c2c01007010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 998807257 1250 998806007 998806013
    0x30c031308010e0c030c1306090f0207020915010503010504020703030b09090106080c0102070513022515050601082806080a1a0711031c022a060109020403152a0309 72
    0x4a40d0501611007681149214100585d80080c00b4960709000b1103178101348a40d01110300c0d00a240d40d0740b10102d281e0502c90b08071029103c0c0d034068170903180207840301500359880740004808145e1b0f1441d4103011440900040c812814607501501000c2d109050020f15040d9000014000c40b00490790b46000f0fa4444005008503401407100000014081c0002c102d91340c20a4009412112800210381881e0390105401035002c012a030105041d1448520f164503800550405050764a070400d819600700d03040c03002148181d445114080c0c0b02c0c1700041c02810070b04403803040b0310700c6c41c60091400035600f5441e081d0102d2440c0b418450300e2a40b510031112004c03104521652003400c2c070001840300052110a02e01c50040c05008801c454500d48a03c40b5400c40f121003d001c60000e00802c528034000c4180d520a81c9090103042c50714541c1c0b05203000071502681e90340c110101c203920030380c0001044961130421012454255411000c02203d5540220908246221a85c0044100b85074544006602d8040000c24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 998808507 1250 998807257 998807261
    0xa2307030609020a0509061e0d0209090601050c031204050f07121101052106060f0d0b0102010f18020f03030c1203180109170a0c0206030a0209130923030c03130801 72
    0x1400b1000055003820640c880190580c010100c07098000ca000041c5501211801c8941180b4908010780c03880c0c0f140f0f00c15007588020b400410110b401a0b0800011407200d42c0540c050300c58103800e580c0118503003e20000303584076214014104a6140c440d401f441d461a000902c039a0001e0003c09200f02428150350a0014800c2c09250100e418032008005c0038084041e80080e12070305841c0806004100d4071880f0204465104004501119400c041681509082f164106131080388003617009000c041c45980c022800c44107494005c3d910042b82000304401814160886da50703205000b0b0035203050441003030300b0a0402d00035200c0400c448030000100a00d080e44003400c8944c40602800030440700f0b035071f6034401d00a02e08030028071003401c1020031209201c0780705040d24403045a001c0c110b2a281c0c10040080e42c0650400e07040302c0d1013802c20780320300312061a10b071080502c45500b00700f1a4186205001400c4a90800381d18507222074041007001800802080000701f490410454011001a24000342d243c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 998809757 1250 998808507 998808509
    0x807031104140a181415010e130b072d1d0f040f11030702071d330a03150b01030513031b050105040b06090c070309060807120e03030f0c070c030b0a23070306 69
    0x11f103030290001b40846002c2d20350740000e042d45d016010300d6241d1104bc0055482240304030f0b00312901e4101540702c4000010400c01c19007030120f240c0f94800f030801201d07d031411100501083c1904110703924a480c10a26042e007040d03010301c440749400245030441d00d000a20340d9000325504c0b40035078480c10042207a480c1d44822842c0071488070a42110600380402c20011545030224071051844109100019000a2801d61090715070000c0c05d580b40c07150b4030f00d0a80105280f10306522404ca10f4010480e00d154041d004030361040409078200941010617507810ba070101a4102111071102403220305000117071003403080728015070080b8003240c40b9183c120100484000000c1899811150900250700025000fa2000090b50840d0600581c0c0741e48100b8207d402450400380490320b90b042c03078500000c840c80071000714001e0451500b6014640d88201c24a20f0313a06c1194801819440004000c10219440403070007500240f007101d01294454058407404804a9151a025100e03070303845d02402140c13074062103440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 998811007 1250 998809757 998809769
    0x6020721080103080a0302180d050601090c0203040305071211180f0a090305030609070e0a030311100207080a0507110a24082206150807031104140a18141501 69
    0x301e1503041d581d9850700e5000d14190b442c1031540100700100800000b50005410b20000f62010289582d6410b065030785210a01c20b074460310345481c0f0045001403000c011201a03a80203c01442031b07518080246070808540c05040e10900c80d14002c40e16680d46410081071080000481400740b401c00b1b400780070000c0000b418404c501480e065480c00080e80081c1a00d82c801811200c142442d6038a0f0003d031501c90169035101d5009140110100400d45c00c04882d050092800c03040300d0204111210080480c0b1508034080e012580c00e0080310240d510500041c0b18092203202d00180c400c44000100d801c540b0942c000c0700d03030303007110608900c900c4031001e20b003200984292501003070034245802c100b01000401035010100380031600f519000d108403600402014000100c03440f80c200d40c1c0d40712017600c80120740422188600e10a42400305468a800b40030413034501c1013030a1081d0740b2000071241c02040010003916241300351061460110709400030707400b903030000e483c00360100c8200161200a1500705030045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 998812257 1250 998811007 998811017
    0x320415050412060e15130303060b040605030103140304030515070f090f172401031502123601060609081f15150905130b01021209010c06020721 63
    0x204140c495408002c9211a0001400600c0000680c0c8250902036140c92444c4400000700500000001c43c141040f010b5000c3da400708030031520754006450903c641c1c407601000a40600050001c9901c02c0171800c3d62817400011246440c1d070b00d942e050306143e00341e189612022425010014490b801031103940004070300349040d0203a94103245d0400b25915290040c800401c4052242810b0f4441c10000031440350030148422001074850800340d8407040702400116280c00741540001c070b24143c94001e0364034a011400740307950703a40d484800304184c490f0318103214800d408c0850007032400c186950394100400840c110010908504182e00900050b15a80c0075660075400509042d8501144400d90120b00c00048008220b40000044d0840324203425040402d03103665414030780703281d90b070820550f800300d5006460803400b0706440310f800c3d4110380d80403040d540542c010b181c58568284144c0c0041090f2078050400c0c00d0200100c1d1160000c0780c0107403600319000040c03600320480c80d00003182c20f4420000d091a00f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 998813507 1250 998812257 998812259
    0x91608070f050409030f051317010903090602060702210403062301061407110a080709091118040308090106170708120c030d0b04110307031a010f0f3204150504 70
    0xe06c44410622168108000030582d6807101b006c20b2084001081036460f420205180c00305070b10700a00f2011001c0700440c040c4d2500140351400031440c1c5105030040d401030000c00c0d010740124030842d141400707100c01c50541000040002180361050b8241000010068060b036409150b8803115104181c11071000c0c8000a1016090442000c0446600580c0403405100d02d03003010003c908400c0503904801c0c401d006014010441c111a80e102644860141d07502100309500c0303000b802071281003a03a600721080209400900840d001e401321540282071480001a0b0325500c0f0090040700ea0340403450007058010000c1046009010015010b89044550b1180e1030541d45400d155624440d49405041c00c40e02c9200a1000e60390300e0b0320000401290a0750203a41e49400b501c028003d05c010540b520607010203a21600310303540309074041c245c105110b40340ca40942060340301c207807904400101c82d59609121030304000440c80a0001a814068020b02241c0d02c1c1c07418141c02d21444174020030810204401404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 998814757 1250 998813507 998813513
    0x209060f1003020d0b0a120b060a030b0c07020d02040f0e0f060f01050d0515011d090c0306131104060b04030212060c09060a0e090c0d0609090b0708091608070f050409 73
    0x181c15000c89040c0c180142d6807401d040000003d00000400d45610103003014002505400d1103c03103d00051089080e90059550f442c10440041c0d2170340401781414601200180381040400000c0c45800d000502c100040c0c03d65030300103015a0a01d105000c82a40c07142142c0b06035500c10880754542a50f1000a4241072a040c00c07900c000c0c83c01441041d1055113484841010710805211580c0d00c005c03180905142d80d0313110320b0095009401110104444088200041c4662801207450208407070018091b20040d101c001038070035403241c056019195118040344005843d03030b8505c200c100510b5000031031620b50f0301c1c45c0100704549114090b004d8407500000100210003c8003c1260b040745412034142d51291804042242d40514001c1450780007032000d03090004040010000d000000c03042c20b82800031944a0b441a001d44035031860041101d85480d01040e44140a451611740c000481c0085410a655901c03148280200981c4400210703001440c0c10710800c0580d552a60281005850034440040c40355 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 998816007 1250 998814757 998814769
    0x6040f051612092a15030605090c0901020706140d1a010e030616180305010e0c03010e010204122a09050703051305060f0a02090d080c011a010518030109080c0a0209060f 74
    0x7004040114a124148001c2c13000d50a0005071600f502e20002d0100c840300050f00504c281c1c0106440b03050044001901d008500f01200c1d03c40c0c1044c2d0144c400240b800c40107940c4410070f040c0c1c42c04801710038409003001200310300c0340400403440088410300c4101a6000544800281203070a402034203e0410411280b5000983e814090060b261180d680300c000c031046500c16081d80c000400359400c05d000c26115190024401100e050120020004800e6510b407081c200d108510070a0040b000810419021130001c0f20101c050441c00b18801c05204d0541104400185550b0050a05943d50f5070030301494981c144a415817014000454030302440030742d201e071541d4210003402c880c8032045040028240c2c80c5583c041e501c0095025018641070995460004441d070081c002c0f10310150300c0c001c114508588013280f104142c49040c3c459600e048491211900780c550144a142e801d5922103403100c0000f0880c2c0c0080243c0b00a8001405180c2d4151040110307003031001d4481440f90040307514140c1d40d640c5072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 998817257 1250 998816007 998816033
    0x4060f05013002040f0902101d0103020c1005010806010e060d0b04020909010b1f02160f170f0d031b03050105100e0d02190e010909050a030806040f05161209 69
    0x5140300341da0024030003070b100292002e628020340207401c100446040c14003030382100c1c04851007183c03000100443c81008807a240110003440c000180c0c501156642ea50181c4d0090a03201d68144c02d03a624850707120800740540e032083c2e21103080c80d4085801040030300c170031003515500b250381200c0503440710314162201c1040e0340002e04041c0c42580c07100041030401400758000482401c010300341032a2005210106401040840078080140c099902605248a03030403d903401605c1d042d400310101c0e00e06082205e4260701a0b40c81c0d01002e03100e00c0e500f100417000108414030141d00640c0e03000c07036581b81400c0c1e6150b2400c2c860f9050000e16040c0001444159034a014a1424030f606240082d002524400082d10700c40001202030740010703400004122102a0441000076a070141c150040f607642e0381d15a4100b2034140c0000507105410003c26400020310402d03846400c0708005102082e801c0d0250040803c0307070000d450900d0745c0c90940d5000b2884681100300304001b00160300040009205680302c4440500070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 998818507 1250 998817257 998817299
    0x70512130b011505070f03111014070e06040801020f130509040218061507060516021c0f09080f0f0f0114010e06040219050405011b02180907091404060f0501 69
    0x240781264450144980203480980c1d1b0841c0381000c400b0310ba8240070b010043d100400709010300920203051420801c0c6e024020700c410019409401131342d501c010840303403c1020354400340e012a08202c0003850600900240c020504820581c5645541c02c8900c801020f18981c8501e01a40f0594100000360f0303901c07041c010040203810106256503403100d00151442d40315101048400f040824000207206456100314800d24100100c0c00f401451503000707030f0b501d94034509240150f141441e070240c11140319101d440b40603841c0d42801404581c0302e4501d40c0c10303d1045c445400c65036000600300c001140302005080c1050380401c000300a4000007070300a00d40780d0014041d046122803a10007141154945034102c0311030380304a094252101d12899801003055106102d41800110a40030017500d07004034010400e441503005011420310000d03650b07c032104000c02419030b8194041c401c40052042c1c003a02615580070744224030792000e45002e2910b02c003120010210440030900e001d00502c1141207407560030000d503507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 998819757 1250 998818507 998818529
    0x21e032b08091212040c1e0b0c03040521011d070b1b0703080c07051005030a0c0905060a02030c010510080c01050f0d1401032a120503070b070512130b01 67
    0x542c04403a0752038020860b150690b50800007130420403144400f01d40c20b000d03500c0b0300c4030080c1c59640d40b0700c0804240e40c02c3c009615003101110041100c0007074400140016080042645d041980d80d400040a80d00d100144915190170702c40380100251081c0b00380b001540281403400884440004120baa41e41c05009507400032000041000c2d0010200240310610901202112919a00d910f86a003c94100c1c1d84224040c0c407502c20040340074541100b1000c82e0000540d202070641d500c00701070201800602000d0170502401e0000810700f504d81200038400030442e90025541c0d0071840200a01310303180201017079284a86101c091007030420115420000c0102442c3c40c0e600d8401c070704164a0103104040030740400034541001c2507407a00002405504a9016030444080341d102044c0069020f4246051480300c1d0815100610008101e08074003e10140280c0460f13081242907650625060008d039040070200741c0116804c031281d500d110380325074425410309020a1240848d5200500c4140c1030007214013282d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 998821007 1250 998819757 998819761
    0x3030212130f060e010f050a080f060d0507091b09030b04020d080418092f09070c0807080d06050a180b01050c011505030105060109050d0b0c07021e032b08 68
    0x2445007070140040c10700451024601c690750080070b055035a4402c0d95a011400700714454440c035001318140c4018514039102c0b01040e6481a00c0c3c003101070740082038607601003c014030b1000461420030114018020504000840311400b05504010b0586107400c0700402260140c244000f0728240c407000c0e00994140c0d065100522145030184140c040c54114080c850f03094480d48002c8049900448a40350190612200c00c07911004001c3c45030000d000a50450b0701801d00c2050f032030500c00c030241e40c84480352411118071903443c2c0d21159103502c911000c3e9000030010071b078032000f0016440341030010003080700c4110300c09190114150b0750601c6803102070301c5140c4d180281140d5900500450f41d10746207900081021105412044000c0149801010700a618150010790654002c039055410b4540050810404501c1a66000c042c200c0c002c0040003c0501801028016100c40342c82c8251940b84c0c0d4074116103401d02409241c540032403200e80c0d0503603803a000340d0b00c110780880070384104411015185ca84895 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 998822257 1250 998821007 998821027
    0x80f1f120812130c351011191e03022118100b15030613060807180908070b0403020a080c030901030b04060e0f04030e040f0f0b01080103030212 63
    0x90b002d411a02e0300101d40711802c00c50b03650410300380503408a101ea50280149070310781600c21448841452880c0c914a0002c14211300043c84821402c69500107008460510040e0040141aa501c1c0105031548610100f18041d40d628581000c41d0450510300e81803d040300c1c00305074152401030700b100c000145540060800c12010100320720340e80e924200041c0c00240e06001030540c600240c409a15281806454803509080e03140b4003c041d4110b000400c00c000d00800e60b402d10855a0001e0003407540008010440c50054400e4028078000b4080c0c0c40140074030500d01008601e80e11084204006564a06103d650004048200342c5016079080800381c2003644d6139140681c40c040d111031000d0035a4030080b41036030038404004000d0010440a90b070501000504d90180011781d10240a243d180001a10019040702008001030713601c24041c3c80c02389000d290010101e000c54001450114041da120010001459518000c12000c04020301c2c0c201c4196141d900c0094070381503617003642803003260b00043d91245 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 998823507 1250 998822257 998822273
    0xb0901090303081506120603010b03060906071206050901060507030207061b080702060d0504060e1608150c0d0f2013060f0c050106120201090f06092112080f1f12 71
    0x2680a001d082240d1b6003a007040e40c10341100040316842e00c0713582003144a0301c0c1814045185406180004000c0c0415103074610140c82030054889804c0001c0c4e600c403000207003584c813800c0c414000c01d41515590741d00d03481400d0003810300034503070040c0041c010741d045003400819a000e9030308001a041402e180c0c4804284c40010481d108a20080800c00e0074031092101348100c1f031b44040704502c001012501500e40404800c062400944a2610f10307170450000303040b400394441d2313035070394092841505240f902e8041e14480c0104c135060840c5401032030b6035001c9428a56004011400d0b000f08a4041d1800c10b940e0192840000509005000030004480b0765004494012800d202039994004002c0c00072b246c491881038886051100168001242c240740000c285e042d0005c801c1c152000d42d030343c241505062000c5d41058000206002202c00c54030b80c0c605003c41e80f280701d80d03022000309542c0c0c8045824022002c0311011b0015281080484000a00d001039405c05c0d0103c03000c035080c2c5248001000b4440c100700c92 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 998824757 1250 998823507 998823541
    0x1303031e050108071208190e0907020304060905060f07030f1b110913020604090905031b030a0f1409090a09060207050303011e0522270c0b090109030308 67
    0x244604940d00103000594141c014905844403841116041691121441c6801080b40805002841c2c100070461352403c80c03d201003150040c82c104696080907a0020550f1800b04550340001030300007050070300070240c0c4003508000520041b20824180a207903200c958040c850240000c007030200c030600407040700d4020140e0403030300008819030020440c00380c07c04900344604880c806100d02c0700c0d40001500d028041b181d010b4010b40191010341454244601400242102e90041d6041e200c00d02045528650058201d410716011801840d250200d116026040115560440091110242801035201800d0059484100c0700301d62190391070300c509116000419040e04e002d49541d00008840c014460000300460403030703c0e11142100d0b50000b0b42e0807608160001c0c01002d0b03100d62201d40c121690300460300106c0c03134a100d0310000250041480805400318400000c04070b4003140c414414070a00c00b01001500040c82403d810616050300200000c0846250380801018048600d012600b241c1c501e503040c80d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 998826007 1250 998824757 998824781
    0x61214040c15020c0907030209040b0a030f080f120a090b18250305010e0309090a0911090702010b0424093b0d05030105120102070c0311010c020405040f0308100806130303 75
    0x200070f402e04880c010042d51081c07274400e00481c2007a03160781403820070301c03400d02c1102d41003181c030908404184d0700c0c0d008951101d9551111640d0a1000104410805507064002c856a500000e0030514628008026190051400310164400800d0780d041d400081880c10704c4650040382c62030003041400320703501080802d030405031156192011503066020000000c0426540456020b0141e5842a041c103080d903003400d60007402d0101036202e82d0001c0c104404036a80100c068000840c1030101000418102c81200402d103006031408142701a00d080a0100300b4003401d034074001441460900d04800c5070301041c15000d0100201c402c0304c04445010070b400c0704410b041017582540d9609000803c010b016030000c1c001c0327611400d172105512400c200144200c5003840c0d405044030000038038646407580824144150b10b41030204050300000180e80700d00c035061090b0721440300828045d8072030900400083c2c1c028251007141c010340c00c081c0000d400c0001c0c12940314041210072000e00c03040c3c0ca0201c01400d5804440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 998827257 1250 998826007 998826019
    0x3040b07180e0412023f040b07120f02030909160903051b040b01030b0319031101060927020108040f0503070b0a1d0c0a0e060a050604061214040c15020c 67
    0x710007005108031013803032528201d03401c039080c1c0f280c1c510400d014140c10480e0002c00300c001c407104106840c41c0300b103880c1e03485809070b6140741031942c1e6a1501140b0341c0560401c880301e10041c182c60b0450b9411013800825008980f00035410525004040b40c4c16142c040c050b81911302003d401c10081501c10031940b009954020182c8002d80c01249a15041c52004460180709a05003910040103510074414411102e0004000700103291b5246545182d805098209800b0800d8034404040065024011300b030042c46801030014018051101c488050b042c0840b6101600d1106c9682030007503070340115001e0300107800c010351211f20380042c5412441c42c890b0020040800020f081003201e150000c0e4010000c127000c0f4440c0303c644032400c810f41521043c10844e0a580040209001d1004030443c000d915482900a00fa00d0041c85e25240004c0300b03900140d02c400c1c0022a546200c40c0548418080d00c0d92001d4054004196418280d6914404440500900c424111095000c4805a2007003041c1c081c085000307025 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 998828507 1250 998827257 998827261
    0xc060115051210030624140d11040e030a0c05010609200c16030c08190302100b12010e030301051507021339032a0c0201050403080a1d030303040b07180e 67
    0x11003407000f449015a03190341110031800040d1048040200c0e4804040200007500046041d49c5080301d0012818846400603a0385451910314002000140070080c0a0340b076250304000140f43c02400e580c0283c001048003400d18603503060102c01c944100000c04a40503003e5220300981c03001134600300190b180b210180203140000014030296625080c140c034522030070780b0940541d50714080c5680c0c00b0700c2801001a44041141d54140640b680f00c64282c41c0018070842c0d144050807803007800c0d10381c40201480281c0001004000900e0190360156001d9801c507120b0382081c01580004024031100d82840302485e40b6400c00340141d1020420244262013200302caaa05d44006103410301d03d0b05071070300540bc0800d140a410510160325851100d090007202c042c01401c0c1c11405004444010281c101241031020500000c4001348000002e02501c0c482c544c2c5402c14008040d009060707418411a07140e0280c0c108200f44008292003000050f072015050520030100300d03080000107800100e0b54048902e0452140c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 998829757 1250 998828507 998828531
    0x30602031f030c0504050a0203132003120a02010c020f0a020402090a1509060206070c050c131b030e0d0c2006040b04062f0a0308041104050702030c0601150512100306 73
    0x16002c2520005e940421071580e60400d407034200c0c882501e490a003040b0640c54400002e0101560482c80402c4981144506841001103464542d03220b0740c0c45a4088085508a10142d09116070840300801d4070092404c12580f092041d01d540034000085d0045030009020b8245896001d400002002075400c400c500c1c0d018014001c003102d00d980030320f5006025443c00b2507840c030f104000d40a0196000000350040030249010881c80011681c0070700d03141d680340c90300328400f4243c501307180120484603140801c4504a02c2e8455017050304400310401800320710b49036000400c86101c9400e00c26103094210091200d10301000580900560748500743d0030714009004100f05501407a4070181c182d02503c2804000e60b81c00f1071090003000d4400390b02c15580401652000f0078801d02906401c18007800b1240e82880010b000b29041d81d100300d6070000503900024454906c50010880701c1d00401640d0b20801c40071035181001031440c4191112000c95010141c0450040800303540c1880013198415005c204a601d012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 998831007 1250 998829757 998829773
    0x121109120a020307060e06270a03051e030a080106050d0b09011e090207020d03080a090f0b010302011206060f030902040e10090b010b0405010804150b191e0b04030602031f03 76
    0x5000b20301900402da4005242c501800240541d48401000c0c1c60500040404101e03403500f00030000c0030700e141d820742848490b4a400031144c0155008001a0843d40c1d102009403100c0703507410000d000300c3e5108100c0164256841004241500c0781403410310f9481400e14400d40243c14044449644a544a0000a609400f10380c55107802124003000310082076907056074000302d01445501a41000c1724072082c000083c46000b0443c0d00c91025000060003d049840301c5e18112003264040302e1141c0030740e0052040d980c120040d2000703204011030510070365041c0030005045d0b0201c45450802c1c562103400100855580740c000b0500e07104075504aa1082c1c554032078000c0a0040740341c09440c1600001e0005c10860300840484050b28411385548030b41780c4a6a03903140503506010b0750303d50b80700d50b0b40c401901c3d2130340e4004181d04100c80c0d05c1500d81d013440c100070031b01440ba25440c08190403840c03422810860a2048420341c4c044075080301c80161640e42d07070342e1a503051204502e201e8100207081c02020007000140c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 998832257 1250 998831007 998831023
    0x281208071202340506070e041b1d0d1401020a030b06040303141803190c0501172a030a0207031b02130e010204090f23060112110912 58
    0x903540300081010100c41e00c10491041005001002c01101e03c01001c0c900c07421a0001c10a0305030009a0b08034080751105802c100e015201c0800190300c056a5032000c1c581406064070907007204011800d6450001c40260030a0084040b030200d81c5144051140c050366070030045003915401280c1c0101811080c0c04503070007513029202c41c0000ca40340c445c0201c820700384141901d0940780d1503190300c5180c900e0080d04c580355411039007485105151003500f41101c1d0b1400d0081000c400c0d081098104040710314030300103a20880e5074001070304000d903400184c0d5108a0341820650814038800349002003044000035040300d2000d00d0251601014000144108010b00360300800040d4001da907052161302c40e120324040884103ca41c0a544021808075003001001103510841500114400040c50a95280c02500a64203c14120a503055454003c00c400301ca1000d01400004101c0d00710400520f0301900107080341c440504000090744e9110060703c20942d41600316048500b00030038110401140151203551030f000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 998833507 1250 998832257 998832271
    0x11d04142a0a030f06030f0b06040e1b0105180409081b010c14091306060c06110405091816090623060d0e0703080706020405100f02281208 61
    0x4582144003521010a901e290084a000d040c90314180852004a0140c00114403100707019035101c2c000400034401c51401200b46102d1108110300c0e25000041204450005200418030f800504e07500b0b0380c0103420800303004c80781c0e4242071198443e00303a0740d4000c2480700e008000c190810303d4503200000307000040001e03004120084101c1c41010f5040c44000d0b0a0360108002800031403401d00000c00811002c1d006001100406000901c0344d0b905000702406982980d8040c0c0c0c04104444c08401c24061035004182a0a1458059a14052030400440c0948500070001c40081c1008601000094400c1c880302408072448441c0703114140e1a1803056005040601c01d9105809028a8903001c4640504113040020401802941010054505c91002d0101d5110144c0e545c056100701100040040b0054003005000b0880140c444d4102018006040c441480748018410752844992002c0d81c0002c11364a03c2c03c0e007080c622000d1072000314030394644000d00700040200c29000401403441d40d215165611900d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 998834757 1250 998833507 998833531
    0xf0f0c020306101e0303020607121b0320070b060d081b0c09010503011506030f060b04032009040f12030b030102180f0d02150f1314010201050f01080c011d0414 70
    0x401140f0304d52400320b55110040c05a0401d80000c3c1d030140c020140250324804018000c41c41002034405016030b9207180c0035420220740d40d0012007001982400c9000c80e032504d00300c441490119a51240308000d007006140c9885034002c00340110401080c04140d403a1000d5120100381d600407074081071910b0364080c422003409a44200000501842e050141c620b0341e030f8074501c4134503506061190403409490040064108a600c4600014600321942d004100941c0200414135160b100c1a400b15810b4501c5c1400300d2180403104d003440041464052940c01d00d42c2d0104100d40110b031620001d40180a0598000da81944049010081c1003241d0070218001001210007400d0302c80d000042028026154102a40200036843d0740c0003070010340c0e00284035900100004134200304100e40c8480b030b81d00c155000143c1c10207080184c0707401940c0900840d0b0b0420100700301c6165540c101410ba47d80c030700a150485042159016501c07411441100c0900f0310444040c00a0180da4801104c0200c2c1d00020380706020425 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 998836007 1250 998834757 998834789
    0xf0c160f061407051902030903121905090a061d0d030507050f030309030d051008030301030305130509061c0611030903070c0e0405030306150d140708090703030f0f0c02030610 77
    0x24007182c030700e94400c01c090f4a600b802c0c080e40c03c1d00040c0400550307041c1015840308004006c0e003907030b081003825404500030800c969110500f84102003d001800081c0b401c4c07000034003036400c0c95651014070005841051030300801800c40b003102d9400d08640b040c065600608003003458810315600c0b00003040a28058022038085001d050161a0381e40f004441d5212550070074810352501c800640c00c940c0d00300b40c2c00b0004d4198543c50348402c60440c2e2007030f402107020401c00034008182003079140480000704801c90310404079260000211f503040c40c503944010b07580800c0c02100700030891076921841c50a4411344015860b4581b8512540d900e40c070160080d580020070210004451a4080000b40b06a0341324004e1402c44e1540400c0c440c42c04081039406403201d80501010804c145a4450045901c7d602c4240880360b0408030000352400002500403072280c0c200140901c0881d40089503c102040030389401092400c0c0128201c0300451001c60095040c0038241c10f1140b100f0500c2015016a1322100d204600d01d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 998837257 1250 998836007 998836031
    0x80d0507030f0e0f06010b070218480d18030906020c04060f05101b030807030e0307020d0318090204090209011412072006090601060909140f0c160f06 66
    0x910080c4c50b12221390307214000500c0000f0064000d05542e62014209140900c40000050341e01c00e01120341d1001c0780c07200640ca00c0054401c5450010308074906004142120080800b04c86150312071301440b0a56030000f0390f62500b4000c580c4004206001c0c01200395210340f40d45002010500148941c2006118880205d030f800c0c50540700b00000c40f4040602603100518060902001c24041e21600d070522002c15280020304200d51032158600344a51780e490298507003450702404854170494000701c03507032007444264016201c909644403201c0e01410140c0d19406890040c1c0000041074004000341d6002017400142890650064030808400340c0380c050010f0400390240025015810006011002540c0401c0e4590700401b900003010641d42e2507000780032002408146410b40940d0340e080c0a41c01900100402d40e40300300c0700c50241030003410078070a401d00c407581840f0148001c1c0200c800c0030020004130710450420b10840c0d130b9000c1041c649091015a030300708041207019144007924551f0800860f4218 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 998838507 1250 998837257 998837263
    0x5060c150403050403060504110901320406031b1806060f0c060612150609050c27220506010f0f110c0d0506070905220903030b03060115020114070c0f080d0507030f0e 73
    0x7030100700c0f4028a0b11400c100c42c01845101c500cc45190825503c03107020001c101100c00d91240c1c032031280c6009200318a4550700241001c00211801404d9140c21018030040f540502000c500c01e03032a28203440281002d0602c0d000030650307079000d4000c030055004498108041440301c071b84409044801001402d5803107070090b094a10446202010040820807112844c2618520b1110300c41400c900c151707002d00c0c440200700d0006290f0b400c5650b1034a4000c2e03440b4110785502903141d10807800c5c80d10041304001450080e129018000c98042440055480d03101c080e0010001c411107074600030002405202d003802e1081d01c851055860200182d02e140c000301c0e190a02c040b410350902040c2201d640f404510300c03a19001452802c0003203003015115039100b902a40c00300a901c6c0a40700601c690100001a03010203402c481c1c00070f84141e80c10304200304220b581c80d0496901180c140c0c000405000071002840d0005083c42008e4020740418680001d00c42d10a51561084515140310801000200340714900c182e6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 998839757 1250 998838507 998838539
    0xe0105120f251d06101817060a0902240910080106021204050102030301140f03070305010227030304150507060f06030311030304230705090f070905060c150403050403060504110901 79
    0x1e080b01c00102250880c100a04030703c422400514100b41c455000343d90a0f058008568811b80c407941020641003811fa2083c0301d401c0c1c1152014804000c0882d00d0ba0100c2d070030f0f40401e0f0300c140d403181034400c842001030340607003c0314090b2800520042c0070910804010f004035100307001d00d0005104907101c0c5450744500800721401c5d114140c000390b0450307180c580c0c440c0000980394001c3c0d4110410380114240d5850802041010314030540000d0385030400780070b0702e901c12039207140200714134000d204c0041c445880c00700c2201d0076140e01c0760b0030500c04034502c01c00f903855204808001b40300c107140c51030390b0b962a039644c1d002005891103640c0d1303102200940f24806569020699000d000400368130a102401041c0740c64002c51103101506907100c4d5a42c0340300103003102c8001c450075808220b1036000c000300503a1013056580a03200440c0c03050706081340a1511607454040618846040602c4c00c0810700b45030161040d18000e41d030003d0140910304e840d00c1d00402c0364108110150180c000c45001045810070750440c02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 998841007 1250 998839757 998839799
    0x301031407180c0e031c0f1b080304051905071a1216140d06260a08030402010c020909010e011413171b0d14040e0105120f25 55
    0x24000320b0300c9203035a000300442c0c1a441c09010800b8a00400c94609000c440306600782c59200e003c80303030b49440300503206141c00ca50550821250791018800c0310845110000d040e50001ca0312134807560342c2e10389146400c00464102e00300c44060080b000400c1000100b000a07075601022490344880c103400114454001d030901034403c003c8420000d0850036462440181d41c100301c1c64a0000b8103501e0451381d4065000c13540c803090b60364581c00d0600c00000303a03000b4980e400200d140044074018440d0039081c0c88164102c0010403c46001010809581c82880c0b00c1c0500d0350014000a02800e180d05120b009000140940706103509200d11010702000b808412446924802d041900b412020741d10800d401c4040c01141e107040c0070510111254502c4081488401c00034500244000507803500302070610b0f55100003a80441d10300300010305c400c3c020542d4050454406582c0c03585004062600607040c01802c00c035068161090303021410b0b46d41610300d8159a00420300c404110256100c100d19880c008016200c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 998842257 1250 998841007 998841029
    0x20105070c0807020d060f0207170a02070303121e02030a050601031b032a0807111209010e01020a1202010c09080c15031e090c0a09020c070b0901020a06050109020301031407 76
    0x80419000c100500300f0b02d1000740b604021100c2961040d0450b06001480601c1c180c0c0400c140041203c1e1800c03240c009032403406001e0800b444c400b4025520511408010108a5a1412072000c0c40180c4c02080b110045079200325441001005240000d400859005e5002410440450441d500922820444070030800c61442e1400c00404190050071602406184a01c02085100202a0b40808090000003540d41c0e2850742d0070700c240000c000000c2000b81618681018035145080301a000c01c031514040282031015189000400507402d00d40c1107040a00f1180003064000010360b410342c810b80f11003a454403030803560350301c50300c000340e941c04c04100090700040600300c07d2410b144030002465005102c0a000510710712110207c600c69002a02c02059650000c60a1101846d10b0b0a8082c060030a21404608001d10340030364540d10001031082031819100000c62908592090080c9500700341c018038103105075651120b00c030000b948240700a690b0702c000d1035280100c0003004504a004c4034400600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 998843507 1250 998842257 998842277
    0x10315090e1906052d0a1109030d02101113050402031503030d020408060f04030c020f0301200315010e03150c252018040606080304150e0102010507 65
    0x101004000070001c60245105405480400071450021041540c0c810300003c10b0604040500c00c2c511301c161794009050500d104100004c25041481c2c0036817080000f4804503010580c81700b640d000e0303c180c0c0c3e40c032905406100904541a90001403900f40300c00021701c20801c4484003031500c4403a00403419680d4409024180800451420f9000380d41c02003044820003180b03096030380002e4910f61021909144140d0081010041d00b8028000503a0003040c0140c0e40ea007070314290350700411000170541c00071b215400c072002c2a802c54500f54010700d0681c40c1d513105200c0000210000800355003040300e41d400c0d4101800c0c0d02c2c10895206e000b450340e985074098020712a890b8401410b0000e65401802c100031030005100d05511903407c100012481d042c0306111800c007107414180710202451040c1400705800000790344800035250b04c030381e107408a854101d4180c40b54640c0d01c0c1031000781900e58041500c0d440003140204001c00150003003100d40029840d540f481400c200016801d903041181c041011900d07402c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 998844757 1250 998843507 998843519
    0x8040b09121b100216030f0509100c03141b16141e090403090302011206050108070c08131d16090504020c0309130e1006031101030926120105010315 65
    0xa0b000300c500300c5107040c0c0350051048900682280c01c9801c1c4100386502c1d4000050034140c21400c45500307448903181c007518150010703000c15600000d0000308010402c0c0080e03c0024540304072101082d2510f800b0007565120000d440096983c1e40c140f1500d00e16000e800ca40601580083c190320045480c2034450b522500040c404001d1020b80c03406c2c01c80092005905d26500550f100e03450749108500c80d481e844105070035400014210b801c94041c402030305181c28070138090b9070b07003140c92664003440b0791520135006085490011454003900722181303400381c144030340418109a20094071602e80001010b441d1a07641d2041c0c6040d00c8826005080081a80d611003440b03207080c90303001003070940d0000e400c40780b420891002260003070030409000d2901c260340f2110400e040c4414404d0403420305114106000d000d0846d11440282e5040002250606030f441c0e55103010400c07c03d040c03c80c900540c4034070202c003500d185100d800986c00240d180c00114101b00c0042070560083c428a1000380308a0b10104101c1d040407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 998846007 1250 998844757 998844787
    0x4061706160215040c0e01061d090c120f010e060d0b0402010f0c0b0a0e0f0703080d050a0b150705074506060c0506070201020313060b060906030708040b0912 69
    0x2a10749421406103c4108903031045480a1500440c800c05008218610700b4a90340541d85c0181c00181c108a1000e2040c0ba44030541403080c01840000c440c10300071610f419400b5038a034403d02c4140b60b040000001013000042105802e18101d4405110380c4e00c1c107603504070410035803075030254000707003107600d048045009540300305031004a08070b16051070409110035454a096483c021640c00c240380c1c0d150300b5a4801d000043c89105900000d0000801401c5d0455445005501030640700c1c9101d135a440700040c0c1803040c160090050f00002804401b144002c04210000356445101c041c0c0b160311070300b44006030504100220040c10030100340004607840310000042229460225142d146039000d050020340c00d90030384264001071030301d81c5403001007000c03c0c5440c90810b40c00414010641e4414010030400000c03d0703d400e100c0c99417100300016070039040c2c1c001500502407020070315042100801080f204030b41050240c0c2c0202d000b00b009020b50b684540e09540d940144a14072301115805105000c4030b46544 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 998847257 1250 998846007 998846041
    0xa0609020411042301050a211b270302092805010b0c010f0b010f050a1101230a091e0303090f0501021c05041a0a0209090903040504061706 61
    0x300049502c040c912001c1486801c0794101d103007010900d000d5210940700343c4007980394088007800e06509019180c4809412184140000103280368000b06801d84281d1651200303c688207000402d42d040d840101000300348014800090404080c0405009211003040e4001d41c00c99500500a4500761380c0c44036540d0071203a00800c0da00a150040007042e1900c41c2600607240a002a1400d1503221505c88950609661201c00158101c03441d0680c0018166409480c200791b1403080d052640d0b9504d2092400c6594103000152010b81c1d51070700c0c1c07515008180140703030b0007d003c00420351030340c0d651515020070040b118540001050008140c8005e821a064412580c4c40c0c2c034000e007000104e40780c1507107801c1405039400300c0071580303654002040c8520f100d0f04000501c16118a580400c2a0b240c2959201c210042c08801e41c00c1201980b000103400000070b80442d520303810013528500450034603100440c0d60350428001c00b031250b0708019010402c00d10640d0364858a403040401002940c480f075204031064228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 998848507 1250 998847257 998847259
    0xe09030f07120309050d1e0503060f060306240702101d190f030506040203190302120d0e030703030b120a150e0a0215190f050304140c030d030b09060a080a060902 71
    0x104d4040b034010503030034009000c2d440c04c80d8550102031701c0c410311004240350003010311405201c828001d000d07598a0305030321480310100c01d40e841a60b035221003002440221507541200001340141c04c640b0038011480015082e81e80c400d46d400c000090780c920090f1800c0d0b440411228410000e0020148140b4209a030055100003842103400d00c0c80d152907900705100025002518181c0c4a0020722046040801c422213020702845100c5109038102d40e0001d403102c58150504800000c041803040d00e00b115980800c810301c0030541101c2c0d9880307136450040c02070400703030f0140c43c0714120001780c03180a2040441c04c03d41d1075621901c209010110319407203000070b2107000c100ea80c551055000100050f00c072000f50400c0315000051a039105d018500c02d4011709960310341f04c00b007040110303141246002d412100340e07500280e1040461041c4403007010168034020020a90359818496800b02c2e04c1c00e00d82551141d54400000d0382e4580080d958541440b03000f081b54411056180d001d01000130108810707a005c912100d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 998849757 1250 998848507 998848511
    0x4061b0306081c03202502090106030c0302040f1404050108061911090402040b130504020732160e010f08030a1407060f1b0206040209130f0503040b040e09030f071203 73
    0x840558036002d18040505c0b0f030078040c40014400a1000c0c4d5100401035010308035a541c00210250b800b041c9850f00605c2280c05141c2c444407071606150080d015180134002200c007840c042c075600c81c07621001c01c10044407a4003503440d1030000b060855000c528035120b010f080803245412864042d0b0304c0010040031034030800c40030341885030540301d50303503030000b00010030440e0185520348002019a00f0546007950010384242c1c4100211400a007082c50070a954000c410200382c10181c18070600c10100a0160300d142c440e0040c0c81c000105d2030766405101094410080c1080100da88a80001003410094092010f0a03403062200a071800d100d2299141c9066440d4605420074040750340360740c00e80310039003103061940c2e49481c1c0d5003000c9000c06a13945501d04d520b02c001d041c0fa0420350041200310b440a00a11158031501c003100c4140728680c8080210035078801c04032950386030754840310a030b16009402102c4240d058103011901c6020000140d420940404000c640307003041503035070703210207d108400c8401415 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 998851007 1250 998849757 998849771
    0x8040c06052808010302010f0f0c0204020309150901020a0905030c1f05040e04050c0108071b0b0a0605090a0209190807090f0612060b0918030711030f030304061b0306081c03 76
    0x18a022085080480b0300780c980c14a25415032002400c0c140e0021050010805a40040c4400c29408000c802c290703034040e2801039032501c07116600e60404862090398008503811400388043c40c8015030082c5000c9100ba0b42e0031070940c2e280e0041584600b4640480765000c003076040e40444c417024900c0f40114150040c181513103030039914920011219400c890655107070b045640d110640b560080b00d01640309032185404801c81e401601c82c0c901440b103203d8090007280d10000042c4601e5466400131000e440001c000c031045240129400c00a50301c2003c02c0b6000300300e500d140d941400060084103082c1d0720980b0140009506202d6540300401c4540341d5100000d491744400100d02d148007000921b00c40c0910400300b203030b50607a002d03c0342115004e081c1c2d000c07903481d01d030707118882c5100441640c1c001ca901c1003402e1020f24103540042d190501ca421240c00d14000042032104204c035030340c00804550805485070b44000046030050701191018402d5034442c1e0065050008814070301c0390414802c0d800d9040c005084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 998852257 1250 998851007 998851057
    0x13021809060307030f0804032003031602030f07030c05040c050307020a08031f09050a05090c03070501030504050705180915130f020114030a0b0102060156040303080708040c0605 78
    0x10603045c02c0954001c1c00005090007481064005815500005010386841045003800f180e0b5a2040400c0e000400c3c06010040003155000d1002c1200062844102d80013641c4a00706513980e039903c1d100c0e040c070035890710f802820000c0c007540a480c8580f000c0d4000c4c10b5680b990782c1300c1e64680d5000800c61740c52454406007008400902008c0940034100d44100041c25290120403a011a48040c240000740d034002081d6180b20303136000990b281543c10038600070540d521a4505286840c441e43c00c0982c0c0081c52060516250014500c4107202e2005142202c031f07540204291241c0c4810300b50382d0f0540400003601d510b008103100c5c8403040d0885206141040c88808607204620054006803920000b030317038855480c4041503a04104082c05403c1c0d007403c1038408840046030701703d8201d4810034a901a02c60001d1030387c08022103164030320311442840410440744000c0114055603840360000320085150003020071580380c401d68580d4450380d808000305001e241002000d484c0c5411044c01148810065900702181c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 998853507 1250 998852257 998852273
    0x1141e0303030112480b0d021e0a050c16030b0c0c0f0633030d0e01020328120e060118110d060e0112032a120206061302180906030703 59
    0xc840d441140f078000030112400c0c1d803c58510040e16403174028000030700610201500303404450b080724049800503580d1040407404450340e4a064141c1c035202001040c0c91405581010080c4408940355042d41c400c10701d140a40001c4032294003005d4215010309001902c030000703910041a00140040899030f02c00803803510355182a1301150114041000c0182c2d0400701003060391041990ba0021008910000706100131a5903092a20848000c028040211540703a0340240b045441200d0300e4850001c06414a0f010850071940d108000070004580080c604040f000da8460081c0801c1e4100107414546d10f4030162489807100303021400100e581e035102d035180840b416801032080161780340713000c5101450610369003401a01640040b018034502402d4100082d40001d00c610003072118111030501c4103070034510002c804c040e0b0100034144028110312100807500011054404e407002c8400004840620070034106078010000c0e016086c095124a0010900e40311690a03803000c0d0180850f40c50a1b942c2c1c80f0341c44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 998854757 1250 998853507 998853563
    0xc0f03030b210105060409080d050402010c021807080601050304081b010b0604030c08071703030103030305190911030607030618091511040e060405010608010b0d090b01141e0303030112 81
    0x110a24800c20109114280100c6070300540c00c0b1001c107d80240d940750000719104071000c0c085220b5440303000134116230040e582840801e401030414140c409540315602517041c0f05640250214400c0300015500d90b1180c41168484d552014486040c0071240228240001003496132101075529030b030400050b900d48030083c00086000e0061101c0d010b1031312000500340002c0ba0064815400303c1618070001610000c112411aa4549000508c40d51002c0d0b402c01880d2411613400c41c0d00341416003140501c880035036000e44045084051754502e895280041e4100d89503849600c60400f03003800910b0190010760f11481056000c1e00c030107550301603856545011940d00d00c40b40c040c15000490f06000b551241d9401507401002030b0307020401941804005441100c05100c1c0744c40702100052011200703441030700440c000da6407000c008100c950311215040182c04690005600854513901e0541c0c45079850b01d03401d0301e02c58028002d94079503420050480340d4041170b9a020745a01510304070040b503040c03243c00300403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 998856007 1250 998854757 998854789
    0xf1a041d03210906040c0b070503040503010207060c030b190b09060c0d26040f080304140607091a0f0409022b020706061502070b0904150f03020a080d0c0f03030b 71
    0x90380c2c910041c52074503003644000d01441030a90105007044000b03165061508261807480f0901915010b40340380151851003240c010b1905075001058450400034260031240301044682c03000c0c00031f098050180b2a198139540502040ca440c0c3d42e07001c01030325660074000c01e5001d6014002d20318085255140301d180039880100100054020400c4003c2700c04031410140181c020540d48070000e007040c0e2100c44214a50000180101c080040482c080003990200504402050000d483d29490007102c06401c0d0f04542c4a840050301c5110750754450341600d141292280740c0711154841c201821306a428000350001e00d46101400e03441400120440c0c0115211500c1c0100c0e841c1c090b984200d00c0c941401990711a0303006003d210040b100004200c0e801181e00d1095405c190702042e11001101e0005002e01203a601d0705000010207100460a20000e560f100152402502e601d2001555040303804d0761070088010082c002001010044001116400c4c0042c400380a860040350302408100080c601194122030b070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 998857257 1250 998856007 998856037
    0x150312040b04080f0712031d090f040b0a0b0d06111204050d020c0a060e040504080405060a0c120503070c030e2b12020c01020a020103090215030f07030f1a041d03 71
    0x104000f44080016655125001000e019030303519281c0989021a1726460007030920069940d60000300c0200f040058101000400403211410041800c0354902030684080d6014103600c0b001910081e41405980455031014000f04a8001203488143c010484558144404441000510980000d41c0252401140200050301c1a6215004041e2903c101000e6442c00782c00c0b40f003030030031000341c10625900740b0300016580411a0f03650361418100380e11a9402090340902d02094100f030540c4c1c8400ca074144580315000b40d2480365004101603815000c105d0b03d100004141e40e0502d00000c3c404e0b4052400c1c00c50290107141440807013005041030f40148a9103410684160310004288600d031686240015241e0010b040c0f003046d0900002e40f101d86010000e03050640303a481c1c0c1400c540b10641010b0791030040b012003a0316414121407191480c1001e8030082c000a0800c1240305042d01c081c030504811501c541030350715000201c14240001741c01c4040141700049200d6080000c2e100082c4000d0004e15801142 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 998858507 1250 998857257 998857259
    0x142106130914010506030606311b09050a0f030215070c03030e030d0810060c1502040b040e0a02040806160512070519020c0a14190603051518150312040b04 68
    0x1155007101c4009040b548607504c00011302c82c042c0c84142701100544130341c01c0d40590b1013022207480146102150720048031985010309021240600d07d4031207001001c55920340c1012aa50810414958a68041d84c200302d05640d50400051500e07100c02d0000a03c08020517080151546840c1c031030040991066000c00e46c918080c8019141c14003611a01c0740540c01c103038501e41024070b0400001c078030320f00440781802400c0c0100800d20846203044014404c01900a40d5101e448442c11045901305120314030910768800041500c100050094809035000500204855921507046107014044400300a0030700808001000a1096031a003081c07088540b80c50b400c0e07803031122221984944909202d0768045400c0610380071602d640d824100e0b0300310b580300c0907062142402c0c1c0c1e000030603014400703180312410889041c001a1054054100510480d0007810100400342c0b40418019800c5016004585520031100026560304101002403403c020240445440c842c000e0b41c0456258041d400c154031503400814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 998859757 1250 998858507 998858543
    0x100f0507081e0402190308030c0408010e0a0b0f0421020a021f08040f030201021c0f0605100c020114091e120c031207060213151421061309 61
    0x51038120948081154450740d84400d0329940320400f0307000038400c1d000c1d60909040700c3c003540142030145402c045807581e0303820094101007641c2c0c0503103c0c224040d400c01001c0ba030208400721300c7c04001c5801c1b00c0003004d66030300d81d8407100030035030000d004455240c064407060380010041071164a40907200c7d001480b040030540104901460640c142070a9086461910310820354046400741d00544d00500301800030b442440c0c00ea001e4060081030010080d500101c82031540090b8100f140110180d0700304004082c0c46100740171010f26034004410114005002c3da500552142a02c400f0660046c44258103160002c4001040b408060303d10140c003074400c20070303402c2030b1810440c204515400761008100700580c500c00309407596007005080c0d40041c000724400c010311100f13030122030340c507001c0c910403003851341e00c9550003010014500110000034243c020b080305124840300445030008240110642420820031401c00034040c000c204c2c58022001510400395002c5c2e038010340720100c9c440c010800010103022 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 998861007 1250 998859757 998859767
    0x10203060a0b0c031e070602030f01061403040803010e0702011116031d0901030f03030204120803070f020105012d0803031003050d080402011d030a05070f090c0c05120c100f0507 78
    0x1400c142c50324a010000b9800941d0000304884050041c9814075044442003030360150345003d0003e02403d5035000104211b080c0e600030942c02c0c165280d603190070b113850b052a050000f0350700040710b004140301e0042005203c0c60000c0780184da80004580b0010031000c0300c2440c40140d641001c00507081a00c0c290924404042d0481c06183c02c0c80c010840034888000000001a04290184009804050404890410b2511035011100a03101c20740c103102c01d40b105890100d0030350380210340b080b000440385054204050b1060060038101c1c1c0590300e114034950010180c0c07040e074040f541401c0c01c0c40c404041000401101c1400658440c40003000c501c4105861418403904066600d00d100d010009241b08000050380c02c0341c0e0820004c50901c2003000e40701a508080f0340342c15003154016019201d4600001801000d801041c400c0d0b80c0e103000180602c990206040e1013078a10740d01c1c003c000e80c100c05400c1b1039420b911005000e20702600f6040b68081481180110200c40030740c900d510155860b9000c1001680e040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 998862257 1250 998861007 998861009
    0x3e0f010203070e0d0b04020603060d050303070c06380103021c0b0f181b16110f030f0a060e16080307423b0a030207140a090e010203060a 60
    0x2900c49802d0f942c01340d500c1d01425440180028495540440441d2a039100d4a8081403a0340e440302c01ca139a80d08142c90080c05080a242d022120b050810741861410f4150f0a042005018828000d840341b21209c944034a5807548004014101130742400060b40c03000e51a504804516803c520004001118406002110907050002030180340c00800000a1841565400c3e0748030780030220b203036000543e040603164113100398603000c0c50b1340c05145c66507014001002c0c000c0c0d10700041110200c400308869001e2644400c03080006074055040841c04c0300128040fa002400c421340c200c1c00b522901c0c00582c40351203100350150050301c4d8590022074100200110b030f000d00019242c0410900c02c41c00e2800d9443d551079002800705162200d103140c610b501686150b040741e00b07852055001c076081c10692213036010350b20180c081d0600052441c0c05103500da844c0041041c0e101d00d03802d5805003150900384042e2600b0303440543d0036036800405210300000c40e41c0007840f45955030f10000c00003580ea4101882000840541 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 998863507 1250 998862257 998862259
    0x41409090129101e110c090718150c170d0c170901141515030705120a020c0a0f03020c180702013803011e090b073e0f010203070e 57
    0x4a14039001e4070010b2107645401d40b031013071501d0610040c215454908004000001d141c00447c003101b80300a00c0d811007515004c00000062201000d9941d6421002c1c1000c00c0300c480c1c02140c050030034000801d03088450400c0a920b080c4015141c9080c5600d2501119021200c0034009080a1501c0300b41105a456494000ca10039000340083e00b480040d01580001c041c0034252010002050042540c64040c11101510010207201303451707191415010f0007603404402c41c1254200b21400141d00e8808070f00c240c036840c0c00284010550702e0119544c1041890602d0010341c19480b44020020f0540c2c0c030314154102e01d610745600f604803801c02c00f802a0a40f80700071407400f02d501003240300c03400b00c03070007104c03400c0ca500304014018041c0301c124000700f030042210f580013400502e001e10403038201a107103400030076680d4801e8030402401d580f8a10100c071607034280260005070103151081b01ca82da13042c0710640c80380120b84099090310900d0329091686082132002e2041b400da5004070400604a4006500d80b94841d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 998864757 1250 998863507 998863517
    0x4120507081014011502150106020f1203010b03070804020d080a0513080f0607051806300705180109090504050f010606090f090507090302060418060b04140909012910 73
    0x1481070f0701060120050160300c5401442024002981d0700c200103170171800c06292030b604a00d50712803030002c2d22444041c0101c0083d115001081c002d20840c0003c40c1d0494a81c810094103540f98150100c880010290043c3da00a5194000d1004100b6440090801d00b01d1074942c10341d6034100ea94000c82551042d4402c100700d40108010310074403240400c6d280e9010803903140480ea80e03179594215218007101040c0d015040000410124807009a84007075800051031486880b01c4001c3c071416840040008907942e03800914144120104001030095051480e001414100605a10340b1020310440c2d400b00c03416030341030340138041c90b0354000000c2c0700e980c01502461412640307550034801c950022641c2c0f4400c8039291581c40740000d81952007020004051607008015554403966036075140c210440c1030107500751281c038144002846120f00302c01c503404c5580c1c580b0001103c01d440310400400900c000c00c41107146d52600c48e048111071107500c601006441c103042e02d41c441403644040c420078075108920035017402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 998866007 1250 998864757 998864771
    0x408100f110403020609040e010e07060207050a150c0f2108060a0b1611040b060c07030c060903030f0302071a011211040911090408041a0c0f1204150302041205070810 73
    0x40c417000101c9008400c00c2d503000c641c1117050300a050040c507801405503101d004031440803e40340d9000c51441b08813182168201383e15501c412020b5090010100428041401c07c401c0d080018a14201942514081d02c41a0f0700c042c410780643d03400c8031000340c2540000e20740070200052032a200c00390300040e202030250070b42480d901d012401cac10305032401e1000c0c0c43c4001d0f0a01402441d942c0390001c02c161003000d0815034035004011a241d035660440d000c01c48003c0d1901802240711403050f040d55080340d0301540c0301d0075601d4402d0001d800030340c05840160350000980c944402044080c00b815030081028406d820181061400c0c460404007420000d1072203582800802e0340812840c0d40c0d40108200d0454010070384e41c440d440c0c00d44840c0701d41c0d44815445c50b0702515400039900480040c00c01c41b032100d015101440b090600d0355489584120007280e2002e1705101c1403042c0f10814002d96592009810011710f081d845410521011140410407162030303004a1090158003814082e284c4c9000d120a4140712407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 998867257 1250 998866007 998866009
    0x5030406210b012115140a080607020c060f0d150603110909061215041110020309150a0e030a0f02010f05040b0f03280506091806010b0d020408100f11040302 69
    0x30203940c855402c2548081e00c461400f18280d030005c0d04034041c207115445c0040da1a0700b103205518241010074485d201104001550140100301244a0780c82c1d50301400c0da44003000c0c00c000e2150000ca1182420b01414001500750910511808005002d01c81620300c03034902c1d0200007000d135071802c41c1810040b00c0a0050745030580f9a00610707074121500702d480650411840013650314061a000480c42128000010311052250080c2c0a20440400361410300c2e2404080500381d940e803103040180da8010b403490188890080d221806405040c5461502400d8409460006458000600815038500e01400c103008110b68000d0803011a440341820440d08062030140e111000303006601104440101c000000b83c4204136502110702080b0507114540011141100118010070085a00600440d01d00000c00c02c80d8021845044100191000407c2281c0c2048842130494201400152086409000109010900740715144000d82511000215903490980d04410341740302400003c1a000b0410060001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 998868507 1250 998867257 998867267
    0x129030402040b010212030103110f0418030e0a080d080a150f09050a090611130b0f220512030c0606011701050f0d05011a13060503150702030705030406210b01 70
    0x800381d0100c400080c5040c1600050342010603005282d5040d0034000000320030480340307100c07101914005603140d005d0f00178104140812141a02d040350b24174443d50800100180c843d590714a040c0401034505804035a0352641545007586c03000285010800940401100a07118800c0b07501c440d21801d640b09109142003400da28507a207074002d2100c0f0350340b50000a41d140c03546800c81782ea0280d20600400440d05104a286959000b180c400c60700340032400d10005298200d0760a075120340320301039603107032500422030a6062143c03079010708903a00c4205c425000415684104c01115103022410185903200e820070b0b001811f001d00100550306000b0ba0002065120080103036550650f5015103001842d100c280d1300059100d81c008500034255801d000000704049000b00c0501d10001084d1890b03d00000040001c0c0b00b5101d09001d941c0e010b40c802c4d080030f00c030507007203030b084581103002c0d801507a103408019143d960445d80a908110040741900040b07445040c0c214001040510001d07004101680350040001c0c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 998869757 1250 998868507 998868511
    0x6030105060342011d0a0e0a150303050a0e011d040209130203070302030915090a030311070f031101060f030b1314070816060f090506180d0f1a04121d04090308012903 73
    0x801c0000390300c0018601c072029400644c120b869441c3c27244d0341d2a528a0000c08640c40940b00100044903082610400d50207030382a1490418000c141728003100c04103060000940000026661080d000c56040ca81c600c80e0784000e41c05031410359000740e80da00e0000300203883d0181c603102c5140496031900402522060104031450002d40c1341c81c0201e480030b004150100320703010303002003d00800c80344407411081503000340219202d22404002406600d9076640c00c01565462848003802103000800060200088860300c1c1590714824000307600418002c1c0f41040c50008540c000c0d0f2940e5102000e0744944a4107008440020003061070140001900c09200504018161286500400f404181008918807616450400a4000e070200079100319038206481140a03240082e86d181d0072034080c0c80354038050401b06a104e980c00c0390301c130000000404c1d800c0719502583c407075845003400c04070060f00d45075a43c4d0203040303520703406940c6206035541050349100520751b00441108154241400049c200c0180074207807a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 998871007 1250 998869757 998869769
    0x6031115030925150903030305090c061603031107111309020618060c1203100501020a03091a040504020c1b040501120b0c070c0605041406030105060342011d0a 70
    0x28810b000f00390b00030070715426183c02501c0202d40c078002c1a400e15070300c42c000c02c0c1100d000360740600c2540c840896450716990075002c0e017034100c501001000c1800e012045880c054500c2480c00040601032440204001e402c8403070211804d4480c080b11202924000302801c1099009040c1002480e115600056852049215042d01e00c100000740c0c00c4199217160580390802c6441069400e058010204c500d050742c400c0b50321102001c40c412020910707520001e181c414540c0e00da1617071007a050502c0010b14105003400c072120b4615404001c08901c0362030324000b912501c0000801400a68000c2d03402240c100d45600c0198006d0b440c20004221600d4420030481c41140c00400581840e15200024580c0703100d5150701400c004c004200026107142c5c828000e1044801000d40701500a24500800207144400c0c0300e141e42c0301c1428804118400c80c10302e02c00443e0f03100503401601c82545450b203c0300c0c1404840064901e0b4894911049495130490b0070b00c0e4000340e010004080d00f104080001750070543c140985 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 998872257 1250 998871007 998871043
    0x10e011a120705061303031808030715060305031216080411060703020f0a050609100509070e090114010608060a0e040804120201021608161403062404060311150309 72
    0x74008002d000180207020040c00c4103a440c0c041d54a40d61060a00c1e110032000542c42225a11b011066074411030259081034024515020141c0c4496600d41403100c00300768001c1d07440303c0020000d0300400003400c200064905000300b52030500911461000918404810301200c2400c100c00520400d120305e00c3e40d42e084680ba81ca58810b410103d00e44074040003000172602c14003111009220b80043c850b4441d0f20800116526400340303018000a44d941034a01d0041d43d44150000d2066a9080c0d070700690041d01c4900010b449483c0090320505507000381e102e58049103070752051000324145030f005140580b0241c0ca44000c20b042c02c2d910642039200d58815070084443c01040d1104680c4207201154090410742c40641401c2d403203220a42c1c440d0354030541c9030308080c403040b000155500c0c1c900b80100d0500c0c00902600443d0790b403401108a43c1d03840c55001103203282480b0704210990f201c5c07142c480510300401e645914101302e80c080c064511528840090040f80610802c04114030014581c6540f1000d01c402d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 998873507 1250 998872257 998872279
    0x303030f33030c0e010e010602120304032a0c060806010f140a03061802030f0601081324020a091406070b04060e0a0f06020703030501170a0602130e010807030302010e011a 75
    0x5929010407090b0001030414244420014440032240c0d00e04e41a68060a2030445517641e81c1c0c004da0341c40480140c0c4070002c1c5410300010f008640070b424026807100e50020f1002c02c400c411680004036240710101207070f055880c40e10501481d03510074005a0310500038204031608691440c00580400a08424a00c4903000040c0c401d0780d00f8840d8101c4d85c000e1031543c405890510f0005450000303508211550180003907404001782081d0b200e560902d010314200d00b14001e002e2441e8403000c0c0c0c041d500ba0010000908108000806035580344003d00d00b104481da90156840d040c0300600001c1440140042e01c9143c01703005070030115413450400d6030802d5110342e001540c407040c1040c050030801450b1000e03000203048058a01403000303507002450f0340c0d442981c04100c141c1c0c03a175405008a00c100c4403503c840d540522060400140c0e66801089446901c000b02020b4995512200b680e94809800030740e40c9421007602001010307024024600000740b10f0b4001d00c860041100625015403042000710710416030448 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 998874757 1250 998873507 998873591
    0x21f11011b022d070f180b0a0b030702011415150307350f1f0803030105010e0d020405070215070203030c0901120216060501051011060a1d06100303030f 67
    0xf00c03201ca24250207065840c81980c8a6519818003442d20400b01d4003205814a8500c505080c0710350006004001c00c05101c203800c0c945010755a4000800170b00940d0b507202e0403038481c2801202164805e03004400e9101303428041c14203204c9d0b400100d440c2d854101005000b030110298214a8042a1500e107a41c100140e915031032000c60400240c000700100003d0103024400c0320000f0300804c80c45807a841440d207440c00c12180f0341e045d42d05603074840c611007a0018401803045600c0703005104101078006000192a400f1074000900b1200d045d161030f00541d01802e000b106104240e24100c0c0d001c04940095070031440d0001c0100d0301f62007036079403250402084403e018181c0c41c1076815550789415008507c81c040c0f11328980076008220030300a051181e5112803250440b24403401644203112200000f0704241e031a900c48000141280c800c00081d4a25a03000c11207891a0400500d48282c2442001802071481c504000d030417100c06410083c40d0600b41051440614940003080c3d0072410140840c00d42c08410030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 998876007 1250 998874757 998874823
    0x9120f02041e0e07060e030309090105150409021809060307060f080a1407090302130c09030f020a030512030423060412031e0605030105220807021f11011b02 69
    0x80c1540c002d0524104080826940024010b02036444640f600391001d101e15003050355901a00f41c40c541e0088074000184030f1400c09076813410092206603a840d041c240c4900400041e6084242c8610040114141d4800d4600d05030107800d406c480c05601071b284403401c0c01c0e0b00400704400741d50000180516880420070340510fa078003030010600c0c030000003641402c00c404010502d011a100c1070340700302c8060612054400003441203240c440940c2e15170290651440c2c0c0e84030f42c9003803000820ba910201030031000001c220b050004101001000900d01d03075900e4186003200a801040c0c14003010441100c0c004a110080001e030381d5002900290740e0f54848000c000210064503174061000003143c1200948503580340c95402100c00c0c0e4404400902560b41c0f66003030149040f00c412041c00c103004071181c2c2280400c4201c40200002e42c000b400c44035403202d90201190050108401140000d45124802d541242082c414032240501c3c402038105100c4a03018001e54900040b066490030342c69690004800c43d40c08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 998877257 1250 998876007 998876051
    0x130203030909040515010506130608060a0803130f0905160819150911030c07080c0f0a0c090b01020d120b0f031e1b011706130e01020a09120f0204 64
    0xa100110034689450401c3e03d030210b10034a0800c24038805c0011036549011400e6440040d088407614002c2c502e003600c1199181d20140c800c9400070032859011400308030503c0206041410026244a2585442400b2800b50322641c01168441d2620f030078002d00c295075002070009410249444000341d16048655841c0640d55811120403c0c981601d00c3c007001c0c0100e400304100c54144900700f01c26041c1d460160301902c803c6a0044041a0401000700020074ac82c0142030740842d000700701c80000281090f0340745030621030070050f14545003800e0104000c0c841ca02580c1d0f04080284060580b0a6014001034104400d0405000c12107480d0034500c60369031074a0404501c0d0080081c02c4400d4000054800c480700020700e5503200e014051040c82e5615211000c9201012000603911041c11303960541c203001110702c000e050b02d548005801c000c1000c0d403007540584c003240700910000607903581004d0340150086000d64010048024403281c40e0b00801c0d140c0ca2048070007901030b5004030310900418036218604101c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 998878507 1250 998877257 998877259
    0x6041214010e0c010f020724050f0d020403110f13020c10050c0703080708070e0108041104051905010501031a0d05070302060a05030702150402032d1207050d171302030309 75
    0x1910102080401d000598401c3c40703c000c0c4c80702d0591200c6550202d84034400b5005501e8007180312858041c142a0f4000080f817011290b01d0a81e082240c9246000c8081c4c0c80140f81c18560343d00414180309201c0b40340120500e980040324180754000e0002c0c0442c0300140124010020780c0d03404182312250082c00d120b102c40d5800c00ca4070400507440c015021406c150000c03001a40080d2000001641c22801203140300d0107a951a111800b074082d1000045513210720041c0101d41c1e00700d03618980741c900c0c0c070317940142c90080b00c5084001c0c0c46c42544ed42aa0116441644214101414240c0c4002c000703050b40d8076070300501c4003038600b51003070aa1400e0807480d0000b6984025007140f40010841c121680c0100618050903890f42900c0601510910508100000b51406541500a0b034007644000b0030004210301d4001e420b521044d0302c04410400a0f0078032072941c466a688070070002e02402000414030040d84410154202403028012750031201403803800050225420f0907141c000b40c0c0035590200300f901c100000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 998879757 1250 998878507 998878511
    0x12010605040e060f010e010608040b040f0c0303210612080c0c09010e010f1203050d0c110f010905060108010510150311070606030203060a0504120c02060f071101021b0604121401 78
    0x20400034210f0b6141d41c100e441e6240b81808600200710b80d46480d00b802c0c106c50b85c9035210031071a203950b1a4580100800740c8100d03266840c18403882d00003850803aa1800440c000d40703071854200d4010003912040b0704034031540e00300e2034a0500140442c02080c0303540c02d11550460003150b292210340c16618a4009120701095001d030042000140b03056803095241c0c169961201340c84900355403450a4044c041c1c101074010041117080c064a541c00c00207a000c12505180e910301080240e0f540303c440c0741400f04012641c141c036512224030106008080010500408201d002000545404403024502d038440740600d500182c1e501c80c045041c5403082c2c2101e44500003414040744c1c1c4001526140c0024200d07440100c0c040e0041e03000042c061106480351320311554010f00d110041c403170b1741281168043e401101c201c1c1c2c040814080001c3d0000c02c940038046a0748102c50b02d01946e40c0441c0003a15046200c2200c409032110380c502c040c1c140c0c4074401943c0449802c1210380d02441c0007447c10000d10b801508050580758 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 998881007 1250 998879757 998879771
    0x1d030102041a0910050f0a12181104150803030a0c02250630020306040f0203040c09060503070f06050d0e010f05061e090103080705010e030c0a150501060e1201060504 73
    0x6100000414403100103c404c0c4051002000041e1114001c1c0301019010702d07424410a69030600030142101c09480440000603101d030b40c03034542082403030440c03c141c070408950280100300e41400c2c49519245401c0c20300d24a0083d241141140c0e8070b00c00185914125030700c1e800d001c41518002c12041008010107041801202c580740c4c02102201e00c548980d078006070082030000428a0f40709921141c6000c404035800054000e81c40300c401a6001030000c503003040e40c408071500150301901c0518002c40c0705054806c2d48919103045142950f0240e080244203030044d8404220100000d440300044410710f0030160386030050843e031f44c002410503552108042d42421105100c59403668881171003402c0c11180e08000b0b45d42448400c812000d0030081507080b12042c401400400d9400c406071445520900002c10381c0b0010380105400c2d9080f00c031310300c40b241c2d00c02c40c07401c1c040049000b449106000c4c3c0300010801d561404400030700403100d4545482c020b00c0003000c1c4051101003034000402074070024200348003407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 998882257 1250 998881007 998881049
    0x12070203031e0609070c110a1d070203030702030d0f0b060f1c0c09061404031e0302010e03120403181a0d0501150203071209030c06080708090d1d03010204 68
    0x3036030086410240c840c1c000d00d41c100300726001ca100240070f0b200180c0510415600c803c015100213203243c03010ba680c041d10303d040c45503035540e0f8145403000d0203092840b40b06840f0500c1c01c00c1c0c07640710003501000940d00b09200300001b16500105807a4580302c03454011455025855058009020804145e90130600015603c89542c044400030841c044a034800c01000704c1c0c0b1107001d18200c50140c990800010b58030392082266511440b40001d40103c1845414a0180c0d250356901d800ca241c5204804001321521004050640a1048110403600040590320703025698841c0401c1040081c8010107100002408849400361111158060300005001849480b42070710044000e8111300310120149050400218803030707030000e0700c2c080070b6001500210300700085030343e41030038041c613140d81d240030005081c5000010941480300d4000621054031406410304000d0802000a0380c000e2843c55164401180c07541d03810751100305998608801002000c000151000103406803007140c0c000c10f20003d04041c0da20314 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 998883507 1250 998882257 998882263
    0xf1b0503030c1b010b0a060c03050d0c09030521030423010c05042303030a031107080406090905011d06150f0304050c03160305190303061205061918021005120702 71
    0x1604050703480c0f0485012050580c0382a0b4004824440d00b00140c64010820300780590905242648281400307402c1000081d00b180449028084410001d4010007080007800424420001103a1802c1505030100004660800c001e00c000f0340003c141303052031108005041120301c2d54100090a180091110f040940c0000304641c0081c05815103c1d0407034610807a40703030003200c1203101e04e035030240c080c508180382180280d0050900003800a003282d0100813031400074220400a10140000e61215002d03142080c0b4003004841050b00900034042941d078890700100e0700c64940d2a8440b20403207500040c450b400481503140e024003140749883d0140842403000304840800d41c05412030007602151440300405a1108070311700640700107080c40d0040e0b515403810072041010700b50624040c1c1000305030190754072900c0e40014003140d0251402e4100c0010b0003e05112009030f00d440b00500d90040c40740c40030001c070384600c400012100074814041c010340c5450301030068050710b640c1d50304522020540c0c47d01c400040c0d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 998884757 1250 998883507 998883517
    0x6070f140c031b101e0504020f0312070501050f220309091811150d1503150f0515011b1406011716121202011b0f0207080606010f1b0503030c 62
    0x188601640040b02c4c1d462a0911440c00d109810062030300d8003915002c285001400003403c260303080130003914a50f8007500c04101802460130b030016010359452140c1403450850f85c024001c185180400c3c4248122103680c2c1801c000410b44030325040303025022529055509078295030210820b2801d000288400788448000300e00341501807000c060355981c203a07042000045018020040c003c8090001007000501a40311410014240c10f000000c0f54898849508128070003200c100182d454050700d19540c1080d00955130801075240c00d10b44500101c000280c0f1170280c620220716580081201e20090203600c000c004400c15690342920000d50319042e000b04140c40d8059111000d12035100400303d480c0f41039003841e04981c00c00b800b4812580b01d50340c0d11100381c0e000e0414881150b482d40d01f00d149610881034660b030703100da19448031400248100c1002e810050035500000c82a0000020000580d0b00424140598401c0e0f190a90f03604140e01801c030550078503450080c0c918400030003000307003030f54030000144 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 998886007 1250 998884757 998884807
    0x5100507020316030f0f08091905041a06031906030c0821030606030f060103090c140a06080415090305270f03030c0a140f010e031b06070f140c03 64
    0x15074003c0c2e103008500d001d10941c0c80b00404110030748441d140428098480190094407840c00c0311724100d00d5000240080f50201111984070504c44401c1003a17240034070446000410210540e00d01c0054400010000d010060219410450b40302603241c1c400210350001c005150b0080b500010261a41c0b00130366100062608002e503610310002c23020750900c081e0162445040e0081c8031900d951759460742021801800741446042c5a141e0001d0700000741140d070b690001c2c003030054591015264003020442ca054859000100340420b950900c4041948018584404803603030b400464500c0c52072a046469200c5d01400340300e2101c1304d00710460b510b41418422411084112220051001050101a16441000d52070741e102d80c041c6488800240c40308440160034981c00041d01c0c142644100d10710709640c00d103586204141c100140078000c125400c1c04420074030400400400451801e0b2001910324003040000405101400d90340c0c1c08074001510882d40c1c5c1c41d80035400d907a1224010001040c450369224015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 998887257 1250 998886007 998886013
    0xb03010504020d1218120c050306090705040b040b090f040203010f09032307080c1c090e0a0b012001050f07050a02070b070c0f0605131a18030109081909060e0d06020c07051005070203 80
    0x648d0f4075002400030302074102c200242c540c1c40e24050070003009100c82d4200b150410b40310140d6041c55030ba450305c414404d04580956015034074144c4105401c48010300c001640d5549032645281c00301e9401510800705040292408500200d50310340035185015110f4020103d007400035940d11328071404a003100400d0241c111852041a618005a8180902d406a0fa007540e04200000f4001032a03500604240d14040c1080b030700e500e1507480000301516240c01d440d1041d079100c41c01c1c4040003100c0740142b80d0041d0a442c00c641070201201009460710100c1c840d4184c000000300312242440030104050004160851080aa03d40e03151f80250090b042024103082e00c1c503001e20000b9020104045941426103241c84c414603020150820b08a0031258043e0281c166503902c402d100000d019074000c003801da001402500540c2004c140042c0010202d4100204014406201d14403039141e00d4608540207038441005030f2107041035400380d031814070306900c09944030541d5603210405d182c02400903c4000d000b43e0503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 998888507 1250 998887257 998887259
    0xf020715050906070f1b0206040801060f051804150e060a05040209060d0b0c0d0e070617010b1614010e07060906171009020702010203070b01180b03010504020d1218120c 74
    0x519600c8070400c40d00380000c540c1001070441c5d018480c43c0707150f985c101101c60201039420a50081182600319070413461880c0e42d6a48240140c18250304c0040c0106011141c90344c407083c18034004070b0440d6014200030140c4d0452100454074103907503003240941504000848000f4a030503003c0e034000d0b000a4900361700640040d800f0a40038203001d4106000990010074040d443c0d141e50301e0050181d4841c20800b08610760780c05ca04514180184100402840e4a5031500b43d003e00301e00c1c0e1b034404c408069010016501301085034640c090341d0ba081105030650020030301c41c003444501f40c80e14090002c8048004c454041d40601080140d0004c14400030303910184d54142c100f00c9140c07150001c0c0c9605450003260361014440401888000e9002017070300910601c1680d0a1007130550307481c40d544001ba040071950328181819490303034006c144210340044900300d0091002e41025004203003401c01440d0090301e02c2048400400c640f9000e00c8505c1c401d1209501000181c40d5124800c2c0700c091002a0100c03407403450514 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 998889757 1250 998888507 998888521
    0x170912010506010807081302031e01111603030207060e010f05220b1f0b0f030619030f111507030e12060403091509090e0c030f210d0f02071505 63
    0x1141030b11441041e11000302a0720781031402e54035414014030000c0c030414010505001600c0600130902c8084070a581c1d00e2000d101c242c03100c0d09550100c05d0070200c86030188400310040d00365142d0f0184050705403c0c01a030326085800c00901030402040c1c0144150300389402080d801c40726a118920981c00808200d0300c460b00700b04009819aa08440502101040c0000c68071101d1340b14010701001c00b041003031650040c1d4900d042c605c1078100c141485030401002c010000c1d41c0c107201d2050348401c2c02804880e84403500359550804503049808014100c150640d440007000c2c0c0f034820502c04d944002c590055200c068619004100311101e840542c000d040701c207802100700c4030004659004070750580b5404a420b0520600d55140c1204600e4075007000a2000005010101d5104071056618200e0180005e00b20407414586070407000c17400041990310541a0620241c406500c91450a400c60381e059038400031040c1000140100d0415200464030004e205000c0150040c144112104420414019a40c0d101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 998891007 1250 998889757 998889761
    0xc0203190e0f151206190e07021c0f08060414010810110708030c0c01060306111207090b030109150f0e0105030d020715081e0a1a0d080d050c0717091201 67
    0x107214035602e1001440310070955820b0502c8035a1107100540107541d16141032030611b2409003558885161000c07203000b40400fa130760500400480c01801c200f400011406808001d04403c0d20702000800c200c1c107130300442d40e20303580c0e03030131007806161107070b03141c0c00070b56180c02107292610840c28504034294500074502490203880c0003034821440e041040c032400c60380c8040215016501194020a442d543c6080c0800013503000c3c030603801607150040b1003030f48070307400d100d0000d8400e18007800358010302440c003400300040c5d0304001c100d9042d5600020041503501d40c0440c40d900da0b002c250800002c1240180c0003042c0307441480704450480340d0807000c071501e80040e500c0c00da807550702501510341c91403603100030300390034900852450760441c8900c0f9010922805606022080c0d0900359181c907403140d11807208180c004c039903505100310284103c45a00340038a8640d524032161141454a09181762a9400560380400f41000d1300e01c01074000039204180086a15035510300d83c0031204240c8a00c412080c1c10031044414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 998892257 1250 998891007 998891029
    0x30106080f0d050a0c170405040c0509100e040e060c0304060b0105030907230d060e010b1c0b0c12010f08060a050c16080f160b060f090106030c0203190e0f 68
    0x140a0503458407880b00445950303120b80f01e04010700080c08002c50000c1c102a40244209004450441d20b4604110401050740c44098440c41003002c140142c4000d1707984c901d20404605080d0801405040c1c201010501410000c2a800400d0140e041000240c40700b00000398030488c032441d02009803130b5a03100151454002500c1400c41d65002c2d0005120300207103021070041e40840c45000c00c4408403a100003030b000035080041283c5640c1c81c0c044d035146c0020240540c030f00049044407203080303944450b940f840035416143c03406032020340d140b400b00307200103d904121400d0b42540348855030217603122080b4101003c92882905c07218071a880004180b4109031080724001d0704e0f8003034a640b6000340e24810f00f42c6520684030651300440101b1407420381c140303034800426005000c01c1e000c0716580e656040401c10700344001d00840c00f0708810301e0001042e40d201e039102da05445c00d5080004090031100c07400c9155014043c82d0b1191404080309100c40c3c507400803180809004200c60b034001032090907061010541e50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 998893507 1250 998892257 998892283
    0x9030c1703191211120f0712020d06030f05060405100606050f1c020301060323070e010831060f06030c090f020708040b0703020f03090a05090720070503010608 70
    0x1051103145105400b11000c04403403100c81c9000040a03075680501022900c480c0d000318060f50001071100b0130010080142c641c0900c44500003005407811410180020501d14040058141e0009034159288a29401440a1034008108407201c030790a1a10070b0742da01c07045d9000e036403900c50140013131141c2c0210300401095a00740e64405051514081c0000c1558000515184000d00095003048044030180301660003000d055038041400702e20241c664601000d940f1a0881e1040b0240410680d10341050741c0c81030b0113000b0700c3d00d8030507a0303a10324107550341005601244030044184c00902c3e01c040508401614480e0080208025400e600380c1d80390308443e001d1000601c40c0414001c00c01404c41203511248294640350401340c0b814040e1394400f041940107800c840d2950780045560014590304101c0f01080c40e8202d0010362902a00000141c0d20007014410f092260103458002900b05125043d00c25105821b28218415140107044064032403c540c00340360302940ca4240c0028848900064106814070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 998894757 1250 998893507 998893513
    0xf030822110906010c0501050f07030b0102010b06180a0909030c030306060e24090411041403030703091a0c1f050c070c0e06361005030d1d0d0309030c17 67
    0x6000c1c00d00080610091005050110307420f2030f40041942801124480c040300a1040e0341407426040250440c0c0c0c02c1411036045a142c0341da071030200d403105070849047c240b000c1000e0701c40076031560010b18030310f2141d04108401030a1143c0d0038109a00100d1501000344251414003c50761601c0044031000b03406501aa84079004068107106098951214a040c1ea01c140d0207501d480d0408000c217040e100c42c0404500c00540000301000400700c3c0300003006045508501841ca000d005442c010300301405402040d6420030350344684450002140126880072000d082074442494001e2400551b074080711031201c2506040c47c000648441140b0100c0e021140c0c4007040480340d9081c031a441400060051107542c0100110a030309841d0585102c40c512075001700340503100511001c4086151802c0c0140088508030070701d000601807680c02050503070a2083e13a00d426250885061030b031080c0281d0703500020390040c0120320102c00b45540143c050302624010825429100c0c1c0d01d0302ca120865044e10024846a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 998896007 1250 998894757 998894783
    0x120620030702031e0c011505121207060b0f0d1b050103050105010c1e020a0b19020723010e1c11030309100c030509060d020414150d09020406030f030822 67
    0x16105603003031080f580844c3c0c0b6a9050032035200005085594150000c8940000260200b0162400304101460403e02c0f0003e0b158490700d8100c0c0c0415400307082d20040040e610b44040300e146c0d4a50680b1800862801080b0242c1d01581e4105082c40001075001c0c5085294440808580365020780100c0d4100d620681d83c4490600c0c054450003c01d144610002c06c4103800e81c100ca2000d0780c0da02d100702d40500300810440f80d8892210840c2d420031102401401c00f95007110300f04205910f04031860554a80040303c10301507a40318100125401d40010f10031503032210803410b4000c4088170130809544214409d10202180c9480729040681e030780110f4486650100e8002c1681c0e00e00b83c41081d804014038841d0511600b441d030b2038000142ca64001242041ca620740c045000c11502d26200714200c1c000c001a034880080c0120200d05442e5441600d15a1100c2900d0301c0030b10046454642c450b40066401100350501d041382d03458003e000e076000b506d100701c0c80a00300c840c040d6840740e0651500c113000d500070b00010130302c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 998897257 1250 998896007 998896027
    0x405041406031f09080304080a0801060201060b0306060c100f0e1501050a090e1524010e011205090304030f05030307022406010c060f090303090201111209040b0a12062003070203 78
    0x43c1e10300c040403010390f8130340c9103020018880c2400355000d14450b01c00301e40c840d10030b50740041450308160300110031a030500a003001b5188110007201d8003c1800e940883e03640e0203444800b4540203400b00c50303003d614607103042c00711848100d50251800101d620259100001407081320001c0d01b8080c002d00303134000c54080c410040400c280d402000000b180405903602e41841a002000d0298200c4030040003441003151361246c40c250300f160301a8807600b42000c0980840341d41c00202404030500002d81c2032540e40c40810309040f070400a960017140d1040d1441410060307841d06503100d40003503031a0300c058481d010801c5500c8450403000d01d10000056401e00c1d455a501004680780240503200381c4e000c03903a03081d078501602120300031189814065100400c400c003072407000511092001c44e080c50550404054045070440d240700f01d0310301610451b400b090f8100c9250014003446c2090b40459040700c07080380e00b0f00c1088000c0d0450001d0519120f000d09014031743c2c0c9400e24032403100710f500e400140c000f04074407044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 998898507 1250 998897257 998897293
    0x509090a0b12060708060405011d04060b03010b0d060207050f0706020a0f0204110c0309030606101205150306070215090304030c06031a030d0509271b070611040504140603 75
    0x108801007407a581007407407508483c18441d0030b8840c0d000140f004c104008180c00c02d8010140142860300c0c50f0120343d8004800480394407005000100240d461300e1130b0f80031555094100b0301212000400d0310300340c02440d1a00f40029030250808031030301c2c01408100308d200d03000490301d10300701c54842e000b828401c03005a5401000d14045607089038001e40c0d6406900d2000d9412015040c0407040c4030041d0794801032072040516240000b00300d2485849200d0081d04256808007144242601051000c80e054407038810241d4044409001c032501071049070104105941d0018440d19a074241c00400c02d401d48540300c140c0c2d00e034402c50001508090000d08200700451199000604102d10400c5030f04c01c01220600007814402c40013071207400184046402d15491a2040e8070050b9494402e20481c241c0300404441c0c046000024242c0c070030603984400a0f03480b00d44440440b20110740c0f214080110528258029140c0d0300140a543c0c001c0e0b10f0300c14802441d07402085403d007d80c00c018000c1c20204068401003003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 998899757 1250 998898507 998898521
    0x108010317040f03060b1e01141b0d051b060c0307050c0307051606030f0213032301060603050103152a0306030512040509090a0c03020108101e03030f0509090a 70
    0x400d5030040100154055454403c0d4028500c1a4400308000301110704001c0400700b11002e0003030246043d910810240c0c1c0000600100c00c4c0340d03070f007195202c2c5e44840800509203039240c0c1e1015580102e024403031840341d1010041003130b4050041940b002c8890b00189070fa46107000c44401c41992310800c04642d0040c041c00107003000100502c1103034500b20181c2c1c4ca4a0074400c40c0c001000d400002110103005044c1c05015101415821340d804509058106851407000240c5203c04ac0c520820105071035070085940070304804e003001c204024040a6503c490040040c0300910095a14000301250380e1403400c0f1034061740c443d6040307101c4a24000b240c00c82800b809481040c041909040d900c0d40000000390040c0941690790701b024007481d40ba0ba24107414014008002046c1c0d2000f0740203c00020300140618901400341c907020700c0c1c4603403a9602c0c85200f000300c0c007498211144d2158003100c0060301c0d0241c1c0904006482c0300b030b5906056034400d42800d07600360160b10415544011100300080c100d01880d40610 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 998901007 1250 998899757 998899793
    0x807230f0c011409281b090b040207020102070e1509180613020102150c130924030f03050304080f07050c031515120703060e0610060c02100e190602250501080103 71
    0x418440003640c500b0040d03030a1003400365402403580007c108911139441000803042040d50154906240d5900007500d402241c00360070840c03c030080100c0d0514001080304644182d002d401c0143c3c508000c1c100c0166410386118440c200d204150003d01198950251929580d9041e00188581544181c1e1001e00c403034010072103014404180502c1d20380c0c00c1e5500c0118000c0c03062207000160018400010003c400b60208907100b54484200d04100041000d091114100e0301031901a489807154941121280304000008044a0011076610140200416001b003030060031001c0301d100394240108403605400c200d400100c2d07185504841e00325410005620340403210399000790344030307030b500d0ba40c130503049034084681260345034441010050174a2008000a001e002942004c417100c0c04658001100703003074034001e094100319010654540e41d0b120b01c80040c54410813044445602a1a000004c2d07403840e0051051042100320800c590a01350340340c0b041d100340c540c103175034001c4540e0850711001000180c820f801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 998902257 1250 998901007 998901073
    0x8070b1f03120e04020d0204240f1b12030e0607140405040e1c030c0909091104111308030d060509091506120f030901031b0807230f0c011409 62
    0xa42c59613281d100030700710002007010044e242c40c1072440507803100e03003c080500712005404c400503001540186492940341c886191101145044403940384540002e20341c010142c281e5640d031056103c0d01500301541c01c41e200021a44a95900181161491481c42080300d1083e0204030a0180c1d060982100440c110454201c42c0840300c00b03030035040200811000b400c0026504c0c00000301d10b507403044404008080a43c8140140d002d10340342c003162031085250480c819a51a03404004c0c034540b0601703640610b0b40400003114229601c242258403584107a990b041568603119005c51107143c00c02040e070280090000900441c0d0103480701811248020b414681e002d440141a03548c060000c01c44040c2001c045d10180d6124031013600090141c41d401d41091105852041e011040380340e101122560080492800d0540d016009040d1000c04284010300e899070b600004401d07041001c0c4a00400c40115034400800803414424040603210f04150b81c403079055000644000d40368601c11110681c003000fa2106c5d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 998903507 1250 998902257 998902277
    0x106030206030a050720060a090c0302031006050a2315160507060305070c0b13020a0902040801361113061205012a181208070b1f0312 59
    0x211950000c42e05103112584820800400726070105081c070303082c8605240740e01c40302c6c103100c00d0603100c80005041418075030b0f81d100d01c04103100c010501c4000840e0041c1c1581d20044c0901c0b550009403486010b914041c04901c400040c91400c6090410b980d40040320f0111250034611003008481145260401c140c0002440a0b203104c40c800d0000b030303c1045c07041d07006003035080c50840e0180a40302c0040900c010f110702d0b00310100c0418046254641d020744218089071a0441510005851840035000384ca1005c3c40850081940141588500d0014103c04d0604040c000400600703403100540c06640750404065600c404005074402c0490402d054000749005070800c0181d0095040b1442e50303210b0001c145001c04030405020080c03081c00c0ca0700800c1912200070001e0910480c01d41e818807101181003103031075a00715150103500242c002c0036084100ca40380c80541181401d090343d80201000703881c085408808181280c15046030000c0522004003001411491922404d0461a2212040b410300640c942 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 998904757 1250 998903507 998903509
    0xf0714030306130e330619050409140d0207060e31061505041e24020a0b070e03160e060f0d050717071d060616050d03020d1b0e100201060302 62
    0xc030058845c2101015204a692051140d4000400b80000d4050b040c2c40b201903044050507000c0314161038059030040780800c4145091200d101c07104002c21100c1c000c5070809146250301040c08422613407103940711900780b002e00c01000815082d1045400400301d605230038014110896242c010451702114000400303991310410401c034003151450400c0003510009051000300c03018400e000d8080390040320140c01c542043c0d5a038101004221a81c1d042a0721004c0303401c40f05100b042510750065005208941d03504010f84045e00801e000c0807420300c0fa004414051a101c0810b031070749411200304031442c05c005d495130010300064080d2400034540100c1924480404139004000e054010111814581010111015542c0c28000c25821000034540c400ca8a0308c2c0122160b1001c2d17030040e20896000d9594040c0d002e142c0034151070110001d209024040c0c50012040c1c0580c007030302c800c01ca4103409008511040c0a00b1806110045000e40450300c04c0e1091011340c103000c0c104a554078003a000000e100360700d9030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 998906007 1250 998904757 998904793
    0x1e010e0a022b11010f18091e06120221301306030c020f12030a0605030601060e03010c0c03020a030f0225151b140307080f0714030306130e 61
    0x2100640b601ca400c0c0f001c108407564020050301071005030b843c00060303c00c0e81100300715205c2c44621a00c680c254440354210256030580320303500411508003208010300d50359102904110040321030b00380e00c51881d440b40c0700528101c4c0000001042542c0d0f0240c003500c0d0600b0701c2c54155120404c0b281d03849101c8030100350190460000103041c01c060500600181310302d454001000d0351803c02d107400844d0070007034070340085050004903076103c0c1c4e8003100420f0301da5403804003c10003024250b1141d0340c14841c03940001100303600301000000f0040d041d4028444d11150310400c5e83c00e40c2c503000000b0700580c07004c540403001c41d00c116044240c50301144107a0b294881080c4088514001d40003504095801c1c2510401604014a9900d4001d030060b00b05914002040402401809442000a8203ca50b160080450300e40b081c01110201076029403420b8895060b038182181035048a02c00721451401c00b4032440044a000080d01e22406000340b6100311a80c00d400140041c021100241c1007600c194444404001414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 998907257 1250 998906007 998906089
    0x20a0c02060a1710140120060c18030102030f0109050a0e010518010609050c0a0f05160804090c0201061a16020a08031c020711121501081e010e0a02 65
    0x3030759840f40300101403d40d0880c08030040e0840d110f20310744a0342081001c1a08014106180c401d08141c00c401213035501c00d013500c40101c551f813003250048804200990303507614094044820f01c4064a00b1700c441100c00c0c5800c030310041d5411401644110010401e002e44d0b5004035500285103880812011002514242900c0068505044510202c0c0d183c00b81c040c402d200716001004601c0c01484103090690311808035109081c2c0d0b010802c40e9014105c080b080c01042110296400c803151043c00c27884908025030a034103c2e005500d0546c2c1003848160100f4414043c800a4445030090004210501001d90400b644802c0040c0c001c03104a03116480541e07540c002d10070040c562000515500c200360900703003441806880b03104441500c184480404502c030015500880403041c0d4007135402d4400360365414601001402d018084010780c070000f1a0340b40340851a0b026120510707052070090f6a009004900b07a07050750301d2185103540b0500841001d454194421170780e080d040d0b8489081c0506c0c50342d0352000d00c108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 998908507 1250 998907257 998907277
    0x602070201180b0d0b1e0f120f3d0203190e0303071707080105092707090501090b01080613020c100204080601060813170f04060c0512070203030d020a0c0206 69
    0x20100b40340418620a000e80d400001701101d81380350040b1000702c08040074400d140403500402c400d5011324415210140101d03100d585542c211030881c0032001c62a07580385404001c61341010b501c000f440640028401d80d5000711440e041e0894501000180804000d40000b8840091604418080341054109201c0c40742c4c44003030f2502541d0f5a02d4240e030054860031822031070f030702c2e400410410013040c03543c030454040c1910310031106010b01d501c5404c008042c101007482d54200e007001c070392600746088100243e1001240c070744d036000b401540c1e030700c1c0c40c04022102a024064082a203007000641e4030301e030201c00b1141c0c60901110050400580340d0740649013002411085d280e240d80060140081401040060b00620007031600c0308540c5480c250310407004c41c62440c000d052000c05040003403004c0c2410280c405445180a036907440316903d030b50060410486180c103a031140180c55110344a0034480c001c492030250060300441ca08500000440000d40c0090040e81c200803018000a00603600c02d0300421030001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 998909757 1250 998908507 998908529
    0xc080d0b0310140a06120b16051219060603060b0d0b040e01060f0f050a05010516330e06071b05101107140a121107170609120a0804060207020118 64
    0x2a2020701041220011b80203011900b0fa10703061180000d50000445600c08003414215890155000060704c041c0905020420212a640104800c000c1104e00d9841082450703001444880e81d187d00540c200c88550081d40005142003003500d104580e50380094109003000b400004105420071907007821180d094201103203400a03180c0070020f01705010303036240c040d160072581c01c03e84911b040000b070280e03c1105558811000707001014000c0c0701c0c507600090b00004011030680729054110900040785030007566403a0800d8581044108410000a130320746c8210420340701d84d001d40443c00039400101c4010403007222140724809801070038070031502600b11070242c18502692513035803614061108030481000240701e035002d0700551022420a040c03001a910a506100c200311408074071040c02c08059400c50000c07040c04150030720b110440051b10a10608000007529900c0c0e112040e02209407103400c00301000259210081808903031164014014079105062252144040382700480c0c00780c505600c0101120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 998911007 1250 998909757 998909761
    0x15020105042003060708060d0b0705030703060f1d09100915060b092b05061302030111190302030a182d0203030304152414010c080d0b031014 62
    0x84160308a199000c0100c000d0b00320002151400709503543d200a00c620100607104010039540e80301c0c4008000850340001d80184286071000028045030b00561b442c4001078602900018030b6070140701d1410690b040c0c42c021402a103295150070348108030150190f2194001c030340e0b03211074ad06101c0c07040f000864410340849010211445070001210502da00c5034840001c2003000c40c0143d6075850004004103041504900481503502c11020190880500103110f403191a00b8450131640b422411500079208400911511103204001a2540100f0981e02918070006680e992200d009030050341d4480d0012a00040c2c0c84410242c1c2c201d103500b051400d541c82105d03103c4030020081401c00c42c07160009018401c00724004075902007941c03880000c0015100f075418140c0c480e114035042d041442da400844110500407941c010812244000318402d21f20310202980414415501420320400d980340c00110f07480c10f00c109074040601800c1f85014940d03060003080c11810246501e44605136400039a80243c0c1c40c28 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 998912257 1250 998911007 998911013
    0x80f090a1a15031c2a030c14030a0507051b01080c0306010c170c01111608220b030117011401060e0a030219050301050c0403050d0513080a0f0201021c0f05070302071502010504 77
    0x603406880720000b80e414650881e01d10402c0021172400b0660340352420103010301e15401c00c443c52305c3d0442070f802c1c01404005101d501d12a441f41c098080d450080058402c06141042e0941801030036002c0b00303001c40e1405d80060502c490f4003000c0c55104506040c11191329003d6a19100715070304d5040e03142035020002c124a071a20302e0074460034aa0380c034040311051a14200e03041440301580101c00050070a100013586007807510014207400c12082c400031000c0c3c4c071030b80c581d80070441c1a002401003181c80451040fa058a640b01405003266003505014200031503403e200c01100c107038420950701508480f40e0a030010062b220f841c0442d079100300c0306501c40840c1c1d0070300c0105803d403540034295201c503007000e100605c0850400304045408010600301965291140c480044030f100c03451380090500e0084100070350500c1007000d2106a120302c03d0307003035035880e800d1001d410542040d400180340016000d160700c0101d0502400040052038004e00440d01c126a40b10350042c4440c00c0f45100e2710042c0d441e80288010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 998913507 1250 998912257 998912267
    0x14030301030b150910090f1506090e09010c08060405040317040c080c06191b050a150f18200d050d0219080306060f040b030403080f090a1a15031c 64
    0x1c10f440481d8240340c5802d000080c2a002061401400881507445589401040d1143e018150082000c1c02128100d0307039a000140a146852060009180000c0c001908040c2c3c11720070361030009465294503002d6281d1000380300060000820890a001c1d0300c290046070991103d82e5184a50320039682d003036446040c04503080c24031451000d03940c010d94084c081c07081505e4040c1c451200380c42d65460464040903002d1007507040c00c4000040038005008090b408424000b0741c00400304111641c000610281100c0b1800e042201d503800c181244410b05105401d0000341e0f080b03458618000c40b04400303000c0403030304000142d0317801090104440c9070f4003151111030055018010b007040c0d11400038641c03101c40d0040d118510140b10051495100f410001380c2c1082110200f810384010b054051801078036031420b403401400348101920715525a07241040080c0c84100b00081401500358050340200910141d4051040c0d1945c1c081d01910002e1a100c22114041d1410032a00e0048a000925940812007003180501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 998914757 1250 998913507 998913541
    0x812040c080123100b03010803071e050d082a0c06010608160c031814090606040803090402070609060e0703060c170112230c180114010c14030301030b 66
    0x702d90500343e410302a001c01c04451030760031249420200441d556000440e40c4041142c100c00605c074004400824a2003000001c1c0c07407068802e9000c02005070541e0603035000e0001c10071006190398800340a9400c0700740700706411500100c160350700d03030845411404800c14001d0001c0d51001c0019010800c0101210108081401010746040824082c10482d00300010580b4201541092088400b012002c042c42010036008076078804030440380050b01c032441c60b0104c280440d81d05101c0e21203840418601c1c5002c204880446207018011450164103109010194004820035240581e136032803400045805409081c0228102e00041c0001506602e04503084681804d80003007000000c5c9000e003a15051101007a054600e050425014016540f800380800c0180b0142403400000403040c0f5a40c002001070129544001117a081c110042040743c02c203810710091145001145080e8202c8800d54001c21700c41402c0c50140e5002031400300c01104a0f85543e0080c0d008582e0118104108941540581c80c020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 998916007 1250 998914757 998914769
    0x10020c0601050d030509060a170f0106030c0206071d0310150f14090f180a030f1b0b0c070305070c0308070b0a0504030e060c0c1c030f020312150d0812040c 68
    0x10343c004041e203000700329000c0c000780b00e03006600005400c0d8001d402011070f0004207a801c8031214580c5010f403140b0102000c20b205d8100880c1c01d1448890204e070000c140d661107140a40d60b82101e00c100304109400c034032502e1b203007240c042c05004000160003065000307900382d440810741810882450075170100641300301540702a01962410105040a1f0b5504141c2904a1841d21060402d600c4400b01c02d80000d21541f43c10240e4410203040d001010b070082e004a554000e83c1e150040305e070341c83e2528201c4130115100c000b0f00040b41ea40001e2020050440031701002ca00900e031507801d00281d03907246001030300c460300700365190705000c5070441c07c020000741107a902c100e5006013030200c1d08155a018219807201c2070b455100d0b810102c2e4903040520100000320701d03444008c10200c04009026101500f61506840540000d5101c40b62154060700020031111034501c030349200141c90741e4400402509a4a00e070034164051110002e0b0340104011002a140c5071401034a040790b141440d2500348426101a4840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 998917257 1250 998916007 998916019
    0x10e0f04120c0201051c0f0b100206131a0a0e06060609010509241b1b030a03050f0708030c130608061005070206040b0301150e18010b070c050310020c060105 69
    0x3001540001203010410a20704000038144028401602c15000310803808000d0b105103000b40d60040400e0b002410900700c0c0000030004007440c681030103590741c0e4060204026902c2207000c1400990142490401c0c1409a24010506103010f5040b0040700d4080c2e45408005484050f0140441c105100c240c0d00960700f1151036150a44185c00a0300902443c16150712800d10030591040280313a1003501d0116555520681c0d90300c0010502002500260300e001c0102403250903000c0b010203007074119603000303010f000b8000c244c00000caa0301103078140c1c84640c404080baa800c2c801c2000003608100954014001124801d44440c0c80c818038044010b840d902420070003011400744600b5032501d41d40f14100454030301d40b43e99601c1003800886c7c2c0500c290750112000304000030000030110f10341c5101140c8201d040e40c92407403500480f030410010307659044400307070b205049030010409516000d009194052203600d80f02486030b0b0314000031303003400627894042c196685c0001e0070041a9500340041ca002d000c040ba04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 998918507 1250 998917257 998917261
    0x4090e0a060c170a154a040807081c0902100c030917070b191805031506041404030e0a0603061815150509040b0904120302031e0f010e0f 60
    0x10036118034041c1c080100a580d40140b006100004c00c1c80d4405440407078a10603c000344c64029900401b90b1030301d1000d240030003500c200048480c015030300004c0000160000101d0b126900d0750301e101d0348940010ac1d0b465004010052044420030030510414100000c0010000c0c2c180c0103100005120002c0e40c1c0801c0039010350300c40003a03000002403064034540c12030000b180100d8488940b40525903005051850030101300d4283c41c50290042c005c00c0b840c665195100c81850300b102401100d210b000300c55168201640a4903902c46c507505881e880500204041007084002c0074200f51002d0550b010780010b002c0b280150124242000c068009000303a29003000254940400d130500c2c004050b111694403515000e6003454490071600171009412107010f82d07140300012a2000e8100c0c0d000046550140741000e414502c10700d80390445512694100c00e01305400b28148d4012002580010305504130f141c0e040c1521004845050442803080281c0c4541500650620420040d2600010919452041c81c01c00f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 998919757 1250 998918507 998918537
    0x22061b050a0b07090f0308031b07050d140f0a08011412060c0a0c050d03200405010e041d0a0f0b0105090c220905040302010906271704090e0a060c 64
    0x3895402081d001910b1400584400b0f10450b07010034180c3c020300521180c80000304c248030142c0001e41c000c0546e004494030030210481d01a2003070185d40809801c03500402c4400c24001c2c0959040280c18421100075840c1810320980c49409402c01190302c4001149000180818168050110a100c00403610700d400c0c02040e240f101c3d507560005112651364030001c40e4050885000e0742500b1499607002041c3d441c0103410303180040090004000c203001891a101304010000b60341800c403004d0f503c0694a8144141040d02840040c21041711010b140010303526400342481401d22412080301d00c03820003200e40880900301100c103100113070000c1c0e109141390001e20a20ba40440100e40c1c44c059400f050b1034424031801c0551904c40890703030185402070b0412081000f0181c1c19400400c01c1c61064004000080c1290000010b0b8441c0890f114080440260300c4008107d5280040c1d20b09801c1800880c80d080c0c8440b602e50540b51001840d14195011200c08070401c80d00d40259500410302e45080030207411242 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 998920863 1106 998919757 998919763
    0x50d02071a0f0601050403031d01020c0306090a030e0a060f0f02010902091306050702060c03060111011e0527060601050304020301090b1014040b060403080a0522061b05 74
    0x250002d180b84d0301076010f030341c203070380d01079581c030343c0e40c80021036100032052514034018190b20662904101d80d40d020422284103c4004024140300500b41c038014010740d0700c1e1a01103100e14800c0209100b020790104902d50040010300c3c04242c4101404810f0f07005002c1c00e04040e42100100042010043c5001400c010183c800d540401580c1d40d010030407600e030310058560f20400c00d810808030b5010340c07140000e40c5903580900000030b00301c4c02204041407240c1080080e4148a44c1303403c01c0001042d034906000c0180b0411103224512216880d0101e40c0360003004003004e050140100105c1c00b9501c0035030148254a40c4405d85520350304018100c0b0528065600c14032414507072003aa10411030a190080342440800030740010b05150440e0f4403010907400000c00181003140c2408004880100006100d003c80807521100a81c28181400186100076940e80743d130010307203803801000010b4800 = true := by decide +kernel

theorem cover : BRFrame.Cov 998741007 998920863 := by
  have h0 := BRFrame.cov_init 998741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 998741007 ≤ n) (h2 : n < 998920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
