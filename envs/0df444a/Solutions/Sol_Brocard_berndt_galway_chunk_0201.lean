-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0201
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:24:52.856723+00:00
-- url     : https://prove2.me/submissions/5d45f5fa-969e-4049-bd05-e7ee7cffee48

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 35971228 ≤ n < 36151084 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 35972478 1250 35971228 35971249
    0x20c09011215180b0402150702010f0c08070606090209030d110c0613090509030c0f15010506090a0f06050703030609090b1b07080403080c1608030901030218090c120a050402010e 78
    0x46015a2000b02c02c101c50200500c2e40c5034503004a4062131582843e005211107030500c4515100c00f41d01c1081000f0040c2d0b8004400354603a0100d180041c07044d1a149440f094500c40d1980251990381071400c00714644d8200c0d4010100148210110b07502c0c9408080c0a0340c1c500f12004180030290040c0541700942e042040041241c071030140d841880710340c2c40d808004101c0c1c0e029100c11049074404240300d80d600f503080000c603401c0c007420300041800da07840e55407246c0c407180c05000301401400003080c449407945840c2e080354040d0a10034041c0c0d40e116261000240250803210f4140c0000742045400204500c140c451141441d400540c0c40030b0943d030f519109013591034504211812140100a03c0d030101c2c001c400504041c40c07140b000c0320741d20301c4262440d1b450595441103c00240720b600c6400c0104c0c44000007140c246d0380080c24096240c03090216030302d1080890181d0940c000107110b08020001c0c0803240102070f201b0020106100c079031202c6480d0808c41e40c04030740080c0481d11280b8150400e1401d00c8900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 35973728 1250 35972478 35972513
    0x12c060601120c09091803090b040b09010e040e010507030e10050103050c04020306061303030c03030608060f0114010504030f05070914070804110a0306020a0905040b030d0c080c0705030d090303020c090112 90
    0x459130700c0e654401680884504002c00d8100c0c00341380401c441090f42c0a0b02ca40000c10b03045012a040509041211101344036840c86030741805421400d010290f180c80d0041c01e65116840000c105a01d440d0001070060b00b20404494500e0243c003040e000d025010384211410f89030840f0090801c0640d54090000039032000d085aa40034500307010208060360148086c40256200383d4507018003c4262401806440d0203030081c0506400038410007880041e1664024112807080c40301c00b410381030303800050314503215a810140c01d000500c003082c0c0a02400117140022a6030088003000580c4200020807491329042d901c03500001c01e810085004640e101e20081004074000300308162030340e520340d030703071300490b4420503100c000f0038184101007049161a1181800c0c000050b0060500c800b40002d0080182102c164014410359000c6050a40904100020f20141170090221403c07840704100c0981b0715022444210010300ca0030f29840c020742411034495040355031018007402da00400b9030302c81e002002d070455103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 35974978 1250 35973728 35973737
    0x90f07030b04080c060403030e010b0a15080a0605060a020102091003180b100b1c0b0102030a0507020904060605090106121b05040e0735060405060603040803070c05012c060601120c 79
    0x10000185014445c59010758420b0f20000b40e03540000444a00790b5040c03102003841141d900301c003001a41500c0c0080604840103241c401c00c19074805401d240104100e420458124101044004140f0740540c0180100801110000c0000a0402e003c4054690b052204074071982c0c0035085100003000700510381e8000503001c0020301c4150b2100c129504079005030043c680c618207640d0291070a03460034031821080320000c0c4042c61500301d060501034080d2288402c006c4c010280708000070300340000c0e60b10050140c82c0040c110002540d4070b100043c0106090048101001d1910312006245810450541c0c03503141641c0310181070a01d008825481004000c1941003884800840c6440515429504120810004502d031820326544180d11060f801c004040768003d1307190209100e056030315481070700c1d8400e91000406690f5507603107104413111741c14801c0041c2030b5030a1285088809541003d20512165500c1c8a45184030003000d005a0740c0d44161140c50108a281c4000030b001d041680262240c008036040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 35976228 1250 35974978 35974987
    0x305030712020d05071707080705070609020402040f030b010b130b0703030207062f030c19050418020315030a020d0303050a0b0d050a05010e0a030905010e040f0509070e090f07030b0408 81
    0x540c0690f40004006500603554030200800e4542004100040a0703100348103070784038a040c8030090440c402c0030b8898014400003185000401a49401640545070301070030940d00c031665001d240c91072000d10300084803000c0c900c1001180341001602980d200c20b4881011044403850710705900e405070320404040e400c0540070803040c00800c040b401016002c4503010815544d000c0032520703400d030180448080440000d41001402807500e0f00308240c4181c400441c0c10506640f0b904002500e8134804e41e17201140909400c0030203240d880311940614450181184c0701018200380c4820107407500c008000095210b5182c2403140c010a00c00da0000b5407000440b440003841c80c0011001401c850242d00d81210903601c0343c6244400c0120a0281400c0301e9040002006609100c0d600504020194040e8904006468050381c1d0142c1d00c80d04071034048200c001c1c04025908041c1c9416031900d18500480c141a60780d5000f0902c502c100260244074005c40c007001d49411800d40e510a165100050001d8404060a10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 35977478 1250 35976228 35976257
    0x3060108070309020d2a0e01030206091809031c0606080a090204020c0f030d060504060807060309030201060504021803070b0301050d080717031306050c120a020c070f0906030201080109050402030a03050307 90
    0x11483d03040140200c0f807030204000c0e2003030310046000710707003880760341c0046064420407884e41103400050543cac0e4115949900d841881d400b0450b48521402c41f0001864100d09002c06121701200400c0090f00d4000e82c842d400c2c03030044074403060b40d4552240c600018a4640000c03c90145544084456480200054980070b40007222914210300c0b0142489030750800200020003001a204070002080259030038400c01b882c1c004415210800ba126200c107143e1980b08a0301010701c00c2d8004005040010800c5494007039013041c0d09130a110300b8804900034842c20402240b40141881036034100c5000502c122000310700b80e0713074650a9801c40201140c1401e0302c074103007a448800150155101700205c031810042c104007420326005603603000d820800c0901c420000382c40010329601160303500014400000d1707901c020a4103550f00e000b1466100c1d1188036481500401d11911030341040007128000d80c2d40c1c980f2a42c0307440d00d01d4225881030310000d5055200c1c200440029001d90059a4450000d0416000080c01d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 35978728 1250 35977478 35977489
    0x1110706170108010b010e090705070209010b19080c09011103070203060408190906020c012d110c01030209030a1b0b0304050304061116060305090c041409010b150306010807030902 79
    0x140c02600109401041201072525510352070780c01044003030001c1c0619411900081e00c0c1c581c0c11100a80249003038800600220b000d41c00325880c00d940608904025a9551541c13181d6801c44000c04e41902041140c0041051103140c0700b038000d00b8500c000916082000c001901d401210f06c50713202140c001404810090b96080c08410b1045005a0110340e8a42c540908100c88000b801c003000c09020714100d040c032134264000742c4d10444010070300317006a00f451402e408804014a08034030811080070000e021902690002e030384442c42070300204440051034603c005400341d0103040c0a06825510180854020407a2130211480704405c0045030a000c98a404814850303a208580039a2140d20004041100c1c0e03074820100702c07400941c80050584020322003102581100786200e00d004054035640819241581032021b2aa880ca00420070441e215042200040c00700341180c48521a5107003010354481400c15496803850082807120303052961341c424006503a010320140000c020195149100b00041e02d80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 35979978 1250 35978728 35978743
    0x90610020f12031008030f04090504020414070314010602070e04080307030b120c090a090308040f020f03030d0f0b030607050706050705070c12060b19120f0c0f03050c0d1703060111 79
    0x58a2a0f0340d00d4001602915204203512181031a4000c10604099800c0700040da0141d440c02100401c6940703803400054090000c40100c210380600300c00510070466055404000784243c407080150003603a0b10b80d000e985400c002d1288500002140300050002200c0600556100300079050000d50342c0c1025020425a1000b0148102180d0050200402500e81058002d0340240442c00601880b405030745d0040400380041d000404d5000a00d40a1045541310b02c1d600380f050001500300c07074403050305030308403806803051889a03040f02d0719001c00e502c00c605020035098850303046a15014034140b01a80c40790b00600c8000c08440400800307109400005007401c1d051001401140300c61030780441d460600004071036513008058480c00081001c8406824441401c5084036130a40d010b580c0d085803402d10301c0079818403240040c00c42d640b020001c41c40e921548034403000d41c2e005100300d400b03034120241400034040446c0d4015103040429100303220550450001103502010600d401c01442d40300548081ca481035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 35981228 1250 35979978 35980003
    0xc1b060212040302060405160b2203051b0a0e131202010b030706031d0d0f030e0a0602030901021e03090712051617100b0d0803060a030b07080601030c0203030402090610020f 76
    0x2004090205001f400c0060806200c40250b070001c14030724120390040e8500c40c003a1a50310041e24095052603a048801c4400001c40e0080f05a17808040305a00c8102100c0348210f403580f15202c01d10003c140580c0011441e8440e100d40708440c061160180c039a040d45c000c010354004110340d2112840e003c40d403400d001d000018132107a11302080c81c240d110b111101c0e10b80642c8401c1415400440c01586155128010782c00440c0305040000c1c8002e407001c00c06040c2082d20401408160000013806103040c4150b00074a801020f801400150821040c0104064030003a10800603640c0245c0c07092041404406e0802c61252080742141c4000c0010b85610b40580e260758405020242c0c440b401c141340070000d0180c01d041c60b2003c0c00c1045079122520024843d008a50400307050b1100200001c0c01c035031201c0361110065038101c420140740e882d00d810000c0c00741d0f01c12509540000d04140b04089050300000a0707074040c3e54010551070680e6180c40a1001034004540d034601144280028001090018044d0845814 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 35982478 1250 35981228 35981233
    0xb0307180b0f040c021e25030c080d0507020906010c0204140609100302030307060209030a140f010c0c21140a1112030709290a030207150c1b060212040302 68
    0x40301c0c2002c00008600c0c0c0d0700340900a90601240c0e12116602161050b2a03140710b80b0220210101030f11007d180074803500261403110095200200307a5081c0c08003000c100e0b031140c0882c18800b078680b00050f460301481d8000501040d402e0241c000107103004503410354041300600d0106000c1034141c00160696464840ca80e072454820001d00280e410710718041c40d4494105241044410f2865000c00d0742c81c440d526000c3c00300c1e0b6011598006035130303090144402413a0002102c00d841c0c0c0007804516180c0da0b844e400d0300c0c843d620305001d02d0900ca000741a082c03441e50300714102c0107181020685a69812419007502410020747c2e14030801c2d010244405030032202e081e661404003c001c4000058500000240c00414074081401080007299116100d04e058400d001030304a1914180d00c0000001c03000b120a4400ea01c0b000700b803091003e1b034154040c12009024440d00280710b00c055120311308036503203841c5840000d0280d00340c0c1565401701000c4144d03050701c1058014540324805400f419900e5003610201c1c0140c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 35983728 1250 35982478 35982491
    0xf13030b0f060108061518100503070f0206060607061a060d060f080303040506040f080d020301060e04051003080901030903110d030c020f0118141005101d010305100b030718 76
    0x26440030090302d5001900b0309140c20b031420a0390004104a40e003440c0005602c1d40019005081c001380c2001000110015009696000d4603800141c01d64104807a000002020740301741007a800d100003601402200050f00700c9151252549603940a01101e0700b4101e00d00c2040500e812090702d40d00010282c0c0c0240030782c0010b6950402e54050007031a819070045d201c6610500074407011881c0843c42c0c98206520800b00f80001e4590300d807400f1180101480b10a03440e10200000407042d4000d2450b00b0201e104032401c12090340c4e190207244205905000103091000d0510204115502035480001c2c91402410030051002074188038a00c0d001d0088411400280c42e004040b5045804024807112404880000d02200c59401c0e812403042c0d8007604094100303407603144505100741060009985048a110045c8010320b4082c0c40341014810b14455045403640001d51070448203511041c0506030f035400350141c80c0c80f0300c41500c500082d21140100f164513000d124000900c8800c0c0e031032040c08640c17a544012650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 35984978 1250 35983728 35983741
    0x1317010b03031e07050a050604030905010305010806090607050c03090d081812060402040f0b0301021b0601080102180405070302040810050703050a021c0c0201200c01061e09020f13030b 81
    0x945800c0d120840c0298000d00c111803140b102c01110304201c8031165aa10f45920090820501c0c1c0085000b0140c071600500042c4428036038824146003da50080c0c83c01d0107241da0742e02885a0f1107000300c0e0700b500c0300d4201e0300218801034803640042c402035900404590504180a0010352a4000e558040362204c6c000500c1c8000f41004082e034603131070702c411112009080481e289268884034020f200034402c81d912004418054440d0744011010034001d0b008544039401007845e0b042075400c5c0601c1d007505100390b000000341e0300d00500841c2c030102640c1c540741c0720030010074003800050301c0b01910703103414160240b2001c03072800010042045000081240030405080410019007154009040c6090640c0100a00080c03001c001200c0ea0302e0040c59040043d00c600c004204a0041888044404003100143e02e1000104082e101a1241c810003500801c80e541e9280c0c890140d0a03440c1d10103011844030072104208000c0e00d81d01070701a40e845659060316248a010510600030013540088840142e41814080b2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 35986228 1250 35984978 35984981
    0x10204031401092a030605010305060402091609030b0c070f03050a09050f09040803040201030615020f010b0f03060c1c140a0c03090503042606010303050c0f0106060c0b070302131701 80
    0x28070040a40200646842a122059180c0d50b80204404e552070030b040b0381c0001d504020003400210340110042101c2c1d6140c0c03034000c0e15141c2c10707038060388594402c1000c12880d059942e40c1142c10342c21604c4030340340d141c610303500c545050b01e00419100c6540018450303000410011040400218402d55400d0b9442d01141009070100e54903400c03c5026444024525195444990904d074010780c1202c01c0710307103982d540e00c01200500450380007560789408040f9060401e64001803841030007400c4a00901c2000c004405010000c00e00c1c0d0f003490b5142d0304c6200450540e1035464001d00040e28046e941d00e0003440742c000c10005440100340004030804074201001016011307441010703104d04c0c440c0b85c180004001c54880503941e010ba801340521030194100c03640c8401d0209005c0341c0c6800d1964041c0e03010703981e407030801070030581040d4641101402440101c07141c886042c0708800550744152164619802d00d0b4603000b5003c0b1009020b0b4041c180e082040c400a0044880341d0700050001a406540702c00603402d4035070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 35987478 1250 35986228 35986253
    0x6050702010606110708070b0313050a03110d030203040b0a050705070f030c11090714031806190b060313080702040b03010509070f1406190201060f09090c060801030f02090403020c1201020403 84
    0x102e16003149100b440a080e007c11200100c40418140980302e440d089080d468001400c0d01c0100640f1681310483c08054000300843d9140f0301100a483c0340790703c5910190261310049800402d81380400340021220091640407540000103483d0076810310700c199803541c06180181800b640401d0241049004204070340c841403540c510203461215660600340300180075032100c111040c00b120300100000d0707001941e1030507031100f4105074400c039049400d003940d5941081d0034a00c00c6100082c14000c14001600b8414101c0f030045246408010308070010f522403580503008204201d078041e032a400c5503a0165824085c00d402100c100000d0040030b441c2001107000501140d000a103003000e845601c107016524034059a8600000c0c5110b61004601008124010020760300104040348081c0404110303080554407004089100f2264803c10300e07101e82060300c0b0b840302440010705c280c07040010500182060440c168000384240103c0d030381800d404000031840381e4421038a00240c0e501190400901c005600340384c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 35988728 1250 35987478 35987507
    0x9051c0209010b09130221150a030308010f08010b030706030903090902040b030601031b0c0201120609020309060103031107030209150f061605011b0801060c0503091003020c010f05101502030706050702010606 91
    0x214a48150f1000c0300d1000c0001500c4190150400700025141c4400400020a23442c4001c1140d204507441e450080c0c1514002c0c0200001324000c0a03000c24114814820345091317010080041c80c01ca40341070310460180c045c6100c2242041580c0304001103000080c0040c00c042c082544096880e441c040b00018110b400000900308501d4561071103542c0580c00c43c0031408615020700e0404a40a2044600d8024041590207074901510010805c514681c022442506036803180c0c2e200340c1d04003c5800710f6a51480c9038000a5440400c0d100441c01c010084140703443c0040010300810000080c4000041e440d400c11403d8500c069804000582041000e00c04c05400c04906000075480000c2100010100300050154000388002c0d250340d00309100f4204141e078210b40c1c00821a0b240c0c50602c11000f0065041b0800c03001d81982045a95a0464032038043c2030710038466075000708246480c2c410f203000307007103801200c0000f540401c001e00c80100fa91030081030720400558001240030b5207400c000402460020004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 35989978 1250 35988728 35988731
    0x7030c021801180e0307050d170c04060906030b030a0c03060203070905180106050a1e02030a091d0601050a110a0b04110108010e06040506040b100801081204050109051c0209010b0913 80
    0x5000340450311107030500c20918101c0c000303140c4c9580c0c0c811510b14841c906001c2c4c4140325030484d00c800242d2041528003084120541c070b240300d480c1e04466841c2ca00680c0035400c00316501d0101444102d100c0d41c050210313103c00038111a80748085481303003c4103160a810656074260000200010316801c9071003100200010780d071584100e030a0302440c010180c0103009000412030005011030b801841105020714410141e81d81048841110320065920b520a03003246000c90380c0c03600c0001d200900e08a107110700603650041000c070307540c81030300440e00c2d82d03c0740c07900c80180078000314405900706040025400d201d12816040009042c142020303820f03001030708491810044504010701c0401070b8001801d42140c1c0c1620086969200c02c000a800341400b40b0507150030003c2072604441c00780e4411a400d04a5507042e054480fa8680f1080214841c42640030342c038041002041c01300300c0d80c2030030700c420060718041c0180d00c5180b422a60014881308030070f82c8107200136a0041040051071030706610b060081e4034840c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 35991228 1250 35989978 35989981
    0x6080d02031201050d02010302090a080106030b100501020d0c06020f040603060807091b0e060702060a0c06050f0105030307030521011e050109030b061c0b0901020403061a061903060302030307030c0218 88
    0x4420b000c07402c14090300d8000c20768088000300310390094050300c00d02040104061603860725846803034000d1020744000d5400b200d40001298615100000c01c0c0143c0b803040e4060801c0301c210540540d0b000d00c8124048912990801249001040e034602800c042c20381980c010504030b1a0117210703490000a41c1003509030074500004200c100c10390883c85070781c1c62510309003803c00c940000c0008450f401010701c0a50042000549600f00c80e1307000c50803041582c0304020811850b02c0d020000348114409008080c0c15610420207400400c0c01500900b01c04c1c0591912120b04001380f0212240c0e40700d083c0d10642c2e4110250203609594642c440c810406000e081c644900d80500c1c40d242c0d50301101c006010039015040c440312141c1241202c0800d2880d540d00b0200c201200d08013048200d0003588a440151030807450254031107511400381000c03c0c2c844100409880c01e000b40c110f0f2400042c540d1040d003406244c1c3c0c81c1d4000005840600240c03502d50b020362100ba8207100c0038010321107805040c115000e040e685090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 35992478 1250 35991228 35991247
    0x609030a02062404020a030207061805030904020d021b0a05100b0307170102070f11030d02030903060f0916081b010305060a0b0c03041809030e03030a02030313020a03080c0106080d0203 81
    0x203042d40e070040b10008075140305070900820000d203100d102c0d40c4940140c00050711400281d0160001d2205a01c22082003000d00e007041c20b19425159200300c020709582017003151079034610b8550003030003000c038151000611301106c42c0040c0c8501202e400381b42c0d42d180c0144114070181b10013030040c0302031000c0d4a581406440801d4001030340360071050040300d1001d1034490856503540c1003541a203485592201c60641c00d0900350501000307403078141d50458800c0c030400589101d01c138400302c2610310280000d0f000302596112040c1c0261142e42c014010101d80c818510f6440c0c104000c60201001027800002800b441d05090141c81002408010101d0500d401e003002d112960300e4510316041180c034030014003038a0342148942d02d41540f00d154403895105442030384082443e100c7e0743c000283c840c4070f5200ea0b8800034846d41032607140c0c06462900d2025030002d10000314001d08068040ea500e0b4402841c04861945a50b1401140d40003804010940d0b90340c0c140505c05100c08100c1c840c09000180000c5040a9692 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 35993728 1250 35992478 35992483
    0x1080a0b060303071a25090305070605040b07061d060a09021903030c0201080a0f090309050316030f0605091c0f080709050a061101020f0a08090106050105070803010311210106080609030a02 83
    0x13610f1599582e00c1c10001d22002228051580d083c20821b803003103004034a1441c010401b00f118001900d00d4000d6060002c5c050303001d94200e80071150a0b041090401281d52144002030032140321202d440c0760080c1d92140191414000d85101c0c000444c400501c00046005101c000d900c09007401d0401a06010300303101203a08289440d000075824070340820300390f840030704120151840041600e0000c9c01c240f0400100754000106800380d271b405400320341940c4120501c07038503005064403004c1d1070540d404503d00041402034001640c0442d88401300e4a00c02098200d0240c0d07074046e03160312030006154020704920146c0c85030342107401c40d90a15000c4c40907803c120000d070000c1c000b031150100f40301408501c20343c100f40c207406444182a41d0f2030229110b8001e80c2c801f034008102110a40903651a0600114266000740c0646171400d402400c620f0450b0b09660302d803000d1030b003841e0722140e102500c600c4013009142014410034000f0b03142c0002042c82813a14691074540742d005441078003141c03c00e000204509500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 35994978 1250 35993728 35993753
    0x9071805040203190c020a170408010509060c0304021201020c120408060601080601080705090f120d0f02010504120e030a02040504060608010c0c0206071101051908060f011e2601080a0b06030307 85
    0x321000280d01d021002051f40f410348800d10040100d82502014501a030383d1502900440b40558000e000d56aa4424615251002141c40c0340350448144045405420700c0303400050045a0742c8001858005500f949920780400d403c0c80d00412200003d080c00510410b201c850b070411000c3c00c01c40b80908040001038451080144010108400822880601da4400c0300c811210350000d00f50f40c40e100d182c1c801483d1a85c00c0800782802048101c240c0c01000752051064030311036038000c0d000d60714070309100008075014141c24440a5251040c140180c015039110322800380120f02c100d4000480900d40300d009401e68042039103100c103000e030700084c02e005a25614112080c86a00a50114a0a51030700040c0c0d41c074080e0003008164100005440100d0301e8009901c0d50242c0c80031208510103800c0c0000450f4a402c11b02c0b45a20062050b11601c4292401165a00342d4842a14280c0d002040942c12440241c00268010246503210109100500915080701c640101c0264051442d004040d00c0f9442c0c141031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 35996228 1250 35994978 35995021
    0xc030801030611090406090f06081504030503101710050105010f08010b03180a06050a060b0a050a0f030e15041101050309060c030a1119080109050702070501030e010b09071805040203 80
    0x11030703030704182244403e20211a80803e00400c1000959203425005000346001120a01d480740360a6002c14400d4000540b81c2000105105103d00c1d40d5582d503080b101a00064661551603041c00700110303640d04803050b00510050003000510100d40e600803580195501a80725034103010860340503c0c035850f4040680c6064458900c00349a80b500e80241d964460700c144074202066001c0e2000703020410002d600030a0103010780bc80c0c14030406131100503604491040c1840c034004600c0400881c0e1500b40941c0c030610042d0440d08000a103024135014060400311240d90020450340d150003000b00300038030604d003110795100a18100d42940350002034255511000382c00d8800302c540c080300140c0300b40100d404c41448049840c0881e51602c07400740403d403c1d07040c400020707800b144100c40041200180b43c030526104020650083c0b004134075000c0154000c201c8110003101a5488211403c21921001e001c54050542e42d070f40c0350384051142c0c1101e00e841c4080c1e00594411801002403100d55140040800001403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 35997478 1250 35996228 35996231
    0x150609050409020d0b040c0305010f110d050a0e0304080a0506090304031e05030d06031127070c0f0209010609060807030903050409050c0d0609050601020c09060307060c020a08030d020304020406060c0308010306 92
    0x842ca000140241921304002840c400c3c40c40c00308820054840b42c48021248600f00030f2018907240c424040588002e0041902c280750140911402d0520503084580c1041e40024005400d1054a1010b0f00713641c020740040c130055101c880e2110401c4000c205081c2e016041c80095402d09045985601030001307444402400740e440140c0c090b0501c44c0500845140e00d0021a08102c05541c0c5c0c5131100c00f1102d1203c80510588440e0100c901060441102c03e50401c840041c1c1d02045c2d0b18840182c8040c608802c056800184100d42c2c00300503280e09070268040d0aa94403840791881c5004002803029400901d01070416080c0915400041d8000c0700f90f400340d501148000c59155035500c5428528003565850074038490500800103000f001580c0442d000320800e03030a032a2030100003000c2c003201010603680190994044401001242d00c1a422490010b10040100464035540d504581c07650f0003480b108007010b81d00200384000c52401e8480c0304005d1100d8200038203083c04c0c0d0b80b0060484a0148000790955 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 35998728 1250 35997478 35997491
    0x60706020a05220e06090403230706090b0603010b0a0e070f030b0d15060501050906040e0a0209030601030506270d0c0212070f1707180b030c100e01031506090504 71
    0x5000d1029943e00b4001110381c01ca40400b040c61a0041e80298425980c3e50104e10001c90014200031140620668060301d030f2511005503151070348080c00041107080f420500a20441c80000d060b40101c4903030304c3c0503d4940040e82008420542152403550301c0d5841080058401c00a81044001c159403001e60b60501c00d0142c04441c5054025007d00a001d96202d1201180603040040c1c1ca0300b0403041e01050b646c00c1000b1603c030f10041d076452050300c7c1c05c254480302c01d01080299281c0201c80b6540b207201c171030015041c1110b12000c00c0c903040e8281c0088840740c00c014204411980c951000c501d0388549084a1740e101c20031220400d4540c98080d20500411031455010015901d46903645009480d40b94110f4003203555540300d10a01d114207000f0008641a2411000030740840040c81c0010798443d441c88000289124000c8001088030a0360f00c2e40501811614400956a400850001200170784030000c1d12038900700010100c03404449120000c0d00050401d12081d680181a00c042d20425103000415 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 35999978 1250 35998728 35998747
    0x13061a0705070b03010801020c06070306080705060f16050d0f05190c03110f01020a0909020403020102030909180601030804050f03010e1e01090b010602030a11060601020c090c0c0f03090a080105040206070602 91
    0x610981c3e4006065400c8000b00029003280158000c2c944100c541c003e641280c0c64081d01182503555500c150f03203840d802010306000b00d242040c001c00310305186040c0149407240030030400d802c0c0d513100320041e5400e811145007041d030180c002900c2c0e5210109032034864681105020041b980244108207441080020000281014052120107060b0b22400c01240c021003000a40c02c5d01079030101c6038003c0003caa151340000c2908450090340d0603264140c000c1c5003440c460030140040d0080003480c1611940302849110b50707000080c02810b02860180c168250303200d0601042c0b02c1d0304042c03981414060387c07400c00d6410802401107804075108041c0100b00c100c000c50300d502ea03030141c0303a00035028050490400001034060703000801001ea002903601d95240f0b118030302441544502003240d074940540c2042002c00780c1407408003042c1e5405406140e142d81032030060a90280340269a988100441d4000110345201d481d00e401d4090040075084000d1020307203081e5010a0450089840c01409079802080d0640c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 36001228 1250 35999978 35999983
    0x30b011b031d03011d1b0d020a0e061909050105042a110c06040f0602060705040e070e0a180903030f0209030c0d06060e070c0201090605190e0a080a08070213061a0705 73
    0x40400700d0351450724009000010391206903d0100042c00c101c0c030300d1980d040c0c0c245848180c0c440b23900100702030f03a0f842c500010841c080500400381e9900c40104150360000d03030020402800a000c007130300009180e42c14081400100c6150307090011090707801c001014810450305410f40042e90581c607001881e0f4000340b085602d00860380700ba070380d4809001b15011440c41e1000c001c640845a050b0300322035540c1c0754003005565501c1030b40102c0d280d84d400a000541800d0166443d07103801c200280400d40029913406000302491400b035160001c0303e86a191240505038180a9008003965000086103000410b1000a40e00c6d0103e0102b80c0c09584d031a2020f40c14001c2650003440203010b04000c0800034981303103400800e2006c00c06022404a003d540d4049042c621a200345c4a041d44c00403107c150142c0d6840d000d48855580c4940a507004030105000310f0410021301064400c1c40c030450446071145010320402c100b02d06110002e100c10751600000b000302c988074001107517407140d5554080c0d5450303280703080250 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 36002478 1250 36001228 36001241
    0x3020304050a0b0913090519111002010e010b010306080a060506040207050a05060108011104050a0605070f05030a09140609030303011712040626250e03010c030b011b031d0301 77
    0x3035201c00d0b000000600c1e00a020014000341c0c1040b00d43c5021620601c9041c1d0403900072400182195000e006610084450f91030740700c00840c0607403802c5494503d83c00015400300c1049500c0c0006035196102c840c0250300c00d029405507440701b424140802d82c20214a05e61741d050543c1c000d00706644134400302d030751500d856040320841c50f0414240c1d800020700c0d0a00d15074039a000e100d01041586410303d01d4118031102001d0700d0998800508810005141400c201c4141e00300045c1034600d1041e022002c800540c2c104018082404140c8903200018501100c14100001000b01790b4003a00d420000b8000550f008011281511003082541ca00a000188507903d010782500105071131600c00174000c5046504581402022008038440c0c010100c680510580b4a9109498000300c0c991941c985c02103188034600f407405648160300d440d00000103007800003402e5a040c81c0310140800da50710a2a256568024505000e1260300601c0401004450b035008100c409031104100305200c6400a081c21a5803e41216 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 36003728 1250 36002478 36002489
    0x60f0f04080106120b01140607060209131a0a050901080705060304080d05010305010f050c0a0914010201140f06040c021501030206181e1306030812091203101d0105060a0c03020304 79
    0xf00a10740d15840031049000440030280c80b003003001d0000041c2e12800183c4a16240005000d0b24140400c56503071070041c6d04940142507201d0682540c011590043d031251100489082c80010b185000700c90078490340b00039541007180600701040051115400005803002140d10556031982d4a03540c5040100c0580644407241c07002900702400002404415007200340e2040800108000da906e0360002490f00d0700c95113030001c01242881c03900f0858407030304402c88948032006000105e8000c420380c08640b1841c0382101c000d40b103644840140015401e00c3e02c46c410346010b04d4001080704240540054081070414403009100f01800220b091400d800c802c1c0107000c888010301705001c00d0312141e400c3c60906817a989001c1c064040c03a01c0c400420456801000c08603504049580e01c0c0c00c041071151603180318002c168041078418140041d003802007403002544904d002e2640d002d00142840e03507402040c9d0102c0301d04080345110000500c555a2280200c42040303a0318101040d580100e440c090b8198021035128 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 36004978 1250 36003728 36003731
    0x801140604031a0106030b04020702010c020907090b040303080901050c09010c12020a080d0c030b0303031006050d02090604080d0305060d0b0c0a110105070309020108090304032303070204021602091005060f0f040801 94
    0x960f002a0211942141079410948052005400d501c060204a0050724000b0340090504514400542091609107030010018988051400d4842a44801329449688200c0000f200031080014503e4284225034111154880f01441c0094120000f04040030042c0040c250042c1c0002314802c0314020411410035036030000c112502c0d03855004803140104100d00181010a08000740000140b1700842241d104104154410540030b042103412151904800900c4000c030340d0801400c1241d540e070f88081c100401000d4028080480d4041000303040c0c41c1e001c1c1025006002901c1002c00140000304451392206245c05215110011040c04031403140e601c0050030300c01d520301001e10400640c16041a4445c5000fa25030542d00d4a030f0b0100e1654038440c511002d80145070101c0034010102d0002511902860300c00222424004150005000c03a8001070b1f010700e420310b8800c5200210b0400010701648412844a01d0381101e1400010942600c43c541803182c1210001801e10b40c00312501d420b030343c041e2410000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 36006228 1250 36004978 36005003
    0x1e030109030e03060a112b050a1d030301081b0607020a0b0a030c05030105060a0f0207031a0105040c2105100314070905160507060b01030230090d080114060403 70
    0xc002d4644200d000003540240160710008540070b40c60700503160540580c500d05c62900c0e0403c280c8144000035800408900c0b940074401100601e50390181e20b00885810300d0005412007000711022848560b2800320140fa00117000400140c50045014102d84041250101e2003102010003c0e510b4462908000e6121101400c085188030383d95000d0102080075490420078150032038425070b180e000901c80c050380b01c2d10800607070750890701c901f12001c03500505004450a1580340d42c0c5030300d00500c0c0c40c6110b00302c6000350f40040049240c40c1c01200d042d0001410040148241c1001c1c20092140000b40703100030b00d0311840880c0c2810036923000304000b180c10500c0c841c0c5500c4202d4070ba40c0c0740c0f1107a21a2070a0242440e0200d181165259592010b10260342c40b030702d1519407141d96003c0540400b21105061690a1040c9100318044200c11070058800200142001c8031091100d0703503404015121500c5a03205640320f43c1c940c0d07080040c1b941520180380fa203120f801e013200b000030984d00c00d0f90001080950b2444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36007478 1250 36006228 36006233
    0xa020412060b090601020a0f140a0b010902090102070e0708041709030111070b0a0e0601060305040303060b030903090102010c050f070b040f05030c06070207050306040f060b0d0c1206060509010e01051e030109 91
    0x1401007024002c126034081440c0c0703a802c01241e98842c9280050015a0b00020b02c00014045080d10240e0511080581e072003100140c84000c61888240d208001e00c40e00010369520355a8140541c4021340a102c80509290034103860040010400800040c00a2041c0d4018a940800c6a00b662101c0c41c0c01002800358000300000700040c0d4005103003c9402c03080c003801060799241c50b80a0003141092813402070a0680c0791a400300c01620001e002607080c10780e6048041140244800150b10a01c420002142e031910090002800c50700f031980c4143c2086014001c248807114008102c0300d40540121098166488604244070717118480c40004089200c00581c01115900119a9510440084e001c1c0c81096540300e003403603140c042c2102e00900c407506018003080000e2240c1d004d044032080103031a244000042c2e50720180d000f1081d81060343c202c2d00203203076882000300b0780c004e0202400055035071000c99490011040055041030082900ca0101d80b0400000704034208441041c50400400038000c2e2400350 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 36008728 1250 36007478 36007481
    0x702150307030c09050909121c140601021506011e030e01090c0509090312040303050a090b01030c08071406070201030c0c080d02070605010b121807030209040b06090601090e0a050a02041206 83
    0x706692008a07004c8440059907240c40e440081c8100e150b40302034101c5503901400c084d0b090b400200c04000300000c83c021041d90b841d40707104000480d251002201c1c0d185c01c0400000e403400c0d0508150310184034001042111990313110481c044802200c06841050850560041e406060601e40c00005580b0301026a001c0c80514415501168800e803580c401e02d0300d40c0500c00d0b4076481803580e0303581c2d81c035410340105001074401c5d4816544403448000004103c0401e54560042d02d42c203a10584820030742c0042071010503020700501005007a8000c2414034003100002041140c068401c01906140d40d0b0700e89890210f020b48032001d6540c1e802800a40d031035a035820300d60000d40000350203644103032800c030010540310644402c454400206072175081c00740c1d907003d4041d03140c241120080c059034081c0315000070060320307000c000c80d008500c80e080c4500b007450048103200b50b15030014082d42c10050f860900704040c1c49000741d4940c1100010300701250340e54400c02100040c0c46550312000703c8000c40ca480a0038405d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 36009978 1250 36008728 36008741
    0x50c011803230301051905090f0405010501050d0f020d0503040807030819050301050603060d030e030d021506100c0b060a0b0a020a0309060e0604170f0d0f0f091802070215030703 78
    0x241c440d18003440c825804545060303010042c10110340c40c00c00040c003580c504480e00035200d030520141039034000d40b10b402060b210041542c41c50a8103003180300b0301c002c011081c0034035405408103885d43c07074550500761181881c03d11032400107801404075130481010720005104660140607003000710b460040e56403a00404640c03080c00b40318004143c241812116a2080e4120381c122a0020202401c3d40c80f0141008613500c1104d10403002d200400504200b0741c0c90038000340540342e20300c1c0c010f044401000c251120025100410f0b0394400e40781c1012070481c2039004620541415084400c81d1220747e54000414213006c1680c00181e11041d02060604025a00042c070300354161188e41d40201403a070360703841030303400f070114034141c030383c0041e05000511a4660080c00403802c1107490003154141804c03420380c541071045803064040082d00710105065046d0700450040f289411502d4081202440c10a200c410700c400002c2c0c941149800142a0042d9500e0f0081501c0104080180b40d40c1c0f07060161014008150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 36011228 1250 36009978 36009983
    0x412030f020f030301260c1302040306150501080c0307091212020d02070311060a02030714030705190203030304030f120c03020306010f0203040b12060d1707060b030c0a0302060307050c0118 83
    0x1802882000c024010060f64100da00a40c1001c1480300d140c0f9500d0405021202400380070303c1f405410818030f03610f40e41c030030155107810400103a50f5400c6003010710960b0341140100c50701d51500c41080107641d07800080c81ba80075001c00711781d6403039031542c001c00c0703c00c0c0c05a0f03070017040d032103034040369003020b01603801301c0d15900c0811a02140d10030700710208142e84600040c44042d02c1160500070008040c203040c8001c0244420900c1680d01d04451a40c6822010350b12020842c01e50344041501405c00400b002086001014842c501036010100d44c00241d5070300c401040101000340e8042c40c0000280600e43e039002c0107018a205203d005c4003000d00500a40007110900e00080314040303840681030021007150700307a03552004018681201c85102008401b000b50400c0d41000b038101ca62004290048a40060019403510865444a10781440401ea650944101d0710035040700280a019591380010003046a034181c4000382c80366220101075070907010385483c503c215401c0000102043c1c0c001000400301d50f1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 36012478 1250 36011228 36011233
    0x9020403150e0607090323070314071a07080901030b0301050717010f0302011403090f070305030703080c04050f0909010b040c03050f0109020f16060204030206120f16050406140412030f02 82
    0x28502c000c1d03648110036141d91000c0340d13140000340040fa070104244182c844412500001c4c580da000d07007140c40c2146580c011340e2145180340c2081c215050501130071005014107800030060980401e401c120611030790100400c1441d0004003c0d910707034080d40006a01d1040100204118a02004081d014800101c480341c4504020000030808074803104400f8107694040c0d455006148860150409541c80038040030240d21880b101680e071340c0404c0003054055442a805192180843d00d00034091503005425411600e2082c0018071881c0c4440c640e079113001c18100c80c1401030380ca6011400d0300400d022120b0a8000d41000c2041c18020b806400c00c1f806011083e0552200340e80c2d400c000f40403030181c1035561071101010800e0b041c0a014600e045202c143c007034200145803907a039a000880343d278020080041041c0403202000300082c2e01e914110780c0304800c0101400400d665460081582c4178a0080f4814040d100c1c0070b1b5a080800001036801401002407040c0300c4a58505002e001e48108007000300052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 36013728 1250 36012478 36012491
    0x20313050607110c0d0606030803010602031803010203011409040312050c0901020709090209040f080c01140703051e0a0903090b0a030203010e0a1a010f0309120e1306080a030c05070902040315 84
    0x3140f1840090515400010203130130901e12403400c2020300001144107460381520f41a022011801007401103000f0700c110b03002035582c0c122615800c03816200c04500f05110780d10500040002d43c0c00c0043d22500c10100700c503411682e542d540b60139501000301e500070010007842d03d003c004900886c0f600501c0700300c03401d0b000c4810840d130383c203209030550742c41d0800250040c0106011400003010021034031595441140003608081d00c0c0c0d8052400c4500c03d4003184c0041022100744100942c0500c05d15802020454098051148901d10103040003030103008030945a0741e41d40e4080501d4841d07002ca4000d040c4040079641d4815040741d004019400a00448080360541070114045a043d84155150792286030004000207111200540d120240e44140c1d4043c1a140c10b6468000b03984448041201405038a414000c1c82d13064082c8030010a6811000c20314520b018014400000006940712200368989049101c3c000b45180060074046a41d21621085001050120410a03503110440e107013540e4180401c0381 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 36014978 1250 36013728 36013741
    0x24090b0301020f0915071b03140a050601060e06090612090d21020d09080a0201090b0a0905060c07060b060304030804150603080a0305060609030d170708090304060e030c040203130506 80
    0x202d03c60b04070907000100d010019a006401c00c4500b00340b104e044900c1c1c1d542030200d2078031030510240c4a540101c200b00398007002882000307030080855040d00310b4000200b2a0b05510355a0399500c001c180261418009601c2c00c1e06003960315101100c0d6011006042c290b129a030170842d2120906060320320350898040c0040700c0040511440e24841d8255100d0043c1b030603141c0c00da010f82c00941c055042c5034103140d00c440d80c85002c1f80c0020b00500070204c3c0d5600008407400c650070320849001000d480d1080e06400c10b078840002ca500082c16540010111621701e50741c200340c1ca401d90040c51110440c40d00110003104000605410200c904d20031405090414030310080c0c024410201d407498000105500001d11045410501c640c1c0700590107000a0700031031900038500c000a20340620450f075000001c031549040c41064200e54031050308003960b4149807132641081d102480c0c6900650250004011840e90300d040c4503541002440100fa001410442d941c0c02d00c00a105800a00c0c01d100b03a845105280c042603d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 36016228 1250 36014978 36014981
    0x10911011b1101090b0301030813060f0504230a150801080d050f07060e1c0e0306010f030311100204170c0102060403020d0c080c070602010b031005160f020124090b0301 74
    0x2a0404900416484080385a844509002e5003088003070400541c3c220114031050948010340c0030314012403030180c844850740449240c8010a42020007044080b440510980d50818160790581c0d00c504084082c100710440c480c00b5180032414a6640040c01440020302c640408019007a000d025075188005a038a0b8008540d072000004103210003d882005414540701c1040e000d4529284240008240310025154240c60301c01e0030b0812011059289031740726081600040d005640410990281c1000d6150132001e29003480a484041c0900044c48000b400b110380a000200141881000854599844640e01400c251108900c1141031055800620349580001602403080398540c1c000e100c500789941d021a011401d800080358220800d00044061010911901001e04102e500006000124504051130440e0285c3ca2404962130442070002140340c480d4280000c0900b820400e000740c05c0b08030102c1c01030482d0800340707000303440c64602c1400b01900103058104031181c1807420f206000c3e440c0c08160 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 36017478 1250 36016228 36016247
    0x18030a0206010312110a0302010203100501090f05040c110105150a05030f07051003020d14060f0901030b0f040807021c14010e06010911070b070309060615050a11010b030a0501091101 80
    0x2015a102000400006040f50801d20303080c0c1d05858040c001703500b48030040e8a001c00c00b081c00c40c0540d40120400106508042c0448020203091a01c0e184492408900c1000070b1901d02409006039102d405604001c3e00510070300d494070107044000c115034549544030402404142c25a284114040b00000507149800501d68041011203400b030031101f0716041c02c100d100b0100c4048802810780900c00307050690340354800c1c5000044010000112031504004106000054820882c81107540c1c85c0144007103400f0240460b4400150b1001c4005520741d818100b2035401b495030025442082507481150201c10041d5000901c0c0c4a040c441410105940c505403e1f1100781080711000c5d4403450041210a0564100540d91300400224604d011100d07114142c228104652035400f02e030f2101250030030070486128000080c61040254041744c145103800030300078452400e182040100074507104007051000e50140149031001021141506034510340b0700d000e01600302065403401c041c2528641d155000700d4528 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 36018728 1250 36017478 36017497
    0x2090606071109060307080f01020309060907080303130309030209040305120c0c0c06072307080705100c0201051c020a11060a09030804020111010b09040311060601090f0b0a0e030a06051803 83
    0x340c840b40e041c0107000f405a00103000c0e42d8184a950f0300010800c00510102c80b032280f070f1800242c3e60340361021941d4a000d001074103041559001400c10080740d2404010f580e008420601c1c81e005d25007403401c0440e0040d11641000c1d40c130283c80001c2c8810160084018004000d01c2000100666a142a1a0041e00400c3c021b0700071900814001902c5140a20050101c00d2040411814140c40c4500705111050000000348890380314450a1110724007c1049074000c100450780500c540c4406800180b00c548d664074002d040c00000701d01709074a09201d08104100110b0340c0f80464880744101c1000f070540c0013010f2710503681c5c0200d40106a1002c41401071501c0365400d40c48910b080d4039607600440e101e1030f8030040315102c1d540c0c441540d0350560b10301690074003641c000d54030060703912225640b140c00c10f01c000d00140e040c0700c04007200300074402d01d440440301103410007120203072038a0409200303440350500c40c002c1d680d041c0160100c0b081003100982c06180603074506000340700750802c03401c8842e50300c5c401d04054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 36019978 1250 36018728 36018743
    0xf030510050a0501030f020d1a0913080f0309010b030a06020a1106010506070f0c03140a021203030f0a0b06040f1706180309040902040b03030a1e0e0f09040503090604030506040209060607 82
    0x74015035004e9004206c500b200d64400610304000080b1080803107e81090490590030a036084814910300f0300c550300e03045180300e071030181000350315a01c00b003507032180e03c00010a846011000807136610080d44080c210540140603541c100146103801d00080d400301c511003000c00c51071100490003080c0000c600c1e05aa0380070300004d02c1c0c0b1009484018408048044c02c0798840410030021001519214900703040703010100c0282071901d01481041050403043e80181c031207910610800081001103100d080d0800e1f2042000a4018030740c0010600d684119001603d280f131605100158903c1c4262000560700d07004400d852031603c4e2002c01c4601d0300039003801c0840c10362050104100308d10340750303000c1411a4402040092003002d00c50100e41590894008400801c00d4510840c07440c1c603181010510841c16880c005401c1c110480c0000c48409aa00040380911102d400140c20002c00708101e541c0860010006a00c03507942c2d16180d55500001c0310220b01809030200030808605151040c0c82103903034007120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 36021228 1250 36019978 36019999
    0xb011407020d0c08071802070506040f0c0b0f030a0f090203070b090418030305040201030e010527030c010204030c0311040204062c190302040b0609150d02070203030a0f03051005 78
    0x559004054240d030301602c0714207140000b56031603101100411003200988611494000122900d840020384031040c2401082881300148001c55076540c4240d1203131892910208030304190511b48029085a054203100007880c04038020000c0185115006509051200e00300350001002a10502023000750160711015007440b000405001600303800001400005000310760304110004040e001c9016030129944400703000070740d60f140c0100050890110000d02a0b030400d01a000c1c10229214088510f01c044103031040000e4000f4003c41c1c40600402c2c0080d074a803074981c180b40080707920360300c41203442c0280345c00640c0048c1060b000740d804968185c0c83d28201c40d150080303000d00340050481d000c07610a4840209108035039034500a40c20344250041580782a6041d44140f1045400a91503240b0941c0103200544095880b004c080c120119000072898031451109c1c0d02c00082d018280c0001d515000200d000070407a0b0380080701400341c4070540d60501c59500d6601080c2025042c5009a940003e900007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 36022478 1250 36021228 36021257
    0x1407030b18012304030e030114011503090c0308040509161202090d0b070306090e0a05030f13030f03120c0f020a060b0102030f030103050705010e01080c0406030b010e0301020309100501090b01 84
    0x81c020034580604000210380741c2c20450b0044015a05804031080e01004107082c4024103502450000300b40c003069000308401c4071103c0301800b1a803014444c242c0e440d010345052000c441d00c00e8010f4550715500c01442440d05461f4904644d82d60014002d0600030407500c40043c50503201d040f4050201003079503c0d030405502e90304040c1350295101d480f4041d00700a00640483c00150502c00c02881614103645c00500e090810118100391184160060000c0e40102544404690302100f1104140007043e4440c0e940c86419103204401655036001a0850310860b01d420103054100d01e040c80328943c2240c0070410001004020707581810b4441d8800c0050748500600320000700e031070740004982503050048904010108001c1c80c0c03564802d0b0001c84c2d41d50090b6500304110750700056541c60129090900105a20b0f1240904425000d68401e80003010380700c100580345a4095034003c0441c840c094000d41d5a803501616080e594142c801c0c0310320010746040c000086200180c0300e50350900b04142d603615584100d50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 36023728 1250 36022478 36022501
    0x3110a11011206031a04030e030102040b040e040204110c0c010207060305040809041d0a0501020c0106060302091f03020702060307030b150307050a050309070521060114060702010807020c09131407030b 88
    0x31407400b040b0740c0c0c0c0c43c8008004904c40034001542c1000c3d005ea081902e2400d0301e0010b003d41c0315030500900130381c010312041c00f041081c2400d64003aa00340280880c95580c0d18000140036003c0700c0355950818000040700340c40d02c00c0100c0d681c9000202a000c80b51030b030b0f41d01c4208030308883d821030303019000c2d501c241310044452419422003150309520203420021034440d000000e0400e444c03403078103e0312a0b46c00100c3c120410740c00e0042400400607810110700342403611010070b03500840e802c441d04090b80391005225000e40a60f0690714142c2d00503020fa038031b0745030450024001f050a0b07150203102d08090032002c4040313001e510449204400581e5070741d0804e1080d81c0140d0726a040542060301c00c0c060f58030041010380b2554a220404c220242802544070100a901810000d041c3c00c40c00300303a11103000c2c0e200c040d1110812240320070790a1820040070b40d558070040781084d51078882e290b07002e84018144540074240700000130032680180ca25003902c4d91101e050382c2d95100700780f0008083c1d06511000550a0011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 36024978 1250 36023728 36023747
    0xf050f060a090503070609092304081606020310050405100819031407080714010207050c0f0402130803030702010c0203070b07230c07150c0201080a0c050c0a050102040303110a1101 79
    0x25040c1002030310707101c0d4002418850742c6c3c0c0046001610242007080124010f01401c002610411402e038801261940760b1600903e00400160142000041000c4e5910900c1d4100c1c100782d82000c011900c0b8142201a080f00c1c0389103104441c400c60a0402203114542031a0100d411110300c140213220318042c0c220b0410500300c420800f54180004d2183c84a103400b0b0440050401074820152160340f560784d442c11400c0040343d035100050f560705c107121400c00900002050300d02c1d0f600403a20340b00644030200c001000f9200b40002129407100c4004002180b03038001000d0360060303a2580003403001800c0d10710100da5174018550040c054080c00e101103003590b8001c2203001b040c5d04140c81c000d40c03034400207580e0b0b920a80c02109201c00990113020100880240e51448000309111342c0343c01c011078046a0002000f1400242503000040e6450307030300050701c03401a011aa030700004030703050721364020060400a000350400e10041c0c001c1031442a11000301c0c10003150824036140e01801d0348106600050044484408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 36026228 1250 36024978 36024997
    0xc0705010e04060509010e04060c020d020a083103050c0d02060f1303080708040306050f0415050613060909021009120605060d0b090a051204080c01030b180903070c0f050f06 76
    0x160f540d404222900c800010501802455041c0229418146826021074001240b5401150041d0503e0b600c0c4d150702140c2920602c2d0026521074441c40c0d10038003260f82410550280d84440f4511000302001508445107408a901a2041c0d42101c80e085041c001c04205891009502072004c1040710000c0d1345101c0503011009010022110450b240c0d80c6008890744a2801519030703810120381001045071501605a02900360380da00025030609503600c51503c8502000c10740c115841e04005006902c8421015416451000040c03040a544a0b1500010400101d080c1e009048a070f500424150041c4038020403161f0b50203106042e10b80c140c54227002040060f190310b40c401e28514140d0003140c40320050b203024406240161031600c1e940e207452441c200302a50f20448a00c030602c400c110881010909005109080c2008103214001e034002585041d1907420311303000d15815a09000c044240000640321603882422043d5540351600c0700115012120301c40e00d030b404905080000c00038204a80503108154 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 36027478 1250 36026228 36026231
    0x1b060f0c01090821010609051c060902031603110409020102030702010c0501020906070b0a0509060c1e070209070509010906050f030106050a031506020f0d03140705030405070911090a0501050c0705010e04 89
    0x1c0207940710300d01c5078811541c5280c12444000841303a00b03200701c05180c0c0104a0760826804035494000071486406103413078841c0084041d981c2440502405401c94540e03141d004080c0c07413552a00300700c1c03c01940c05a00080d90481104200545103042c03600c180e05800d42c0503001141000c0740703540115040440174108a0300341d5024001c80c20262628405050020302c64148800c203803801410010490780b000b4503a0503a41e002c80b0901c1070800d040401c0390036003003c49402d292004600306101c201803081e540d009401420010402552030f5012002c2c000904099a03818680c42d941d0f41c0488443c041d1414207106c5840070001044820f001d00001d0017190341d182000b045d40301170b003880604d03001c0b500c1c3d00020141c1c000d078044600350101800259054170150030100201c0254440302c0409600040182c0c041c000008081028488100541c6d00208240c40080c46071850b040040d81c6560000d0207144d00030701e44280007080d42c5d0301403400d44814090807001890400c0c5001d00444099800c0c58503260041d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 36028728 1250 36027478 36027491
    0x1090b1810020a03090201080f0601080a020309070e09030d06050d20010306050301020a03050a06090905030313030e091e010605040b1804021e030103020a050a060f030e07120b04051b060f0c01 84
    0x14160b001900404203240c4000404000351300000d4840e207001040c15402c1d29844c0d003082a2681c00c49034594201c0c001e00340050726651480c101760324000041d004410307910340c00020422a00030020050205c980c40660034042681d030303039043c4400881150070052282d940445e0344c91144015500c00404c01c00705240202e40316641d10701081c01c91703100d040d004000075159400c20500c41c0d034a00903880240440b0a08110a100307903203e0a07181d0002505460480309080c00c2201410f208904198101d0401010010103003040904006440d12410141c0307400c07031051000049060041c01641c080311a031284a82c070b8101c01d60000301008080780485540b0035400d0003150005001c800841c91030080046d8419603950442c01007100040341580424818041141c00b4800076901549440884d02d1a0070301103034914408000750300b01507203604110480080c008200040c08901807106010768005c005a40180050380419000702030780303c90441c2c100c202000000c0e00002c1030b10080c09610035440000030b41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 36029978 1250 36028728 36028753
    0x1202071206050403020f060105030706080406020909010f03030806060702090a0e0a050102030106030b040b1e130b040c030504060c030c020d050c030c060112120305070c0807050313061805010201090b18 88
    0x100300303110800303450455036141000101a01001004d030030119400c000c00e5a90300d0840080d999854602426040002007008641001420740564540c40070003400741d0003540c0c5504020640782c2c502d100a9000401500c0030038103504101080b141c02540190802050760b45420000b8050710300311910382844c1c8600b00030040890400e03c0558043c01d1580c1c0c010a42110000c00c02044d5401e954031244100150b03095041c0702041c5461043c0748c45000d42d840c0802102a00f404c50041100740e0006801c1400c10b0003196400780d050780032074840c5205010400c04040b402d20101d08031054604e4241c007582c400791900445a018101404940c071071407048a2802c10000308480c00c02e6801e0b88801c8078103441c0407070791040202020319010ba0031050300d0200701c14900389d48010030403030001502403d400c1000501e4018841c061003200d0350036038801c180c2c0505994400004081c1d0381c0c1214400d642080a48000c03da42d0710600507205616041252080141c40314200100411f16000d6101c0c03552041d6481c24a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 36031228 1250 36029978 36029999
    0x5210604030908010b060f03071413030b010302041a0a03081b0f060702070e090303190e061e010911030402060906041a281e140d09060c0e030307120207 67
    0x8a54801c0c0d03a62940c02d031503c140182540c4860110038812074040c0205840700490f4029642d01010b40d241c90f408486d440008482c0074402d120b0407807403880e00340b44080142300d01000d0240c10ee0b07100791010052403005030400c0e41c1c03c0075901603c44d40507282110030404a482c010191030200c01c0040d0380042c14030810601ca16010400c0400d0301d031a08890100300f900f46d0180014030040080c1d0903042514030700480240e4582c400108403180d0584074840c280c0c20a511944001102d21807802190007608180c142110041c45074658403030000d219500201d0720f28814010481c0880c11400301c2415525651f01300210758004002180c0c0103a814400000d20303001143d02901803078441140c266980c50500f1140c0b601c54841449480c1d042c0100300c29241c0e0310341c002700c0e01c0d03a1070362612003800f00e840c000c10b01241e6480d84500307030b5061090045503080e2078550035800343c407405110b00d00130440c240c0c0403642039840c01042e0104a9044d0424001f8201041340003080d094411521320654044e01c0e10340440c45c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 36032478 1250 36031228 36031231
    0x3120c1a041502040e0a110705060103060c090f0e1006030c050409110705070303050408060a020304171b030d060906091419140403030902010206130b01090207031110091a01050109052106 82
    0x80c50761030b901c0203018404d1b54520a010a030b101d05003c040c035010880c1c881c41d6032490107101c003e0410703a580c0030041c81b140c858601032002c0d2886071441101c4a40d54181404180d01c25511404a4032a00c08001002800b0784141e80c1c0c1003005445050805180c40c41c03210062681c0910008800d40070006000081c1e401c0c403c10000e58402c1c0c031200d07103941c00c1c84044d80c600800108418070b82c41c4104148000309410b41d23130f0007250305800b10210380c0d2940d107000c040f8207004031000510014803012540c000d0701c9025400420945201003000c10007a96500e042c01300380c0303040c46008150005030001096660801c201190f200b4803003400003041c0e40b00601d25080c40c00104540940000b903454541d6000c560303050100701e411001c080c8182d8000082519228036000c0d041c0300b80303146180d001038888105802391091480017580102a00c052020307048402015159a03a0102c0d510018100d5090450403160805416100180c0d2828480c50402080c8100c081001d482c10101d8079010707001c018401c0080001d139 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 36033728 1250 36032478 36032489
    0x110702030a0b0f0705090f06071b150e091006050c070e040305180904050d051b0601030b040b010f0e0a021303020d140601080a0506060609010e09040b0103120c1a04150204 75
    0x210390342e240c01c030203d0a403010040e015000b004010402d03082c550b44e0702041015184402c50748d40340d40d000c140c40c0000a1315940881c28248111401000900c200e20742c04000845085488203a800f1304450104544030703e0480e1900040600700e8018056a403207803001d4800700048008950b681c41c0c0b80d0300c4030030100d18201c40840024400150000f0042d0784034401c0402c010041c2c0d65101c503405c05544007901c81030700201c100100000070884084130000c45031000084060042503d14a5849080070004050111030544140d000300000080708143c02c01c280084942c0d115880f016512803420f06800780d8444040780f18075510018000c405641d0715002032042600c155295160940b038058214108074059000c00f0640d00804080008100080b0340182e1007102141d03c0c076070724002e00300181d4140003a8503031140c10000780d508100c100954400014181c034058100300d0b08281036139004841441c88101c000f4041d50034900d0281c1c0000b070b80800390360028884c407024420120903204610480e0046d9028 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 36034978 1250 36033728 36033743
    0x10e090108010b1009030b060108070306050604080714010203070b07050706150b0702010905030d0c02120a0b0f0a05010806070507021002151f080303100e0910050a060501031b02060a110702030a 85
    0x100418500000006030045060510005c2d040c07035a26021000312004190605001d403c10000302058840c0d40403201130032004241644880d1103031300f52541c0302c03141d000d94420091124800c0342e0640c0008240e9918a610203e103462a030b0b51803d0071101a04884000ca46142c2c5030b0360300b9003000408031f0002d00074000100e100c549692440c000104544504c3d1720150180d004503941c01a15548860b620004c26015104403010481644040d486e0608a01b4058840b0141e0010301040710000c4850300e001d5201c03280c0a002c966200e188454a4840903250900442e50400c00030005090044d07407001c4021107801500c500648070111002003a404445000e07c1007c16020f8185400018040202412400c0300550461805a84003c02407110703000b1110b407141c480c07002480282040001e600c0c1203040080c10300003403c041819201428140c00b5030350103e802c00c560300841c044900803400340e80005034010f1169440e00c00c2c005c4001c102001c440c0013400b10800030f480240e10200106560f03188174164 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 36036228 1250 36034978 36034991
    0x4050a09030206061e01210f02040e09070602100b01111b01180e0109091412090a0b1603050c0a0506090303071e0c150603060515030c030a0b0114010e09010801 70
    0x10003e0a09400800003031282c0000b00300340448644c0701110020150080c20000d80e00444c007103a0892008603080000c1d021814200030018081c5190007600495002c1344902d00c0c82c0c1c807000d04040c2c81e410300e801100c0041c0e01028490280c141c0030f0300700c41100041070401d80d0000c0d070208002ca042c80a94845144151813044507000e00d03507030107a00901050995140d4922907428181100f101217010300c0b401c0030194403500c0d44070501c840481110b07d8009881c04503003c3c0b40d42e240c179205880d0000760441d840344900340e400050030a03000040b40c410100b49894031641540a6609440c65040824021450710400b000000080c1c01005041d001d04500c0c0029511f80c50409001060100401039101c8680c5042050001031030300200880112a840064010708400c0b00c81c591700100b456038001342c40e89041009209030b054003100304d40444c050603070035100d000c05a40b084c151b8072500150300900300c1c4075000c0100030702c201c00ba007028a803030300c145800800908a41d0024a01301c1c020307003149000385d54031395 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 36037478 1250 36036228 36036233
    0x70306030516061202090a0e04020102010e100c02010b0103050603060f0406020d020f0309010b010905030319031503111801050f09040204020c0307140f0a0c1509080d020d120501030b06010f0e04050a09 88
    0x404c07107000f43c0c8006525107006500400c90039544ea1060f4100d4449074000721301160300070741208800401c8001101c0030320f80c5a41021015040c0700e0300392030165190a17001c4141d54841e02405105010144c001c140d04d484010f5980c00b00d1f00018415201f666092103c440e5144543c00100348500e201d413032060305c9007015600c0508542042c02d0b00ca0510450440802030350700d012041d13605203440c00300c80d00c045510320f840c240c0142030a09034144c181056450080308000d040e0103042c103001800e5030640c03503da408405d400a14031080c060039a2000308070015031a2454140c01c00c6600c144007920150500000e01d98013843c40e08140701c101e691103100f00603462040402c202c601d44130b07182c2c1c100415228060791038155010040c1c0c091600c6414044d0401a01d42c3d000309a00401010100300300c4d082c0031664940292524600c0c820400040d20382110296980e41901070a81605d0304948421901e803550f400548101290152000a00440c0381d00c0300c41d1a0399603c40c0a00c6210361030f0022070029030f80d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 36038728 1250 36037478 36037487
    0x807200303013002090f0406090605010e040302100501080c121203040b090d1b02061b0a0803180102070203031909090f2c070302010e0102030d0914060105031b04020307030603051606 80
    0xb920010500e28980043d2400f5950700c2030519008030356030250755000d031118100000600ba944002601c2c80c2c0c10b0600025183c91250b0019210354026401d13160003c101e032000070181d48003031188505680c019040542a46070000c0c211006500b02c000702e420700081c6500c00c41d003d070402c440644013140e05e001000010f1704284440050070800e0300e8405209100512609000344500304042c0c020320000c1204150b484c1c0404dc3c8002403444002101c084004500d00400039610884601c040045602ca452044007014001d682402d41c0c000d000d54204a85910240d9004081241d0642004040c00000807501114440c001400f0f166507008580c0d20720182e69100440c1810000002860b01c146880000390400715107030003a07990901e40400d4150b00400101d25500900b2003d550681c94100381008000b03600d9400703881c3e0703005441a075081d0780c0da4008050700c0e0030340000e2601e04561545840c4140e03280c240d00139039000c03c00c1c1c200042d8480d12a110a072414603201c040c10014901d0003400e00115810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 36039978 1250 36038728 36038789
    0x3060b0f070b042f1311120c040510050d0b01090e16090b0d0204170d020304090f060f090b03010605060301050609040504050f150f090a03080720030301 67
    0x81045289000440c4008655600c20040007600b07600014011400300214a0043c592840998040c100140e0500c0150511303c070040c182d00c2d10030880c009076080d400c001405400104189403a0107420103c4032480000e4100004101e030901010400022402d40d4800700f01c02a43c1045039221906e420001d4031100849800c41d04040c1406602c5000b04107101d24081601d51020401c03880c40340c400d100000c1a95100340306d0f08114207040000c107a1300c0080110f64040c08c00c8401095110b103200f81501c110320340360740c540104000180c20404c0184a6805590804420500da0080005c3c80039610081d410a440c419002046417079125014107001d864240504c2c4041c01044444031302c3c6516020002e030680c89103400d218010f90b00c400019040c40010b004405600207040107490320410100700316413014000f241d2481d00c1c0340e420004582c00102c0003071840e00103941602d840351151941032080e21011210381003200d200d801145a1400f00d0390501c0614001c206a013081904560380b20004040d0407030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 36041228 1250 36039978 36039989
    0x9020d02040504030909060e06090c09010306091d061506120403020703080d0501140906010207050d0204060b0f0703020601081f051f0312090b07110d02060f030c0405090a1505280905070306 83
    0x480c14800d09d591250041508442120103490f59008020010380280c0340c2c0d5848076010f14074125041c5804410a4141400b2003200020759000703a0350b00400403004000784440f15000304050000006801e656a80990420300038012118420b5403545c0d00c521380c0d4401c56000000da03445500410019130782070350084010100b100c004c02e184c038200c0300007590348016126103880b41e200f085452003503460715400a0060100456134075a580034904060b4141c1d40454022070041c4102c500000300e4100102e122207004003980d00d100e40d8502d00302449005400c6c060700700128a50980746c0b110040c0c10300d80d0050011840b484d416240161210700103007405207036a0010312000803c10074140000c03800294078114003002c8511030021085400403030701c21300802204c807124103000414051a210703070300041c00481d02c0443d5108000c0c2e030354160130b0301a18007001045100c41407100007882146000b0754038200c2000c08401d0420b41e01c8814040211640301075210725480e07076441003030000c0ba50341805144003404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 36042478 1250 36041228 36041249
    0x240f020f0a08030a14040f0201020c0109060c0b04030306080604030201090210020708070902030a091202070e0c0c0303070f030221100b031902070206090405090303071107080d0309020d0204050403090906 89
    0x180200006500c50012501c02411840000006a0740864076401440d074500d038004a0001032410f880c0105689510f01ca09034098030551001da0380740e41c030903400f500507190306944401d41750400e56030304004540040e0003201450b8075924041800d52003000a40c3c40743e40654000715803602c481c01804002c1c0e8940f0350503421504014020b0114200c002510003c48220b860010382e260386156681009040c3c081005041400d2402003d80701640058540180c0c6d05107030750b503200e6440781440c5000c40d01c9144200301c10794009200003110a07000744600f40040140f81005894454a020075621403003481295840c0030b030040003800b9202d030105201c040606800000ca5182d8202280c0780007140c840d91801c3d007056500080ca030003c540395a801c0d01c1e60704030082c1091025040c07007090740380c8035003086030044006001103a40398007840c0c0000e108070480c5c0b40200500307012480350760214040c1511200a07030b0810060590702005880e03611030684618001e555003000305003080f00030070030740b6800c0d400780e0400f5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 36043728 1250 36042478 36042493
    0xe010b090a021b0706141303020d05030d060801020403150903170109061d0702300a0906030b0409080d180c0801020405190e010509090f070801020c0c010305010e01090506030304240f02 81
    0x1030700310150f080c000c480865480d80340c6404902030384c070007c3d50340c000940051403c0300400822070000042e024140c1c02c50000d210f1643c55003500d500f01d019512014100000c584800c066000c041d0f070201109500070300c0c0c402c80c0c5000c420040518920207070b000c03c00c6a561000e00304603a46149000d82032040846010b4026400c002400075610070b0318000758800c1e4220868040c0c080020310612640d0306a6044000381c484000750800b1700007181502c50500400e0411030581d20a2905116001d1250381c041c10b010706040a10760084004d22030844031581e024415003d0602107001c41300000010910300c1300141e44d550030017080c02000410031004a40e00145448140500000c06008074155101a00d05039103a070341d0150001d150007580703e80300a8a009484020038020419002040e121008904035032003042090f00460480f6000d209801c44646044014040240c16403c0940c03c2200102104e04094482c1284042445c07451800980740091404410203590002c1c00f00d400b894083c00078203040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 36044978 1250 36043728 36043739
    0x10110f040302040e03071b0f08030c0a06050a1503080415050412081602180411031b040209010509030d03090215180d02060c010905030702040e0d0906030e010b090a021b07 75
    0x11400345020091203540c6600280501c0300003081a10800da4000324404280450b20007103241c604524012400718840d85ea1000c115407074000110b50340804050000e200070300558a443c1c000b028094200210152201f5048a00c8000d151100c8080c1d030080c901c856880345060024400040c000e00c40700148207060100b00600300c42030b015400b1054110184a542d601c0200c581c80e81c402c0c030000001c0d4011402d00d200c600141c03818200c40d06c101c0c0b00d010f0060104450608260b03031090341004da000000c40030195000ca0381429000b41402110604056091130f42e00c40010f410301c2d0765502c400e80005d40e00c40d20001549881032020740d040001c20000da00d41900400c44140c18079203c0140790245059802da8000c64440104540858070000020081c9041a103491a100c7c0d008041c203034410345c1000c1c1c3d414075180c0003090f0380f6500c03803094540710902032074020158080c06012010003c25562840da002c40d03915400c40c4d03079208040103080103a44401c0c081e403418030700031070b01c0c2c0c1c00c803e0390b000d103030705104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 36046228 1250 36044978 36045007
    0x303050d14010803071e17030f01080f0c1c0204090302151b04030f020d080a0504080c100e0d06060305070b0912060906060103020913020f0a08011202060306040905010212091011 78
    0x179040d0032000c8091003030000880518492031401c0010140da030030710000c00900d090000514021211a020880e00c0c0e6a161400d0f41d0310032041c0d103510850380010840c1c80c1c0c00e10b0f000b103c003006001c0303006140341c4607d4542c000034122500c8540a5000d42c1180c011404402a60441741c3c0e8012400e42031145100a505582100b43c0078602001300310103807c0d2454001c1d076469030000c00259074800d89550b59141e985d400181240c005202c0c551240c494007854091a00d010307007200d01d035009107654048904034100304202d44a02d4580054030510340e100c101001007a0140090b1018182e850b240c00d6480802505100c41e038100c40120001940010040c060305190104289030071400900c0c0c050f03101c010000015400300c062050494005c3e1000500300841c103e42c10150001c4941626071000fa0faa8900c510201c91151f080000e601c058100b0000c0e20900d030540c4900010750080c1d00060030910901d09907844c40a082e1600b800980c480c0d00c500c45a0341403402002c03100050005601e0070245a51344101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 36047478 1250 36046228 36046237
    0x5130306020309010b03010608011a0402032208250b0109050f070f020c0306090706110f030a0c1e0f05060c04080304091d030d060e010e071b050c0a0303050d14010803 73
    0x20310698000020584a1000350080150070000070020404540c0d18901c80740204041a00e000404c6400d4402450518003407098900c40d503400c20003c80c042081c10211422200742c0708044070000c50138454600e17903202d0f00c3c4a0b50900c0c8007082d000003d29040c1c0c103003640321002c1684040510b50a000c1081b021140361005240c0000190511141d81032445600740e0800c06040103940e018480d80c070400102c6540096004200c8249460341158242c04115403501c6454000e58000740741d100308280400c80d0300c03030203890300e0700c90003005800f1a518203c07009200c11940c0d81c8083d245c1d07000000c2d00e501407280a12541c0d4100303c000c95180d140528008005459004502c244840300e40d40e000f03056860b1003804000245d143c0300700140caa4680c82c681c0d0810080c00140514941d050f4800d0001c40c203021507a058500480603a100c4032510208400c01c0322040e0300807035003114180034066400c1e01988a480004010350701c00e465040d02c0da01090100c804442c200c52a06c0e9011401c400108010300002c011103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 36048728 1250 36047478 36047483
    0x51c050c010e010905061c061a03070f050706020a0314060a0f0611030409150f0812070803100b0301120204050f04020d140708060c0c0f0109080f1305090c0c0d051303 73
    0xd01d002e036528070040e1185002c030b62250b43c200d00c0005040c0c1c800307074000da0403500c110f1400c0410040140c483c800c41c8114102d000041110100030004101018069012010032100c80d00e8880e140840b5a0380e0401a40c00440044020a407601038880154680101280e8495800d03a6034001c502e10386040803070580814800c207801c0c401c1381d5908050204040c41164003411504005104a6207070481c0030209070854420582892044040858003c802184200c030700c44c100c94055041c1202c5442e5468540d1010746081d002203005d0a0001c0c0001210000e14024884500c0c1940a0800350045c0030540b400200f444507281010400c000050365003404450070070381c00030058481d1801e5075102c90314003221a00324140510a0b0f104100d0100010070080100b07110a000744c8501920f40403031582a0f07080008020460300007480303801c01140188000d030400c84100520000800d5035000030603d074000545940500315000540d60b80c1c810000c100d9010303c0c44891414a141944501c05030590003243d0000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 36049978 1250 36048728 36048737
    0x8040507150c020901060c0b070c03080c0d02070507080607110f0604030e03070806160f0305060307050609010909020f030103110105072d120f0e030309010e0906030a0c080304051c050c01 82
    0x5022000d4403550b032201d20940c1c0030f40036460380c3d61142c130058905084c00740708407a25106140010407142c894254864002d40c10b4030b42444580721803003050302030340007211600502c035424400702d000b2900420240c001007204801500542c205114010040c40c0c1c0191550001d5010016078405074400040f100d52041e05803515508460340d800008bc2410a541d00040300e034803481c0c00b840700081148510022004060301d44152500190500383c06840b000c0b00d0b4207605400c005030420031414040c008211809051501c0b40070503481d104420103d8004107400380c070b07001e000310040c001c0040b909810701102c0c4003401d2007810402c49035036034113880d4040803c418001036000a000803a02c1c80b2198401070f45c0c0c2c8004681184403031200c00400030240030071110006030070018030441d079003030210490b40c40003010307940c0c006c0d240015014011035910181a607070b0180324181c04c285c0401d10344810040a401d91201451303445107004100322500d00300b052642008203961016a0005000150541e01c2510a082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 36051228 1250 36049978 36050009
    0x50f09060f0a02010f0507080402030a2a060206060a080c0d032a050607020c0103060b07020103110c070b040905090606010507060b040605212107170c070b0c0c0108040507 75
    0x20034001d014404064000d035101090482d11942c041d0410311007000500d108100955962804564000c2e09a401941580007906680049241082088044076404c0e41d1003645001c040d0703400600900d20781c41a0700680082c810b1194a01d00071f540b110090946500900014650340000340f40d06401c50401414007800340804601410b01d0900c011404550b81201d980c2d081d15800c21a031950700c12501000180030740d080e0750000703601034854002580d918920f01400c0280c41d0b03005600809280303c000002000a122075440101c0c1044040041c0500c2c1c2c00098603a450490880c050f5400a41a055950800300c108841c40e42d100007030315080c1d82c1200c1c0115411400f0b9003ca00100111382009402000000700d15110740701d01400e01d02c03480e0221040f5000d021604400d1022650b99000700d1000e0081000440007280311249040005819508528680507001120510700ae44a600118115001241502c407000c41400014415442030821070b00625040d99000d40300e5000d401031440c2800c2000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 36052478 1250 36051228 36051247
    0x3021203040c03020901181d030d090615080f0708011a0409080705060a0509160506090402070c0e01031209090b100810030213090b0903070f201818030a050f 69
    0x842c070710300840e0040c202c1502035840d81901e64401321a22001ba110714209a0394030360881c83d44c0c13032106150308110060745c10643d51928141c05407200c8034045e500252901c07204480104181c0781d05004210300402424059540e83c20035007041001d902402040c0d2501401001c02059010703441036006041300e0000d20800680b900216500880740003a0103840781404200b04115194800c501456080f002c50304030501020000c0401e64240c0100d83d0060001e00000d80d482c1080e4014000042c13150102c6010180c6403142070b0351002d8240d00030f496000341541c103400c0c006c0e00440040007505480100b40300007061140401c0043da040340804007004803560004010701100b001000140d580200442a05083e048055014100b24031041e10b8001d500c4012540f1b41d4000401ca540300c55104800782001c044e1501d9014a45031620f4201e001101c40d80400181e9a5403041c00b000560281009500d2508001c2224035444041d4a00b80900703600400220f02c2c6660410300b80c81401c445110442d95071000c41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 36053728 1250 36052478 36052493
    0x41e110403120e0d06021204031805010903080903120703080402100305090a150b0607060e07090506150c01110f0304051c050d110403050109050f010c0509180403110601060c050610030302120304 85
    0x502c0041d00441c808209940290466610940158001d984041c20ae800b130314501c5525280c9072040340c1c0410784101e4100700003008000505200300300101669820f0200c0e80415000d0303488000c0450018605004000843c50481c0d02c03115074403500d01d01003025103000c900031541d441c4020405800780c1c1d03a144883c800c0600c40d41011001d4030018001580701e90301854184003a1002e07520010141c021414003190180543c85618400d180040009800c49003980000d6101d038081a0820515521200080c22200c804001000400c0100b20006d42c0c81c0b030702e030030024140401c000544100d40e2901b0800001c081d4401d05031000001002c10002d850501610304c00100c0c4120b038401004c5508040d2040c0c18098040780101c0c1c825010b900038440701c0d40c035a00c01c8610344545512507601c40c8184c403035038a85501c0c0161482d4054413901380101c40002410000b85403600036808a4005401048540f04002d014000d031030b00f00d40300c40075000c0e480341180e4000e5110704060141c03103420a0040005014440d08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 36054978 1250 36053728 36053749
    0xc0d0f02030c03010c050403150c020a08130e0c12060306011a0901020a12030207050f06070c0602070201020307140601050307051e0108040c120503030609061c03031a041e110403120e 80
    0x400030070a603105d498010302590840e1000303039400c45440152001d02c52190080e04031585981c0d025000c6842181c0e11002c441e001500c07200c40520040c1c1c000728518416445050003400c0500308a61a00d1228071072903112080141000e01030b8016a00400c1800e280c40010300c0c0c050540014952140044030040303140584000000e0080500d110110507401d4040d4000e01216000e4020f503001100d07000c0d0042d99412054924800042c0c5080c480408a840345d8003a241861051068a241c003916840700d0018101004040049800080042141d4030b004c01c01c0c0c1c80140415258800e0250030011510b10964115088906101c06071000804002c1d00000010241c40c05040d204055103a17402c0142d965001100d019000755002800b14800380f40915821018000b040c1d20812000c2c220354085000d012854a024402d099085500c00c80d0b43d10741c002c003c00c4044555420401c40c040802d900c4c01d1703984050074400b09910401042c008155407105100c0c01e29a00e0402061200b2042c01080d00c1d00c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 36056228 1250 36054978 36055003
    0x9020a021e0c060f0a020d0c08190e0303130509010f140d05010e030f0307020106060e1e0301060909031e0509090a0b0d020d03030c02070611030406030504050f06190e0c0d0f0203 78
    0x3d00040252001440001409480c40d0320303400c84148624880c02a0b81c035201400b0090610041800b107411461001d01454072104124500015042c02c103801227445c45d00110014104003140440900c01c1d400c04405440c014402040c10b01ca200749001d00e40300c0d281000702c90303580c0200440d000000501009420048003d010401100da0f10003c00100302d1090300140c64540c01542040400615603200718014080540c0041401070441e0030208a030024500303004045815549840c00040d02000c140300d03c1c2401400303501c1c4c40089225a0210b0f40740300c000b400c800000d020050060800d941c6840803443e0344040c015500141c003003080d10014128164101c0e00035032006410068130105039068028007440d000d19004c594103591034040540d0080003c41340c01ca06a0320510042141c0c84c881c0d000160068060000d603a0141e01040c0541d0a24400301d032000c80000d1000b210740740340c103c10b01c502110300184034041d26405441170b000400b1036181e10800f03019921540568025540d0610072461041e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 36057478 1250 36056228 36056239
    0x2030312010303080a06080715030c03140702010606080619030807051603150506010806031c05040504020f040501120216020d060f060314010e030705120a2a0c09020a021e0c 76
    0x603920f25005044007004c0315030381c6485007000d000046107840010751105480100c40c6980031815100001c0303005050b5810340c0010140c40b1106006095500840c0c9802018564004145a41060005030400c04060882405004000c1a9100380f0952042c1c540c00c2d41c1c0e102d00345a40d242920309100b860141c40400303081503007a400310b0000c20800170880c907424128580000340724aa80740070040d210100201da409805400550404104c0d02c07040c102002c20303103802e05003141041d4076000071508981100c10446c00301d041c000390510103582c006039441d84c00f0303500d44070541c900310090207043c100c43c1e007030100203001d9014040c00500b0021140c020f0f03d0080555181040307061303900d040c20246103840c81a001d0f01c0d5440d181c0080c08103440071044400094001d401001d05c0407010207240c140d036202d0001182006803506107850030345401d42c0500740341014491024000c030203d0402c1c25050110358441c003043c0b841000501c18294022950304001612070b11581207403030690b40e2841c100403c2d05a00707940003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 36058728 1250 36057478 36057481
    0xf060a111c0c060b180103140304081002030a0b090705071106040b0a0e0f120a0209060102011503050f060a050103150b0103020d0606270303080a05250503160e01091202030312 77
    0x182d4000b00c0048800c2c01020203000341100041880400e405c10905104513203091001030001c41c0a101030030360038204030300480f85046e9583d00030a0400c100400d206218035000014400e18202c00d02501700c4005040311894a207007081038000c1d0051003003290040050100f09102181c503500e0703500740c0b4014524099003598500040000070302e000340d800f1120b8480c442003440c040082c00c00c0c0c0c2e12400e04201d804000c000111117502040b000703040082134281190340390f818524000c00c0b813070841c4001798454801081c025a1040c621800c024005080c01d1000e4500381c01000030980586800015003002c0e000005c60742d00ca41c004070080e00c00c59030078001c02420024002030322903204840c2d441004100c1c1d0010f9074048495801c42e8080788034480035000031a071030046a100102036101c2134000481040080032082c1000c03c1c04c0460f045101500041a00401000341d51000c00058002d8000140b030100da120741d202c00060000c0000d4021103034403c01d0280e0400464404104990301c41c81d45400a400c207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 36059978 1250 36058728 36058783
    0x20030f160c0f05060702070f06120f06031403040303030f0c0e010305071106090c010806030109030f050d02071502040e07090503071e0305060c09011d0901030f08130602030a0306050f060a11 83
    0x844d801903034814010701c034403a4001020000001c11200f9140c0503510790f0f0600780300c0464a400b0340f4411601d181c0007992200d000000440190184610822200141d501c551a504018003141c01d9090481e84bc6030500260b034903003d07400034010702c4401003405d000440d902c4034201140d8104201c0700001c018405c0100f40301c03440c100000c15840c0c9210980c2c03195503d5880a00b030509854224500a000c00d0502081400c5280107070003030a281ea90500b03006042201e59201d5800e03140c00390381c0c02c005040d400035052180461040319141c0c84007490401607051807501c404641c1c0c030182c0d44141c444010940302c50903152014000070800035900801102d61b1070031f2000c00c540003688040c030791070702041d580e91242c80c210303009907000c100e02a4010401c1e00180c0c0b039502c071207c11907a00c0c9002c82da002c4081281103145803400046a014112640c0110740b2004030100150440c0e00039080180700760014864841c02e56030303810850300c0041702d81ca00000182c280c2c11250b03260442c003a110310302411502c65070101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 36061228 1250 36059978 36059983
    0xa0204050901052217030c0d02040b0904240905070201020f040f0503070e01080d0509010e060d09060501090209060711030309030a030f02010f0203070503071d0604030620030f160c0f05 81
    0xf0309034124102e41c1c6004502d00d0402c50711151000240300505214010141d10305c9080510b6200303240d024028a03044032000c13203030200d0303000350440e0380500d0010800f005503040c144101c2000800b10a050110b128a04150040007071032449110002034452001a1000b0301c00c2d01604c441010303001c00c003910740e901c981c6e500c0703480210b40c06054040c4c0f18038035001a180001506141c100c1707588034050090700e14001011601680720241603414408907000d4a201c58581d1001014807031310601000402d12018901b40f000d8410617881000d11900601c02945656550011640c4c1036904c000619905980040800d046001350001c10703905010f820082e50a06400c00c11100304200194000c005145000006000700e010913141d100c00241d042c400a071030103000d00094140c042d4642d843e90100c0000c80300240d442d03070068004550143d250042c007030121a001042014180513440350a003549080c10700c22440c400003c002041d07140c030003c40586658066507040c941c0c40d410030154003082800b03060156 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 36062478 1250 36061228 36061231
    0x20f0c0109110103050f0f041e060c020c150412020a030f080316050403120807020f06090a0201021207020d0b0414030a03020307020610030c180e2508070b120403020a020405090105 79
    0x849150b150041952990712901c501072241e6000d035070b1141161121480002010001401128649952021442000090146c50848038030585012a0b44650140020308111566201500502807103440a03421039101090703500f40c2c1c1c10041710300b44849941c00029004140c43d400588050070025400080c013501200941c440c01000b50311a400f04220b40048079644902e100280c03c03e40119075a003190ba01c6140a240c007e2041d10488886114a0b8400b07802c184003076440c00b8066014581c0700046580500420026900303000c0c1081c00d06034103401069100c113440c10001c10144000e0006410002c540322000e041803051402c0b01c2c0c5861170428058029841918a000035200e4500010b2480700c3c0c4030628019070f0350010008030344038a403c0e0003600c5040150348a1003046c0d21303004407103201c15040006003681c1140d41c0e00c0844040340ca0608480f91141500680c8068122060038095140580c003210710a01c0610b41c022850b6840e41012824420700e00d60095105041c1024810500015080b26 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 36063728 1250 36062478 36062483
    0xe0d0f0501050f0c070b01050607020d021002011b03090803010501180b040f0f0510020a060e010209090c04050909070806060d060e160e0105040204050d0b070e09070207030b060a03080d0b0103020f0c0109 89
    0x510030fa4844189012060141001c0141881c01060040c46942005400b802e6840d10241c030f5030380000321541c00250403580325018240117070340d01d056074000e02c0342c07107131202c0e04c00201401d08200210040d120304600d4881409114107001169040080c00420400482c000784010145192540c0d260190302c4e032460810720650303101843c001c0002c00d19141c2002c03082074102d500e4000700700e41080c59407200301a0a5008a41c80780755400e0000c0b540c0c2d911565001c51195440b490b020746d40d1400c100810181c080f01030183d1105507c485001d215180d00050b40d20b40000007107610070500740c003d1610901608012420500350700681c3e07c50560390702ca2420501c241c0c0c03101521400242e8907502400128080c91298070b40c0070380b900b402a40882d500d811321313503000070040c03400e080c008201c40f0216240120a481ea1760068ac00424100140000415800d401100c200d43d08030086141d0789940d806801080b90950041c1d03500c00906030f07280e0203641150500300c2107021090710380f01c4200203d4020010b0b44400e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 36064978 1250 36063728 36063751
    0x70305030306150406080604090804050d0515070c03080f0c0409061512150e09030d0207030f0206061e01120e0f0f1009030c0f060204030506040b070f08040507060e0d0f050105 77
    0x15004810482554251860746e5907610b8544d50300c00410019103201c0070107a408940410021580c0d84509114001282c010b00090160041c20022001907074402007082c0700700b086440d403c5000a9214207503640085c0c0303a1030b260600fa1500ba0358107d580c8155070002c42964602100010141041c0304650146d20f095100e582c0e0090034200d50300191140141c000b000c800d0240001d2105001c0b0604242d000041c07030040b40d0130b01350389544030012030f0b01080303007600451032040e81402c010398108281980040261040407185580c0010080d049800820880c103021030404800d0410a0641c042e601040c581021a112180300d011101e0700c1c3c0307071864540c0009005d400c0c0400d445401a000380b68107540d15903030b805000e10941d00d5800c0b064010a60854905400b0080040403c008101c6540103034010004650f2500b0040d20103002d0a8000c4401e03070030300515404010100d10003150010841740759050041003640343c2000640c2e4080ca01c030004004c02c071420380f07150911505500a61003040444036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 36066228 1250 36064978 36064999
    0x91306080c0904080316030209130b090c040f0b0903010905060f0901111204030e0a0801050a050a1d1b1908011505060c0c010309030311030f060406050f0f040507020a05070305030306 80
    0x40c05461401118084d02219007040464041d0b18044e080301940182480c0050070401154005546031030050244c803e455103c2c1c0c0103c50510341140c0042d0418003005c00c0f1417515241218040030a5801d02c580c2c0040b510208070403005071000c4d08042c034030350b600c1000d9841ba458509a1451181c20559000c1c0c0698600f01d200340c1d2210070380c4203e070102341444111052581d0395644c00c840380b0042c0ba00c16600f00715036000000d8004000d00071706000b0701080101242034900f15440c0402c0782d81800d601030047c1000b0b06c00b804608000705090080360000c03d244009280c8980c0401d5440708414110456050342420001d0f0b20078041d844007191010b40d000200c1c03440d650381e04024407406440c8205005410210b89021298001e500c9424620300c40d0402180d5185002001c4240e50021100c80c03070005000400c101c1903181c20301c21100540401c540050040c840741010410b1031861400072400b45503940046190140200490098a5030001c2221552034580c035150762a81c0007607942a0040081f040e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 36067478 1250 36066228 36066253
    0xf010c02010b010804080a020708460615050d03030b030f0106080304170c040204060c030e040507050f0d20040e0702070302060a2d03020403030806040506030303130809130608 77
    0x2014031000050392080b513a80ca990f220004254407013003e1105500c102c42c07000402d41000d101c622203040c407440c0c80c102044601005014103000300c072000c52140703080c081d0800a070a2041c039213019440e0850400100303205804a00c4e40741e525160001640031502001207001c241e4141c22030340b00c0c254181d00390307541400d190710900c0c03e9860070f00501c101038005200900030b030483c0c800e00b0500a1a032400703d0b41d0020340c1c00042401c980c81600311900103032964600b1000e064000c80b406106800942e41001145840316008056004810f1542070800740095030b001241060b81009401000b2600300320510030107540c45a075558400e11410903181102d1002422039400401e82004a9802a01407480c10b1904001100d00b000007550144502c000b0000d880c06011040f81740c55019107540d10300582e6035007103043c058410140286030600c5141003008101c010b85020095036042101c140c1d06040350380c210700e4002d40710b0080700b003a10340140e6810b03403041c85d409494200c401200c0d054030503514482e8414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 36068728 1250 36067478 36067481
    0xb0118201803010b0a0605030723030610080f0a090f0c060c02030f0c060901030b1c060c11010216122106060809060402011718010f06080c01210b1309050f010c0201 72
    0x9000d201e500000850040082c5801f58000715808112442d00141c0c1820304200320384a04c0510410038150f1902000f00501810700c1321600300c41c0c58003418900041c4c54101811703100b24100500e0250040c3c1c80381c00d402c0820049030251a000366200d0300c198481c649400c802083c0208185041e842403013100c103a425181000b08010f484810054502440c00b02004015405000b50240c6141c0019020849a5501c00c628200003a01403046601152880800400801901804040b080c4592042011440c03090504100442480d0300c08820840452081410398130101d4403055030744510b65006c52141c20941a500c201d0030b45105445405440e250500402d5480b0700440d0028007103100c401aa80c424205001c032907502000d4940084800359062500d1030079241001d4135171034002c0d100c5c2d005218141042c03000d86002d04080ca000e183c501410811481941e020000715603483d80d03101b0400e9407545804120f0100040622030500000e40a481d180380d4400c0c0800320650385500c0c0c040c40c608124410b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 36069978 1250 36068728 36068741
    0xb0c032a1606050901140906121501020f030306040e0313080a050105010608010e0f09120a0201061505120103080c0a020d120f0e030a0311030d050106091a04030b011820180301 77
    0x4a03642c0310306003488513005443c580f0349165154590002030240d040a60b942c0d40040c0f1544812103030326481030030003205070360b8401000012203043d500300d000b030b000701e400d40001a00c0d40044202d034041039032400700c00502e085204101c1c9140e09403007a103001007040c00c40041c071700d5030b4284280000c00540c0e90b202011100c2001c28020f19140900e1003022038103110b081c01d6000e41040001b8160380b14901403490a4440750f01003560b070340150751a04005c000c0302c98142c0c0b80018820050a2144c5494404c0c00805008841400001c006000125000c1071403042003040d00082940508040362002403810b101e94866140b070170300400201e0700d011420009209440c01c10113107502400410302c2d9840e03030b5429505842c40e052050302c107101c2844407030b038110160b004d041d0081695444004440707003003404142251590702e04070501010104000c02c00106c0348000141140d6180c4400c090094000b1203d401600c0f0102d07403160f130200c1010203003551135000c00042032410b482300040405030b4040814182138030b65 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 36071228 1250 36069978 36069989
    0x9010b1e030114010e03010b030601060e040f0216020d060905030d0f0506040905030405060a050f0409051006030506030606090c0d140a0b0f060f1e0d050106030e010e070b0c032a16 79
    0x502103e0181e503540a120307410f60b801340040c000305003045414003083c580303d0300340d0289000903c2c9904a0a9608103880307120703525041d04a05514100383e803c210501c00708460f0000b8041c0001c0c4c1e4070b090a0000070380c8a030740115444025a0f65030a042107440000c0c0502034020104a407521010514602d0903100d50f410b202d6104d07018609143c41c1500300942608441e0644007480010052038001ea800c0d0001440901380c2240c0c0002c075410031201d100450121508507006140c500824822280c0c5c00041e070a0340610211400704040c2d541c0701c841415401812203101e00e203130526210049808034002140d100c0d0540f01000c0050b14000707010011005200d548494005004019882c100c10000000f41581901201c9103401c00c09032002002159007e82c10843c0341e0b40c0e8cd0001404025454060781c1710f00d91030f590092001d010f1002140380c441111348500e103d0000d0010700c41422440c148160380010144031401c440003001e10b404400b083e01c07a0300c4402240d01a00000340500d0040c0c420180c15100c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 36072478 1250 36071228 36071249
    0x309140f0706031e020d0207030e1008130c1212081b0301090209010504051c060c08060f012a060603020a290f0d06080c09010f05180a0204030209010b1e0301 69
    0x2c2c5021015001003180130302e295003100e8224100b00e5281100d000408540c141194010396422a03410f009000341e20a41e000c3d032196100581c050390107980010590f030400032080300d5950381021407400c00304800c002d9003e84c000300031501003031050240c041e095101182442e140c1c050300341d54034211818141981c450079402424240014008030040794007804c50702d00d060402c0740c68280c444000a40412138402d030700c004403041301c0a001c2000704600804c60400402d0900c2c04c142c0c1841c0c1c00050400d030460711450704000c40c10000d90314041149212400d000094209038200041c40d00b00400a05218001640200741c240030014031502c40c0c03005a00941500e141c4d400c10b180340352100301103562014681d203004400501000c0091041340c0719001c01000b034840141412458101400700000050b88600b02c503106046081106480b100010842052a0744008500b03075502600d08009000343d420107500142044c0001c140c05011074020620581c001401000410032000505040d2000b400b6005840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 36073728 1250 36072478 36072493
    0x506040b0321090d02060f130506030709030605040213111803030313030c03020a0602180906010906020316030309050d020a0201080a0506010e0f03030d1505040b09060a060507020303040806070309140f 88
    0x150103210140981c040f0080601c1c5a12140b40c0001e54160003010501c1035800001031030300c0b03028100c83c0c9140003e00e401e0301c800d81503240140e0050a801c009110140580b40c8800c002070841d5500d204142c030141c014a0200300e2428001f6004007950007414035074000300c01c144841c02032403a000003075071f110b50005460030341030030540c0d83c0888025845d10000c41c21745c420100c0d92000a0740c14006020700c10800001c01550b00f07088000c104008501401a60500000e07a005114499011080302d07500b404140c07410204580c030303107002c0b030090410000c003804a00590091070101903000c0303071841c3e255000740d840a040d42c0382c012008040b22000e075201400724481c601c00108900f04024011030400d0300070b00742d9040c890002caa00007070321860b00340c1d04030b644031088060100d49000d219061460a065502031594035000b000300302415118022602030120125100c030440d1307020030440d0050001c460070f0703401303a08103114050003520115000701e8107410075940340340940c08005182c0304001840e03c01000d84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 36074978 1250 36073728 36073783
    0x912080315060c0a060f06120c0b0a050705070801141b03040b04031202030a0b0108070903150b04020403020604030305030106140f0a18170708010e01050702100e010204050a090506040b03 82
    0x20081d001c0c881c00c0d08880240301041c071484040c041d0109960007404003050f1420b694017a40b003110060b80103018204159140c010200d100b00049505480a49810644e00d0b00181025034003802501d031700520b5881a0507002c10300c00301c107410441101240380c3d10444a522150115148407010401d0201044010300c00140400d030b02e0110b0036041030107802c01408000d040030404050740d2040b120350303000b581c444e88801304950384582038551021042c078081055504650300c983c0d070350b4010107565551507282c00c0441d44a40c0c4907412600219401003056945541d039207009080c5410911030640466800100c03510100b4aa1044410042a45180c1d40c642138062109841c1f001d12003401c410442c0c030300b00c00443c00c90005007a40ea00d4100c0400144040b80c1f40c40360650944130303001c107080c50b50b03410072081c006202d030005410a0310380c40c03a50010540c8500289101e0090280d40c0c0030035400b226207000005c503010b45030f020302d0050300251024400c1c04090010700d5511508401c1c04800c00e42c0f02c4a00250 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 36076228 1250 36074978 36075001
    0x70201020a0f080d050109050402010206011e0302040b1503070f080123060310030602130e0901060e0606030c0c15070e010804080301091806020d020a09080a0209060603180d090609120803 82
    0x1e10710501110341884161403130842110300903006035102640d1002400150740e010410207004005a0348035400154101c142201d001c4101c0c0700c024000c03500c03100303c18115601c64486074003420302d01d40c1c26a200d02c3c024134001d04022800c0d00110201c2c0400001040c000410b5040c1240b001e03240c0c0c10031282c8c0006c001845100d5100600420590842d0785010001400500081049011300350740344001c141045172800d03820b90301800c0e02c20309a14081c4104258251850301c103a010100301d0701c441c0c80ea03448101c00146c030311a10f07003c3c1c8400e0066600014102e0700c4c0008040c0111059a10b15407014400801036400d21419900074010b0101880104a01d05094200d6100350340070040c0c0100036840c3e990745400366081804041601c07600400c0d6185800e0784020507400a080b0400100000003980d008180482d4014001500034480040051324a8500445d10030001d040b010444070461805c040c001d000000e02d01030703180007805640000403030041d607160056480b0b80140e0038078655100e8044010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 36077478 1250 36076228 36076253
    0x20a0210080c090411030a0b01030b0d02061b01140f16120c02010e06040c030215030f160504030f030e04050a0618020901110a030305090c0603070c03030c020c0a06030f050903070201020a 82
    0x400d5000b00100f480e0f0b5107850003080845440582c0d00c98030303402c20301c0c01e007401c0d56a40b0304424105451b106043c0d50310b544039100b65007420303010388189a940c15492a00744403e440d82c1400242c640c2844984c0184030755056800744a001c00380d070700e64855264400280d00510119208000003120b020001e4504a01c5500009000c0c040340000180d449407503a9250402c01e0864007900c01486160040041d820200314260320003415680c0e6500d10b262444843d010f01300098000038a92040c4205001c0c811300440403240915048a0405120503041c0340040ca400040c40b92103020b40d082c5008180d41c4d80d02806500207450000c150100c0301c1803e141080020340200d00d1460400400e03c02c07020f0110402e103c6860300314042e42e404281407400340e0225240032600b5892501800d0304000700b244240c2c1c0303e0b1a0151781c990520b0302281c840d03608002249007042800d02c40385c1c400700101b00000c280750181d0020240d031201180502459980818640e124020540d010340543c016196900c0001c5c81c025205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 36078728 1250 36077478 36077491
    0xc030e12031c0204080c0301090c0603020d02040504020c010218090601020a0b0c12010e0108010e0a03050301030201050d061502030c1011070b0a060b0a0905120105040201091e121b06020a021008 85
    0x480c02e1604891820016040c4182d0349111241d0001d4140b0610f0030502907920840c205400034444e540d001d59801c0100c074401d101d001d082503808904859068070702d0f0121001000010029911800c1030304100d4000d5100380c003003a41201116196041d13a0501000f428880c03078050300a0940005e25032980322403028000d00032113801c0c4042100c52810100104598043c00b01a120710b9400c0d0704045d00d1908480e1140600050b0b0750020091f040002d901c8002c40b815a036083c81c0981d16a03810511000141409810049118100010301022550f00102504484414904072404403445542034421146090441340280c84200005801f1030130080000f500031400540c0052a256511204403054102d042c0d41e40025131001020030079868110301c01d140ca1145400200720754207180d40081e0140143d071044141c01202008004070703e094042c81d00000b4102c801100d180c0c8030309490890001500903901c1b200e400449100455407500c0094880e1146501525450040355900002c3c0d0351607600903c00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 36079978 1250 36078728 36078733
    0x105070e1c060e03070606030b0901020f16030e04330513091401050906060405011401080601030c05040302030a0b100b04080c0609120f010903080705070302070e0402040207020613090c0c030e12 85
    0x21800410f0100300510305a401140000707100d03411032a0130410160082d020030083c2c0e00520100401c0c1306000c1c01c80e41000a0f030b0400c0706042c1d000340340540d46090346806955000c0e181088028440800c40801c0d0107054454010001001c514060700741c01a90a00907550411307100840030b400e000207903100e100c41c1405581c103460284401c0307840c0f6003550b50403144000c0d41d400940c02e1200c07504140c05140d0246c80c949040032540503215000900c1c22030f00602243c10191655001e406440c0070740100d030040d41c0c020f8156690001c1d10b043c40f10340070805807424900172202d1000010b981c40d1280998003030304c0c503a402800d6400400020444282c2241e60515840104c821080e41c6040d4108010700300342d9840c4001003550242410064400d03035000b06140b003809410440880002e60100d6a803083c2da403201c130201100d443c0d42c00450300038014035000a420004c009141c504651800d020300c02258003440c001c3c018542500c03c101d030b01c00b0000c0ca004010429400c0c2c15002c600d0801180107010380700104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 36081228 1250 36079978 36079991
    0x613060b06160b070305060306060910170313050102010c080103113007050132040503061003060509010605060706090212030a05041409010501050712090803040e07020105070e1c06 79
    0x2055a8442c190115102030507070072000030008820b900b95404005800c08000c0c2d403602401081d140c0b4030042c03100d44a14050700c00a00301288458010014140540b455650380051041c00d907981c2e0311550499a4464580800082c0e561050103405016600c940d100f040b43e91171652008411028200c2681d40020361414014002454400041c010360040d4410030034040700c101c11364241310150700301a04000c44180b0380300620700000158080300040303d224581e0f4406041c3c40c1b50023809a90001640350040e41d0a0080c00f011030311238142502d00800040010343c035044092800c9030030606c41c0a41100040c00901c4c0499445d521000070140003030500d040394200202d401e81544e200c0d41400740450320124081c0030103c061038a00c0304c40308080e00c48090950404c00003070321500810030014915108001c1e0410740c5407041030341100500200c0101d9031a20348030041d41520250807544000158039140c0080c1c203062003880600c1c5d4440010748240414024254100c042c03a203600015540b1640382e11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 36082478 1250 36081228 36081251
    0xb090d0c0302090c0d0b04092103140f090708010e0a17070b040b011a030402130b150c060f0708060f0f0307030213020706060501050a021903090e041101030605060408061306 76
    0x1031183e071041e80f134074040e2642d51022040b8001281c0c0400000e900661906078030740c1c0096243e0341061440c513042c000450100840300401c4000d41041c81c044204012403500f0b002c000803200c12454050340b00c1c00241c1e03060940b10070075a4229940d000340200359601080b90a0003140c0c4444010880110030050140781203a15120543c507000e0640c2e007101c24181850042040c02c2400c0c40c00d00070700700f041041e81d00d581484d40020300759400000545034071603524190201c2a50760000e03010850304c1c807000e550340c5030303200710420070340b03d22080302e0390b80000c0000b4000400d494400c0c4080d5200b0780d402014150030802d11800d010402e205140040d4161003040004400341c2d6801c0c3c0280b4401c1c00c04000503907500d05601e0240d065801943c051410b1000c02d004200b456a00410b90032941000d5020b024550600c50030308030b51402d40359000c4000208400e0900085c00017181120710f407c402a2403d1110658400c28480706124074411085d1503002000813400c02d042c0d00e00070100440c085e40e404a5501941d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 36083728 1250 36082478 36082489
    0x306060f0c07080d030b09010504050a0b090a090b07030605010f0305040501020f0c1606050403170c0c120c030610060c030e0d2103050601090f03020405090a050601080114100b090d0c0302 82
    0xc1004000d5100c604100300c242804c212981c0110101c0c0740070702c140c2c00d40d400420340c00f001c1030080b039105d15111000500300c00b07410344c0301d0001a1002420154503081c04041540240311114055880208a100090b030040c007038001c034022281c06079505468070003441001c900500c0003030b004070754075502045201c82107025039010f0030840307902401a000580660400e5440602903511840a000090000304045141c511080c190480311007041c42d510411086a01e0620303240104803580135908010030030b00c1070300004804445820035412540c036a16407460715401c040491003801d0020340c11100c4400060f1007980c112028074001f4005191212041d503c90481c50009080d52103981d803403240681c60142d05004003500400c003030802c0c0b0240b5051205440c00c0c0325540c080640520b4844020031840881084107200381d58000d81912070b256165240140a00041d1f00b0401c0f082d900030001c07440800ca400d000c3e500720343c12058202e142076203140510243c00200b800c20398040b0b214042c0000980c071407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 36084978 1250 36083728 36083737
    0xb010803040f08060603060c0705010906060308040509060108040b060126010b1e040f03033e010b040e03040302010315080105040302060703060605161e05031903050f1b0306060f 78
    0x5805107881e2410400d164a40140c580d014070440d0744036800384802d540300414201d80041070300000503a10301d0542881c070f0241140040085c196031030403200009010480003c0d0007994000c5803c3c80c2e0944400004450b4040140d07400f4000f001c0060202ea21903000340c0c1d104041c50040e503070000e13008284480c2801d510509074800180340b44001100c1c03c8008140c400310720041c1c0c800b1245402c10b030420740704e28201c400d980001010f2003507001180703074040c0c2c1260070310b0781c1a128108012042c1117030401c101040c00321055080d0056082090a406070315050183c2410101450700030750030a41303540c004401420303444481c11144020120b0101e00002c00713000c0c0170302c95402a001800c0c1810950001030480e2a03c1d4018400c0240912035000c200d41d4010b61504500c0d04002e91200d540078100703640c240c03007035051740003080d034440018041844440c555520307000d8101510100b009070b60f04d41c0d1000340c03c03008407455410390024590045084c1d030700d08041c41c0c06c4040078205034108104c0c02081c0906901 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 36086228 1250 36084978 36084989
    0xf0e0a090614210d081009020304060f050604020403020d111c0303060e13080304060b01120c030e070e040503030a2c0f0706091401110c040516031104060e090a090b01 73
    0x2c00d00203641581042d040d80b0521080060368540c0307042c014002d0355241d00d0f43c4c003640801c0045040125030006d25800c0800301410420204540d81c0c1414544040207114a504d12900c00341080e002640c00c2c1382c1403090b902242d802414000d40c1100c550b9854a4004081c041c056100d54000320700701d54500d103441da04401c14031a80380040c8290411019200244005140c1180013049185200c00252400c09503030304198400300c04505096a00016180d11f12072040e04000c0516145130914060b51580042540d0004041600d407515240c8442c00c0703212030b0407900030742030f6841000414007442481d4071080a100d802480000d41c411a0300482803603011805aa9089600c514034000c14420140b140703800511903401c0c4998458034158948514019040003641400341185201741641d4040c0104402c512009200f00a5454205004c03904e1104a50003900043c0c5031448490040350039604440c1510070343e4584c40143c0700319400300401454010b16402d1010348504420740000e00b460401c5000c4c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 36087478 1250 36086228 36086249
    0x204090b01180506060406140a17070903110409120804050a0609120206090a030923040501030303240303020a02060304110916020c040b0d110d1b0f08010c0f0e0a0906 73
    0x2c080c0d60122041e248007800d4a4440d003c10401000b003243c115915219070110098000c3d1148150003090382c42d400e0a803800010886904100000a80c0c001659000d40b4480c06068400061100c24001100c02601d401000c5a1082e66905800340c012145142e0140c8144104c1c4d054141c199030703500c00d50354000c07411540d103801010852041034040c0b00c0f460b03200b0201070080058003c0c42e2401800088207108040910028242d06851400c1c021484448007501230404e0100f540d507403400500810700344142c1e031620f020000803409914105080181203c0c0c042e8020600340c0c1c100d03000c000556201400480c1d4051203904e004607a5114210790f01d10030220020522480703090b980000c0d080c0400c07030760301e588261700c0c20304c08412590b41c50103010f82042c0c2200700c0e41c4d000c42a20021801c107a19182026121143c0c045101c038a054514030341c4000c0c0c544251440108a40e83e00710b541c240d801e042c0d20359011492491111884030301c00e454101181c90001d110b02c4480b995001c03a4012070301c060f0041c03510013 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 36088728 1250 36087478 36087509
    0x204060e040e010c0c060c0c050105040803040501110406020d050a0504150206070201060f0803180312040905040201090611190206041d01031406040302060a09030c140c150903190204090b01 83
    0x3032038240325000b06425000000e01280d40c00c090300400b0700200360401014540c1c0c4088401c210341c801c4c5014446142c0c0f0800810690400e0305101c0d0440d00126001c488035828240c09040002880c03090f50102c80700d94000f01078109160000f9a5070350852030412041140c148000261400d4a0001d0320f0f4150064016202e03c1c01e01d40402030960740241c200307060300c000340c040401180b00c0002c2118600100d004500c00130f11044000241071030014001d10303400c07180108020a50000c258084d600030742c13003600c500424aa4445050322184800340c1c3c000c15a030814510b000e07820000b40803a1a2280c802050f072440c241c0c455142008521302c1904030004c11b03120000505c10400f0101e65000b100301054000d12861600b6034000b952040f00401160041d5187d40145e000c06005407261402c0c01e50042c641e00342d00c614200300355907840c50342004a1044c454003503820201c030841d404072380d08140081c001d45920244030144405d410150032040782c01c240e032288041c02148941e410b040c042d00701e20300140c140e03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 36089978 1250 36088728 36088757
    0x3051006050307090302011107090e0706080f10030b04050709060602010e06100f1503020403050601090209030c010e0f01051b030c061b03010509042d030e040c03050f0c0715020406 79
    0x616500604107205082081c4001103802c00d0b9008101c99091810b480301038292028a401d080803588108440360a024610f4801240403401070240c941503503076030341c0f903940302800804000000e492403551140948020701c0881d402400b250390044c041c0c0c003100c4105640d10984002c40d2101c1c5d0100005075500c0b010900310000c01d00a40342c001d02c2a03940c00d51105e05058801c40d1034035442c880c07910040021840343c204140240c0540d402550040142c49081d82e58500c51030196000b611514802d0080303607550b001542c05800b590030450409031090190360209001503500e64014801c0754a81860860303003036100081000240425641c642c007400150400e14030b2010307115903807210076505000c140018001912441d902580c825042856800307a509003015004040c024055210050701000c071509080c180c224100c1d001041c41913030204141c600b06001181202c0301902d40c800e00b031100401090100c0c200c2005000304138040c180c0d0600c00e1400b0840d074030482c0c1c003540c483d401203403100b0180c0c0b60 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 36091228 1250 36089978 36090001
    0x20910030204051e0603070818070b18010512010306050a020c0a1109090609060714070206071a010909020303041502030c0601080c0916080403140f0706020306120102040e040b0403140a0305 83
    0xc040c400c2041282c00d07280040002200c5c0d000003440c041c2045030010000e4031511000001c1210702050505803000c80c2c1e105c00c860301403a480301030b454a0581441103641e000e03511500442c3d003d1610451420101d9013199250409000050011200d40e07400b4400507203042024404600c040740300317401d900c400c000c203802480102d0704000c1c041c001d150041810440c4030b10012844aa0040503458031010f01d52510030724046074056401e003c0d411a201059a504002d00000c0680307116081d00c40e10002c60ba650001102520100c1714006d4060700280400c01914850b10310046145901d40103490800141582e92072800c1000d0307101d000c041c0e02c80600b0000c6810102d202d0354000f5440200c80d40c0e96070a00c40050600400900020704000301c1e4804900348004d0001030319a5051131103c280d0f1f9400c00d60410744040e400944805110304608134070040c03c00d105100316001c8441240c4050f19a9440c0d03210340481c0b160041054003440140002402508401d000600c50411640c80000b800c0c14001e09685 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 36092478 1250 36091228 36091249
    0xd020405030d0c03091403070b1803010f0c09030204020f040b0a1d100f0c2604030201090b030906060105070606050406120b090c13090804050301060602011b0f0804060507020102091003020405 84
    0x814400e600f54001d020907800010301054400988501505203818000b181c5400c43c141e100320310300040410b5200500b9101207000b0b484100460090149000c2d454001085500312054980803880b0540c0c100010300703094024102076071452203c6400c155940c146881d00b41d1114030040000303030b0200110900c0c03100881e010011600f054610180040f400c01d0094030000da00202141404801d0214208101030303441c40c920ba03a1481d5403c0e01c0b07400c4448080911319086070004a0105003004c602007007180079082940d100c0c0d00001c00a01c80350b1102030055407981d1091009a0710300e612910041090b13110f60103808020101d012100304a100581014450b110001d0216035181e04006040d4089a5032884c3c92418402081000940070368586070040076442158030581e095402c00d1000561103070194081803410780001c5040121011108007124903070007010301900810108400315002c680c09521041d13000d0100c1c00010702d031918060000f905001d1401410300080c2c0c0019003445141403982b01e40d0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 36093728 1250 36092478 36092503
    0xa05060906040b1f0f0905030610060e01020717060103060b0907140d090209040f0308010605040f15050d02070f02030f0109050c04050405070b04080601081209010f030507030f020d02040503 83
    0x1005541842000110800320141150344640d444460b19045903440400d6410501c00f18008005100d101383d2025122180118095012403095840082d1030300f80421094443e03040d508102c140b01d4145207060718503030032001440b411846141d901040c05001000d21400050082c40180784079032542c5803900554440210107800307640c281090000142d003115030b60314400c02ca50380c4e0940341c1000700c81e01e00041c05a03134800b0390b000a80b0418401888145d400c030a800c0d5010380c1d10544c0c0e581e00d030001590300e031085200c1d0840711050020302700206400c2e00d80c011503aa1461500a180121403171500c2e05981200d41e050f12283e04015103441103203402c12110414251355802401120304603260a62a82551420280540d07142d0f000101004020305c000b9000d1705c00080f0140c4c0f92500c13082d446503203500c240aa426103105400845400302420029200c21480c141e44124844190b42c1044004d030801418000030b2580380d0b030070007002021038009048030001700180140c48a250404140c601003000e445c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 36094978 1250 36093728 36093731
    0xd1d0105090108060d03030e0102070605011502010e060103030c080f030114040b01090f09021303050706170702120706090c0b041d0c0f040e1803030c0d0b010e030d110f0a1101080a 79
    0x64001c0383d8201c1c4486900100c101c418a100301194103042d00603141400c04510103510000d0360710100001980008d0581d002070404070450580c401e81a4200c0b1140032400401e80d00004c0100300081c0b223403d21046035481000207505202d50803030b41c0d0303906410a821400010740c0c1c0c44113112040c1424426105010424600850b81610700100c14481898a010380c0c00c60b150001001c1140c08909201e00300116030040071102120307a50b04005007002116200e0351758405a40002c6100c041c0b00040761000142003c030880d2825400380d981d00700501c240b4004447d00220640e0010301d010000001e00000c040103108005841c1c203e4801800c06680142280464441800311641d40002031040c0c03400d540703014900d00c2050f141d980501000d000c2003d00601544800402c000d00e06008a001e0b0160000056003031050b500310788019030f94020f00b000e1290f00360b80900103400341144520005200001d02c20203a45401e0800340340c050408000d020240d5080a0301e00110500e540d1022115521a004210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 36096228 1250 36094978 36094987
    0x190507050405010309020a15030606110c01050301060503130c080c030708030c0c19090207060906060b071101030f0608120c07061b0201080601030b04050a09030f0212030105120c030d1d0105 83
    0x100541580198041c0b00d0405644031050700c1151215040c91015002104008010103042003005015040c14000e55000562100d0450806000004c04180c5250144c46080c1560f003003110842d002d1300000c200360344080094400102103402005c000028200070005803e0744030a071014136240c0013441e400b01203103500c100003500030f0240200c3d02004018040f00d280d1303c81c0041c41c503e24031100c46a0402c8403030f17620008a240030040658444001c480c81000c0602500d0b03500e030440441801444405025001c41c00d0600c4190740c82030b8800c0450b0030790f01c2c0300003c00e0741d11a400300c2c3c0341020180703200c84000b00c0021140601c941c200858801801da91511118140c40604440606284d81800a0502c01444086010341c0c0c0250441004003201800401c414504540554050040da400c10740c0840d098144021040d403000c01c1d00850b9407a40404c45240d039207000c06122660915408181841c0030380305028801e41c2e014020900f40d0f001590303494144c0d031000c01a031050f500903e0282c1d414444100b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 36097478 1250 36096228 36096241
    0x20601030b130f0f08070503030c0c0c0603060609090a0e0d030902030c0a0605070303020307051603120f020307270b0c030c0f030a080118060b0409060e1008030429121905 75
    0x5007003060b9130340074214801a03109403500b40540d01400300024900e0102000300a040190040a0a18000311404640410f0042c00520449100c282d0300e05802c96130401030000315050101d015a0003010030f103c001150b404900d1205c0c149450510b04800090700d8180182c154a42040a404c40d00c50131905000120714041d405400c612038200028241074000c400102c03485c0c06001524070300300a0403030b154045030759490010040400780800034040d92500c415900140c0761803007a0391044841d62100302c2c12004031140c841c1050031035090b002c20003c200c1400300f005100c02e00605903c00c0b991f0020b54846d0090512a41445881001c4000395442804604681c80e4040d0080b41150302000210410b03100f07503485040a800700382c00081e80c000340060009031845195002c54100c56040b000c1c01104c0e202d170341b40c0410340c00c004d204500144e8810301081c814171040038074404100c500901c0c2640a81120a00c1c10f040b0741006030144442404101000800654031003006090042804100410314094 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 36098728 1250 36097478 36097493
    0xe04060e04140106050a060503070206090105161101020904020f041809050c012a03020d020c0603011203050a02070f0f0905010608070f080601110102030114040b01090b0712030f0903020601030b13 86
    0x10805400d51440071242c21071181c00313522220140c500580002c0b002e98403040040c003198829a00c2c1c00040c413844000a41000c2d041c4502d42c01100c1203d8003960304054040222508103264103244000d540c200400314140e03071188020610407469468072925a46801211165118a444182c00450a002d01300307001580103d426460600c00742042040d03175a03030780e035140080d410319406294481c2d00708035410300385600012807041c0150701c0c2d402c031504d012943d4144141c0780400e00c0791102c1c62039142c4151002a0055015000c801498411a100555601c4852941041c160b0049248041a074000c0c0301d2603e0b6030264602500c601e041c003d200317081c000310040c00707491400c0242040010f000081010b5a22a0411040c402540c40c000d5460f540c43d418920380707201560605070301c11490b08241d190b095028980705800c880201e520a42003421641365110805001e03104081010364400c101c611a100500c0741d000405c0c026402404658151310740084032490241c0405409000c00c0c05400c002002c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 36099978 1250 36098728 36098731
    0x3230606010305040c0314010b130c050f07050c0306041104060f060e090907090914061b040918020a0303020604110901080c01050d0902030a05150c041401030e120d020a0e04060e 78
    0x81c6400689a510b508002010911710b410040004c541400030301c0142d28150001c0511036011904000d03030206018800c1b048640c88c04092000c15010b001071440116058064203900d0301860540f49400e4411000a00340030f0b08550445514400d00b1a10150341028802e03e0003410303103a520100f01a0070f142c0003a0012800058061082c64240c0014080c120240034280003448004014400b0b51445d1400504071402c10074803003c184127240010700d0034a031740c1d400d080e0079691503510b8510b007608000800000e09220319030b210028440c202c0da400180c0b00c1c0030106c0006c5000398050612400c01d850003100388103d0390f09040c0300303001710310061140c00c0003c10000036401c030034281150b075811101c0c1484050234610101a6240c0208101300040c40404900a0300c524a82c41b10084a65917401c0301d0b00140c01030380290007400d0308520a00c2d0342940264041e14603c01e51030100c441001d500d030018926907010041281009402040d20061180c004d007522817007000403501444241d05101c00300161410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 36101228 1250 36099978 36099991
    0x9020a170706020c0f0d110603150315010e0c0a0c050a080307120c0909020c211903020304030903020d110a0603060501020f07030b070503060d08040303020307020f030d0e010e060409021201032306 86
    0x2261000031041180c880041c095004012304002e860b840c0800c4081d0311001840101c90103400b4140c2e02c0b44a02100302c0104c2e058840752030f484c110710340314100c194070a50001840f074030078009001c410340041001000100c00c15446200c0e055503e1070b0002c0700400441400c0221405582017070400340609400c201e555003569814440140c0300d0206002c10f0345450340f2202070502c4640c3c403844510f120003042c4010320301c56100c55081d0801c0e0000c00d404400b01e1100f2680640001c2d042c80c01400103144c40c9509502d8039003c1d42c05607000b5811103000030f5913001260b005001103036490b20f0411542d41c050249150305880a0b01400d0098610f031210043d0f404000c00340c80030001c1c00400105180c0e42e500440c0c100c1504016001c1d10b85840745000780d81d030b60000105070310075000d1420020913841e0008005130b11111556900511084003030044d200755158481181c0d21100502002c110021a440a01000180f907180d0014035403550800b0009045028618004400450101c241002001425a41101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 36102478 1250 36101228 36101239
    0xc030a0e0f0d0312021c02040942050909010906060b0a05032a0a05030604060905040f061e090302070302090903040f0b0304050316031205061002120d09020a170706020c0f 75
    0x20381013681400034815080c054240b40e01c2c40d10391a0030005154098002d440000104019000c0c003d8001c10300c03058170741001941100192005007007400c042c51403240d010404e080c1120b226450b1070018021800450b07621205030b549441450038043c07140900c3c002004060b0005203402c1e80303070000402c2444004c2644a0244100f500d21004e81690701105030340381c1c0700b03101d241e413a500b00340001000b1703030f00c00c1d03a545c0c0c070079401c02101250880003441140d0245601030200700c020b0743c0b103550b5400a0862800d00702c80303881565800c0081504d0030300900100912903809000024118410441d1003103016058100c0c80e07006020034403005100c1040101500d249804403502c035603030351070010b00e94410b50320000410701180c2c541408064200102034a80780e48800140156a9031805001c00d9100020b903800042e80302050b000c0d5040d002000428000714a20004501200140c01040e00048941d00c520f6200380010200b00b42c441c07040c4520806050036101a00900b2494030015031040300c0e00d1041c500c00c0c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 36103728 1250 36102478 36102497
    0xf03050618040c0e06011d040902010201140a150e0408070b13020402071109090f06012106050115080c03060108041509050607030c030b152208030c030a0e0f0d03 71
    0x155204207960031400c810304600c801e14038041c03800c60400d042c10310540c0c90b0b2403d80300104050358000c1e60041c103840c1d1010580000c251540b0b08000c080c005a9000364155541c4079015030510300d1320515640704081da807038086083d400758103914203003c4181e800b419a204500051000050101c0105c8074410f410803204030311a00e503645d060720b00001c410b4000354850710010381403082003035034000c803179102c2400c446486e9960340e4040e42c01e844d2500d442c0c10188640003000144501040c19102001c801c803881c40405001200da65142c0440d007007038014402d035034450f41e1183c0d503590b40801800d0348400c620100c542141000710000c1c000308070240c0010001c0d84486280d03d040c202e1030384002507154100003103852074141528060006c00010760b180c0000790800d039200c802401c010107403518174004c201c90f0030700c0c014003180104d2104400603512071401070404c100203001d4104002404100c00d801020b140d4441c00400b000e0491815188020b02401d1824034851843e80c0f0040605005a0942440d0045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 36104978 1250 36103728 36103741
    0x150503040809120f010203251b1203020906040e0906012103030c03020d05040f05060901022d09030d0203090a120302030a03090507080109050601080f030f030c160b040807050d0f0f0305 81
    0x80180307000b01301090350300c00310401203000b0100c0181000201c0c0440c9440d54011070799006c4940804091180c007078641e00c1c00c0440005400b44110300c4c40d41c8914900141403180f03150000f80c0310b6200303510030700307030705089030f044c070004a1003403122070700611102d0012254003058a0400e01c15a0311040e020341810b58031580c8400242c02034049500c64040d00d00c04200c10301c0c1916101c6c00e80049124181e170a4854100020401030301482243d01410f850120001e0201c1c00c0c043d603c0072505541c40c090350641d41840301502c3e648081019401c2000300303402841d01c803400e05082c804502202c0e07014a01c900c940d2494070001c6900401100e209030381c0c1c1d18005c29120482c1c02d00303501d85000d41d4170a0001307601c0c2031101818044040b5200341a9004001504c41400b503042c0326a54a0003003207030601010178204081154807000030020660360510440000701404207896100400f101101d090f1841080040c10700f04112051107000b4100c0e40a0a210a2000d801d16000744583d40065010090682e1400030820 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 36106228 1250 36104978 36104983
    0x50408040504020c030d0608010e03090f030a0501021c05060d0201090302010315170706020c03060103020108011502010912050a030b09010b09060c0109050102030702010c020d0807080a020a030e061015050304080912 94
    0x350078081c10a40d0745000b0b04005a07541d91040d003009016520f021004202c0c0c01d01806484660400c2100071420300da44141000107084039041c030b2036414412a414000058002c1c0042d00b01c0b2035605101c5000c43c00c0217078007802a42c000030542031150342200c40c01c0b00181c1e04944410250707a028603000481645905a070b50083c4084d03000030902881e5000002d0302400002201416111070351b007030fa4529051103080c5a03460790280002070100304007400500c0190046015020711030018800440d000070f03541c40b081445910707810030000040c00092600d115a80601842000c6603040d26418810740c90503000d0407040c0540b5001d0384c411a00018140103100c1c094011149054000c0b00031076503410441006402400720440c082c015005100000307240c2400342a05034410203040e22400103603501c40b40039800940c8500070390018540e075500345203841c0d44104640c510440c40d100c40c890200d42810042010000f101a544003042400c2080200080241080d00d24902e0152030310300302040d60024050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 36107478 1250 36106228 36106237
    0x605030a090c0306290a1403030706060e06010905090f1503010e01020c070509100b0406030c0c05010c0f080c04050609060c0705100e190302030c09100506160c0602070513050408 78
    0x8201122070b000100c107210f11940420184100ca83c601810000e900b001004030602e02c820555004031116810801001005511181c2c114014242d0b032418849a031200107c4500f034104c02182c1519030304002055810042d440003030300c400c4960043c5480c084581802d142c00007001a04c0000c07000d1f18600040d02c09400c904042800c24000755240c200d411610396030350000d442928419181140810989903d4984c0c203410b444546900074031340740c100071041d00500880329001040207107114068000c14801e10440b89520155a141c400c407903088a0000e1030a42c01401d485c0c1c2c036040170070041241e82d45604c00c64a8a42d030546500b0f440d41103000002c0d081c082e281d0b01040e00302041408140040380d000001418650003159401161807c0c280c012030040d0300c82c08000c3d0142d025160158143c6007140a40d03601180600c417071510035031110b001c90080d07040100d15030b81040400c1c0c400010058168000f00182c4030501c01001801e00d0500000c1002040700740c0e12047d59503c01c003040c10701c4a44030448 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 36108728 1250 36107478 36107483
    0x5010504050c16231018030804061107080a0809010b0103020307091e0f0609090e0a020108013503070201080603060f01060522060f02060703060b0301050402090109031509030206100b03010605030a09 87
    0x42007001250340c3e200c25948106049484c0703050106c001540480005020290700b503034452189a8480e901c02009118403100700903a0203091000c280003a041d80300604000616580b07a103014200b654581d0b0a6a400c0c0c81c10a05050040c010400210783c4403d148080b62400b011440c000600455003004803009504041c8040022803030114130290400c0d4a10300b1256614403c10800380c1c006059070b220b00f81000000d001810440041110381070703600c000c00b82841c1041c1542503070701e00d03c3c204281041c0e0b01200c00d001d94201044c40002d568209201c3c662000c0c007a00544550b180c0b1801751048894140120810b00902240d0410881c00316481e01d06c1c2d0059904140000316124080680300b00d144a48241c0103200340e03000588064428003d81c0100c807803d0102c2802c40e420082040040c0d04440000c904000200d01c0000c00304090b8400905d041c041c4500014520245060080c00d08000401c0110040040881004a0142d910480781110050319100e500ca4940c0c5924030040c2c001171001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 36109978 1250 36108728 36108773
    0x31602010c02030d020c1f090e0a0b04090b1801090b0a020c030c12031605090a06030f0209090112050705030607020a020906010c02101710032001090b031905010504050c16 75
    0x4120200b174000442e00480c2d4402c480c420303d9051404207000490307010212100000300d00304001c01020a4462802e50414180000841c034405610007040032a01d51800982d0390044500c05d0080108000d40303004464030710880248840b42c001c1d2aa01c480c96030151411410755800076001000e403c05000b9030b0f840e103020000340d40036000d5070303a1548290b41095500c03c50700e014108114030898040c60489828030000341240c0038040c900902070300103140740d0080c404141d8003088510801d80d03c906e20300d4042d02820818814100190526510302611a0440c038060350182c0d040c40f60721038000802d00c81715541111030348000e507a408012500c0710400c08000350080031a2544c0080140c000c0c1c0c4c04408484403c216158650740d8000c811592506484003038032103013104010340d16a0300d2a00c40086c007a003060419000c02039441d241c05580351720031105151001065504000c0d000d4250045c0e40c0104011507091055080101c560a03039841100c01c1000818040d0443c0700822281050300d81c8590341c071081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 36111228 1250 36109978 36109993
    0x6070b04060504170909043504090c020102130e090a06060801020a08070206010b0a140408070b040f0b070b01120212030309030406090e01080a14070302060a1101050a050108031602010c0203 83
    0x1c02001400c0c05441c101c1c0c205141c0c070850b001c0350240350300343e036040b100c004c00450403034689442c0c25440d60070740c20380708618080c2228140e0701d0184c2c0d01060603107080441e0f01c0d07070b5031a07182851400403284100f04030b0085900401c14064203070985440c64080d1100c01ca458502912a2002540340c0380b0744040051100e1306217200010800c1c0c044d405803800d0441a29051841d544042049860760f5090242001d07000051040400d000e104d1000004800d110903951071529446822091810702c0590000a54681c005000c1c00b0700c0d81c2c4085240001c24005c0c0031582040025594414140d030140100e40e48942109080e2042d5590528500c0201c44804180d0390360781807d04200380c495005c1d01660020810070480011940000d40b0103138101c880c1c29007d0110700c00e080e40d0340f15400c0190402d0981c64881c181003c400f45e5140e100501c140403540d169680d50385901540c82d420744130000d1410035000d29040040001100110460b030045918003e003c4203141d00b8801030310126060003020350548140c50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 36112478 1250 36111228 36111233
    0xa03080909060906090a09080417060613020a0e010f0e09010b040f0503060603100207021203031303080906090c01030509100e0304030201020c190e04080702040e0d030c0903030509090606070b04 85
    0x40003000c120005541c059a255504014045100000d5941c2074001940c0c000041d059501540710300f1100d4803c070010343c5004c0d664000d1140c104101203072100d8580041083c4096072800c01c0030400300240c03840044d814540d104030702521404034030403140d05004140c5c50340c01c1e26a00c2540440c0c42c00c0300080944942d56160f100104298115015060501c01c1d180000f040c103290000b005842081c0c01070040c6001d05000038210080e4010410803a0080c0c40014410490303c001d2000e0762080840c1c07822240c03020780504005141e0750000d040c40325a60001418405400b40101b69914284401c1c2000704540e115410107918013801801003481c5546480d0311040a908040700070001c680c002d82c2140c00704244141000f4045240303120902c41d500e520341041264070410400d0a0380640512402802c20b8499008078043d90359aa0f500b031200e80000580842440d0544140c0c0d28800d06c900e054030159066a6010300b952003880000c0344200c42400014015035204400c9914180c0c1c009004102ea0910b403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 36113728 1250 36112478 36112493
    0x5030601090b0a030e0c03011404061107021203030405010b010f081303050904110d0b040b011b0314030f0a1505030d0e03070902040e0103060b010c081209010f0c020706090906082104050a03 83
    0x5c610329054015002900d510b4501400390700c1e0314940c030079117082e22500c0c0c6945110003001c070701380c0e00c2c05040720030702c5070201581e00c4e0104c103e030100740b00c3c02441d074078a0140380181c21500b03280d2440e4188484c103c0428021640700f14083da02c0b0409025080312a40b103401c0540c0e850144461240d80f0900745120081403420003400b4180800e0088402c1c0441c5405e00108410340e080108002d0000700c001850f01d031203100da400c214a0041c006d06000441c021400403000059008852002441c074a80701800b180040d2480350801d8240410760f005802814800069252191005d0700001c00c940800c0e00c039207540c2c080c0444401495072200031541d035640c1d6212803003154424401954503600d0603014900750f500900075122440e41c04030030940342a03203007102c0103520b40300900104015035850542c0b011548151180e80c0782800e087d00145803662401d071000301304540503040b511040d030820f001000348800c00165041c03300341c140b00700960800c081000100ca409943e12040c0e000c0c3c2d00c1c49000081c4000d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 36114978 1250 36113728 36113741
    0x20a0c0201080a0605120d09151e0e030a0b0f0702010b0319110d031e05091005030c13080f0709140f090a08040905010e070c0506040b0a06030c0905061903030f05030601090b0a03 78
    0x3503111000c20f503581d196100d0101e24148109800329440c0075803082c43d841e006510050ac0d02c000c1c2082d14002c1031420200303242000da11b0044405405100503c44440004482a607001c00d030ce10003070110b0307001000841e8a03250103903200d5091486040c141c008000311031000501755070019001501d0304055050042005007451644000b0300c034050b031050040ca10030380031103010200c040c00b60384031180303000001c5449a0000b0711102039084180060703021148c99000010042c1190002028011003000f0040d080c002207910060440d45003800c008080344100000750360140c2203042e0304200b41d548402c1c1034100400c502c0010000d840005021490f507004d9400b140c1aa010020580015581c0c95407d5610800e03c40000c0e100c2e510110005000440543c451544820b0700000441c0440d130703907620b00c2c0c600b0100e0f4210321006600d45007042203d081034040c640b080211064075145040c40c646000c0c1442407250340c00000c00100000098490f4004e0300040021701e000719829a41d11403151004008024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 36116228 1250 36114978 36115003
    0x90605040c0e040804031209090504030f080c09130b0103060b03040b100b030403021f0609060e0105040b0a0312080603010b102601140d11030106120b010504020a0c0201080a060512 79
    0x4a00100b0304070004a00540701d103a000282c0c501d82811906c0b051a402c903130002240030060200e50204031610b1700d00880b4080c03807080d16288a10802072001800e8000000c0c45c0c010901002d1054540640d11124059404241000f00003050290440101c000c1d24094000b035514101c000103100811241d03090062003441005400700c58035490701d0b5003103a140700c05d88014006a20030030682690440b030080c3c42c4c00b104211080003c026a031840d248060315626840203c4100c00940100150704140c0140d5407040340846452001904503601c1d500041d03058814941000120381c0020401e840940c8042007045000303064241e51001000700403d0a00c0c0c02c805410888610200c0415180300160598140c98500d0075401c0c98003484c0050064599074400240c0311032060070780700c8219803000e03c40c002c0603080c407005013210a4224180f0401c0e190040c1d1109010354810030509001c0ca50080f15a80b02642c246449040d03511003105200140203c0d4009a07807009041100c1c604a90340028244010103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 36117478 1250 36116228 36116243
    0x30102041a1914030612070e07030c0311041d0a2403060b01080606040501180b030f090f0307020d06090206070203010f0519020903070611030c1c09050d0203071703070609060504 78
    0x5502e9500721215050144814001002030022401618141400704040200401220312080d03035400c2d4001d5106060360000c011a550f242c01041c400d9050184031041c6000f040120324261614030101c215250b0040342000000d9040013294152005400401a0700c1c00040d2800b50001c1b407591001402038584800c0310014a0001e4608140d4010030403144541c60041440c4d0030986040010b441c0120201485111305030400004070b002a450f002550040070760301d0300e2003030074034110440038070304031820000072a198000d0105500580d41c1241c80d40e001a4082004030b1b00b100548082817036030048600c001c0d41542003900110300d030511580b000d4440e0311400e0191000030243c0d01590100d00c82c920403503415400118050101600410b0141e00a50b12003084a14040c0e20a409608110740c100c00352030400c00c09404001c42c1640014050b003d0039040351003040c5400c2542c00a540c0e05110712072401c07480c2d424a03490724038000520941e0249904010b003440460f206150081c02048100c03811120745 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 36118728 1250 36117478 36117517
    0x304030e0a080a11040c0212070f03030507050c0307031d0301140403020c0f030309300a0201020c01030e030318010213080102041805130b0603030405100e090711030d0b030102041a 79
    0x40f00c10030707a41c100c41c11119902c00d1606010150a001c0d0394202544955022150107108480042038401c0c028540ca0702c2c1e0000b01d2500806aa0000d8207480800c0000d1062000781400801280c241d103030f01d803c00c9218110f603d116158000103a04225900d9440c119122284c00c0c00e80b01d1492046200307a09031081d1400440800c036842020144441c0c00d9401440480114184192083d007400303003444542180e000742c0e81249415031141001c1007410341055580204658042181120b40f0310700f403e0a03c8002d00041070303103a4a01006220f100740c01c90302144481607502c00c4d412502503090301081443c00300c0e110468107000c0d620030310a440e4205d600360034000c06828148a00d0b40502061200039485001070f45490841100c050301d0b407503244c0030401c00000e9030b44e500706e0300c0510300c0c480751120b01f0300c490070004100071210002d2014080c08000041c121411f80c0c0842107450004603c40001500f0b05080d000c40d00a00840c3c00c80d4400300201801024507000c00c0b0017500c02072041620a1107030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 36119978 1250 36118728 36118739
    0xc0d06050312040905040c0909050a05010507031802220f0e0f0705090f0c0903060106030e0d1d060a11070902091002121605160b0a0e031c030c02030f0304030e0a 71
    0x1142021090014050424442444521302d940c000075002401560003803035250f11030382c7e010f0407680b22520884083d800950b40ba000c1040c00c0c05425800503007801c007002500c000ea0340c400800040000003e104248460005020180c0c442c1204248400403508001c2585140b0fa01001090498882c0703199103d55010050203600c0020104c064036005071200d041034444582e40200c60078044c14a02003180140400d504a481c200011802030009a0300841d0388844800e159091401e82050784e420046000d45031582c034410301000c8059108151261685c4000301c140450b450410041003c81c00e015180e40054101e101e60003030080184c0448112802c006124416a03854245d40d6442c2200f401c01c0c0405410003110582c2800642e019006648920311040300c1c10318030210036008400c01c0a00419200c03941c95100310242c068610980c01071104101211030120300e0891440340d401015100e80c1c8a203403940c400c0c001ea07607642a4804901b5140d0900d0700d0017900444005103441c1c059600101c00145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 36121228 1250 36119978 36119983
    0x5090a0b090607030305130602070308060414090d080a09050328090f0b0a050906120a1104030312090804031e0506070504050108040f0201050906040b070c0503010e100c030605090c0d060503 83
    0x400c100081c00e680c43c190340380d54294042d00b4000c011700e1041413040c5200e804915940000d004081c4641d90f403000034a484010401111040c8505490b026003903010031041d401c0010b4024400c0740305040c011955503a555140b0b0141128440091031030101240009008141c05155222002d410301390042c2040c800340c01b101d51401900ca103003540c6e441c10ba010440300004000405d6900440e10f0010300e0700c01c401700415182d41c016081207900504440401140200368400c003d410621078140502c0c040c81c5841c001c00c40c0382d2125000d40b6555840700000100016407089030001c65114201441c040d13003040182d4900c5c0304203142a903841c01104000340125104d04200c0d810b448050310780e0f1106844a4940d9512400b0041089040c0041008580d01d555500409400113180741c480a560310103403440c100442003006e074801802030b030402e000e4000354400824410050031501c400000c84074103444007100508407591009070405800340030b01c418204002c0052003c180c4100e420f10219948800313156 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 36122478 1250 36121228 36121237
    0x50610020f100902010203070204020415030506041815090f0506010312020307030c0b06030703060614040e030406020d0809010b0406120b060a0806062106010f030302060108060103020906040c050d0c05090a0b 91
    0xc8050b084404900030500b0258803001200f401841280e007450919070100d401c130f074880d4000b4152200c1100d00d000525503d4003546134401006e54043c00002d4040d110120005500b100c01042281c0d40c1d922900b1032481a40302042d400d400580500101c000360420380d0300d8450a0100b500d40318185180310000783d00020071152100d5242d80c0304400b079a44c64489600500000d07041944c5809400000404918240502e4019114411005d0701c544440401c00003152150300401400c1d800600c41004080c0e004038144070300d1222800d18056503500d040c0010b0040580c500c1d40ea41c054a0f11501040c0314210203074201160380710b04081401c0d6224071081085540355441401100d9210340009092400c200711201c2402039400a90301429400c0414941065026000f0b0300d400c1c003105104001345039041042900402c010005040d043d411600800d501c3c05004000600840c1c948440d0f98025125100b20b030522001303900b00300080b00122000078000d50068802c00d12505c90a40041005245103040b1b6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 36123728 1250 36122478 36122503
    0x605090901090f020d0608060115020109050d03050601090e040b040201030b0405040209070e030705030f0c090c0c2a030303040f0212010b0612090f06010905010e010902032a040b0c0105061002 84
    0x110803a030b1900036044054a403565001c2c0036560240038000f510402400750344050304010000c0c00e20f56040140d04c0490720745800014046a0526030042c001c9580031820118002d940d290201c2c4030398640005884058850b4006081e09d84408100001e00c100504044c0c0100c2c402d9809100c0d0285000801c0b003558001d80700654096083c1c1d02040c0858041c00046107200009420fa44203191340d000028202a090890b40d000350700a003890000f01c3c80e0640e03950754450603668543d800d00c12448a099a0303140c8401603d40180c814500481945000110301d84000d0320042c11240c1d40c1c5031a142078201c41502d402c00300e01403042484509000c20040c00740340c11031100600000d04110200001c0317600d224011340110028010300740c441c1f801d1401445418082c06640c8008122945802ca202407812030580c480c590151040c420f002c6d03414214808d4296a0610840030207070800800140d415a110790362044401e04e01c0050001c0000304190829489518200c0c1c464250150181c0140c0c1c03681c1042c20003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 36124978 1250 36123728 36123739
    0xa0501060f1d10031b0206091501030f0b0702011d0102090109060504080d08060406030203060408030405060f010b030c070c080f1f0b060306060a0320181014090d05160f060509 77
    0xb0301c4030078142540b140c100c40c0180e29010512003035042140b50b900072011820001600542c0070031002c184100300748964800090001900c075803654541c0d0021101025004103c40d503954007250a19101750031103440038411001d02c207445140c1c560128000d5103d201d496001c0f42e0200800900240581c3c15601200d4010001d491507420390300d4119070821009007244d50080e544c02c008000341c4c0f402c0040d20310441c45504203503500d041c58204a89003500042030b110000c22514014849880e9000599810090795a07100751241140e1410b0a60014a60000e1480748554040144040f0700050003070050b006a05803800d180c0300780159001075902c800704031a0030050401c04141c0030b0400c1001400304400a2a000a030004006a00d0310300e41010030448404a0001c0380315a50340c850915210407691044400c01890f54101c1e802034600f014090380580b0301600800c0074900350701e480001c418601d5001c0b040c0d035400400180c0400001e801801240d82d42080004c010600c507024008070f03038840500509 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 36126228 1250 36124978 36125027
    0xf040603060e07031a150d05040302010b01110601060906120e0d020c1306050618030307120306090f0c0e010302180307030b04060e0708030429070c060e040c050711010c0b0a0501060f 80
    0x40c490021b03003011510700c1c041410400c50803084641e22a42c2d000c0d034420360011422a031808001010252696082c40c0d854014400400c1002e40004102084400a0400700c070071000e1120440d000705446000c2010700d00501d03000c43c8080380d01080003860181c0881e0302a401c03041e0001030038100c03241c5025154028500704004945c1e000042e40b070000003003000701140d01d44500760b51101c0059188548820109460344030502a040c254041c05100102c000d004210740200d80710700034090b4001c01840c44c14035500207101c004d804030b0318100108041c0c01400300d501455803441d004a00701412501034801c1407800e8200da0050320045440000c86080c1e000031810607042c805c070101210b060011004410562540d507503040e603882c50140500038060301c0004880342c80c1080240601c00b0b01c034030880c407c0f8604501004080d07084020386500c16000805400c010b091800182c82a20809074013621181e14141040030707200311508500e0588078180d54090f04816080c02c01e03030381001440441221005c0046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 36127478 1250 36126228 36126281
    0x40c0c0f0c05100201091a04060e120307030c0318021e0a12050606030c0105030f0a0632012604081e070c050f010f080a090804060c03090e040c0b030405030f040603060e0703 76
    0x311f250f0f4100b801002c2c0025503210390008645824008000741200003000700411101c41d4042c030070130955044030300b4107001001d250070602d40c201c18803950007403088828001d071030f05107210048c00e6056034801500c80101903440f41003264442c4051034003113609100340d000086040c2008a401c1d0f14101060710b4031403c40e2140420b4003e45000100741145448c1d0354000000d883e000d58600440f1024400612030308051310902042c5010324085c040b0b414401054005403440c000160210080c2c1041d5800c240d05883c0d5240010441c401c010b000090300d03820380b20401c0c1440d04c44001303062a80c0b2807512511600e0b0783e002442518054200c0f110b000c1144403070104040f600031030080d640308810810014040d4050380d40c4030030580040c4c01410002e081c255010080541000003070300541030304101c074840e51a0660340d00c2800c42d1640581040b011000c0041400c100c000c03c10f881e00101d0015095444603127030f0308000c0c0280240d12640e1641d500d010301007034106000748a04824141ca4030000c084043d88034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 36128728 1250 36127478 36127523
    0x40302010c08030a022107020d020c01140a030b0604060302030105031513030309050f0f0102040f0b0304020a030311160b09090601080405100506010e03030301090c0f021209040c0c0f0c0510020109 86
    0x505040800b40c0800040c42000c40031b005982e62041c00b607002d26600d0400100c000e160401007200310007994040d61400d4040da800804014041080d020401d80d125000c510841c01390010009003a0001c0740850041500e5425801450680e0030940443d042d8894803160802001019150040740041082403800405e2198111040050042040310001501c9031103481c03801005002141869502260920a2160441955000b030441d500c500b4214200750300010300760070300c520004052041d4100c0000803c42c007031004e0300350003580c0d116500f081555111010142c7d440300550328812801170340000c802e90301801c1024007603a00320005041c412007966021004040180025041c413005c00c104042d2684d00300300440c080c3c02c6d42c3e0070210f0008060000038054510701c4804034250740100042e0034a0250410545110f0502150b010a07980320504099411180c00c060140c201c03c100c4906900340a038400209080f20ba080c0d800610b8240507641c120300301c42d03050781b00400c1d0f0594010712803500c2c1c601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 36129978 1250 36128728 36128731
    0x30f28051615060803070f150c091e0e04060e060708070c0b09010b130905060f0105060708030705210601120e0309040902030c0306040b041203060b0405460b040302010c0803 76
    0xb000400903109440b440f60fa4916000740c001200d419004a122500f003080103030842c0300b103100c101014481d407451028007400c85540c0b40178000f15504e420b4580a01c490000924800424a2100c1d601c640d040a0a155020300900340c8840010310070a0007140304584184107542c4110016034a542e0050666514041020750103010040d4540d03c44e1580d06035603690b0b0440d086010100030001804441c3d0f49801c5051803401001e4075a5484c44074010070064940e401200c2c80551b00201080d90380e0380b10304054515000e9049850218001c1140c95044c01551240312801001c090b03ca00500322080031480094440380360301000c450b001482491120f04198100100d218401000e80c1c914804480210b49400030403107041c1c4e000c00700001844140710391801190414a880d00d414030485003410080702c0349200e28405c9a010306a13100c40d83d80880a94190702c0d5100f1815880c20200f0682d1005c40000d20780071030100f038068108007030300041c420030301000c0b942101e5044e1107054200d240341e1180e18051300b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 36131228 1250 36129978 36130013
    0x609060a0201060902160212010501060e011206031707031209080a0c0303020f03090105010e130201020a200909010b030106050609091b040f0612050901050601081503030f280516 78
    0x4a41c200030a451445001401899615903150a040c61b01401000b400986101c0141c0480c0d2400d40140021603100b104003500c2c400c00e082203007005410344403c900421080d44003414040701860043c00190307246004004440c02640c8100f44101d4a034524000c0360b403000c1004101400400080c1c441758042d5000324031a5002c1d00f001800d200c140310b00601c580c2c1c8102c4280c3d0b05d81e507503a00140490b850300700016070085900b84035080901c02540c0081d64807208001c0261a810b9012074000308410f1803030340b190b180000a409105517007041c034019030207800f00030141d82c801d5003010b030003007aa070510340309458008400915010081e2100780c1514000b403148041d42d00110001c04c0049520b10202000c10300820a6a4401d00b005584044001c111100504100c241e80d04050900440c2d0380c5c015200c80e000544d00f084002140416030000b4036600c1040b2504955520201c0c7e80440004c040301081d8000c0002c040e103521252a0304011581840790301c040107540d0040c026004017007801007092144014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 36132478 1250 36131228 36131231
    0x30d11010b19031b032a08030705010507110c0303040902090301020f180310090503070201031109040606020106050306010605030702190f0c090218060a05040902070620190e0609060a0201 82
    0x18000c4012414002e80311040c1d21650741070080400400101c10310344c242c9070180c4029001d00504680d0f8003096900340004900581448000400b01004070018102c0184501e0080387d60300c3d0700504d02580600012540312020440910840c0220725001c40d0000e40500300401031072419082c035036444025048640710a41540d400d211555900040303100400d000743c44554242c0702402d80c00101403820040842c20a50319061401d1031000990020a8810035582400e02203992901d8001c401c0b420301030f105007203a0041c00c110300019801e406500c801c0580341e080d815146281e0300d81406491078401501c4600c016801140b0402c41440c076034900003c9a8400c0038051300e00711031038580d40e85000381500078001d01940021000b0b00000071305100410b660090b11034900b84106190082c00700e00036482900401900083c0c040d003040501e503c400c104440445400c0ca43e5815441540400d80200c00407948240c180520316a085004030440400280700070055880c01c1b44400500c801904484405020756 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 36133728 1250 36132478 36132491
    0xa0305091c0903060c050a05070308060f04061d16090618050603040b250207120f0501020c010203010513021315200303070306050105040e0402040905100903030c0e0102010506030d1101 81
    0x10103012640e006000d2035030750b6101c182d07070850601d1803c85000c90070740000d102040010711141a00601a1001e0907010304282015a55010105240c00d4400290030b50040c80c0001c0880c001d8600c0000806d0045204041c4848d503586074001032280e02500c81640104007407000420001d131085107020300060010030140542a42d50000c00c0264102740d5048804000c800200030f008040428050368228041507000402d0504210103900c4003414042ca0322503104500c03440d42030102402c89a00e95030343c054021540d078800d0658042c000e400c00c1c02414030680c509281007040541a009540c0454002060b05c8181c40ca0120b0802c6110702494050040c0b1046000310250ba62220861070b07030124808003c1c544e2403402d80c0c401001c80e00300380c1045046c030400740030a1020401b40801c485e4010340c10b0f14002000c041d2820058600428542030304100c3d8100100c0c001015450b81000e82c000105465803004420310380c00590a8900c00c4401c260154080c1d04429105485801c07542c4800c0c0d0b8400001895 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 36134978 1250 36133728 36133753
    0x30121020a033002060403120c140c0c1005190302031302060d0614032a040e030f040f050a0b0702040504020109170a0c08060c220b0307120605030609030a030509 71
    0x2000c000d440034070300e00100791800b03e4140600300360001409aa030310103401d41c1e160582e000707488c03196101880284103a40b5600030382d000f409101640c481020040016448000c0d40d2000c603514080c1d4415140580c5900740e03c00481e81c0120107840d0011124543c1c0035092240e5001100250802000030b41100c0c0320603030f000d0160300c52074000c0c41064041c410100c0d03100e0400e004200500c0c61180d0940c000d510000e18102e80180c211000081c1d030320008410901071003400006005815001d18000c0b19000000d40b80000d030882d400100f0481d65803800301986159075004008048000703115182c0c10800400c03540f401480d15601c1164803074030504042c3e248580340c4500d028a845c0c802c181807401d41c0580c040c1030900410120400080c01030034000c06692601030301c0500701d80140e060700800c108219090086e40b1480401c0400507061070902c0c2034403458422402800d001c2444c5030300c40c1944ca0142c0208040c1804915184140c0d0650000c500e0014420740480080800910b504424003032060a03400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 36136228 1250 36134978 36134993
    0xa030c171b0303060102010b0319030c080f040807180b09010311010c060c0c03020609010b010207030b070c05010f1a0a0303050a050702060405130506031506010c020d050f010e011a010302030121020a03 88
    0x1001c2a504010354403490000c001a08440e2010b8040b23120360b001d01d80500519426036145008254145030481401009150280c418001d07591040b0300e40c01c000c07401055035500081c1544c108c0706035010b0303a0040050703c0e4801e005c4030303160b4040700d81000c9000b0050002c180402044080114180740c1f030041e005141d12210100c4049080c22000200c1e41c3d6070001c10315178104089500601807100800c000c0d408440040d584007601d22000b401700070041c00003030b60030380901c0b592012107821100921a02c0000da1302c1c3c2004100d802498043c3c0310700c029481c1c40505010f081042965455140c00b403801241d210151500e4100c01c40c2240e01c070000700804901a11603c0034102050000e1202080f242803000030541403451100408800100c40c80820032960780c4444141c848a40554200090b4a101d040050030280c4140e00b01c0025030901d0309950300484154401070104440d158062400c0c4c41c0400118141d1100303200b40700480c0e405102c0c24045031818a0781040c2c1a20040074004210798980e110503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 36137478 1250 36136228 36136267
    0x9060c0706180e0108060708040f0f06060501110115060302030a1e02070b06090705070b04080c0a110111071a0d090c090e060a06061205150604180b030a030c17 70
    0x30005440c1e15540b5a602c038103241c0d000007501000d8406030300d40d81844941c5503a030714010b107210104100340011400b8070501c00e044200c0c49800c032100740c11141e02d1342001380250000c2d21403240003440707510003064880c02c188072705040300010015080b503480c80d104088005c0d401c09001901c0035a964400d2030304000c0e52105c004008840003201503160036480c10980b1061a00a1501e4001d1201404001c04550f10000f00c3c0e0600b603102070304031800d403514240b0718a580204510700d07000d8030802c190b441c10320a0031103004e5083c40b800d82e10040c011151040b00340c1c95011b2445a1800d04000102d03034200c60788184003810b41e80007040c40020b03041807540c8410404400b254810365030107680d5155811404405e00c607555000c0494501408194a0164010300b0361000c091240c403020380c0c580110f64800c001071160b900c0c005000b48040e0300e641c0c87d800c10b21300056800514000c072619050a242250a02040d24540d094264440680690582d262303a0704419495a407103148482c03c00003026104452051038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 36138728 1250 36137478 36137489
    0x30c030102070317010f1a070f02060f0912030c070506030408070602041212090b0702121204090f05090a0804060c050c03010507090314010504110f0303160b0412111209060c07 77
    0x203101d4511304603000d18001060308090155403941318140000880044080c4206150b03501d92551080c0d2420b02600d04422940000c3d404900042c140c0c410080f404081c0c1110b5804481d811300001482442980d28441c0b07541c01142030708a24410403880c603161000d50b42c0240a025410302d88407c40d50b55804903070054000c0c41c4e0580c0b40c6500c0c40103000d0000c0d05001c450000c0c0c1400b100321030801d070030704600c2e0003081d000900c19800c0c1100c41060351002d110406580b0006407510351a41c2e20340016802400d07002030840c410514003c00100b1130a000900b01e4010b0340c110740780504c1d141c1417400803103c2805030001614a8814441f0694168900744105481454503598a819407415031400880264224210120302c2c4c0c18803092002144450b841413590344011100c9000900c0c80c0b030046800d50007100301c9091007460200014040c80604401c41b4802c500c1b60340e1030020040400d800342c40900e8643d009001702d078003504280501c0e4011000401002c0030052005003803d003001b0300103103001c990740c204 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 36139978 1250 36138728 36138737
    0xe060106080c180f060c011a040e030f04060302161704030c080d020601060318150506030705030712080a0e03060a06080601090c0c020409061404061b0309020f0d02030c0301020703 79
    0x40000a9114a0040e0000380aa2140f4a80500030200c070080418001d89280b044ca00407001e80032594940707048030000a035000c028850300f142c0c01110400e100d0541c094600840c1410f404940990b804003c841e0001144444030f030505080c484120025004140c1400c03410110040c4031001c9454803c8940d200100c242032555254250709d450030904c2d80d81d81c464016640140540340c2c0098000c150b1070b05542c840d2030001070b100f0354601c54007452048424090010207401c004110340320025000030b0300c03601c015000c45207000d0b03803030703041c140e5600c402e101d200c0383c540100c9910400242400b00804510300ea0380381000074a981840000c0c00c0100070b840d407400044c0d031454100a43c510601c41e0500502410b6402c22134003840c0c4070082c010110991000f445541d840890300d0403c00154020341e60a07000c004c4070100c40ca441d10703068000b00041151042d81744400614525010300c280200c05146034040c00d0b0030034180e0322000303126030102d403280203d0303140c01074910a84907900d091006c1c18085009580c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 36141228 1250 36139978 36139981
    0x2060c030c100203010e040b0601140d0902031209030a060b03070e0f06010f0f0c0b0a06081218030106050a09090512030c0a03050105030f0706050a0e03100b090f1b0702030c03010e06 80
    0x2452400b40e01c680c03541005401440100f140e0050007030515445a0012400d0009540e0100102c03608140030445020804001c10b0001c42445903a2180040910a07000c58114003890700b2030490901512800e50b926030300a45540c0005040e64020741d07051040038046540060b181c480c1c10701c1c042000c9031682c00034a140802c01100d9a8052152072603055941026100c0303900400c1d004000e40005107002c1c0000039400d0200e886000c455010100401c801c1c1d094805c214203030580d49145601c1281300d0944400702090780040703450188524811a08000c119001d00d5280c00c01010240c03540400980f8180911007841d2403030008000254841c00040403142c2d611144203030081c080781c00680200303009900c03254900c1c51812001501005449503070810b0ba846040040c01140e1a402c400b03001c0d45c2601411b408640044001d80103200711950440f04400644d8070280558215482103c500d181044220441060780010b04000c00303030345e4005001c1d0380ba0451841e0100b400d444002d0340c034281f254040710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 36142478 1250 36141228 36141247
    0x703030c2304140a05040612150b1c03051905040906060503090303070507050717100501080604021302030702030702040e060105040b01020f1c0e03010518060601020c0a0e0408040302060c03 83
    0x140d225103014200d2122511034428154a6450781c0200d0003071490220309400c83d40c0c070540d1842c0a0800400b0020000e21016480d110002241c0c1e042c60300440d44c18400c2c82130952100024020440140030152006903075400d1100050180d03601d8103016000c1c03000401c11040144107041c0029002a981d4071110b50712840d08105030212031299001004001052062000e4554048101c94008840f450540d486501c03600342103003000400c5d44400c420b521516410926000c0104003140341c084c0b81103081007640e07070301c4404503210002150300a40c0700c01a0705400071149440c0d806990400f0300e0748102d900785050347e40842c0c11030740007010202c0264030100c0100510b280034010161804800c3c809170140503800030720142d440100610100d0207405050300f031542d0600c5043c89507118803000b00203100c641070501c403e803000090400040428040d2900140c920750002a07135142a902c003400460440d840c0604011070003101a00889594804000000150380d404000e41207044507000036584d14031144 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 36143728 1250 36142478 36142487
    0xc0221100e1002040e040609020307080703050a060c141e0408010c02100f02040302060d0203042607020306061906030f1d15010617010e040515101406070804051c05030703030c 77
    0x501010042c07500400c402c0c0105017120268940095200001080d00c610b01c0c070000b41041c5054010741c0540c4151000002400f1000559a400790b000380000c0055808542e0129000b442c01038070520a09020481d0a2164040c503007005619880b0354a020304098641e51800d0035201d69003c03000040e0301c01504201d00000901c00c002643c07032a01d104614080c81c541c0451110700a414401ca001c0383c0c00310016007400f1030a000c03203113003240c1a0001041070a0302c00074400c8603086080705074001d21803080010341c0e600707085607202c40580320910943c550b1860305004801400640880741500e035150075190040481c01c40c0441c42e41000c60014180100c0100b650b000c070b481c0e05a01504c00c00001d01d2039070b074001070394100d50b506684c000d44507000309035245c0c00c0c0149401c2c0d50910440c024061841080880082400050103448041c40140c2100e44c480c000c109042c061844003401d1084100003c000a181841c54101d14014211710080000c006440b00d42c1190400c240c190003281e01e50b152a0601e9610 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 36144978 1250 36143728 36143743
    0x703090306050702030406091d072d0903050d020f190201090f0306020c060f13030302070f02130b030705010507051009030909050a0f050603010c300603060606020c100c0221100e 78
    0x8035454201445c1c2c504118405500007034440000c2c8044030b80f2f0041141141e4820078544d1642c0700f01190052104c03a03000380f015050b072005540c0c038003541c1d09200b00f1500c0494000e802c90b1440d030003490408070042c0d0301080000180070490502101d81000180320007450a8100194010600140c44144646000782450b40042001403255019002c2081084416401d01e248541518005886032024a0422a27011001c00d0203540200510304051440b009030300801901001a0181c840e80d80e59440159024060414000c00d11380000d17401035140d0106da81f12681d614000d280c50407403d81d035499207001310754007524031710201c0c0d031261742c0740c55451914052280c00100c140c0080111703610f0f00b00c0050992455020b4040c201d404055010441e408a1090740b44485c080b101c00c001d02a0b882c1703851402008c3d1b5210740c1015028900100206281c800441e0310701c0440742d121004c88210726800c00041c048032070441d15240e804943e041c214084100b1015400a140c070b000010740310b0030b44000d6880d0004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 36146228 1250 36144978 36144989
    0x4061701060501090e1f09020d15060302040609030b06030c0d06140c03040312050601110d031b03050610050d0212010e070e150d0b04020405030f031308060f010308070309030605070203040609 84
    0x42c0702d0010001c0301502105a9403000384a90310b11906c04455024003e110000d920205a240c00415608111f80150b401b03169101840956421503030750784c980580981c080d82c4900000301c0c0007084100003050940c050590f00c807000500340e07076004404000040032112400f10036511142d554400f85400940440303044d8012840c0150941107141680e0000c05045015103132003040d9440710b010500c164001c11003c5120041d80040d22083c0041c004020000c0c118201e0081a80c0642c0349401c0d8198041c3c805e650142d00c0183c00f4140381005054103844030303031000c1a03c504055080043c0707074446820800c0b8038040c0c0080c101042a500b4005801030070103100d825410311800010482c00b0041031090304540c056940004041022100d0000040003802a035010350f8140c00381f0503a011b00c40c10b010005140d00d50b11041daa60781142c442c403410b5075882080f641d1241126068005001250080707000d844440d2003840c001d100b0303036140c0d6111345c00c0e260150b03401805079101083c00e2002c0c41c3c01110b810050301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 36147478 1250 36146228 36146237
    0x507020304030209160c020306071701050a050109060503100302130204050123030105010c020f04090305040812040302060403060504330b06090306011716060903020f030a0b010303110304030204061701060501 91
    0x1d0854000030301101001c1c0c00b0707180c040501c00103009064086e040d1441d1940d0010181c60080c070f082c00e00a00852500010707505202550400801c0d079180c4003011a0a0303907170695554031840c2c00e00300241c03110f0340080c1c202c0c11503140300100040140d580c2c1880010b041c0d801c160158580340b408002410800030040e800304680c6c070103040100002e0507a81a241128000d1a0070740704503800340085044902402d0080c0d80050800d03400005040c1c00c20700410850359000c080340c030480144404549640514040250710000800c0204041003c90700b00c941c01601034a14109580c0b03a0601201180ca84070903103181d85c0c298403111142d09452881140410042501d1080c45e03e814000020b80751501401220624031038110140008403003000400c0f40040400c03455183e440e00c60b0f00c00f416601091008030320680402a2282031403d0215011380500c0d0b01210f8001283d0866906580121004040314410b1205110000160307586006007401010035801c140c0c01250034151031400d440194100d1810712 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 36148728 1250 36147478 36147487
    0x1020702130b0604030203030d061d0708070e04020d0903080603060105060c190809060403030c11120613080c070303030f050609040f0303110d050c030a0501090605010f0c020301020c0303130605070203 88
    0x16101c40d00503890700044a0400075294884000251031805180c00194041c4004641c1c01d048a009502000998000070380009400d4040030005918000032244100040e100358041041e0600505042c504650010405418203094000b04411550104415400148541c041c00003508042c0241d034003624056032614a001c100800140d03139081650071191020350702016070700901c004001503c1e0346940040c98190b950b07541c4d04008100d2034100314103480c0b02c41001805041d5103000c550340d01c1e10100c580041e013070660700c0842c02500c040702020140c44415003003203542718009040c0103200103144203840001e00c945040907028201d420041507140910b6505080c040802e0b12081f5196034194107290200318880306100840d510b01814440c110014149014844605000c40145200300423800040207180e036507040d880d0580305240f060764046842028a116814414120709420b48d00240002d46040104001b15113964811200c01c811740e48071455440803c606406503681015040c4015800d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 36149978 1250 36148728 36148733
    0x305090703030509030c0402041d060402270a0305010213170c010c020d030c0507030f03080601020d0e0f0d080f0c0d030606140c0c03120d0c09080a060203090304080601030c030b09010207 82
    0x22480c0a020140c02c1c0280840e6041c00c40d90200000d910b1180c02500c02c0d515141e039070301030944140e09008418481c42001000942d00e05151098400c5002c00cc6800c01015800302c40003903840014056890704000040c60110120b8001d0004001a00d001d0821b01c08151500b810b02455100d08120391101c0c0e04240381c401042ea80c000c08a0540d0b640403603080b03240760030514094615403404c0c00020305038001c135180002805030702201003807131601a89402d81242e03205801280c40b5a6044100008a4126114140c0a00707200340c140c00070031005801e810320803c0039242c840d059003200481051034032002840c408444c4040c48815981d80c8103040602010782854005050390403044030382032207400c010601c2d5002601c10041d19222100240c1911440f0804000d902941c2d401800c0c01080e0508003055148024800c00000007204c003030f0000341512800d5559240060b60000c0c000e4241c9220a00000c20307012020301800d030007140302e804040c100d03038070758076008007000802440102140d106001002c003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 36151084 1106 36149978 36149983
    0xb090a090f020a090b0c0604031416060e070503150105010f050d0f0b1c081204050a05060114090c160f05010f240f0501020a0311010615170601030509 66
    0x19003e0b01c0e00e521690511401c0c91b00b400b03070b5014600140100b44524103640e085140a260589032480000c800400b450103180152402d84da1055081c00c01e20040041c4401000c082d8040c01400301d540791500b8850b02c0511810f03040c04030200095501e01e00c0354044655800702080d04001411546807100c009002c20541a4010140b030840c000c940640042c1c11151a640101880c0ca400780c0645140c0794290080e00032541c41c8a810b084900084050041c0c90280c14289070300c1d0342440c2d98008100c2d42d180e01034210600c0c000200000c8411a00b0700745001401c54203c9119a407000701d910307005004011050501c1d115a20344003a203009440400c0c3c60340158000f0155a407149902d230307810986000740901c00d0b180541d000f03000040001e8000c5000c468185041c0000062541e503031007080180d481003061000009100800020b1019500c115103a0001404c0c6020030291418008065 = true := by decide +kernel

theorem cover : BRFrame.Cov 35971228 36151084 := by
  have h0 := BRFrame.cov_init 35971228
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35971228 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 35971228 ≤ n) (h2 : n < 36151084) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
