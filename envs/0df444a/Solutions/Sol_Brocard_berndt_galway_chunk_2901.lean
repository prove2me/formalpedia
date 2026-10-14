-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2901
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:05:21.517105+00:00
-- url     : https://prove2.me/submissions/a9cbb526-bef1-4fc1-beec-fd8ca5529cd0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 521582733 ≤ n < 521762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 521583983 1250 521582733 521582741
    0x1b1208041203020705060a0b0316080609070608040209181606050d14040b0f0c16050109020f1504060f1b0c0503010506011407081608030108070302011701060e1513091409030a0f080613 81
    0x40c0c4000203315520300007003c03500700941078000804202c1407005100140e030f140e420041d000801f4001600c1d00d2003842d044945406940004521007034070109001071426001009403650910f01402404006c0b03001c18295583c100440b801440100003401145424600301226a8040300385541c0e685480d1003824403109005405404a0b026074440317601c0e0046041c4001c0600d605030050720b0300c17642a2441d00b1000e0040c0214005c1c242045140c0070580d035054480c424404080540e2803901030405c4603800c1c0385c2c8940d4214029180250f0074030b0042021035100e1316000340c1c079144103d600341c103000450ba00c41c95503610180005089009001003100801c4d0070000070360007040c140700208a420301d58800940000061100001700c00031881c01041002c1d0801c880482c400c408035010b038084096907a01030528014013014040e840384c00c0c580803510703003e26444041050340402410341140d0395040744990303c3c401c44044000040a65068041241c0075080c0c043c1c00040041c00800c0c041e18070b6000360115 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 521585233 1250 521583983 521583989
    0x60804030f02012306120d0f08070e06070b1f080c0f0a030219060e0603042003070308030a1e060807061209060c05041e080d1b1208041203020705060a0b0316 69
    0x130040702007031001620348505060707480e0003017101134030019045190181030b810315a044002440006000107110910030f0300c0d450f04000001f030210b6220841c0f070810840e441c0088230b1100344003040000ca014507101485d0941c0441e400c5078014810840c0480a00c4007403021210f0441e0481c00e1884003100680e11032a9001a0701c0e00143c02d40c00d000e2906c02c0042c050040240d4240c0079080820600003c0707460854a8002c50081d0581c0b01b84c40000c440202c0c0ca0954558005800070320301109204170401c01d90008825040d10305c254407203907101c0c1c018120488003148140c500c150b01009042142034080c0004250000800100064400319a100e4800703882c255a540b00001f1000603040c0428071108181010000229140303802040c1001070a582d207086039031051041c004454100020501c0d406008048541c4c0120410b407900d9642d140038042600a0f20200c490031040f02c3e004040d5846407080c0c5040035007140c01000162901614800140014116150140a206c40707910f91160214030f040d0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 521586483 1250 521585233 521585291
    0x901090f200a08010e04030504170f01050406060f0b030f01091e150306061706071b1e1a150f0a030204150905010f0302150a260718060804030f0201 65
    0x242d145407480052040030142c110740c2c1c0348494002800046548907050700c041d0382100c140c0b0544808260801441d040e207890321280b40e13609000801040007100d41246c0c044806441009607600c0e00c507512001c040c0012600c0003503a42a1b5401080002000e4000100e00100001c140b10120303640b0046806841c100414400002e5407030104008120340e5110300e03001000c4000304030021025844c6855203a140107002141040700002c4640016600508c00004c10f90340b0203d0090038589041d000c3e004400d107250181ca103900f451791100107004d00042000d1007040c00000f600074082603d4100040340340140388040c1c010510311400300046c2c0f50380c400d91010080c4118001d42852030040d0107030a03514140c100c82e03210800444104010784821008812a02d40c2c0b04400740c4442c00d4820403955000c0d8000d050400c220b081c0c1c041b0792903017062403000340980307950f5035040c1000481520f444003880c034911403100001c040600142c082032080b00d684525400520001c54408090300c0100705000c4074140040b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 521587733 1250 521586483 521586487
    0x503100b011b0629030a0b040c0506040e0a0f02030603030403030c03120908190509060706050a0212040f03030e070e0105010c0302070801060b090102010b1002120f09040603060222050901090f20 85
    0x100068034801c4103490303041002036284d042c520420100f80c5421141d00300030200d500c4000424100641d46031810040e02001d80303000d490b0303603642d0709840040c10182c1d170316501580313004a809100a0fa90003103a00c034480140040d49850701e907030ba080300c0800c1080b03400e404024400c88164024000b0307000c1c2c141c07254000c030f07a42a103445407641800c0004540720240c00c2440410042c481640d2907040c19101c10b1504040e00203621341c0c0c1c514500e0040c0c0329000040c04824074880c200010000c5001d100e04a450003550304010886520058a5441280c0e014400030010321310010423840d841000384d40d0900f071092040d01e4640da55030a26609440742d40e00420100880031440c00120b503030912480c3c0b100001291440109080075601a4030340d003020440103c02c0e4000143c0300001c041d18012034004004c0500b04100d1299203041c004000c7d0004c003d80940c010300941e030041250950300104059590090022886901c1e0042c5100104080d00e8251949130311204800701c400c1d003c8155494074640f05c01c03d41c0e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 521588983 1250 521587733 521587751
    0x209190302011e02060a020c0a0f0804030b010b090a1211040903030c0f02011a0103090201021c05090f1e0f0406030b09060709060f05030c09010519090f09060503100b011b06 76
    0x1408204001c0f5011406015403019404030560000f07000f50040300a190060799102520012410710800d024007400c50840300861008101400005104580c020492514181d0700d40e0086140c038814485081e0b484424400248480d00050040c2035009100300490501c91081c0f1002c60103a8000b294160042076440016103d01031704034000c21908560361002304107031440003111480009036001124100f40d5540b401c103046900810164400d03081031000c880300b00c801d902c0002c3c0b03281c7c40000e0341c502920060819007801d0420011003801801b1031143d5202030503500040c0b02d402a549a4829403003038035440000041520180c40d68050403031180030b0701031441c00a00291021105074408400c06c603899045c500c81950050540303030405032420701141d480d8001001214140103051140034002498099840c0b85c5800184000c00c4410101c540f00540f503507482040100c4400d849a00d8158000380304015070000c00f40c7c0100e04a900504129100e00c0c0d01c1859101c0311800c04104464042d6500c0e41d40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 521590233 1250 521588983 521588987
    0x30b0a0c08070203090108161701080105100501050415030c140a17060901050a0e0c04150e010f0801061d0a030803040b15090c1b0f030310050a120201090e070201020919030201 77
    0x4076034000e00c1030009602e001000f900007024070100414180c400c000e2a45425100380c42040d0049500708040544100c03541c540d02d525000705400e95280031400100400040c05500850503101200c1070754541c03502051010740c090b03002c1c100e83e0b02e11a041050300c05002028140010191408881a40d41c00103d50810701c250b9010300d10107451103204039030280040010b5540d040c40a000d1b40c110f1082c11480d6150000081d00300d0146402c6410b050300c1070700302d0101495100294904044c826680c040415001000542e8542428059140002c50490640d20b01001001e03454000b054040c0501d4042c40ea41c0c0c032854580c3e04151030031a0001070f000c00307000101c48401c102070000c00c421503529080e41081d2030300c038010340b1590003150350810844042044001c0d040c4141307201e88007803000740c903500c0c502020351074980f40312400b540c0c1c842c2103010008a00e00d410045141446a8180c481240441c1030000c1912680001428a001c40d0340802c05084561a001002d11810006c034020f0403c540c110f00c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 521591483 1250 521590233 521590247
    0x908031605060a0908041208091003050f1e01061d060f0a09170c09090c0a150306060203181c060f0911030c0f011d03030408030a08090307050d1404030b0a0c 69
    0x1c2c003040e5003013004240c0412081d50841c0c0c121072a003100b0158807a840d280c0a07805001e41c022240d403009201d1441049280c1540090707100d15280100003820780e595a100e602100b03032800c00e184c034040400c1c006000c00343c0a0024100c000c012050030310004500c21000035000e43c000030030605480c0020407410340280e000200000585010010304003420050103d842d82d0f1010010010311901141000c2201e00ca014020914502c001810800f0070075240c0d905044600c00000008000a291890000da07091010054070740d6201ca00c0302141d01c1c030040304104090418005d220390f808403030f20001c090020301c09200d81c80c0400070410020405000380c0c1040c1e5424144c0080890181c0c12003600c1907426030f2462113140384d006007424091081c0d2024410029811070302414690540301c000380109401304004003820314032925986240540d070310201c140e40ca0740511040280960311000d0007554150064019005100c4690011803e003a07898880764500c3c0e1081d070f101422035903501403601d0800c0d0311001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 521592733 1250 521591483 521591491
    0x21305030a08090409030912060921020714011115060f0a0e0402011101061715060409030206040f1b091406030601120b060d021513050a050904060c090803160506 71
    0x10107405a10a540c450074064802c0c007480c0c074401c954400480e01090300840310310002d0242c09401da814641c0e2850000d004080c00030059031094040c0403d0700e5014091300d0084000c200c00c1c0e010341012031405112043d030418490350305051000281002050f00410440c1c003541200c3d802e00d034230b92810910144640c81c012400070900038040d0100900c480c00300322401d542c0055081c42d0588810200602d543d00411103070304100c441c0001d90710100304c0082d001a0001c0d021003c60060303181904e070743c002c103c11105c51280c000c2c05a00318100090210b122801c145e00c8103802009455602c0d0224800c03c055000e03250850908281c4e40c1c070b14490810a80d158481d84814103500600c01541800c1c070781c03da11130349441e000f0400d88680001417541d4480c0407211b1030b096406032001903980010b201400058002010080c02030502d15000100e41c5001c400490442d100540800c6154581d612880082c0c00c0c0000008288000c454002602d480104000c1c59240c2440da0150146412880c0c058104040a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 521593983 1250 521592733 521592739
    0x3020d0825200f03090a08030403110d030924020d020601050906100c170c0609060c0910020a050708010204180e1b01200703030f03050f01030b0c0c01020d021305 71
    0x80c00089105070741d980050303804a014200110700110340000310100c222020703000c120318081d042c80300c40180380000c041c00c107201003122402141510342196503a01e0050348400b400e03080e06910a040ca50030608008064140a4a00240010340b11808014101c003400349054050f06c0d42030105c15504c1e4140090b02c0b10f04860700c050607095142400240b1035413009002c183c4281c40c101c000303c1100780100506c60384a940002035080c0c1d5034002210041581010f01700c0a003c0c0070300000985048800310b2000c0c4603287c0d48440794144400d84090003990000c0c4040c8030190f2140800d1000030441c00c0090000801c500800540e88508040c42ca0341200d4030160703400c1a01c0c0c10320b2140d001142011801c540d14444c04100290b1024071100102c400c14046508071541c040c401280c96026000070a9020580e8003030380754048882d01002045048030002c58072142c00d150850010700c00134985e0041c0c6030308051942d060354207068001c0c2030139003260702ca585d032100881c2d0b001495242001e046684031000300811 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 521595233 1250 521593983 521594011
    0xf030114040b0f2112040f06090315090204060e0f1f0305030409050a181505010b0a0e0d03020705040e03070506090703020306040605100b0a0c0501060e060a05120309090403020d08 79
    0x40000300e030f28040143c4a582c42945a01814003c0d1041240141c1400e18054104d90706000015004c1c00950300c20300910120100710309020031000d005004000440e58042d80420f54035040c1c030034641c014545c0d6401280e0142d1a2100003a500c1200c1d20250300800d038040400301e4900f0480600702c0240310300d120400340d45a1041040010601c0481a201100c0300860041004d41e9207a20050040200c40304007111130055030301410a014144034004d210194040302000b5698883c2c51441260140c0c80d809000180c582d229625141400342c07815680c0386c400d00464801a4865001401303840c2e244a0301c00a0380e10108be010103016040120b5030700503c07448041c00795130307003160003013078940c0c10040000d0900740c0c680d404034015042036503a140c020060704100c0c5403103064114000b80040d04030f01c0284d070150300740f80e0b004c00c2c041034000c1440e000e50002040491040d28101c1030040c0d1040306c034041d84180c0001d04c2060070a4407034420180c41103211340d000e8042404d0081c4003400d248009428031200c2641 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 521596483 1250 521595233 521595251
    0x3020d050105101e03030507050705040c0503091b0a06030e151305010b090609040807030c0c0603020c0606040b0a140303070f0b040b0f091009050c0d030806030f0a050a0f170f03011404 81
    0x22084013802500e0305441c15550360320460400502d860141d622041d005480e0034a115013440c1c1c00000f03580070740090ba0640d050048c0207892144402c0b20000381b503030b010b0040130040003a1750103039110b8030310b000c040410350f100040043c0340700141d4101241c1c0280d0000c565544441044028440c210034200201d4184010b030800c000401c16040f401040100b060100068103000c0c140070f5005942c1d01c0c4d61154803d8445516028010b029400488240b03034684a1480031590303528280c02028213a90001d00a8401c040c681281281d480321121007881d018042003041c03402242002c848840a5401100b088240342003514083e1500380c401841c041014000c0001d02000724004113150a001c00ca4a20100d0400158103055040482c01071601d54041c0074200d010040507001202284503080071401d40c1c03405034048180d15128010701c6001400e0350030241c18280054104004003c401d800b0759442200c0200442520300c159019140c121400d01002c0010402c0c2e40400c5000100d0084c156014081d07495 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 521597733 1250 521596483 521596529
    0x6050a0e0105041119020307110306091f020d1b090608010b0702130209030d030e07060203040302060d0e19030c05012003060f0112060f0311010203040f090903020703020d05010510 79
    0x4818042c09125a403681090b0391300e60141d400303881c6044030f4a446009042003d1101030740c2ca9226100450303240305007100110301e83c80c1c040f500c0c500ca207404202501c1c0c0060402d4104200c000f80300526860141c1c00d000c007240e90b500c18412106405584800340c241503e210f0030182080f107095202e442000500d100500510544409a032449a03058880e960204d841d18503003400fa000301050300e9058400c0c2c9440307000b4290f054000240907003c0c01c0980314590349691080f0713164420303400041d4000e8010010710145c0401c50f404000038025200964004500b00381d01c01c5106c03031506c64180d00081c880588881404030a10800000c4c0706075507401100001c140240760300900000709864425841c074003c4071990390140c00d00c129400c0c600c450030042107071195920b68810700280020781d02d400d0006035000855000000300c400345c48800070046840c91501980602800a0a50440c01c50041d1440000103859483d0610740070380c400c0d0004501845d0000d5400031701d0075283d0103088100400150703010000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 521598983 1250 521597733 521597759
    0x10f0b0a060302130515070b09010209150c0a0b0103390b0d09020613030c230d050a080a27060f0f0c0203070602151024032003070306050a 61
    0x1031182c10003603220403141c0000044080e2992216403c0042c070341c0c000c2e103070340c000b0b40051043c988295120f80131500c80c1c1c65841d00301d0140791460b0340c0020082c4540310170442540090301e00305400300121100352100d0f9031a1000b0384404e80c002c445d40c4007600c201844001042c4d51180102c4407484e18a903100a07148a00c0003c001c2920811850810008028a90b1304c0c041c3c000d240c2c2c0c1500609002d54074400d4036000350a01c01144401d440280085001080750340ca141c07054070960044180728040020020300304402e40340700940803101ca00c114880c400010749584058900403015894040341c2c000340024034004d00f1120003500071850b07140320060003c95080340d00d100c3c03d000f90b458540e0440300c070783c2d4040d00c00f00303a000b03006076051060f240c2c0096201c0e070000b00c6051514a107440c120799603c03106241550b0703140c58000c0c9810410004c46c0340c1400b8032884100183d0310b906190104288504c2607090741c5070702d440300544021240c0002004403140c0c05000308001044240d416110480c5840028030b140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 521600233 1250 521598983 521598989
    0x9011401020a06020d02190207081506060304020f030307061b0e1c060f02090d0803010312090e040b0705090603070f181a0912030d060e0a0207080703031e060e010503010f0b0a 77
    0x1440e0701054400f0191059410389000720108806084140c26202c0003075568071040c810301a4074030815800c440414040d10800ccd00440f0040c0c00303141903480316400c001002c0ca40d01b5001d50940700a02162000c07410724016511111010b8640c01040c1305c00d008010482046090701078000d0581085560301a1304950f4204102078100c800096100b0036030100c04081e11030311112030740c0509640c00389410300000c0b40046040f00e200d0f0b002918454100481074800101c24801c0340c004da03030300c1c1000038003250061a01c00d51150552501030301d480344440000d11580c20a0769804001805622241401500500ba40601c0380758001d034203060350300d89102c42c00c1e40c0f9002c4460440800000c61325141c01d89400d00043d00c0490310909490300e80c80c5c00c103041030003800030f44500a400080c840c0818100c9101d40300316040c80347c01c10303945880c1130b0340341d00c0950280c00200748038000b41c6c0e208500b03441c9020701403081101401890b501c51246500d080c04040c00d4078000405040d4251030115120740710f0b41c03503040150072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 521601483 1250 521600233 521600243
    0x40e100f0f0c053c03011409010303050f03100308030108030306130b030a14070504050123010903120c02150d06030605160206011203050d020a0c02011706131e0e03070209011401020a 80
    0x501040040c18420042d01081340002c504400810a038060310001c00396040c0c80d0f103150200900c40388442040715a90080c480600422001c21140c40c00c1d2559200550b440303070040c0000d5449550765610903103107900c00d9000082c0c9030008414000700b8a0180f100074a20040300009106a0807080002130b214070500c003004121601e442c0c045a9200c0c0144030580042000030020880f542c1c1d5030401030f03200310292000c40d02481c0c203403c510f155980200c404a050303c1e0811110702c045000d465060381d59048144050343d201005070b00004291810400401500f03d0384c2002003010b40c41c515100007034880c0905001031202c181690480f8555000a016046072040414003441140c5814207480034490307000015225030000074458404c03600485000d800b907100782e8803042000c01542d02040118425600d4039404119031a01d031360a96407907040004501500400700c40c0320802c5450040440b0142407517140240c00c003040315400d6107000c440690060103055241e483c07000d403010000f07444441c0040000c04c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 521602733 1250 521601483 521601517
    0x11070f05061803010c0e1002060f0703020d090c08370803180706170f0f2a03010906030c050603130206070c120b0a110f0315040e100f0f0c05 62
    0x884000320440b07901c01071000d0020002c07110101c0303006003100031168805010700110250400654030000700320303201d20707000c0e8500082916001030032006580265801480242c480382c0600c00309604000710300041c00004004d064803810130003c240d880c43d21010390024140003541d8640d00780f000d14803605115a0195009660781d4070144241d00c402c4181030002d5044c402c081c0c001c0348441c0c0001032807008a03648045007950382c1c0e5034100034402c0c50007110a040d5201c9500041100c812312000311014054002050f00080524842910040c0c1c000342d00010080307480352010401c0c08105805107000d00b81c00c0e40c40074958a810310000525a85180c002400b6020000d211424480c0c0b808564002d88115010f00c035458003582840031703c4070819540110840d02e80084200a096194111403415007812a00c504561b138a14050035012000060150000e80710404400c0c007100c148175036000d00c1440d4800081080311440c100040f07820042142c80d03128904140010aa5001030507115a5528008001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 521603983 1250 521602733 521602747
    0x906140d1205070f080c0105060603091011160c0e010503030a0906050a09030606180b03030306100e06040b0a021014040b0c0304020d02120a03021b09010510021204030c0611070f0506 80
    0x2c800384900300703002d04010aa10080b404010304000200300b1a28403500902c50f60b25060304000880c07006981c42007581d0300908000d5a94840c5400040c424a20110710904000c425480d071181092030b180c00b20b0303140390861000e011281c0a803608a000d084198011824842c540e000038020740105e01078142800b10220385c41401e14410103c0d100075607401002449025503900030030380d0f0101c10b035035528096414001c181c8100d0a000090b2441140300801800d101c40340380030151207602c100d90400e508000100000310392400c1d400010248040aa4010304034402e040750648100c0d0340c0090106a040c03e58001d0002103070922014035040a400781585549446905c001804001d0481d4004c1d04a070302e031181d0912480002c1404584c141c020303000d0f2215000080b01c1e43c4140c0e4102c00440382e0200c038003030041c4090b0501c40c40b08901112280100e4018031605880c04000d9003040e48201c4880c11a49824807a25501c040c40304000c0b80800300420302c1c1070a1036001803800415018213805844007058074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 521605233 1250 521603983 521603987
    0x30a0b030d111504020a180b0402280809070e071803030f0e0f03060f0c070b010e010f080d0e010e1305101a190c21090906140d12 57
    0x91000258010308451042201e0040039105500410310500c681c0512101d20308040b00c0051960701c1030790b00408800590b030424944c101c0c2c8000c1c0044d00000c07244d4400769151603072102e100034501d901e014402c7c03010040700000c002c00d18800c0e85051108110581c024006240070000d202400d5502080c039000c00c958030b0500032921003049000e084110329981c6400420315800c103070701d002e4082050740c80b840380b4281441400204641140555019880040000e25641c201a04c2076080469018000d180c1859901e55860f4110281c0204081d04400c2c00108210891400d01000421001d005004450003000700500700c414440c0c507450502409840c580700315542c80038240f0034111806000c11407814040e480143c144554003070483d040d40444404d0300420307065010381e1080c101240200e1990f00781c100e401c80b9148a11a030494050078003451360050304051885d80c9013401c00903500c0794041403604014005075205944450603001018400d01902d4440c0c54000440b40d4005804940c018090304003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 521606483 1250 521605233 521605241
    0x8191101050d020703080910021309180b010807080d08070c14010f0e010203061c051e0111040303081603060f170c09090708060105041e180204110903010e07060203040b030a 76
    0xb28000f4800a500410544c024440740c0c00341451703008450000341c0030f0030f490080f40304a0b074480b000d4260a041c104410082900f189400005002d804002c3c545555078852041800380c0051a068210007414401c4401c100074075034001005242525003030030161005040c40022030f0340500002800c42070042c200400750009510803c48401c1004030740c44031030380e580c001e4000b603680714420300b0540e106154030601811482c1000e90401c015000c0e05940c0b518210389140466502c0d84555280d08035011082c0c100c1000c3d20045010b0381b5103009901c1c0c00c601e203c6056010008030414980342c141c061201403a410483d2064071081c010b00c3d105a41c04100c43c2d40b600c800c82040d0f640c00420380c000c01c19880404140f003412140c0701c0085481036600d0383d0800080e41d1048019004070980c440440050b44080d0b0003003001240c030002000188001c40d00410159403c0f200045105a000a1490301e2030600b441106450510740014041c4141048070094880c8540d2042c01c00d0302c0008000305d2000c90b00f540c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 521607733 1250 521606483 521606497
    0xb010824041b09140d17032802070b0901062108090d030c030f0305070203072307030308180c0609010e1503040501050a0506010c020a05060a030b15090301060819110105 74
    0xb4140d0340018030350100900180c61801244200c0483c0108101142040b5130744404841d4040128401c9403207490822280b5040188106400194144651107941c0b1440c0c4100000c0610200582c0e6103419041119483c5009003070703220542c0c9004010000c0603400851190600b005081142002c2c24904080d141405120062a0f1003505503e03400105500410100825403003505d4101d8141c1403240c082d8100c51003142c800c800742e001040618005045140244842030549038422a8041d4402002c0d10b00700e00c0b030b041180400c200e0000d0110340900c0b01443c0c0e96440c4100f0007000d80804210204115005500b140c605000c013100025007181d403001c07450402c410b0503001564913894281450b034060182030700c0c2a001c01d4500000300c1c0c0341d5480352800a500540180410302403d180905110a0307a01c050345450400d0780e107001c01c3c1059030314540c0740346000791034013040c90b101e070195010103085581750f0388034101a81c03080c45c2c0d01401d07003c10703030031404403a4101401030388101c1c2500060b555481303080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 521608983 1250 521607733 521607761
    0x20907090f0f091103100308030a0608010509010504050f0f070b09060f0c1b0a080d0c0c0816050a05090105090a0c12110a08010b0901090b130915090b01082404 70
    0x1c0c4041a030011001c03401c070840c0c00820050044d8040b1001e004030034401a95440351b4016481000d00110f41d0081c02940c2103402c8010004070395544142642c21100c00340c44000c5c00765120340c24841070000400c4118020982d00f000b44c07400300303076241030b185c0d49121910511203100008120a40039a8541c0f060700c00c80440c40a44030743d2030920b01106a142c046040d00c84040b9004c0140c2480b080c24140f84680541700d505006081c080d9008405407290b11072840120780c0c41701c43d59400f05000000b4008920f020802c1444480c0e49810103082040c0d18500c0d4116500440346040100000d0b41c403a200c01d900000143c00010300c880344001d0454241a480b1144540340d82404120b1514540c008010715811186503100d108503606c4084a502a2050b04109400121980e50078065044090000c019490700d079080c58581c1a520340301e500503100103e0803200d4070316100340c0401040015004260000f4000d1a01c1304640c40c0020842c112100568081c0000310942560400103445aa1004480d68500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 521610233 1250 521608983 521609009
    0x31a3321040221030a090801050402010801050d051006080309010915020606060703050702150403020301051308180a03230715050a03111e03012c04021005070f030801090c0f020a02090709 82
    0xf10b0b5645a5030350054400f84000342c0001400100d8020611605024940c1603446500ca6445c20040141482800070300b1703038680c05842d1080a840c05148288002045a8030245454603444c500140c0a02000da10800400380600707400359603180e000c40c000d030f4042c10854010352180b0850508031450f00504d06e00035005401c090060040d03906640c00f500481e8401c400038415551415004500070121150040095406100381e40807103407415480c00300c80b80c2c050002c1c1030046c1c0e680c440f03803100208052a400412070034000b042c542c440070301040026101030361600e10040f5400500801c1e61040c10ac04408161365801100481403051049070101814040010205060001450041d6000784106152a100c0000c00c0c8a28070b05e001d078000c0c03044000e201c07583c0700d50f8940d0284810310b003040e07040350b041103410081000081d00c284000411140030b0740d290089581040f1001045a02c111115000d0203891600d039440c15078002082d4804035811707218281d61343c48800d03040d91055115005040c80c0080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 521611483 1250 521610233 521610289
    0x30506131509030903030e03151503010b0d111905040207050d0306060f1416140f010c051215030c030d081515040303031a33210402 58
    0x842500c012040d0050704203018032031200398400308940807404018007090a000702040070078020340c4c0c1c0418021004d01910061881244e000c03001540c11160b007420076507400d86140050400344984002100d055a03000161201c07900c5640d03001621040399885640510007181c5a2580041014018a00900b080d906c0b200d00386041502d50000350304000029107031020001d4514480e20000078400425140e90341e94254100007901291300c00551038070050030901c2020b00098001101c100884100303c007803c1c1c0c840c4101503007030a41d01521801d01c2005000c0c4248481f04c8042c0c112581c00403501c050348a5820541c0700401c0c10202d1540e5403d605001d0490030b0f403c2260000c81d42442442c1807070030032050100e00350810080d05042d0000100f003406c24001031001034081c2c0d008903020102e0007001c03010303040c140001a01c00340c800d10b003000150113103940c010030040b004000c111081c0c10300120301e4100b0b400d8503800d82c1c1c020a81402d907000f100100000c00d0540d12580d0001c1c0100e8010078040c401511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 521612733 1250 521611483 521611501
    0x20906090405010e1e061e030a05030403150c0306050f09040c181a0402211306020301030f060c0c0b16090308040e0910020c0c0f04020d050a0c140304021513030506 72
    0x304c122048049800b541da020a9100800011725200d80e030700402c88141c2e0f41210141800308131060300c03000d400d0b2052500b46d00c00b0440400290009611805132400288a0701d04001d0590760540500c03000c0c07608198081c0110760302c450340141c85040c00d40b01112a5a00da08102c030b088521a800020324102072000b40305c0c009821780012901c80080000e1054048402d000d01c0202c0c0700e055103146030201d51268041c3d0301280070a0054100108030300104030b40340d480d2585401c1364401e030700c105e5598400300800002c11805e40185816024103080010a03011191200c401011009140c44445240c2d116030102c41070048040501a6421240c21500c0c0c41d2101d0300b04000340c005603801d0703031607100d9501485650491402140c1c844000600174250040710309040c0190000420201176215400740000089588544104da101c0c8041c5000403407281241e41c00030f807003000324240180c0c0c140010420080940c5410003a400060240d03a02c003075540b40344400304a580161504021710300c1c01030300f091002400c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 521613983 1250 521612733 521612759
    0x120203010212070f200706051b060a020d050a02070f06020a050408010f0203040318060522150c120c0c0e150d05070807060309032102130306090b150102070902090609040501 76
    0x2005900d0728421068100d0805d01c40030709000203032003164400071050004c41c0c400c40181c090b0782800340d100c5e041d80c1007402d002030a1000c100c4071642c40704e9010804800075107060241941000346050308616100440d215501070450503a40502003640004c7c00c290b040d4800c800f1076000b065500000c000c641075000900c40030b94403c1c1d030305500080c802c0040745d001c00042c004610448146440391441c1840050b040d241116080c20007600305010321400096445443c102012806590b40d1178001c5480a40740c040080f10a40c0e010300c0810840f15188000120303204140c2c015910310b40980c0440e13035521042d804c4a1184a0812504000410340c1c11040140c0020300340c0c21b4510440c281c82660340c813010200e048030144e81001d000210751a5480c1c2c030104050180c044c3c000b100072805450251984600062460381e6842100e0721ba588140440074096580c2c195500940c103040305411051143c00001d5071351900b4020080c049a00055103091507450a08403012201c000d84180490743e5250385140f410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 521615233 1250 521613983 521614007
    0x1c0219112b06090c2706240c060902121f0204080309191a03010f08161e0306050705090102070915061d0a060f0f0c170f070501020f040510030203040c12020301021207 73
    0x6040403070118180760441e59807545204811a11600e402c0085421580564500c8e0250b400c0356454940e0005601c1e02d036660302c1e800d58107000804440200c0701d4282c0510071041141d001c018418001844050ac002c02259090102180e40001840503280b00d400143e9071544905040000c600c05100c8000e01140954102c1e031507000a80040366a4011542e140d0785c2c143e020401905003d00c051000700003502051915110301d1101391303880390301c940e160403c07a82d049e02c0c3c80000ca0004a07100e50300c0d41e0304000c9030340038007001e030310a0003409001c0d9071000390400380740124805e0103080307400c0d683d2a000455002c00480e02c001c090708500d40d603440c00981291203802e0880002101002400000e500521000c0b4207030b9800038618403150119040052b26801118000c021401c0030410030000c10401d00180003002020f000041e661843e0604100c41c881c403804400c810303d8014410000402c0118500104441050b01c0819500c1d40e00e10000c0e0081c4541040102e0400ca000d0910890b10f40c040350303034112 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 521616483 1250 521615233 521615309
    0x60702010c02100c05090d03030b04050a0e010b010c02090f070203070f0803060a0905060d0809190e090c1002190807060207230309031c0219112b06090c 67
    0x5072070b04003000f00c0292903020040c1c00104808020000c00350400400d0303039448038040d160009542e841c4000190544c2d506840c114205a152107034401848420f1042c0302083c40242051400d000c0c55601040c1d078482c0081200015140240018070b9460090048075103051b8020803820000d40d2078685a803543c4c2050751540d0040e448464042000b610b903104407802450014032428507802c240e0f4940146a00c01c45c0525084519910700d440420114040000942641203081c449442d002030001d14256000d655144134840015a144020f500407c2c821000d000115031134244411a04110525204512000301160300c0040c44000b44488120401c80146a4900d50b0061400c901c42103580c070701440c5080f581c140c022111482107002c0b06e0745054000502401940c000d0703104001c001c98403511215090303d41c600d000b03400310550316021324030702c11f000c504523800200e40e8000d008211101400ca60700408481e42d54801720140324071010202e00034054046503003945034100905081401c2c00c0154000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 521617733 1250 521616483 521616493
    0xb1e0406061401031e050903042105010c0c150c02030f03040302030a030b04150522110d0c0302030115200d120b060405030a0f060902090406051518160908060702010c02 74
    0x40d0b10038000c0c5c4e8240c0207040e003103200b0313824440c07040402003070b01610140b100d20080000040b0708080c01c682c01200154020495880003482c1002825141e0448401080004000c4c2140009001001c05014800c01e2100003650b520341004c20fa00d1072181c0012155075171008002c100070950f00000410000c0302c0ba503000e000c05002c220038131040c0c0b4030a900c126001c140000c03041c0200c0c280124482c5030000d00080044d041c4c1044042078088030010300c02840103c0c0300241c203245201841c040e40c00301100501e421450b56140144411031910b461180a040000d03100101c580070400521305517801d2101c2050300c1703401c2c060a501600d070f0001010a04541c80c181000103409191510559084400140141c1170b0600ca80c0d58640781c2c4d04c80c0d042c048071440d690b41e12041c056160b041032944103d01c1080002110f003400e0030b203000d05c0e071603810059201c0cbc8400d6050011030000e40d605141c200300c4052070f82c505a42c1e400f00558245a103a0000340080c41a40100302815505400882d0307068166000d82e9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 521618983 1250 521617733 521617769
    0x30c0a111504060e0c01050f0c03070602040803040e01060905101b02121f02071a0c07050d0c0b0c090307050103050c09150406030c02060c03070c0f02032e180b1e040606 74
    0x940c843c02c90321117080c049007003400495900310211000340303981c000e22000d803450026113584030b9080741c0282c1c00c40c60a81d40003140c180a203903100480349000d84114281304400720f01e4480020104048840c0071000c000200c07441001d07607040380301c000b007810754000c1881c40c4509003444841c0d41c070100c1801d01410400c1c82e680315407201ca0207200320344102307411924040c80364810203020180f0b01800b60400c41c20000411080e400305405204202482d0451381e215015405c0c01c0c14041e1400360003500c500011601080120881e9900150841c1210000e0802240035a01d5030001e410034000c0004440d0842c100c002c10102a201180003002643c2144d03c00300122035041c60200d983c2c05044031141c40f2070004201040b4a18098240c04031341ca8450301c400420000168042810b0074000c486030842c030141c02084200d9032031440e9148200d054500030030800300d49030101500c0c4101c010840600302000e81400305c2c80020300941c1044100f100c5500710780d0ba81c2001e14002000f040c02e07120300468000b03504295 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 521620233 1250 521618983 521619011
    0x5072f01030b1801090510030b100509070e1c0303060b0403050102090405160c0b04080d020f0c0706021204030f0c030503070f06200d0f0b120a050c03010c05030c0a11150406 76
    0x3d034507407103100701090040c0e00b03103880e91000341405400484c401c010381b07000100048801901d2480740161107801c040c000d103001c040c0301c0303052001303090001031143c036a003d0025078841039440100601ca441c0c600c00c8090311818240e001b4080c9800a540101c000038000c001d2100c150003c2c0286101070303608008030340e1017070b0560003004200c07603090002645030b4501e14041004100800d40050043c44420716240c1c101c0c00036002c030f03400305d0b440701c840c110b02049103d580b440c00d00c07941000304518005415484602841c1091034841e81c0802411f40c0d0520910406201c01407272410082e640c0801141d91f140300508001c041c1c009085011984a4100300d10580000e20703010b200a07907411210b9500d4140019052410060010b030885d4610071a5691401d100b280e842c1c910f4075030807601d80790141c40544080d0030301d0303400e00131a0300403a8003e81c1440d080d44840b5a01a0481c2d900c0105806c07169110703425480304440d00800306d4941d04403072050150400d44003190351103003805184206020410301d40000c0007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 521621483 1250 521620233 521620249
    0x903020f090402030616031103040c150c1e0302250f210204050c090a17120f31030305121602060c092b050f120a05072f01030b 56
    0x10094064010344003280303415501400c140205803803400c001c560014600022300d91608119000d454000058904000c81d00c034401d038880508200740b502da106075810f41c0316400c4901c80f1004040e01489031200c440141407081c8100100c030210120301ea44413429107a00451149800d015074001140d00b280001984004800d1031410503154603802d14030380030f0507002c0200900009211032000f0408103c01e001a584d0420b100024105c51180d10f002400c224000600c0e207000d0031645400c1c00802c12030009082c00e001d055464610b00580d102003990b640080d1485a80740d882991000d400c00050040304040e00035004d8186810328071142c02c2c1690369a80c440824180103c110301c0075070840b40101d03000848a400038094500e015107054643c0900b640d0b54030291883d80b1102d440811040f81040c1000024800130041211020007001d0007c841c07610006075100d1511100300740080020001c0c01c0007111040400107904030400d0384207400c0c004440325101201d5028a900103450200101403524254207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 521622733 1250 521621483 521621491
    0x6060f03030c061338070c030806150c070b04140d03050d0b0604050a09021306020c06030a05071e05070209010b0f0409020c0c190e090c10050313080a0903020f09 71
    0x3d150079280c4410fa54002c1e0082d400035684107141140c02801d20400008070041e0341c2d0005d03c15040c0200c1041d040808000c0070308000c2c1002683c2402002099200b40e6181d00148101c03015828843c41108451b910300c00c104403e405030041d07440001c1c03000c5803800500304984006075110802444131041040d4823080300002004100e044c8409040320200f07500c266020040980101c0c601a100c80000b00405110752000c00d1164000515003141a4107170a4580104840d0006000c41075031440015210301001340f00da441c10f6130380c00000341458454080b07560040e154400404050407160b03001002d0b03521809003a0300400101d00000b591042000480e0f115161650300d413401c260405580d0b001035840a0302001c0c0714072449203441c401c0e689001080300f445410340d8992200d00d141c5000600c00e040c0082c030070207040c1c00100c4030200c030b600c0b800c1c101c0d0f80d50200b51500380e5880d581c5050940d9034100d030000113400b0306404039013030fa100c641040d800c00c152802125205040e2440104004080340122 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 521623983 1250 521622733 521622757
    0x211003110102070f27150609090603030e1005120c070515090304090c090b0406030b150a080711012a2a02010804260306040501140117130c0806060f0303 67
    0x2410405c284080180c524880380458991a1100402840702d0340035175096096041030324000680030001513400594190081030b11010501141d4030b1520050300f44141107804501428602d0344090a007071107041100c110070903020340155241848524178401d6003008004448a1042e5500980702501070f500c943d12600c001d078000c41c501070a014044028040e41c50005040c02121000441d92551a0000d000980420b40d00001c03100070303020410994a0b41c0c8103590320820300411181c0e0038142d0209102d0361140b680e040c002f6031910212081c3d80103100d00306000d00e489000c0006201c101444081d034100702d034200d1342c0c0c041000d81c0700070341d03240d10320202c9500845908089030480c005500466034030b6031203405005000d440031b103040410300341d4044901400010213070000c100b0041c0e1a2512030103006d0400c03001d441c0e01c0c031880400003030074410105021541100c082000070345c01580b4808041034640d8810405c400036a500d8101e241d0b60b55050303550610035407203040c9100d014200041510000c05900c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 521625233 1250 521623983 521624009
    0x8130603091217071202040b0c1b0d050a030e220b040b01020106081005040309050603101d04110d05010e01150f05150301030b0a0b060c0c010909020412060221100311010207 76
    0x284c070140e031154a9110001002902800001203031401d40c00905419035114001d1b200081d81144284040700d402d800c914451040f00043c039001c618005003400072242d0508044004d084500005070300c0d80a0040f441081480d94850081250325580020701c00c810251814055445080010b82c05da8800703002d140e041d580301802c1c07080356150a8200e507410600a04148a1641d12480850801d41c8100e03845501d118207004100300900c061020b5501071050521100c10508003a43c1d00b044000750700343c040e48a00000b0b4510380c1840700030b5000c00801d1201304020403400712900f001b040d0422841c4140500d51711040310000390742c14800da00154103090040d20528503030a690700c1e50075000d170103808402117a5a9072050410754403401c00900c480034206000b055981140800100364420a0b00500f1140c0e0040c4030402a00d2810380001c244c187d84900b0141e19040d084120385a840ca400e0340400c0e0042c1c0340001d0020164421890000340d134090807202d80c401c1c0b01c04005a9451100e44500c224003240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 521626483 1250 521625233 521625241
    0x1060f0e0a1d0606040f030b10090501050105031f0b1c0b0301020a05121b07200a0326070209010e040317090a12020f06160f030902090f0408130603091217 68
    0x7850300b542c1c4110000c001608040c1c07294000c824070304482e0011074a1400003030070b00051030a42e109610041038a850144980d43c1000c0c00281729020280c6590070049444002100322440460032032b0140603590150390701c4541c0d010500c030502d010b81860500da540f40428800704c60a041c001c4a80390310b1540c413101d10700350503044a20300300c1900918105042c0c40c001d8a0421020410004024190169501c6103100d000d010194903140001100c040c40707910207050800000300c040b002c00c4a41280d156041030100c22907004075141e881607e600a50085200c00045264011005018082c50195a41c1d000c000101c6220600e4ac44091340c6c0c0800c503900841d121400109e025003c0c8146071450710540d594504030030140c51800304103807410400c8050054030051640e5201c03611070f02051551505000a170a5038001c165030a0000c1c0a024146071709030001414000c000040318180d04000598220213681c0750300c010020a8400f0003201c520b01460b480c9003030248101400041c01004e140c04800c6511 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 521627733 1250 521626483 521626529
    0x50a08070515070305180d02210d021606050c0f030c130e04060b011b081213020303040b0304060501090203061c02130e010e0601080111120703060e01060f0e0a 70
    0x41281140c01c1d1007000030741261081148510b500810b020b85001c50349062428924680004824140f01503600045514444030341c0007070306000c0f140c05e001c550744405d4040e40703a2200318400c13015444059400000c840d0205407070550040c034014007902d010849a0ac1c0e540c5801c01e41c0c40740001625210303e0a1000c80c0c078444440f0f0080501024451502410a03581c8200701005801141c040e1380e4580c2d101041d811550700801590555003807a1508103440321103549040c55401040440138150325250001411010304c901400359450b001001ca948445e902d403803442040d03100301c9007103a0450405000142c0300440f402500c0c01280005c1144c0740c68189201507501008201c40183d078010a01c15100f02c14003001d218000c051050080045400c00209000d14685003043c0d0103854580e140610410030031000c441034808501040c040326016071580345044000d843c5581005e640c00e5091400020700319007011240c035003a40603440d202c045c02d07600e1040140343c15462041e07182100c000d10302c070354030a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 521628983 1250 521627733 521627737
    0x3030c1b100c12050601090602030a080901060e01230616020d02010e09010b0a020c060307050909070e1504080c0a06080622050f0402013b010201091203020406030606020a050a08 78
    0x202500c0200c480c125001d812140a45842080c1c480c0402d40c5403035250846401401000da1049081c00d01181039490000025580e07c642d207120790030060340394082116078000707400c000000e1450000103909940c50301704c070034001076040803c0d842d20781101e0b056030214242030040c2d4407603a102e030305040150300e115000c0c4450302840000c02c9042060014001249070340c1d201c2c00901900340740c1c4100c0c0c1c490503003074006454040c030502d1140c4a840c0c24010400302992110443c1c0c039401003918150301540740c04809403541000340e00010390010402040c0c040c0b054158014008580000d01100c0c66408000c06119080d82c10b805048001020b070400110700f418410440000043c002e00403001d0740038282c1ca80030495030180c46516100d03550301e0a1005543c1e20040f02040c040300101d00350400b02000711142d45a011108240e00d480e8880c0398002003da00039808190f400780c026190800c002080c06008000b58000d000320004a480c01070041f85940c40004c0c10030301d1680c458010314510659031100c0c0015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 521630233 1250 521628983 521629027
    0xa1107140f07080109080a050c0f01060810140f01052103070656030f3d090305300106091802131d010303120e0a1506080a210203030c 59
    0x42c0c071905201800072b070024499000140704501c00b5092030740b0417000f66001d03203290044881240844405200c07145244442c1c082c11101c0888010300c0c0c030a4003c4210340346410102c4c03248584c0c0000301c0c601c4c05005145d0041c0710752017010710000c4a40c035800d08a01d9020b940c80301000700e62542e43d06135200700801100d800040da076801d00d032203000c80815500081c41c00d0a08000e615035604a4400902c420603000080e4182003240c0f10903c0203200b104501c01400c00030105a200d505454103a11800d150155088600c50b0030041e54450b01b84540000141d01181c641221007070b031900850000400034491003015090f5440300c0710140c0c211881c404550061b401c07000703016400c8812190001803c43d80c00c0c0c041c5000072a191003d030801c0d0f00d941000380a501401000005040c20b003040700c2c661140105242c40c0c0181d001a00a5402c6084442d0720024070154020852a10079058001c051110220b00c4031111524000d60b0600f0740358580c030498a90006a55100d003022061201c0401d042c0306500344e0210b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 521631483 1250 521630233 521630257
    0xe1005150603040b180c0d03031a030f2e050f090c012a0804050a0e100915030303020a03060e240a0e0c1606060909051c080a1107140f07080109080a05 66
    0x4031000c92000488100341f90500700c001c80d40d101d10000a05600ca801944d08546c1180034043d4184507136074a0303407117807410281109401559036150000c8030014140040403c4441002c10840c46c1c020003401c1d03840010380d400b080031310400003040750711f610450a010b400003100c82248442810000b034640c02441940b0121a044010710001c5400d8540542400051040003209480e030b060064140001c0f160070303048000e100381410108010340e0700707140800c03080f41d40c18680182d49051103c0124018203c0f5002500141082c0d802e0168404444a8070701d044020031100e4034603100020100487e003040d5100d005400b40c03074000068040c403042005002807a5914410121184681e502d07441155050b40080212503138400b00c010a04c9001c2010140c0e1202d211000c2040055040019028083c010048420076468001c081c1440071080d09035007400b80e0110040d581c40143e000b0b920f0b221500072405180f10300c1490750024030380c00c05000d1010a42d402c1001240303040c030030000c110390b15841070b520000303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 521632733 1250 521631483 521631493
    0x603030e191e1502070e0117032b0609150b0307020f0303040c1404020a0e040509030c010203130311030a050904321611060105040905010e1005150603040b18 69
    0xa00b0300c1d0b8000c1c0305070351840c884000030301c442e0410300920003000c19801030340d045500284080c400c800c00c1c0d04849054980100f03000482c0300a61640c80d2540c0329000480301000b08280800401310030b112013041440355a00014000c8031b480b94004000c50303440b070b9407181c9400030303c0030100603280d0301400840d00036034144159004244003225907451540150b8003216039110b070039410810784025241521988000325025490b003000722000801106407100d806106036560000326001020400c12540b50003100e600a42d120701d800b000d442c0365486800c00c2600401e10821965204010110403146501e0f4aa01e0b01c9081c0441034040c84000e240c490411802c00a0303030401a4426141c6400c001d4012140b0b080030899032a0500341b04000500700100d0301c0078444040d90442c44a00041190b9040d903c0603500020703089003d00f4442d01416400480c5641401048204a1800b2031500141c2c414404403414411345140074041c01680c0c8012100904642c04807408107a80c44148400001240c0408044070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 521633983 1250 521632733 521632739
    0x1e030212070b0f0a02071119081b03010c03020f030412030209060408011a0109050312071b0b0408010c020a08030f15120a11090112030521130b0a0603030e19 69
    0x4225402400160b402c00056820400d1000ea00d2212035804112102c0640c2056400c2d65101306c0c10450484030382c070176201c6040c001c03000c0030034400032801881020110b555911009504001d60510301022174003075400c0c50380c0c03540d01038041e0085611007140500307194030755500d0740c80c3c8800c20b40d0400c21036400c0640030131845c01140da8410250000e00a40d6000169500b140100110b10f80b012400f114180003100d48c0c100690384d0081426140d03160111f4056548420300c0c44c00c1c3d0074000445120b62000c560031a008240120720002501c1030f2805c96001300701200702c4500a076501c2028010090180c0c80400000f4008482080026007240b0983e400c9000c1610040006d00b809400c410003952903484580d00009018881c004d00304075400c103a036219010350400d102d41c003020030881f23000b405105000520042c0340d0b03200d02c4800c00f0740c1c448d030f9491880d80c00e140d50720303541c00034401c0c0c82540c0c004d59440c08612520303030030b1243c034040b69850b494072130003881c008040c0400710000042401006240744800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 521635233 1250 521633983 521634013
    0x201150e041212020d052d0a0b040b330301080d0f020c03010608030a0e061c0504080d18031e09060e010c050a06020301170f03090d06060b1606181e0302 67
    0x10304480c174a902d4012501c1c1c600f110107543e1020210303074143d99000780c951103001c00403c2c1c044150742120728003901180c1642c0400208010f07050b03102c100394200401c45410031410f0301841003412303010b4814141c4009a0312034400301006000038024410b9540103607600000c0c25000300b208102c2654107005655013861010002407c55000350b21600700c0e5000028080d001544c0418002c0216030b00f10381d01380c1852074400d00c82e0001035104944181c0c84d0783d0380c0042002c1c0711408080d20128038016005010003007802040300c3e8807030440711045000c50342c402421414266034143c41072040e030301981d0f807699007071500c0d8085031944810140d02c0d061104a01401021910911003072283d50700401d0701590365403402c2010341c1d207143c4460440880341c1220544030400000802100e505010482c3e4481e1114403d003000c000810181e071000c0ca0140c0c001a501400d03c0107107424039240c5018400400225000c0d80e486544804d054034000e00d000d50001c42050784c0c0400d03408070b0f405180a40704484082c4180164 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 521636483 1250 521635233 521635237
    0x8190c0219080c030f030d0c03060312210218210106060e0a05010905060d0504020a0f14090906070c06021b1207050607020106031a061f05040302010201150e04121202 73
    0x5880040c0c84250a0120b0542000403400040064000741040d001e2900550784078050400400b14554807490544805071190b00414003441c0c003c9164100c00642d0341003d08545910aa50400480c1c0c81c103c0c04818102442500d4441e846184001c661550490401c804e00f8008044100c507548034504522050b4001d00c01c00380600b10503195910303010780344020464291195400300f41000301d0140144065254002070b940c8161b04070340d0200d1151a2440010f07407030220340e000080d001450039000241c40d4825030794154400820340b22880507484040c0e010340c445600725003890214214402c031a000490302d5004000d110003510780550407841c003800d414144000c94409850103400401c80401388201032040c980c010700f80c3e0008111803031955032068814040d6140240e019441c882c0020115140d000700b0b0008600d802c00740704000400310b803000c0e1943c1c20500059006610344100c1212045804a03021700307944400381f6030b4819607281d95a00149a41e07c2c61030204000d0380c0501c600d032a000f1400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 521637733 1250 521636483 521636509
    0xb2101060e15030919080702040f0209041406010806012703030c031103130b0f0919080f030c100216050607020a110d11010806012003040f0b0708190c02 67
    0x18552040400380810480003850041961508003010004d0000110380000c1134108030303050345028108229941014040c501500c90040c0d0013504007190741c4060301c2c0d143d006020581040360100f00c043e2002c11800b0035140c1c00c0314141e01040c400e0022507202d6002e80d2008040d99801000e18072222a40d442299258060b40c0c4103c0c0442c2c9000d171484209a0860112010751180310000c42c148003594911212902c400d1040c0280d604000650000f0000c0000845071f1014000d01031a42041e070320200c80101005901c41c41186004500d000001c803400401140d1000310840f009182c039141480823040294001010b114912040c0483c0100185050107031602c6916150090507074440c0300d040014036050214070880c8158051160000002d85900e00c4c00950003003071800e04500c0d9507200059844041c44078511040d4416090044001c050020041090303441406500591990364201008240a103e10042825600780042003c0554480c00080c02003040c2c50300001c4400d10b40c0200b032101c40c4c511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 521638983 1250 521637733 521637737
    0x40f020412060b040e030a02071a0705032b060303051210080a081909030b0a0914012a17040803040f02040207051e0c100806040f0608070612050c040b210106 69
    0x180311100c0b44e180c00e101e944003411090000e5883c1c006042002034480845010741503400c220b01203200040c1011900303035010103920034100c0ea034a015180030303000301e803008012401ba80f00d007081c42c4013412820340c018030040725815251181808886040c04e01d101d80000d00c0e00b0f240c0220a080080c61510400410800a02500141e43d80c0c1e2012455807032101040f16911050080401c010800580c00b90785031035100f20300001c0041c10401c3c0d440c281c0c4000c40400300304103041d801c200a2041c8488180000000c01a014000f140001441e0380300389c940a01950f00f5501d00f0005a0001c0c011404a1005551041c8a18580c01d2100b0b4a940020f089070031200c0c0c03d450070703400403004416003503055400c1828600002c0c000d2484d01c104000003450024092200c3c8208000d00380825119240da810408501304202c40500c0901d444464450f0341d00030a208103070001b092411407000507451071003041d01405d41e05400c1d41ca0182442000d110590144094819080345000c02a000103842c960140c0640229 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 521640233 1250 521638983 521638991
    0xe010c0609080f07111504060c030c050106061107080c030a0212010b04021305101e050a0215011d0f01050d0b07180f0821040515160308060103050a020a0e040f02041206 74
    0x160400c2e0100c8802c60480034028100b01c550340306e10011200649003104d40914101012005a03d01201c04a1403042e0007001c0e90700781580410965082000c1e408088242000c843c41a0340d07654565a640c030000550582603009401c6030009405c0100006107081d6185d000464884105000321b02241d000c0b10200001240d2050144030520301440c4a1044001c10701d00010000403500340c11884201c500d60b85428880e0025001d00454022310800c0e400c08076050710b180ca5980c0da040c0d6142355146036031a006c4040d80e0710f40094495100d40d03139100e05940010b0501f0040d640e069a801c04038200151101c410301c0000d028502444030409a690041c21403180c1e001c0d0081c0c41c18032410301c2c00c072040c526036039040d0942c41c1c51500c0c000b0000c00e59044640c116222074100305050254090361007484099001306001c070018030145500208080e004504c280c0c0c04102a540340144070080340143c504000c0042c00d1108101030614141c0c002e00503100c2c02c50030040c41c20340c0e21141c1203592166a0001c503091071721 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 521641483 1250 521640233 521640247
    0x17010501050a080d0e06090d1a0906010f031a0a0b04020310051003020708071104090213090203060f04050615060d0f1a01050310061218200a060e010c0609080f 70
    0x4100101001450004002c002c1400c107000c01415100d0040b05e614002d020102e1012055a2a031300301e00d960b540c21160500d0400601202c00c003007940203c48143c1540b0502d00002003034054518100222500314050712510207510807007184100c4043c14405230312761180c2d04803100780d480344000d6005110440017500d010740341070140301aaa820121a109161041c4161000b04840c01e040b02c03201544a5201d03448104110005001003506440c041d420801502c10101041c02560111242a0085003190604d6460a00d4031f0200041160700400a0b0081c00100d2000d081c0180300026440001380a24200007a051001e403c45850510011085403510034482d4030789809104a6028107082c41c3c164a145003501e0382c0341140000d03110300010040c0700c01c0c0103007822601e03600503401c2d403003003504100700444a070501c500d040e02c01740c50f5659000c1075080d107128240340180025080703030718032303110418200081c1c401519515141c0b0b5098401c25104c80c1100009402c0c40002c0089210124181da02c07016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 521642733 1250 521641483 521641489
    0x909130303050a1118041b05030915130209060f0319030e04060f29450f0d060609060620060c030c1614122a03041701050105 55
    0x1101901d9409000d1406204c160302495100450f6400c00c440b00001d88240740403c0804c00400d1803000b0405165128030103090400d40c007800843c040e40c0410204c5040000c003c4040070041300960704190494010b0036244010306201c1601c580c8000001c0140c25810154008207040241280741d01221034549101c0008050304400007003414101614200310f100d007402c02c010300c0034504e80110710210785d1404082001188811a000004c040d42c00700944030300d40071030440c241d0141004400050340380340e285c601003410401f0426a60301c00b071130b5184036104901011310602c060040003143d001400801003001041c41d07801400b005254005000860915000c0000d09440200b60744811038260b010103005841e070002241c2c0d070411400e9411560380c1d29001d60900d420b01c11841e60004094402040400f4403804040c080c0203000d480c0192000b0748041c0e640840c95106403154a044560b4001d00300c0b44065108813001c101c000e1403411645403079100c51a0310650b41b105211483e00303a440390014400e0381 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 521643983 1250 521642733 521642741
    0x60e0f031308190b040c27050a09020d060b040204030602031603060b040602030a03050601110a0c030201020c040e061503030c0322050919150f18140c0f0d020909130303 74
    0x307880010f0004a00f00759550340c0c10f03018415000d05811410400b01c0c0c10700c00190040c2e00201841e2480904600c00c602030300e104181050b4040e110717075160400140141c404e40c00740003011540144900815000c564805001b807103224107a6030807507030901020000420324801540a20b2070340c019200c0007900d0351001016540385404c000d0001c00103000c100241c54000040d01c0c503080c0729060105290b80c070640101d861007200c0d800143e0b00d20490b1910070503ca200c40b0701c0420350f4001c1e82a1103444024a040c0410b490320031859030b40c00e50040c00020703a0104c6041ca00030540c030005060302e18200f10090a0342c61a04030540b64020743c40f4401c0019010b2003440079140040c035003582c8041c40303442c0440f00362000e04217500054160729211001400c0c00071510b000440541030581d40840303440e8442034840c1c0740000e44007082d010b103494a510010303440640340e0418803644a0001d49890089003c00440b815004000b07904c01c03843c4c0074456407006a03660022030340b0a05c0400312a910303242007801d0050940e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 521645233 1250 521643983 521643989
    0x9060504120c0305030f060312030a1e0b061819080709050f04080414010c12030606031802033d020304050129060a0c0b07050c0d18050d060e0f0313 65
    0xb01c458211000d0003e90028140c070f90000c920400280310740e44010110341848080e64011221030400070420030b100425030310408149031804014200c0d101c51014078000c42d1020800191b0003c405c0c004c4001100010028170b584000240801c0d00705000c2c0405000c40707a8950b01720f540142c2180005000c960014800d56621868000b040c032143c1c10140c86404052069001d0540d4500d802e150480581c1d00582880c81c9840c3d22409403049291101c43c02001001e050203260006400c08100b090b0100c0005640002c0e15001000b03040041e80080b6554407103046001300040e00510003240c0c4c5461300081505070a181c62144015035a85020700d0880c0c02c4820348040d0803000841202881c102aa25040710700f1880000e581065a83c505184151004141400010014220700302000202c5a114018201e00e10340c00040302d601145e81007058803600143d0400140011b5245001c102c41c1c0b40640d05603107003134040d074000241c21030600c07021420300c213542125010b80d50001400d07040c249100d00d0001e0007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 521646483 1250 521645233 521645237
    0x70e07031b02060c0d050c1606061d040510020319060303050901140711090c0f0c1e0a1707030c02060703020714030a050a0b0702070e0907030204140c070212100906050412 75
    0x4501c1c02d0f0010701680d0055400b25441c046d501d83c00103002880c40000c03030f0101e0000c03200328030300342d40d50786030a04c003800d1940a4210504c180c40c913001507100c90303030f1400c47c040e41e4885c1c0500101d101191a2070029040103180d60f122595007080e04109204a02c10035020b54020b5540c10b41d16801c040000d0b0501c002481b2095a802003040018041280400142d0b0800d9040320756a210f0344030b491148a00e409841612007044000182c2d05c07c6918000403c041110312600a0308840000d060f98684c03510343c40b910180c00d45030b20070185c480d18800340c0c004111052107400c1c9810098000d07001300c1e40b0740d0009541100941c0c0104800c0c4003c040b07004004545000440050603824070079600c9a864101452004001440c46800324000600901141c005014400c080319020700c0d01c4140c095031000c582c40143d01851800440c0c000751668488202d200d02d1005010f00e15004031380e802d1100320b0703d0700d003800d11060284ed1b0320540b08140314040c9090050141101040f0f600306414040050b035514080340b01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 521647733 1250 521646483 521646493
    0x6030204061701140103151d041e1203051f080c09090c0303070305131508011409101509080313030302010f090b070c2409030f03060803030c0705070e07031b02 70
    0x3100c200d44501c000e030744c1002031034041568000750009903851089a006004400701c0307480748e03207480e40001401d40d10840c000c10150001c0341c00c003c125400c401c0c842c20064222184403d05410282c041e410940e00005480c85c407025208680390030381450184c982084965402c503000c021602c0c9420380d551074214407a0409050b0000c69000040d035644036200b4024240000403d6a4803111014000300c0014480d5031010510703042940310080c03803a182402407413400518000c60014505044a003d4460358091755220b000750300b4000c20400d0045401e10040c104107d04d003010405200038405000082c041e08012038a650451502038251030b00e00a280355594070340b44004002c40c2c100c0b0305017500132045040c50044400c5505260310302581090b682030500d0091203013000d5200d6154007041c0b0f81c0e80680d4800181e0240d2450803002d591080c8a415866481400405c2c00344194000410080d4070036021190000c0d641c1e0062002036204490400c00710b69243c507103004959036480110300108080c80902 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 521648983 1250 521647733 521647739
    0xb090d0e03070612110417190503031b07050a030201060602151e06030a0501020a2c031e0c03010905161a07080d0609090b04050d020c011b060b060406030204061701 72
    0xd40d5203002e84200e40803c048141d203104104c00c0e03540980f00c100b603110f03840d6558039240c440b044060300700c04040c101c5074814210180074107081c030907052254507480800b6528545401400c4030000300b240ea4040d180440070071220700054400c04c0080d41040c4250000300f40d043c9445000307420200b41d205400b0140c00560100700800b01040d40d001100d510010005286072a40d0f00413918045c0400c42c0105558400100307420740c0c40d00550742d040d202e00e00d0f81c0d6a030b00080b2408400b5401c0c903100d800158245d03010207020702c0c1da100c501c5100041c180702801158401c02107100003a09581d02200c098030b0b01c0d00122000440400703100030210150a010305a80410b01415680c14800d00c07418802074164503000c200400c42d0503490300141c0c01444040300501000300b96007031007024002d041d030742241c0754441e28400142080c008a64a84040e50585621041d0200c0cbd82c030a004d030b00e02140040740c200c0d0f80d488200c0d00c5541c548000d403018140580d00103072160700b849000740202c0150700203000380c100554010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 521650233 1250 521648983 521648989
    0x708061501090e1003080c160603141605191205090d02070b030a1b030c0315140103180203011805071409060613211106160b07090306090b090d0e 64
    0xc004a03502042c0f402c219940728500e032045901d040c1c00003082800000313200440000d00041102c2da084408909803000340e9100000e90403100d0807c000440c80f00140000b6211410304420304070406510700f040703450100f10a0189a070385081d6400040854103c0d1141f10003410310388252540b00f2080001440311140000c400f0355605103512a840a1300d00000000c1c1458a680d049500c600d80c400319500c0d10b0005001010b4060402c1d491032900091400175040b08503004004804115400f440d0302c180b08294050044000e080c8030482264903201c000411001600c00b4070820b400410105500f00160600b460701c1d90900301240e001100ea800c3e0310004440542da41390415806c4030080320b02c40d47d1040c1e80d80740d04440c007240764010702001000b0300100c0140405404800d44051003076003500b1103821020b04002160140351000b00c100d440d514981c6000610080106410100d18102102100e5907a0741c0d9000341c40c05076104946004a2405224000e0f01c10800d8001d030802034105200705004030004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 521651483 1250 521650233 521650247
    0x7060f020412261204110a031101050c1507020a20010206130204090501090c150504080d05090112240506120a180f0609030906090f050105090f060c0708061501 70
    0x107000c030502104488004801a014800340124030300420740c540c00d56150b0f079130f66070030304440c01e0764820045800802d192400310001d85c1502e5024003510040d003100001100c42ea088030000407218410400400b15000120f440c0d948901195070051401050f2071400c600c038000c9500b0782c0000700c1c2c904005140b40d0b03038006c01d400b9440200300b40541007144007400020050001c20f4006030181d46013150306403e1049202c2c000042d64480b240d04140070030300c80c404849912983c401c2100ca500201200d64681d80f203203005220018051405051050494030341008481c0701d4a20a03402d0601d0711303030078180b40402d440c3e030301d00a0504694090400443c2c401c8005c1d0110020880b41d0380c242d5800c82d4141d078145986500385d1054000958000c000c3e400d203030010040a4409040c1c0100d00c0302440010f00521888102c402e40e000d60810300c200a18040040d1820f4100b004510350040c0c1c2da044984c05600c0f04800f41200a0b0310b14000c01c84039107007070380050400b50050306000208030014403004241c2d8211407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 521652733 1250 521651483 521651519
    0x60b03100e070c210f0507080d3611011b0f0f0b0108060405010f020f030a1515080609060a18150b030c07020a0902130e1b1908480f07060f0204 63
    0x5404118511440401d40b00500009895030581070ac10004501e00110b15035541d07141840b81c03407054503108c036900056038103040c00303951003031203070380c00a624030004000184501c4040d2251807890303100655513a440c45010f0b070980090301c40d40d101030300300028031200340101418038604e402e0840c501b138029400d40a080c80014046620355445130b444410204101c1ca641c0004c018139a400300c030498200314010040c0c0d000b524000d1044409001040d01c600c0c0c403201c13034000c4503e1a040740d1803c06100b147c030409001102e011420b01101400005042c0e130031302c4000c5200c0c11406058a40d140d046104006c6a0040358005004061044c8115004101c5c03001c008415107142c42080101070f59500f11000c1081d5514583c110312940108044030019000040d18104840d2500c03034820541e41c040710786c0406800c040b0140c400c803407044070003206090082c45c80c50610f0903003960310512000107a8540883d034020210640d14400c00203030305c0144112441160b14050100c0e40543c40d140c42c0110480380020141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 521653983 1250 521652733 521652757
    0xa02030c030f041103100c0e040204080303130503160c0e0a1a010315051801031a1603050916030803100608040c0b09031e010b04060b03100e070c210f050708 69
    0x2004102400f02c0303d40f8800500c10020211001c900e004011b0501030200c80d1020800700c0c2d0b4600070b00d40c2d01e20301402510261902d5a0040d41981e40b0a4002c9910011703180d803e4409010400205250f84804011420420300511502c140c00d89402c2d0180310018004020609440c03030885491045240c2c3e034101c10071079100740f1f07001c00c03001c0040b05031003100d28041c0d00181e80400400d4103140b00c0c8061050840c100c034011900140790050941c00300c00304038000c8611007640e00c2c1c401701c030440140c0264401c0d6084422030041303490390908010040381501450300151901e10020040103030803050803080381e007d44034601e40200c95007419980d482c02454070380101c046030000850300012603201040124030311588181040c2c0194042c48009009140148501713014605254022444802500071203014a00e030b0040009014602180740b650b944010784000b013042105819030010454040c80c141e90903100b07040d05c1e480c5003103e000180411210548050510009112400104101c4420350b08210304107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 521655233 1250 521653983 521654011
    0x801140102160e070201271e050f100608010605061b0f16030c060f1d03031b100b1008070f05090619080a0216060b0312210a02030c03 59
    0x1040141d0070003490360300d510303540720a0240000f040c0211614040c05560316030020060030010030340f817008524020030407441810390180180000703401c0081d10b071001e402203110001600d2482e52500e051002078038040c0c0301603000800c00500b208962142c1c03070060004030000c001c07940c5820f01050090040343e8186209996040e001551890180000038441c4e042c0d1050740e03040e46400b01c58801c000703443e000035a0046803000001c0f0b4058000c0d0744258403080d89886441705501d4102d2010282d0031001c5110f13806000c280240f2070041e03050040c194060300000b000d0200c0b00c49802201c4119011026003074400d100c07040c651211190080d100c00d80200321442c2044000d0442e5009844d00c0c42000b0a40f5040307040052581702c44000d003c115a1110001d6807034401a8480000344001da0103400008400c0c3d40310600281b0000b0181e80c44555480c00190a450306081d00f03589500d619002046007182078004602501c07030a090048036a40d1006941900b10304506240d0280540d80c00010809950701c001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 521656483 1250 521655233 521655269
    0x15060e01030e0109050d09031401020f041203020705100c1a013b1014031209060c010f0f02030907090c0912110901170d14030403210515090f070801 65
    0x200390440d01c6005e400200305d50f0380c070348005001000f50405102c203981300f030314442d80c0c2c102c0143d06000319040010301105650626003090180303100e80c01e002004400358410001b000450b034031034040d03d00c20710025031185440e01d400703800c0c20710072554001d0303c010749070010000510644198001c02c49000520320300a06599400c0790031450a4000000c928101c3c0c2e08103010040f90100881ea40800c0d114fd2000301d11114207124181565100c40309050600310206000801c49410440040c25070f15501d8400030500040c41720a07107040f1403112440780502a00001006540e03482040742c2c1008104604041103001f00210000b0072541c20b40c007900728010151200c402c14010340368160741c2090f800516005055071344605107050402e801c040318600e8080c00203070b00300d268000c072100a031244819060340c1c80c580d500d0b60110b0715030404800c0085451540c16004140f85447522030f480c801c0b41040c26840c2145401020094030600050002030746a0054080040d16640640b45504541c035100312000d024207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 521657733 1250 521656483 521656511
    0x506040e040507030b0406050403030e0c03060c0309010f3207120203040206190806010201061d04080c12040f050f040e0327030d35151804030201050a15060e0103 71
    0xc0c0d0014080156200c140407d0224650005008900c643c03000c02c00782d00b041d101d1031348401c1c00c600060b0703040d08540c000801d880703141c800445d0310458440c00043c00102d800c0b00d00d01228072000000d00f119002203080c08860742c035a450481078010003d070b800c40d141382085d001004440d40311003555101e500840420210341340c50f01076569890441c1c0c0c018401501080004002c007104503003c80c01513081c00700020b0720488080311500903800245100700725903031755101d2000c50380c007104c203031a014414025902c81c200b103000082c1001c1c0c407600d10a160001d182400b0401000e0030320342260300c1a885c2c410b020301401c400100300c80115803c500c04480114000c00c0348040840d80880c20b54040c02004600c04180d58400d40450800345003107544207101c00c11130030340c20f044040383d4400400000c10b0804201d07080c240202298000d40000e1500d548441c0c00c1c20504207880c000d031011030150313448400340124103140d4040c054107144041d0101c1ea8191410100801d64880c8c500b03410706050392103461240800b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 521658983 1250 521657733 521657743
    0x516030c15050403030f0f020c0c0613030b040f0c080d120c0309021c030207090504032316080901020607110d050904020409020f0703121416030e0616030f0203010506040e0405 77
    0x5078040204010070301e45410041c1c050215080b407451a10302d80b00c004c442856541c400d441102c2c01d010010f090105500341402120ba0050140c40c0502c0e204020010008110300c0c011383c46944104181c144510721450070010080c51600500344c9904280a1402c1155202a141c0359007007080801042c0480704500a072700a05482c0390107034005808080d0814502400500c0e080040d1099003240c2d0000d40e03c1c0d015400315001614024001403041d160440b42030a04085c28140a10010020f4581310032032480003000001d89104a881e660045a45c501d9980c052080c1e40e0300c1020b900701103454445071507003962180110214a0705110020440f50055100d030781c1641c014042d201c0c0c0441d62030054a5003c03003203400c00e0f20304070000b40b040b41c0e0f01703080c00c003160042c80c440010b075605641d400d4840020b034440d0482c610210030b08255071403103016100b5400708051801030048168000f92100c4014000f010b031091060006041401000100125100d003022102180c0c20b00b04450f203107803030b07501e010740c201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 521660233 1250 521658983 521659013
    0x70f05010f0c1e06020a1205060a170f0d08010e07050703022517030903010506060408120d11030406240b03010902090a0e07021f0504081b030d0e070f060516030c 71
    0x2e404034003d0501009025801480701c4106622070f50001915050039009032001154625004815034004000c50300003008081045c404003011307a44070784562580d41d850000700c02d8904000401200c01040316506911205403c0701c0185415840c141898802039a10b50456000130140c04500c2c0b120a0290000255400500200b02c1c8083c042c45100200700d640c2e40241c030340c144c8030703520744404100f107071038a8021241114104006014850204251125503400c07070820320044030b48602064019004100045200e00d01c41c40c1c0000f030005040c048640c1030811840d90a1041c0312070390041c41448600c0007600e044a001d2080580d41d8010b0705c1c007059401c180c0d6800038034200c1c0d11701e051103078240d00404c0140c000d0101699a9a811800d0680314050b10010342c1c003e0010102003148018550070710341800050904541144d190028040e100011112612401e0740d258100640a1144540c515425001030005241050400e10588209107040c80400c0c401000d021000b2482e800300b1000c0d00c4402d4071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 521661483 1250 521660233 521660273
    0x110f010e0a12050f0a050d0305040f0803160f03050c120c0d0c1d010203040605040e060a0803030907060212030601081303020a0b010b03150a230f09090c03070f05010f0c 74
    0x1038039590056940ca040000c50211804d024512052580110014a058100d5040340040104030740801090f40106400703801074890010140c035a00214200c00e0045005070880d43e150312900000b488010303c0804081405020942801c051000658405080d12000c55120300c454800d5295001d0070800c274403580e21819400d0b410300a0003490035070047c0302003550f0106035020700da44d01c41c05401240c0b00d00c0340b40544d01c04210305010901504da48404040d900c82c0000c4c01a4900720307145d07400c0614540080347d40d4240c41e441808140403240d070502401e65492b904004050841c185400043e008a200504c10301030042150901c070305040c0708006500700325030454a20440c2d0350316003540b480b42d40d108481c3c9003e9400b410140ba01141400c074645021160181484070b01755420a00501909240050881d071100906d90748504079907510108a0140c0c0111004240603841e40b01858200011580034880c04103410604129034bd810403114091784101c3d141c18800d02c036580c0303031054100d4818910089 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 521662733 1250 521661483 521661499
    0xe0106090e0303040c0b0408060106050a020c030a151401030f0f1a0103050d171b0d090c1206060e0405060604051306140a0f060605160c0b0d09020406050d110f010e 72
    0x91441011000f0f6010b83c0c05440c014000645549000c0700c6481548a400c0c0107070b10000040010034816400f070030000c4000c0c810745102c2865880040d1500c05200010340301900441c0f200c00310500c091041824141c0a029030340240d61458a400c80e12130100e08000d07041c3ea400304203d108210300d5040040400b00e58041d4128296140e041550317a0301d070710f00d8005020845200d04502d5100407110030a02c40c0454100e1034041e0643ca000c0d1048036040b410301c01d40c01d540c0350a070400c0002c10111642e80604560b000714060003900303080c000b00340c4210b503100c3c100f011016018040411004a2040d070300641c20b90b80400e1588404c2c10301d51800001d0100508400d00d414000e10341c601014071490700078000000309011035651196201c04403012842041e0110314200100345c840c001420035030030f9403800f40c00c242200a40c1d4181c1c811040e44000300c000b091a03554640707042180350910405019000964884661100325500d42a440f803042948030711a16403140c1031100342e8403c91500c0c42e040800f82c1202e03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 521663983 1250 521662733 521662751
    0xa0807050102040b1809070c050a1202191109010906030209070c08040506040b0a020c03010c0f080402180106210209090403110106050402040603020903071e0515040f030309080d08010e0a0e010609 86
    0x1070305ea40002c41300501c5400c5040114131458402d601c055003480e08200034000101683e626000051a0b1011510950003441014480b6040300c00b0450b00581c0100544c0602403888000c100320410143c0101d580d003441c00e5014805612100c0c00164005803034200300c08006034900f00540305020b15400507a01034000240450040718100213803004584036002c450303100003050205401e0340e0055030b842c00000e2200001e042203e00c0340340344c03a0b0810300103450310341441100f07403212141000c00d800640c0842c641c5246013050869400780c01c0c0b0b0140c80c420085003400307504070020781f2000c405030001c0d00700441c6042e8440300040a42c0804024070000340300315600c0d41c0e1107002401a400092109100703014100c4001001c40f443d04240407907a4408413100c0020303040104102803100e4030405032507401c030107000c00b1468001e4244210b010718002c3d15214002480c117108c0d00c1c91f00d100c4d408000c0800090800401c45007140c0801f9980103a000d00000c1482068000000c1c018007580c1d01802819003002c940d0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 521665233 1250 521663983 521664007
    0x1f1206051e040b0d0b19020c03031305060c1801110c10080129070201030c090306060303090306110a140906091818030f090907091d010807060c050a0807050102040b 72
    0x60046684292010320445010204205288a441c040507005c1ca00000000e072000c0a180014135400a582c2801030900040c007080300c4c91504115521302600030b9082c01242408801c216082d03000c0710b1800458909050441914100355940014906100400c02c40899001c5c0030310020120100c0540b14642c103100d09000100746039400e100e1104646003841c100f580d005490400c11496288030210389103803282c9580110700502064150a0030070074804001700c0007540354081c810007940280c1d640a60300341181403c0040301d40f20003400c01c0035030702000300504d440d400c485d034210050010a0301584448810000c0f45442c403034000742551041c80f8038a40805076240c0e103c0e140c015030540740c411615608031001d6036541c1c80303000c00240002e07406001d1250140f50090740564031440516003a800c141d0f454802e203138418031040c501900e255401005001030700302004054010031052a04400d10007603601d5980e1911010702d000303071003070000080081c140042501110000d1800b0313004030f95079010072004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 521666483 1250 521665233 521665279
    0x3020105070906021204031704120b0103021c0209060108090304181e05010b1204020301090c030807030f0e060403061d0607020f0c0303070803010b0304060e0d0e0307051f120605 78
    0x4003008903031034442c0411124800200c8241e018040c20039689058210b484403036600c0c042000f104c0e1084000c120105000b01c43d0312849800c02d11a80004810394154410002d0615509004070100c462842c00d101c00342e600c450f84a90403440c2801e08400707545904410605620841e00006845240015109078906155220042c0e00f03030301405190500c10444a41070542d1400e01c0ba00031040402e001e247c0c0b1440303c01c1076181d04240b00030000203000b9150341c0c500108050562007520190302c045040028540c0041c101040442d43d0b00d01902c800209034006242c0c1e0040b13000182136503640700086140641c285100f40c414200b25030850750140f4002034029524207400d00d405210f4000c01121010703601703001050f00c500f0395200700030034256030074000c11003041d4000500549800d61950b90b9151550014020a02c10008598a0000700c113882014507161100550210340680300c0070341c21180f20583c9143c1c4074052492807620440d0325080c0403140001c0c1a41e42c00960b40000040d83c035000e40f0303c8d1400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 521667733 1250 521666483 521666491
    0x90a0c1502120a021f060915170c0328050604080319020405060403060b0636010206090307030302030619090203071407020d031b1502030114030a0305120c0c010903020105 75
    0x30031642044011070b203a40c114007400414602580c812100108038220501c0c2c400d88103002403000040079076888003035000380c0e81d40d0042141c00c200c025000740300321410f0361525203140101c240280261103058020075500c0d07d440c0c0039a10b00e0303200500c8038000710865480b0403074a40d4000c1d00312000c40c00e142c100a11f00e40d006070b131144000c01049070744030006400d0b402620308440d8000c1c48181803518680315039000e40300320307000b00d50b205004115080106c0030080300c0161724000050380c0f03041d0107c4000208034006030398a84605551081e400c106044200008840d0011b600d45000758898072940d02091132003800e11652a00c003c3c2e8100041980c4402e0380c051441500543d440015400000c150080180709400340a508840f003203088001103030007800344c20700b4910b40d852080b4000d403050300c44180503259402240c40d01500000104200f102c400f60101103106c00300c0c09040c048080c0e60b07000d0705078800c03042e040c00f407500001d000441c92070b0644103540944181c54001d102c00e60941c03400034000c003400c035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 521668983 1250 521667733 521667737
    0x2030c0903151b030c0408100c030e070b0301030f0206091809150c0720030328210504050c060a0e04050f1006050903190b0a0c180509090a0c15 63
    0x402a5490b1158001d409024259400114060f9559501d412009900003130240c0421407003000f00041002d000c0041694103c2e0080e000204408064002000d607508000b00c00c005622280e01803044610860490b41188c1c0d000310014507210142c8042451030064000302d80e4401c9804003400c01080201681034400d07440c0005803803c400c4038505801c036550095801d868540d209111a00c002000301d140c44620030344541e1540c40e00da441c2c4000034a5580200f02040740c0d80e031040e81d41c441c00d138a10710002c5000600360030b12180740004041c04282c240c0e11018000781c0181c403800828240305080c000007030301c00c0c00a41055a034081c2410041d0450408004880c0250314090010f9007600d8508582030192401302c94441c030181c40e041c8211003a810200c2c0c076580c18061822030880340100800c0407072010703100381040b8040d440c00b420501d04075070342c010344c14040c01400c1d80b10b0812401c96002007410741d801160501d01c1d50322400078140c1781c00c54408008001c80c94081c4049102800458503810100281d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 521670233 1250 521668983 521668993
    0x30605042003010204030803010501030f1512021207050319170a0903120306180c020c06030108070e0c0711090a0f06090b0f0114180d060207030302040f0b0c06010b0307110102030c0903 81
    0x1030280b5080b80300368030002c5d018600c2800103021540c4240c000b035240781a854030104603205000350403000d000071603005580b1545441d00300c030110304242c05800b12410111002c0d0007902d140c040820340750a8907007500002d500c1d0003100d60003044200204113040c2203d820f645901c1e00342e180130140141c1c030f0a010940d20b030100021a00311b09413007030103480113544c4980d0510042e035028108800183c20800101010b60140141480c2540c840340302540c001c007254001482481c1c6040700d100c09000e40540b0b035110041040041c1004224000e038444d07040c15055501c03807140d980b0031051000520038901d1603d100c90500100090241107600400b000c402c040b51040b903a414400c00654802c5900e800204da510014044154a1044980d03076020704080070340440081280d5513118412a40038500c110082903002c101840001e501c0803481001d444803890305440c0c80202d203160369071100c0500c90a02e444c1d000000090fa6240318003028560044130300c000f0754030390601d10180006078002001040c064411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 521671483 1250 521670233 521670293
    0x150f0b030a03090308030c0706021207081b19030b0d03021005090d0c1e02030d090608130f061e02120405210a03020f091002011424041503060504 64
    0x1000c140348030840d40c540c48801542c4d2465a82d5455070300010031480904406004403004607005000902242285c04a0901c1038034000a0140454402801162154414409680049400e001196040b00c0080e01500b2078000800c0d0840c003a1a1105100d508800c1d59111481055000503d000e04000307400000c0c0f00c1ea540d080d1103d9940d05448082e040025101d41305000441e908083e40300c08164040191410802030b80c01280c0740102c2082c80c1000038200d000100701080e84000708135003000c4c10141d4048650340c40d4a94800098400030050181030b0b5500350405503881d41e805000e40707810b4068055456440110500d076270380700201c8064820740992103041d00040c2a180c10902e03000d8680001904012200034114000d401c0181c001900d10410050b010342540c90030002c0610a60399030021840c2c10001039505004800600400d01810046e02c156100c2200e4001c0a62810000d480c00180f04c10303800041d4540c40125400513250a01e000d00f030209020503485048040281901d05201c03140b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 521672733 1250 521671483 521671489
    0x614040213020a051c0e0304170c032a01030905070f06090e160c1518060b0904052515021e070b0708031302040c050d0c09080d0c02030a150f0b 63
    0x2060110f00740000d0b004100e03443c51340c4442e05181c164050945070002d443d03840248030501d50b41c0282c222010000803081410b00c05402003048030000035041d00036024454150034209101c1c01d9480700c682d400350303018640e4012a413096000503c101d070030404480d8295507580c1400107184490207010005210060081002850420340724060003200010f03003140e141d4450129102280d84104440c014103550300300c650b00c4058000c441c10349181071030038140072805181c000308540f5004080347c040c400d22000c0000bc64001f1410100311141d4240100d403101c80028045080b158541100a500d0500c8042241880e40003501c080380c40c2120305880602c0d540d4a90340c59a40d0818031600ca20304004001410001d02000051600840301080d1305030b07103215a50000c1c0a80304040104000104045000e5095040a00440c0107030801414414a41400e01000c0c0d5101d9623031440032410300541d05007200454404108080a07250000c0b00c0500b079202800c80c80c0c0240c02c15403a100060340c00e00600c04040c0c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 521673983 1250 521672733 521672737
    0x231e010e010e0607031e020403120e0d0c0513111605070609080d032a120b04060b0f090d0206030709061202032401030f060b03040c1203020307061107061404021302 72
    0x2d106009114036500c81204401811071a0341ba1b80706044040072108000c55240094400b075071080d88440313403404a00d41d00615030385004030744e00c0c4120380c9400e010f4081151071484c403080c0c40050300d5115250548150320400b500640c005100c118800090042960b10403801120306c5070301c04c0c425a40e80c1070f91840304946001d200d000e052102c0c0c010250708a6070030700a03403207401040c403110282450f41c1204c080070f901100540000070701003070b014184195640900d00c07801080200403601000707130a040c01d140d00c185000e80c1442c10b0a03850000307405031707041d6190402c80711000e900414a40e40d038a03240f00000e05a021910036a40070600c0303105180d08030700841c000d40e40b24485150054921205040d0b405594400e105185414546e44460140d08413200303000d0200a4074002282a9980c1000d207416070380480305521030320001842000741e000080c1c0c04000c441016404c01400b20b184041d0544201c081c0c030030040000d0840b480c2008500c80701c01c04107505480345000b00c0d4100314811264a45030264 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 521675233 1250 521673983 521674001
    0x608010525090f120c0e090316081e04030605150d061d0105240d1101050a110106090905010b042a020f121b0a0f231e010e01 55
    0x160140158482060801d9030003101491454a00121103a99448251026204a40001c18114003840882003031020909521000340303131392844501039191a051907602e074015212110b040e04245100710041c0238a071003d40d000762541e005400301c9000c09020145542d0300c180301c1210b4240c20000010b40b0050181044211214098400c00840e08690384540042034541c401981c58440759103230403040c001c240724542c800c0a42c9084100e0884a004201003002d07040c400d964441c1500718440800a40d4071404000215420300784161a0076001005484940b114106542c0a41c60318100040551203500480040f038040d40003000711842d140b00344000c0d2502041043c0e00c0c2c5500310380b0703142d422588514503407c003c142d00c16245101d4202c0c1d101c42c1040c401c815075185482c004a07100805808009110343c03400c1400000308422150b40d901c00c40300d440c10200242c0131141140102c4003a00c2c106c110b13080858000c00c16103261100c2600c210317007016200c4d40141c0f0550301c0d011640660310390512442d414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 521676483 1250 521675233 521675251
    0x32703030f010e1e040302030306040b06130e07020a0f05070306060b09100509030312040f0b01051206010b0d0b040e06070315080604020415031227230111070b0405030106080105 78
    0x29030308100f03000c1e10f0200050140510103400713011000214080740e5200e401107119078044c6d99241000c00410040e1664455014412501041000401e03001240c4010848481f0402546550341c0c10600b40c0c207020006001522205038020343c9810800c0200325407050340c2c820902001850b07280d10500d00d06020300c81c1c02c0c0d9008468205000e18150007000a02004d2400504581c42c08004417038210b045031003a10304950010008007190308010070016000e0141405071075022408080e440038960b01c0d501885107514070715000943c80a0b64401e50040100142c004d0005e0200d8140c1e41c403025668031044940800003071601155005103050120120105c0e02c110b0000d010a4480d070302000300400c40c00c000100c12034000311000000600041001e00360310003a80321808900084d025021182d01c00d2030380117511404d0300c0c1080c031800551150146903404405004607080c400c000040c1c480c8111011a0100d82c40f5200c80082d042004d032005105494050300244075184c0d0300c3c0d017a1400c1c1c810030707500340305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 521677733 1250 521676483 521676511
    0x30b1e09030714031605010203040210030213091e050f0a0e0d0c06051f0303020a050c01030606140a03061701090219080705091f09240602060c0a110303270303 70
    0x300b5060900c4000e40e841240030b0361714160790351100303201494012104503100e0f50040108030640c0f820700170040c0c600c075080c2410f5182ca64164100400c042031801090b404964500740d41c1290901d0488a8005210401c4d00300f125003481600c0f4280850112054408507007030601346902540c1c0401c1d00302c40b001040c0c84034003d8010380d07602d1380c014041c02040d401000a01d210078010300f4403502e220f107008502940162003c4203403828400d007050804034003030703040c1420b21008120309903100c6100c01d003841c81210b2045d10307030340500804c401520180e8070060038500c04005941410310706521070140103108840c420800c4002c107200ca0351040d20741c81b44542d1600b0450b000c00a604020418951101170394000f031303040440c54130a0f802241003d40000300d1056961407094202450060351040480725681504031940c0780810095a03039070020008940d06001182d0740d8016801040e014801c0c400c40c4c0d040e00d4a900e000c000300300000085580c01c0c00840320b0343c2401d6102e51404400c0728002e43c0c2c0c84030004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 521678983 1250 521677733 521677747
    0xc031c05130203060c1606020409020901090b0f0a0f0507051501060912080a0503060307120f1505160509040e011d1216060b1201090318230f0d0c030b1e0903 69
    0x2809600026041b02035440b0680b14800061102e20003040900603840d40182c480103d44001054240507402c04511070004200b1407121014480540c0c80b52180ea14100c0c40c11040140c08840034024a0300040c540e104000401703051041000304141641c410b503071a001c0040d501d08200c0088a0302e0b09010b41110010082005901d12601c0159400f0401404440519a4605080300300c1c03420004240e4110404240b80e0703041007090701750354400c00e488190030f01071418215a1841c14012084048051000c00120f02c440340d122500702e00300140030540200640c0d22080540150145032603250506800f920340c011401840c0901541d4201c1508003202e01c4022a0703907134030b00060012303180f0158865004c200f6450010f500340039444e5860300c203541d102c0c1c80765032034420030903d2419500020003070400f00040803054501d02c0400f071442241107403642100590f00c1d02003402d50508078405070224001000220070300c10074020040c02401b50700b440050099403d10000300c000d000356210000703500104944 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 521680233 1250 521678983 521679001
    0x1b140d1815110f03060d0c03150e07050f0102060a090204060b070804051002161205071a090f030f0a020103050c0c06040803070905090f180c0909070905011a091003020c031c0513020306 81
    0x3034452984181c1071010b90b65141e840e1009c0700702c214100047d15544130b1480c6035000c007003413010100a0030103446101241d1400c100103912094010306401d41650b459015509558582e000080203201d80041644d492800341003c41e4140d0203401807a00801441c0381d804105880016a0040c1d01500f001d120071940c20074845061141243c14107603500c0c407802c2400710300520603040d2124000076091180d6600c440703400912041c5010b40c4031007032194112140c944504600481c01140050f42440d0018603607441c81001c051500a0504000c844e210354000c000400030032000950040b00c5c0c41d00d880302025034800801c0080c04040b1641c4580c0880c40c800315200d403840700114000a03894600381c5065007040f00c0801d0706030404032840d0089502c000d50400c140c6803544a03950241c4132005401260103558030f4002920b1142c8080306000343c2030b840d4284d21003071003641960000c41407001039942da802d00d034000507114000ca002d110711080c40d01022400520b54100c540c540141c0c00383c050720140d5942410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 521681483 1250 521680233 521680249
    0xc0a032c010b063603010f050f07021c0c0201021c05040614130b0c0a0611190306050607120504030b01090b0f0405130206090a0314060a1b140d1815110f0306 69
    0x3c80492810000ea0301c0f151782c00c7c080c0c0d0340e00d1106031400245034507020040034034040c4060702590075500901102030520746019000741001e01141008000b80c405031004030b150042c0c00902c203900607101b0842000e0a0360240040003107030101d6984082d454403651403100b5500c80e1500c40c1c50b50080d621000c000050b9905d000e005150340c0366082e0307041032010b0340b12034081d12800d400c1070400302c000003140c8601e00f401894a00e015403017841c0c2000034904203008201d19228850780540317890440c00070410341c64498404c450103190700407990200380d6500c450640c00303011821004c030f10800c0544c4810126081501c105881090501042454041c040c2c0a00031540d100070051074200d0010200400482d2a18041546112001d030051038a460b040310440111313440780140180e000106001c0c00c005c82d5002d18400074850041d842180d90305011041c550080c00110303c1048005018414a400e00906c0403400d0282c5180440a01c01c0541104410a483c82464003502485105001146060900e504 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 521682733 1250 521681483 521681557
    0x6010f210f1104150e04020405040f06150203070218040602071707020a0b030c03070c0507050d0326060d1401060e07050d1a060403060e03090301090c031403070b0c0a032c010b06 78
    0x101c01492300d520382d0045010342d5400c4464900941d21783c1007c10a401c16034604680010141c400f640c10302e00c56900045c00311301408a990b124000304000720307040c41030aa04a6240035480b4001e80642003a001045586401c01d20042e07201d420034090004a030024003003100d104002d65401c1c1480c0d591091000c4d14448840390040c0c545201d003403400b10340358440c4c3c006c0038002806510340c1c00311410740000c004c2000c0740304551201081c0020092002d180c0729600403d0085903c40c110701c9043e890318900500610702c40e449004011038460074441c140341c10030f008001410703400d0b1081c496105c009052030a1650300078890354001808000410200c4c0d515448960303440c0049045e6443c0c03005803000a42500d2904c882520701002c1c4a10801c00c0040300b00300304502c14181d1b005582040469124060802e40c003c040301c8900b5400501d09100a220b940032900400d04111314200d071900409002e04009600c46c4500015880d101200443d0300c1d002090354060703444042000c0c4403e01c42101c004040b65020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 521683983 1250 521682733 521682739
    0x612090302100e1005010f0506160f050a03200d021903090312081e04030206071b0209010609080f030705030702060a020312010312080708070806010f210f1104150e 72
    0x74024800c40969000300f411507002e4400818400541c0c1a20408031041039014200304070752800104415103508040c2d55055510f01c10100700b0ba690f6040115a810410100400c0c3d4001c03100404205074000681d200c21500391001040e1000b8030001c0c903640c03074201590403009640030407900c2c0d0131101c0719141c8000c020321034600000031664075035a40d65003851003207100010880040c00c00641a0581c1600c554550f415521846281456240691039100150204080085094405850700c8140009201c42e680c050540000c660391807600510b40342c00c500a480c00e900a249006025207000010b5130281034004024500d000d46560030041d0b1a4059081201940014020142e02e540e840c11907600850003440c0c8907103186c04e600b0300104002001000720041c0902c040500c106c040d441008254449001c3c241442c410440c010250303411180407514210740c40f03501940340d00c4c60126401c14104881c6034501484098444400912240241e000b00c1031411004007003c4001c0c2e10078054503800740400303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 521685233 1250 521683983 521683993
    0x204060e0f0d080f0d0f050403031503110d020a03051516180537080607030203071209050304090e0a0605011203021b061c05090706080c0912120a0908070f0612090302 73
    0x480340317501035075402d1000545095403030042105054050154001344641d0740f40f5515294216910880c04061064206005400303280c0030f101192110300c29103002d16000012107503041b040c664580c0c06000700702e40700c03002d811100741c1880340c46005441131280351804915001072913041400380f21442081ca0806200da000c80c0e40c104441801c01c04040103111240c1840443e102c4c100134442d0b24004000d0880c40801d80f04108102400b50300c0b60038808012000040421250390504016241d8002d80e00b00e012503a1404c140d5200407040050b015842c20b100e21824040c90780da9102030700032484045c0780a030158010881c406200b0706141d401c040d150070b0003404030341032080c40b100c00703800760f900d01443c010309680e10010b0044c103800400000000b00240c5c90001e56038a0002d01c60009400b0341080c0b0790081c00001468006c0003c14001c079100d0f90b100c10016501c1e50040c040040c240207081c40703210314600900d903001c0713544440b0304003c1d825104c2c50f03250b0401185c0eaa042c000000c00c02100150114094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 521686483 1250 521685233 521685247
    0x120d09020a050a12170306131503080d09110f10051b030d0c02060f0c040909020609190f06050c0712050a021011010b01050930010e010204060e0f0d080f 67
    0x4001540c0c000d001e1032410a0b109000e58684180303800000802045080750034004c00c10345503201c00c58194082d07238011010030420301c02e40303041c07011000a03040140241d0000c180d109403010954000d00c00c0600507518004884035810500c154450102c42241d0080702000802100c1400350005040200c40030202e15002c0d042034024a0950308101d10340c4041a84412415041550410543c0d07040b941ca01c00e03c08071401d00d80000d195501c540d2084280c095100ca100d40b00399a140c6041d0b4800c00d401814000140c600403005900d5010540610545401e0288000c03543c10301c12025200c0c1c041e80000242221403d04923100a2008549401c4426209402010005840d4000e18800c001040c0d142d0882c6c03a2807103100c06003503a00c4100c1403410040d0034000011f0640d00c0d00003c11034005a0034031991912620079141c0d22810b000000d06003158240494085010070560080044031402c0d61050060700e1104c0401620407600703006107501550b0144054045400704004001008070124076a10300b10b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 521687733 1250 521686483 521686489
    0xa090c09090b06041b0804030809030909040804050103052a0304110d06050615161209080a0503030907141807120e060103140d171e010e070e03120d09020a05 69
    0x48001d08403051580c2005010440c00d0500900c0d50303011074800c4a03040d5200c4c0034401400420010005020040d203840810280b44083c4101d80041c40d020380f04040d540b800d42050011544180b0501c1e00007032408000684850000c2c480301d01038030a5042c0e40d900c40d103034170364491255000a00107444640401d480d003021a51038000001c041031080401144903d816010060442d0319502c2c12002003004120004500ca541c81c41c903600281e204201c0080e11100bc032003150312905c00e800000403481a40d01d00d20030310600102451090f0750f480100d0b00c00c2612030001f92340e01b41141940980101641c3c1f01040c1040c44051565071201403890b000d540e5000c1e141418003541d2100090580607000080140b06008001c410300b814441d502005180300d09040703034002c0410b11100340001032001c0180129030b1403803848a02c5046100700c0740c06840656101c9420321201182940c40038040703990300c3c85254035800c010420465040d4603111040c1005221048000603011500c4100da1019440d0400314407030f6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 521688983 1250 521687733 521687741
    0x403120509060304150501142b02060403051509070b04121106300411010c050309030105040c0602101a1c0b07030e0607051315020f0714100905090a090c09 68
    0x50103428460440440c50f184d41c0201c45040e0854000240c0b034912051598541c64000c1000271405400b880d050f0021142e00c0100c0030144134020740c00280064000180000040c50a507003448102c13200d26140c68102d40c0590310300091040c0c82d43c0c02024803040240c2440203000c100c14034001c00c00c04ca004140d110000350b040d880125400b40303510842401c14145401c0c080c600b04040000740d01042d00d070034141c444124181401c0000d038100070001810740100f000c240305503504488041c0080c0b1803801c007864243e0705148a4005c0100611544003041e02c4091980140785005040f45030101c2d4419041041c090b146003404088036081c888141c0c01c000185034240c42a100e481656070000d0580403001600303003072040140c801c82c2040b4040c8142c0c40302c0c1240c58441c1049601c03c91a00d5131820303200400340c0c00c2c81004101e50650f40a00200080c5500032004900e8141c00100d62507001100085001d84404500c1d0040581040b40761300002c80581060f4040384105004000d4440d01c03550350310f10302d000d41e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 521690233 1250 521688983 521688991
    0xf0904050f0703061e050c04031b03051002070b06010215070f0309020d08040e10270b0303160c051206010e1503060a0c08010e061e131d12040b04031205090603 70
    0x442d40d5068003400741d4151170701940c668881500500c001e05161201e00c5090040e0300015185800c080b4144452184000d0b40000540d0302c06d003550030040084991a000350810002075501c0c00c000000681c0311342c40441e002a5849016015226680307403004111440c200e40901c4405040e510f52113400903949031052204903902c1a21000e640b00d086c0100054450005040344c103100c0c00c1020203200000140006091806204c15184014140c0c071001c18041e06107032010079054000001c420031185000001244614001c02e4041c030020b50701c4080c8034001001382409002c0b03822800c01440742d0050742c00516003180155000103800c814074000203040c60310950b400d420607030355020802000d41d00500380750300410312406445400d250041c0070402c281002494184401da22401000407941d8a000c20490a0b01c0618100328a44505d40140721400c091058064603100f907014442c035090480086a05403103c4010244c00d1601d5541c075841141136000041040c403600340260b90f51a03c0b5003010b5441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 521691483 1250 521690233 521690243
    0x3120409090c080d0f0f0c020a080f2e1d0607050c0127120c050105130506101208030a020706050a0912020a0b060d0503210402090a09020f0904050f0703 67
    0x1941c07a651628103007805007544144201c4e00301d03203076540e03007507400030b140486240950a10003200c003140c0d00d04440710701c41900025405030b804200850000400101848000c504408a81011050680c0066001c02000f90729000380f1360252001035a00d0540c002000600e261a03c010030300d807002c00c4480c18a48200c0d440000600041408042100240280890341140c4048201c465400d00e10007420030f240c4040142050888002c14a80741c1e2003050610070300794100e402001a42003800d8240e801c50b2001105541e5072243c3c2c000304001e500307110340c00c80807115440400700c014041d9030b60b00080c1d82c00081480f5010b40c0d09106a00200b8602d0098500ca040d4440c0005000c00351761a02408a495558a49045511030302c84100040c0b4940c4403140c02c80000c807100d50004520b4a0001d2540c0700344d2144003c0c507805c072125403046d900320401c050302032403003103441c1e0504e81c4d245c44c4410101c2c3c00150002e94010510101d242050802c8050550060300a0381079807215444200c85030b03e40702c0c047d802216 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 521692733 1250 521691483 521691491
    0x11010c210507020607030e0315090a11031c02240f0105010c0807140105011805100b0c010905030f04061b03080105041e1a011103360a0b030a0c0302070f1103120409 72
    0x21f02d52400f801080780281c8e505c451480103040040c2a036694032443d80b0000c0480b01944030401030f90b60100b04c000000d40414407803007125840e0010094450314024806130009040558000c800706484014500c00c0e8184061008282c0c41e050044802010041064401020820904000c550b0400d28299510413140c00800c0e55454124160000e00250110710271840c680410302c03c1700000204d059040b0b4425180c10784d141c00c0c7c0c14044500401c21620010110321000030303052401c604650181c42100c8858a401c8802840300031500301095601c038004001804800061056240c01d500c8070b405500c25005201010000c50101d008980c4000d85290a1030a442d0100f1410340e880004404502c8220b0065403e050110248100803001404a005021030940c015600c0225101c1d80b000d074608001e01f091102c682e01c00580365a030303205071100014542000701110049000b4000c484580b40e0040b5442c4070050715031030b421000c2a000c5011503142c01841440c0176050744d1600a040079001c0160000b0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 521693983 1250 521692733 521692757
    0x7180207080702270f04050307060e1911120a020312070812010608090c010504150804140312070201060806060607020919020415080a050108151506070c0311010c21050702060703 78
    0x903131480c0d0002c1c03003100c4000c62801004009038000c4181c1e4011607000d440410156a00c0d4407840c180081a6040418034039078011980500c5a0f20800180c0b100e030a840c030342410303400c58000b1030321001b1f142006501030344101103403103040035051300520509004002c0e0f182481c00598503600b034480283c0c8246c0020b4002030a00203409020f0ec0543d51000d800d00307107e03203003900c1c00782120022002c1c105c00b076051080c81070010302848500c001d800c064011070000c4e039540c2c1544044660080030103660b002c00540c0703800c0700420f94010008180f0301440004015606019541d403c01070510002010801071640c08002c44c14506c071280094805410f0714091500e0400e094280102006401041804200c0c02c003001008101400709021180d084100207010b00d582e61004070202d8003102250954001000280c1402400f00500301a0280c1e441222410000042c0c04011a1102e130007200150a140c1c2c141040f209820f0074a114500e074100382c5c20100d082441a800103146034100403c240d0105035419050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 521695233 1250 521693983 521694049
    0x50406110703170315040e060a0f0e01020a0c1a0705030c090f040e061b03010e0a09140f100c050901090b09010905220615080c03041e14070807180207080702 69
    0x2042c800c65060b1810004401f5544100740c1d2098007600d29111259030391031490040f4255040045107038a032200a5680e4003c4180c000c200c01341c0b4010994400c2046402e160010005402142c0589803da40301070468607060f4a802c4030750f101900481d40f15020140d0720703101c5d84035401501009220032000d011903144c000b41506a800c8007080d4440c0c042c004100604c83d075614420402c0d0804070100000907240c800d03107820780000582e402202214801c4134224201803c000401e454900c103811024000c200452905460350b004030704101e40490100d0906000c4840f1900250099520524010320b00940e1180800c4010542c407a0b0f80c0741010904800040c11501805420020210701d080500c6124420800400e450400b1342003242c3c10324004046014041d880704154000c29070340d03442c0000c1d00b180c0e140200b130052401000c15940d0060130b80004111074041118011240c02c103202c450b51200454050b0020b6104150442d0f401000784031510244c0c4035000e8940078450408510070b074003a0a0b40315 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 521696483 1250 521695233 521695261
    0x1206280608090a020114030c070203030d0606020d030b0d3305160513031401021209030904050f100306021317031305030304180507020c041104031403030103030504061107031703 78
    0x10702580d0f0384800c2c03d400c01070342d00c20030b0030340d00248803001c0c10384a849030209000148076501c0c000e0b5040c840890100350b0390390b5950007a000c440e8650204c601924000300143d040e0354803d10310320790001100c2c445001107400e80100750010a2013200880080d40e42444292040c0c003501d92001303120388d4070350810010905440d15840d91041720300380a81420860200720842c40c0c2c00d800001c01c0c0d411503403a44a00402c2c250155120040c1001c0d2161092400b4440300303559400c04c02c0c5a40c4a94200004141030801081c03a26006400440a8518070303030075a15a00b01030350018101611a8102c1d66000070301616240380701d10070101c010041c640c0da0101e09502c4080000d079800081c401e40081004000030104040b00c8101074030303117207030100706a80c8009040e0308240800032010782007810301427030702d10041c81c2c42c2c0100213070f80c031840c401d840d01e6010700c50385503481c0001d000003030104800704401c0c07010b28019480d010002c000310303084452a41d00c0e035a035141c21071021200b05000002c080140910788119800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 521697733 1250 521696483 521696491
    0x30e0d050606120f030415083603090a0b0910110d030b030109060510090c03090825050f0a11040207020a050f010311030129030702031206280608 64
    0x4058408041a032a956151503020340424840e00f0a110100304560b428030055441c4841d03403060704d0310386507103000c080f90344d41c420103051000849500014682c141340408014039440300c96030b00c3c2c0440c220701058481d0b0604a8810403114407091040c45a681c1c1c41520000291405102458071410040180b03e49901140710741d40030310182c402070103c029400200f000001ca080c2c5800f10703040a104001c00d005200014002d07041c9814070007040b50080c05c40501c18115000c030f2508000c02110418100c1c200d0301a008000e00c0100104602c1c000c08190300e401c151108048400000d84103d140d41c0d40b4502000c8203850f0301182c100c0c1c0000da00b4440c2c0340b44a03a103000d10945056107006d040e81c2c0052152200c50144512601ca29002041d650744643d0002025500e198182503595856404105484007070900303011140481e402001d07200400102524050915a001035041604202c00c400920000400e2241c11990700b5a80c0c039401245403400d8100000c075292400c88140c100750b402000220018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 521698983 1250 521697733 521697739
    0x3020a18290c0a020d020a0b0a020706020714010e06030a061d06011206060e0103050c0c070305011e0902090c09040219030e1b01020318130c12061202090a0902040905010612030e 78
    0x11210412080b000301e58248483da0484100009007490310000d0085070701600410601a00403ca1910107600002c0d40005d41c2c03610340031176085603640d005540d00c0400d514501c2d400134032507480650803402c01d84051078101d55007030400b0800b1902d400302804810b0f44814010071507111607040c8800e950700b2044e610050030040005001007814007201078040450101881c0c1010b50303c03400680401e0850341540d0142c810781094841150343d9040c12400b801704508012642e40c00740314120002401032060a8121f075010b0a07040081e0f5401da215013550b001200c04c5a000f94003005803100d44140307112082c07030000194030b0028010010003203a178507000c040c81801910010a9100b001c040c0c1e00007041d03586059240112002a0341400c010410b400c0b003c03051007407600d040881c01c1c2d11494000194036034100101004210560b41c03404032202a50a9a601a40020421010841e5407119070040445140040c00c0031491004541d1a5030031528141d200a4010840100300f20806900004a110b030800403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 521700233 1250 521698983 521698987
    0x605060a050d0b12070302010818060412050c01020f07110406031e02010905060d02040608070219030309050a15020309390a090207150608031903020a1829 68
    0x1012850610442494109120020610548519503608a4410844040c1000c10010b000d465007960340d040c103020890109000780c0004a50662060f15125042d26000c0101060740b69611020701c041c0d0405d01e880c0070060100b20010705144240000d185101c072401c002d5036110301c0c33803e04100b4401c05140075440b0f181440303005c00220f02c401c0c5000b64211780c0f54800070000c180b40d2005850030100d075404181c1100b000f08110841942c00d0380584100c41864443c0b20841e91400d030202d1320f4506043d903407507041011035140e90100340301340d2003844650301c500c044030302e410440d499124403010040b0910080c40c0c1c00104000080c14103020b0006900e11040d07400e40e07181803c1c5d03c0d20007030b40c4881c03a0440e800d4042c1e2140030000d40e1a1220040202440070301156160406c1c1001d42160b40011940200c0c2c0781020000280800300004a82d060a4800403040001015400440181d070000211004200036814250784942409060394000d28200070001d428000c10f0148005041c0100400e4020140c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 521701483 1250 521700233 521700239
    0x60f01055d0c03060d020901090506040605010f1e12090f0203010b04060e040f02030c090907051905130f020c15041106030f04031103070f030c030e0a0b0f0c010b060a02030403031206 80
    0x2034901480d400002c201e5070b0350380f0795541401107400301552102c041e5014005800006138001d055010902551041e503003480301540741c0b8015200e45122074801d00029244400492800b2070b0303040294250301091074801c004062030400c020944003c8602035494002902c0c40c0d80440c542440340c078040d9103040c1c6003404102d243c1985035150320030080014003191901c1409900719a8140141501081e0042104649080001d4102c1e40e50706540030741406605c11441c0061b0108030300b58408121030004103011002901010305401401184120181194003030050b04040b44d004d002d22101844200801c2015140a04012a15511100041e4020700d010001d12a45000010001750302a4050918030342c0428500d8035980703103104030100a441c1c00c0c00070300b4060406600429190311980207982d0306030341c00300a10802c0303030f403040d18480c0c80c83c4024204641c20001e61403201400a42410000000d001c12507040884e03901e0348079444400c0103800001c0c0030300405402400c110200d0010203030422a00381 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 521702733 1250 521701483 521701657
    0x12100c090807050d08090a0f08010e07030b0601032a0203131e0501110a0b04140f0c01020c12030c06090106051903150504060b041401180203060f0105 66
    0x4141c06064024404031300d03240184580c1500b190b140c02c00c0501022a0b665503500c0410003140c0f02d0040c24540d50920741c914884d240001402c0c01502d0308011240c1e0180c079000700540082c82c4075003508038098480c42200e052021986c500c0f0949000301c1d000b03035a680c4011803c044107000c1c250840745d0904e0980740301c1d50601303504c0d2003854281c500a00f0003120301622050b811346030802518001700070320705007010881003003210071500e80411640c1c011111880310440c2441c2d2240c0080720002d005034012041301d1403915107451141800048102900e18003c0c000b5030f0300d4205002240c10260583d100c040420190400c0da40b01a4a070f15400403005509055640302c2d42580802c0e03213003100440e200c4010405000e0594001c1c0c4070004010420003454000704204000c2c17010901c00c0303000a141d02020a00309103803034021244a01001054a1071520002c00117595980052042c2107034007002d445100380811508000c00039240c000e182680f620903000c141405586417a00030103009100f108c02e030f20300c080b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 521703983 1250 521702733 521702743
    0xc030b01030516210e0304030c050f131109210d02060403020615060405061207080105010509030a060e0f03030a090c05121c1107030f020f04050c030a020306010c0212100c0908 77
    0x2803a540340840f1303103522400807541c01c100c00d800d1034a40f5910745480c0d6011440000003c1c403c80b0712411005500c40e035208100306050200901d0a508120300b54041c0300900b005070f025081c2c0740d94000049040c40000d5003c0b03020061100c43e90b0310f120910340e010761000e4408021802c1c0103080c5100500c52403400e84d81c003e4a84001038080360362128040c01400f038a603650415940509406402c00340c4916a511031900d40b01c0d010785400300460f000c04004030f4107500c101e0803294001c0c1e0203802130880500f140e440600401ca003001c40c120a0181c803036100b003149001e00086026901c4201c02140040690408c80c03c03030440766010340d1240d030300d07014112a0045e02081100b0f585e007a06c0e070310303128001c00385c041a0391005820144460034081d54501204010300701120316031440c026204e0440c20b101d942e0034041211026251410b080c40f0600009007a83c6198004680c0304030180750440008036940d0110701d0078507104101d418141c014180c00140d4110900c12070b840204249450603841d0b00d0140825110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 521705233 1250 521703983 521704021
    0x605030106140312130b071a07050a1b0c030c0305030417011a0108090a0209330102060408030a02070b0a02040e090a02010f0e010306030803070810060f050a1b05060403030c030b010305 81
    0x3c010017060400f0310b0800c034110304000385400001c3c0355032081240707040c0040c424900d40e03020b031155004001c10006407250b01554840c0e07202c0d8941180311244100301c285a13044001044403052905a0b001c40003502e013615040085115800035501c5038108a140380c201501c40080b120144c1c54002c416081441e07002546005801c2820700c40d103181c903659402c50a002007100003a412070410014403858a101c03410781241e16084684000d8000c20381e9200d80000e004102a150040c1c0c000c00215002c182e00c00000c540281c2e49841c018075000d035941d01c046c41003d08032061105a5800304040064440c0d201450354461000e0002d0060303c00c0c40c0e0300207014208100d03c848104070030050440c40c4d83c1d001c1d620100103103030440045038991a24000c000d1039080308880d490b2422162581c00180f141c00b80065145000c00ca4541600301082c83c40c00722418a900c428a2005540c8070340d2b4031010480030b00680d4001c500980d00420800c4000c0070103810b840c880c0d070440381054501001c0001400e41c1404120319 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 521706483 1250 521705233 521705263
    0x9020901150e0d0602070f031d1c08030705071403180105120106030e1e0a050c030d0e13090f030c030813050a0b041a010605040305060c03242206050301061403 70
    0xf2450850610350001e010340c60004000c01c100504000a042c2c10030b01c0c4e51030760b401000301101100f50f190b040c07024845070b11508510800780c0c510400005103035503014640c0550645002810301a50761900d80c0460320240c00540703203800014858858243d10606100004d10070b0a240e8074154040401440a101c140b00f50004c25584188205c00785001340720f01e296001c2403146480c0307000d1038991080d407503808854084542d0702c80d200b8104d0b001c2c00c0c0031428011700c10141c1c40749180d030712078082805055503102c08420110390741c8408581c00503c0c0c0c4800d41d01e545d130081c1d4903820030703095a00e0040c0002001130056140010007070b00420004000142e4508502c1d4007008100c2640c4680c9070003020400301d41100c80d90150308400104406611034094001c0f603002c0e02c11a5941e444641010300c035440182c420314440e40a81c14070720f040c904e4090000c2400744e4090404120f4070a051b00c8404100754028a003054540c480008000601c0d0900030032014052640c000704c40510003000003591040740300800d000b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 521707733 1250 521706483 521706499
    0x1406030a061109210c090613050c090901090e10110d0b060c0f0a0308060402070f030c0203101a0111010e07030b0a0209090c070201030c08010302130906110d09020901150e 75
    0x400b8070094410750790240c002410020307140028000c00100c54495048031207007031003111003d45651a0040d401801030754094511080001810f44100191100804e90315150b00200070340e9004e0349070040c499000340038601d00006ca41c00c030144212304000c1c100c040f00c007031141408a0b60b084106844100da0109041403c00900340a114000c18107a000d40c98498400e40036000a8070a00480403a19604c014442d5491485c0c1cbe944110801c0200e0003441d202411160b008140000000c1c003403034100c03030810300041c21a07242140751000300054514400c0600d440034041807010010756004600c2038110b4401400910441441c0308415507541410311014061000d441c0114852441d598100d81801c0d0025140704007620b400328480c800c0b42d00c8100c007280020f00e00918172a0842c447d072000350580764010810750700c2d0016009032801403c0c2c15441607034031030f80e542c0301c03002001000e0b0000d201c0030014034008103660707425004101010f04160320030800c20310a8080858055400458035034501800c58072a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 521708983 1250 521707733 521707751
    0x3061809020f0a30051b130510060509120607030c0e01030207080f03061c1b1d0703050a0f05040f0c0803030f19060806130b160c0602090321030a1406030a06 69
    0x484108414113001d8068040c011a40564184900b6015010b00e42640c030046002005800350701200d1044920295610050b0011720000303120303034000c0101080003015058502050100d42c1d040c1202524210003095903001c00c80009a01301060244009090800718141020760310380b10864401c54042006100d000400074216696003c0c6052960b48003071500040b4064514105075418485034280c89480004e140c005039040c0448280c6140440c21800c6926540320840c05601910010349003a074616181d120f0030004e00d030188201482a405100c1030b4030141010304003051aa08a03410403555608108200140382c500300030720b42e42002400a00201410010b201d20f40100080d4029101c0c5c2e000e01070600c550f40f4242d00c0f45041660207040313403c0054550549180041c14402e482c1004130b5840342144020500c141d01070b08005034090b056030740283c01500c00e807100c003c0301d80d0034946c1d0701804800d004403480740d3302c80d4850340c0044154614250404000003a40d03820b56000080070b0907180c507128 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 521710233 1250 521708983 521709059
    0x1a0d0e0a120509300f0d0219030e091015022107030f0f050d0c02011a030601050109051504050a0b07060b03070b0f0d1b050c241603061809020f0a 64
    0x540030020f035100544d01c11741219600b054403615021181d9005201d101e207003000a03000c3c445000381d81ca900d82c40c1c10300c01c810f000c41403050000000b0496651418400c00005aa81705644000c41015141c7c0c0a003001450024004c032000155004440500c54103200d40e10009401119855540c3c28504100903283c030a11000c88461044c0c03580026075900305800007040701d405401070b099114102d80810b0018854009140d50b4010912915000a1a83c0e40c204542e05000300030703c0001c110101c00d14542070b114000704044460359071011560450005007801404058842e0a0400608038050644645000fa0107a40c0340199029020280c0c800540c42c000003c0b0b03540300c0207480201c000703d11001001c00001804a07000140c84c100340d40140031881c0040c1010242240000d00411004009621103090b00c2c0b074510058001c06050641c5c80401060f42c01e00400043d48000d2104404580041103205011048110403e007500441c8042c000b40b110b542c403e100c00343e107204160b00e40340c0302c00c2c2c6401d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 521711483 1250 521710233 521710309
    0x240f0b0d0905100905060a1e0c120c080619030507050f0103020d0903050d0c0e06070314130f150e030c0108090109021302040305070602161a0d0e0a120509 68
    0x4000e14600c01c031107014003419103c4c2c200851990003401039507000e41e201d9002000b030300d1400e0b07256425240600350081e00040b080c1d004034100b0041d80b80560070400c0000c60b000403652106a0180880c101c81c08100d09442c2110700304802c17602002064000c14a5a542c40e552500705029261040c490b42a098281d64880e0741600d0399618041000c0c0302e0100d003800c0c0500160300c0340c03035001566410511240c4e0170b60302504000d541d0703c001070103852800c005528101c8024034020340240c095003040083d0300c030600660480034060a01d0902c1d8501c038901c1e0001c0d100214200c100450240300800d400c0d50803995002c9418105a0400c0c00c00d10310543da00c805290062040b0a4006c0d4498121004c2604c01100d960140c41524482c0f0100c4040d1926804141da6481d2200200c4a5403050803400f802010b004d01d080f0809413203c42d20440c10300d000002c100b02500c200f1000e0303c890340c0c072070402074080c0144010304040701c1c415424414648184103010404180701c01e10612506e606014252b4003080704011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 521712733 1250 521711483 521711501
    0x240a0806010c0b07090e07030218100c12093311071206020304050c091b070c0504050c07170a050909100305030c030a03050f130b07090b0409240f0b0d 66
    0xc60f5400700d02d0100c101a02d4001280140b141416031a0001000700307009208548841c4421140d0642d0000150200304801c5002205401000300e19213416002a001e54024038090032180c903010615801d226288000c00400d00c104035a030300610a07400400c069100e03205041040f03900e080913401d40c512440740d10b0b10403542e1294020000440f0080107111865000d180a41d100c1c006580780d4000d0b071010040150020703200c10402c1c4521001c41e10381d00e03401c94010100144101d201000465441c000641255401c590803801c13401c0025403041000b030307a82e2400f8000240c07035500b5820000711040c010f109028144a00380210140d101051f20f200300c01d20440001c5a000c41141e07940ca02d075902c5d00c0d840740c108204400110b400c5c1404100c1d124040301d6818482c641e6424040c0b0071749400d0311140303114240034100c43c1c144425401d0110b8044082c138002c00150051a0011904840108510509400903a001c2400c0d10004100340711801a45003144106e850401503207448a004c000c600c402081411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 521713983 1250 521712733 521712743
    0x6031d0d030b09160813060b0406030c0512070f06030e0f1608070e0f0a0203040f0210031a040e030a08060a0e010e06010809031207080c070f06020306240a0806010c 72
    0x10300052820354590040c9140e00d1080d601d11040d41ca50403081194520a041064045018100002c2941c030303900f1003c140d03c900a15012034460030740740100703040b40c1450f0001d0b01d0300c030040329040c003660800c44d15411103205020020022146454201d064407001d5001c1d030010540c585c54010b1207403c08129201d00003c50500b034840c140e01c4c45840c036919207464400c3c21280d000300d440029600245603061482511016410020340d515003071210001d45c00100211070322103402d80c0031400740e2070f1242c034001d87d0021a117002070303c0801404044040c550b0302e201d49128904100300700401d0300e404800d46004e03854900707108102e41c8490f07000482140c00340e0441042800031000003d0410001200c1030300500d421388560120313898075140d664a0344203a0542c050b4601c3c1030000300d81c00d144102d089550019084401c00d080c40304940e030781c200035862084250f178040c0e0084248881440d0529066000c24070034200c04100422220001d4414080d000408081c400440001401d40c4d000f02c080c07a403000c5e808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 521715233 1250 521713983 521713993
    0xb0f100b1201141f0e06121801061202130f0e030a03020703090b0306090423160302040c050c07060e0d1a0403020c06130b071a01170d03050403050406031d 68
    0x14105100c1d6511091150826528100e1103840c1241003440c07064048022415402a1a0044180540708001101c40c6550840410406031340c04010070800607000304400f00b00b103141260040300c41c6096030881d40002e07140740c0c018440000141e981000000e1040e10451000c6005070500e02144001c080352514100c07240030000e028040550f1603401080c0147c401e4440b203e01c940c89110003102c60000700c0704103401c41c4000700031802051944000c1d40c0300401c41c0e81e510800d814404442d90800080300d400c1d080001c4045018004c41c940740c0a602c02190b800e160003410031344000c800d1542caa14034440c55007400803481e09801c0c0b43d140c1c7c240b20a20250040122401c07080c41c02c0d141901c100302200c00b940140a243c604091a250081c200c44800941622512505003889044202d540c4a183c2c105ea43e0144040c0c3c4002c0d810503074020070700810445010310002d0b045c0000d0f890400c0b85004900081601e0002000006a00042990280ca60500d40001c01c0549224000310800000800799014030030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 521716483 1250 521715233 521715247
    0xc040e010603060504050312070e0105040504020c0f191a060d0206070c051801060f08040507050f011701080d0906020309010504090c0c06090602031f15270308030f130b0f100b 77
    0x24004e012802c2040d10440d6140b03503003112b0603190340c942240002d0302040b0422041c0390540180958278500019100c0c12800b07148524500090303200d07603810503144003a1a0781400300750003804000078401c041e144000e20740800010642c40a855000b84245c4011503485c05100e21040d440c0b002d40b501030b0850300c140c114510300c1c075038070301092140354001280f20101505451240c15414000c07076101e001040118140302c00c00542d101745070742d03081c10030210084d203961110101c0e40050003800d454010f80003811440340003e0925000d5089001035510820505031187d0740703d0111402c90721900d40024400e404500100ca071116000000707000982041140014003856500031030184001c1c07200550b0b030226071046000804540d1254103094030084031138482041c06804c1e4844075100c4025601c0411007055a034613016285500190358400000c000c0050082c00c0000981d002413034100240c43d01c08185c3e80b50003600300b0080c0b0031511003400401103074010352040002d1010341161010070741c403804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 521717733 1250 521716483 521716493
    0x6050a090e151807060819090c0e0a0e12071119030605040201030b0618031b0612070201230105030601050d1e1407121101080103032c0a080d0305090f0c040e010603060504 75
    0xb8040c1c03481f904021807810300290311072051140c01901d80d030041e880340507546004248540000001d1180410903201c1040414020061002c044070080e0310306203035100d08042c2404143c401144c6103d500030703d20500c51240121500d00481c0840e0350081001c11280da840c40100c0260018420407500104080395281082511001000c2d040f10194200c40080104a110fa4070050140c6c00c1131740c00100803c12000e6203604058216030041c072500001c59054507408540107030848007903905203000c0050005000380e14041c40310500404085801110200290711030001f14a4250b00f040300161089552000300210340490b041e8160034a825920032030b685419403008a00c800720211040c41d028641c0e104203600920816040c0d03601991a441d120021089001c201c001400c40d88610f040c0390400540c0f036a41c0c50380c226001d032106201810800d05924005016039002405100c501c0c1c0140090303030550320b00081d14420044048401068001034003505500510740d0380c1010302a181080c0800c41400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 521718983 1250 521717733 521717747
    0xa0b0310150504090911062a03090f06092704060507030603020a050f010201200a02010b0316060c08040e0c0c010b0d0b070e040207051212070f02070605030c19020106050a090e15180706 81
    0x4051000c0c84081052303419075054a0384070301c0c011290301074000b010038500c030304101e000380c1101c0d1009004500390412001c0742503240310401000204c500420001c00040001c10f0040036005122428180203060465000412088850040f82d004030800c5600010320380c800d400c8051240942040c00035062008411a5483d60004035004003540c2458407075500d90a0004000d1826901000c491074058180442110301355602c2905807002d00c3c081c000030a24140301550319000c1d24000b04481e42e12420002ca4a095524500c0364600c10300701c8240c01800b04200044003036000d45030746800b117031001e440307030000e4000e002d0440013030403902c103a48209042d00000402062a000642c11a000c956030b0b65608640c18080002104010380010b5000c0211702e006030041e58111058404203400d001c0c8011803030030208500324500006079180d000402450034907a0055002d809014000d1007500007000c0c01c00d82c0e81c50250390b050300311840f800c0015081c0100c200000c0c10b010241042d160403d90f6100024101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 521720233 1250 521718983 521719027
    0x7141005010326040f031103070312020604120c03021002032a040503010605120c06090d02040903020d090b0c12090109030209191104031e020a050a0b031015050409091106 75
    0x20502c90030f84115154a031a041d0b43c22610320385102c00035103045503602c03003000c9071520030940c051080210104c0014101d14280011512960041c042841c140c14051039a0710211040300622072030410302c401003540421a002410502d20016030b03603444174408091400b160002c0420781001c8210070303022280b0b540c07000f80100c8404600030b104054840b4100300701c4480b56141c0704101c1d030199030825407070300309013014100001c001460420702444540200702514080441100160800720b00349103040e8002c64210b0140920201d07030741c10b00c442082c40e0355498010401110019130041082c5203140e01c6a200c4030003440c0c1c082c148600c035041003071884008500801000c252181010701d03040040d0000b07810f84046981085d420850009182c40c90140c000c078184040c3d801c4400c070750002c9515211f001991008140400003503980303150416980b00881ca00d0b41205020a60582c069840141d03c101603600f540c0d186c120004a164036440c2114203006481c0b40c403070700400d000c120000c42a601e0000405d803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 521721483 1250 521720233 521720273
    0x40e040506060f060d0c0201060e010b0c0628050405160e01080d02031213030e0913050c0303131503020c10050612010e030f1303060e0307031112071410050103 70
    0xd540c441100f000031034520007070159088041400380601e070300074540010880c40e40c02d000010350940c96403c6800e410400340c200300080403000900d030030030b50f104000c0c4503804481d440c5101d6400c0d8882400c15648958081d168100e55102d201280a1001c140624496001e282c20100c0c40d441d0f48a03280175840909120f43c1007140109042c000740c0f01c3c00442100d480359500d8100c00e506a8a211403200e900b078284105500700180080608010307284c6290aa000d1440c007212111030850520b0602e25040310702003114001e410500001101c81e2064a075001540c3c8580380e05d809019090100302d0090080e42d40c1d40b0701070700c1101c120544130f10240e4030060048000359a21811850f05c210400d080c0d6045004842003a442040080802003041014100e01c805074600446020380d0b035115030064500d07000312a0b106400010300780040540144a10794825072090180ca1a9000302d580260b9a015400000c1c3c00403000031600c804000050007003059120941100300b1465850f07040c0b4900d018031608003a14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 521722733 1250 521721483 521721493
    0x909070806011b080d0509011d0601140103021c09140105010312080106081005120102040302060c15011508150402040806070903050706110c0f0111030307050706061505030703150803040e0405 84
    0x3048031546503503a883c15008500381d0710702040f404908001b45001004514155600c042800c5d1140002610040e40030a000c01030401e541402d0712a03040e942d41d442035906151041001d03008000c2c1a00081d0f0307040301580380c0085c41e054103080c419040d00c048180c4035015440c0c08008400c004264040c00310714540d56035020856130700c3d0070068514103401e40e00f455900c1d44403801040303d807038100e40c0c950a96000c0e10003d8149a5240d01094003600402004981c9401c03c2901c8400010150130f15801412441e9180e40300e28001a8040c10580001c0d100d1009a42e0250a000c003542303ea8048a0044c28142e0443c1e10b9880c140380000d1045c80c0c0c84c00200ca950140d804c000550a20400305003d40c01134032009000c030800d500d002c01014139502511a4140003088025815105081c0050b504c11070f415142d043e5180030310300e01203003214601d4002609000000080703c034450f5101041e41d07440703023550800052860074014a10f12595007a031000d601440000b0f004210008400281d070700072403240c01190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 521723983 1250 521722733 521722757
    0x4030c0f060204090f180204090c1e05030c0402162a080d02101b2006130515010b07080310030501020c011e050906040f0c0f120b0a14060f06090907080601 68
    0xe400c0d91a21b09061a0070700c41a086517015250035030086601c03d20502c42c580710740d03603036080c00d52604c81c4520128900f048141c0c010000e03810184407401281408540841c030b442d041c4447c10440c100c144801030007070401c0800c0c01348910f0b04100d802c1d0718901c440300d508135181d58520b80c284d0313070392101c1640c41d00601914181a031002c0f800d024000b046102c00302c1c001400c151360801100d058840013040941c0401002c034400d000c1c8000e01c0114080c645c4074055500c010401d0904600d0190b02013919409192007100400c07040b00f000c030941c0d8100da0b1124240d0b50f40c0d100e800c100d2a200340b064101400361351001031020700142055000c81c1004501c2040340d007810860b01413100440b101162840599049900014002401e01d005100414803816407880419280c00351145482000e81010010a125110b10310600900080b11640200c40040a02c80c00c404450840031740d09001c4c04042c0a014145040c0c01316a6425050303440054019146191901c0e0001000301503080541e0380a0116040718880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 521725233 1250 521723983 521724011
    0x81b0c0f150c010b06070b070f02030f0315060913050105040b040e0a0803070210061214030306030c01110f0a0f06060b16030f0c050a06050403020f030406020a080304030c0f06020409 80
    0xd444004000308030310781c040845000c9650740d50082c1c1000089559542d1404101d0340c3e08005850303490301a10846945240222000d01021981c16004055520a20190b10200708660449600c0055450000f90001144003c16111300400c1c0e4801e61140c646500020704064991016040b100202c030180304e4040c25000788001c4588001012115801409014004c65429002190031111034030455803280000070141c2c0c12a040c1d6001560074003450581c1d0010b100e400500c0109510f100d0b0069440d50500390006942c0c0d1224501080c1030000901d030240c10500c0c180720707480301128800280c4280c80d00038a0105540542c50b03200f220304614150022560b1359541c416911003480c2c5803080b403040d0390140c800303031160100740c08008104410711484e800010340a1150114080c4242c1002c0391130700781807070064280b0740000d040d51415407040c402080426400035142003444d0f0043e58443d034a45503410100c1d50030b41442c0007d072107210030003614401c00000340e00500c203d407094102082141e40742900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 521726483 1250 521725233 521725249
    0x411031603150b010c0b04030c0516140907030e011104170102030105010206070302180a080c0a051905130213120b06010504030803061e1003020a020c0a0e07120603081b0c 75
    0x2010b009203640003180703114800c042e800421100c005040511205550f41c0d10f05e188800111400c4001482c1980c0038010060200002c0d25016a2044056903007402d0070350403190402000c400c00e00c9044c43d100410b02d001c0c000d6011502d003554007802481250382c2c2c0f050080351a4054822040d080c0c00210130b220a080041c802c0e40d042c0c2d00c1c140c3c05012a03803112035080b0701070b42001102d4003c01d00c0004261100c1c2c0d0b80c6240d000300820b10780d000303000d01c108a041045000080d50b40540c0c042e900c0742c0424401100b4455020041d039000312a40404a203401d82c0c440024041d030410b10003c1003903002e01203100316000b40d298910503c07504546207a40c0d680001141d941c052407100502c00344003030010550629090b0b1000c00c0381c0c02030050b0610621074460005c3d5540d500381a4100c00310341c0c00949107a00aa0520100c9010841076468542c071030b02e40f2400080202000f0040c030104440300c4c46a070b09401c02ea400000c011038101d41c1c403548501d00d9240328019034003e0035804000d40f140009800880c01d09000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 521727733 1250 521726483 521726489
    0xe1603092a090614060a090504090309060e030a031b0501021204030503060a0929030a05071e080a080901052107090e0a0e07180b04020c070501030e031305101704110316 74
    0x182e0300c0d800c484d03420b01509400c007545800c207201c510240440c1544462142044042c080c0d902c442c04149000409828807a24105282c040e40054200d0401310350015061211140c0c2120020307500520743c1003040c0213004000c0550314208040c400d000038103501c40041e50003400111800d10391242e031140501c045600d04a50740303140b44603950108250120400c40098140c00103003d80785014001d03a40c06082880a4000b401c1e44e80e59661007800035120034148101504a000051114002a44640d456401a008100e04100700041c5401100c04015280b50120030001c10000b91410444809840b6170320034042c0e0300c4850a5480028140c424601411000041d0880908071082c1403400d103100c90b500070a0503c046541742e40c0c0c094843d407543c1c4028801c0c48000009040120308000c001019900da2903103404460b07006220000702608004520411610110b4500c4030030050300c0c03401c1d26404101d000894a00700302c03008100910420007411501a00300310247c078103803070b40082c400c0b0031929140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 521728983 1250 521727733 521727749
    0x201090f0308060a030812010603181205070c0810060f06111e1612200d020d0c1e030c080604022d0603090a0201030b0a18020913092004060e1603092a0906 68
    0x1a00ccc84640100024960740703004110a0311000d4661642d50726000440300300b003149542d100303030405c10203101080240141c60300d890401b40b20300314406800d0740caa50000c02d52040c143e1890224101d00d100700004808000303c0c4070300c11192a5a404550501d02d17116a041d64800400c21881d081c5042c04210a5461900101403d640980c146c003400328550006604894484a1400109a00500c01030302c0551100019000e140c9905603e48080d42c102c46601003240c584c03140092100582d1202e49404950034000c081c212504e010790f402202c690740b40386001e03401020000a001030210f01251400780c41d4001e807400c0c040c0000040a02500315510b1088140320802c1001c10001c05449800820303221a00604031060180c10041100454806c034204440b90170315004642040f4154000300d164816003200c0800200f448c0081d111080d00f0014010420f4100041240512074025480800e05640203c01c1900e0f0aa0104082e05852151400c8103191481450009003805142c003d4005a960705 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 521730233 1250 521728983 521729003
    0xb1b030906042102311104120807020402180301140108062d070c0b09010c21140903030612010b03030d110403141c0201090f0308060a03081201060318 66
    0x1201c3c801d0320103a62074621114504455101e07002d80d41c0c190040d00300c0c601909a80c1410286141c0c1c81c1e00c9100800340001030181424108688074421005603411202880c06003036800b0080d00d001112445070b0000203512510100340200304508070640c0c5e030304001054001f041445000302d00030300000024455081d080c0c0c0701d00000b58084c0c01064100022840e100c0180202100440c2a100c070f4260444560340000c203206a200140f08064851607000054400200502010b6000003001d414200f14500b03141884441e0760714101d15691f000b520580c0082c2040440f6050142d075080d02c9520984025103c1d8090b9031100d12201810300c15409445001401117103042d01045810000c3c1005140b050710343c1c0d41c180000004620304000c01c034a50905c001c003800c002900b9041041800035070000c0c1d1400c5a2605244000154a107240381e04451b07010704020000d41d40d04400120300b004207400041c000b04001c54540d0580d5607440e5814161110364509010b16481c20983d40b14004521001410f0f011007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 521731483 1250 521730233 521730239
    0xf0314100b09030a061a100c0305030c13150309030e220e0c0d03030f1119081b0a0315060c0c06080c0d180209070306061202030a020c070b1b03090604 66
    0x40008190180a13591880c105444420444080030844409000c2c0341c0307004421841c043d49501907500c2e243c10002a07461003924002d029000040c0001c810f0340303000074003001090f0880b801c0d02c01010b01d10038007076001c4c0d08100b004000d017526650882c0800c0555401c0f40042c43e02d0141c5603c5092090324030305c0c001c00542050400340480120300c11050041c07041e05011030302c1da4032800c00010301a45000c103207801c141001100301c524085040a01040a1140c84880313042d4501000c901fa8903468001c1c0d442d1180d00c0080e1f00341c0da010721500c100000005000702e4080c0c143d04880314540d910500c0c08030941da24101543c181c0c1c00a640200851500042403204501443c0115000f8142c0e0036010b05240c030031418401168036030a40300082d200744440d60411460030301c240e10342c00203240c50140140d51a10780090421440b003000c1c1085c941e0084009210428580e054501111511040f036550641e159000d4950f0360265007103115003824400e0720000c20100108032003500741c0280c030052a1500d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 521732733 1250 521731483 521731499
    0x1a07020307060b1203120f0f0c07081305030d0201090b010f06050703080928050c040e030306220203250e01090504020706140403020303060111060103020315040318060f031410 77
    0x8a41c010743c590100c504190440140f4080010b0300c14007048454030307030305404c221058180e4040b00070303c20194042c0c00c2040000d421850f2094406181d0301c01c605945840e07604100d92007203801c9400181d018400d0340d5048070000d9054000c10070450007211101c4841c0d0300d0340421f4140401c20700448021500c01c104070b0300024410741e15194061b414409881c15071541d4241480c7c3d000440304190700701001c0400c0c1c2400c0c0141030021590520080f5020802d04186e540216141e01004142d5881440380c08070310904403c14010000c0340000c40c960455680c5002012020b1000c1024003810555110030082c800a41c01268102d045110584071511034618010400020794050a42221413580b036600c00311610b9a0742101034003942c400c1d000745850786850b0000501400000b42c4200341e40e0f01c80307001000035032008141719030b125511a544445503541d40c01c00740c0b503100100c041d005890450010005046900c921111200700e510f9800b40921a14100e4a0911501c151a4440100c034141d0302000400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 521733983 1250 521732733 521732741
    0x901031112030c1b0a1d06120a0b0903030f01050a0b120c1b07030228090509010e1b0109321504080307020a0504050c22050a121a0702030706 62
    0x981e03074034102e80c0380c4010300703044904012001c10941d104413001100e00b100c6180c15403600c4060300381c20840704031b009011071b0702c090420742c00351146000d08004203101d42e008205001c42608244c100070041c3c1c1c42c5c00c14580c4250f590b8400c47e200300d050044400046141d141c40c900c444102c07120f079034555040c0014050720014010002d030904130b108000700100445c00750030061000c034906003a4050281686580180644207030041510001d548070303140104001c420342c0610380c040c0c5040820020b80d580e26203070060300501c030311010050f2910409204014400b8800c0080da85400d080c0d0b42d4800b143d80d100c0501e568601204003154000070440d10303400d6425614203610b1201e0f10000e100524441400700880066881500035128370f40001408806504104824000501e41500c00b004a0b24100c85000d106000c0c00c11181d910744000100004216005203400b00580f10040c03410b13556559403c030105d0070040100044502079500c0c1c0c0034208a6025a41183c030815541c0c002d145050481d698210083c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 521735233 1250 521733983 521734009
    0x5030c0a050922140d0e100c0305072a0807080102070c0905062e140c030301061215090209030c010e03071401120e031309110f07080c060c031509010311 67
    0xf1009440c4400100d500801d4440c040104039014042080030000002c142141407400305008450940c85000100c2d03104414440158262500c542c44900c6031400d00c5408030510081c0784070010b450100742c0e101c048000c2007802c84a686045490540d6a40c8129090b4040c101000d01545030a180070001c039025504580c0d40504000c002d403640d180c3c0042131000f00008004020700180109030824404c41d0021420281a103034011664201034805070030315542d1005000d05010048041c401d10b0006200d90480e0b00203c00910301960349640720301085000790045c3c0003552082c410340c011340c2001c1d401009204000310028000d041c0c41402e0103094080002c2022400b8100102800c2e20003c42c2080e100741c403d104200000340d44e59601114071800c0c1c00840360070040e0a18031702440400006526800c0f1040c082482c0881c648a0800d420f0100f50360080301910000703400b4900c2000500207130b42c4c0c0190310502003808200c0d458450b1500b030021607042400020b042c10b40100403840380740780140006c070203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 521736483 1250 521735233 521735281
    0x3120a0c122f1e0d0606050405030d0f0c06140601030c080f0a1d06100e010e09031e040308030721020f0d0908090a03080a021507021b0109050d03080105030c0a0509 72
    0x5000025400040c001403203038043c006044000c0f400c640400080d000e0000100b90624010342490b040200003901d41ca410301030b02c1c00380708811032600c588500410035050481d42088040110f004840a00704d91300b00121002d03800686004900343d041d40c00f5021b4203002d0642c0080092107980d8040814000b2b2001003469038030f15501c03a44044074640c08001d214452503841050003582881c1001c41c08080c201a08020f0643d8070500401c880c2d03560000561302d4000d100b895094008042001d038441ca881aa000038110050000800800c2c40d000003549000d41c107500c0c950001540c2404082d0128000d04407a00d5194104100b040c45076840ca0b0071004d4843c2c010220b07549004403000008404500c0307940119694000403403902c0c0600d030184007101e40146182d9000c007181c548040c000b5180d4040c6a0b55401c03480400c803d090349a48200031900242602030041100141a800d015110542c24481c0c0f521903c0361412040300c60070314100101c00c5443c00303070040c0040d8542c4c01102980054082020754 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 521737733 1250 521736483 521736487
    0x70308041b0909170304020907031802060703170106030b030c010c110603071e091a070624030606051801180f020708030411011d040e03120a0c122f 65
    0x124504410000700520198000060001c0d1900d802c05072040809820310002c0000e2003004056210060b00b140d028040c0d01d00054503009040c0c1c842030340600308001a4101601013148410541c012a0001c400407605100002c1b5a03a120320840503a203041c006a03070507411003800d1035925406032850300300c02445139584840e075566602c0070a5645e041180c1860014000d0008030740c0c108403090441e041c0302d01901e030036221103050850001d0b140405814045015100282c00b9090042c10380c0105e41c0d10100e84401c2524080c03103e405000040940400c1c0c81c06440c20100103514617049400c1c03081c0c11102d02e1a0041030b0b2030913900207544c29510550602081e150308114081c007505100800326180708480d2191039091909114240e440751040c1e035810301c290205a8245640c10041c002c0c80080c0440d404581481c00c640502d05602421500300d1601d140e580c144000d48402e40c00143c00d07448160f07a100282402c50900100f070761044103565101c04400a0a060100c00118000540c404800b01f00f038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 521738983 1250 521737733 521737763
    0x141b0f0f0c0703021c1110030f06031101090e04151503050f060a050c070b0a1a03010e060601110d090302010c0611030421020111030a0b0406030b010303030204080705040501080307030804 82
    0x1000e900481c850038194201401c1031046141c082d284809001c9913081e01c20b1025155905c2c00410402c50204c684105141607051240c284a43c00003c0c0c0c001e484501405010b41d249030403143c0d0b00000c03110078081410300e0400316081c80c2903041148a40d41081c0030070070b5940b020004400504000c156a0f0311110641c0c000300101e1010009038401a8110005100c14a00b403004c00301141d01c00f4091140c040410050074011403502c40003a50400a803040c0000c84141d040951400c150186200c65015420642ca404104402003a4140301e8202a01c600124561407214a40ca03408c0601c52040841c03c400e800b800554410b001020005200d85000166603501c0004a191604101d400b06e80c4000100002e903098039181a4402c489650b0303000a001030300c258581140d890000910242d1401d60303440d040c5000b90354540210300111340007441041e00e542c41e420000e020750b0060080300210700c41c0110000d0142041e202302c604070768400014500b4441c0c6654112540f0307401030425109824452284 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 521740233 1250 521738983 521739007
    0xc09060705030307090504060e0402100306080d090905060906030618011d06090c0f0a23060a020d09050f090a050a1e090204060b0703140c10110409141b0f 68
    0x1456410301035070086480e880e08901c002c0025500d500043d00440c1800b404118400440c080d044e0060360403191440d240340b200404800601181e8090b0500d4445c0c0c1c14018506034005010f402590141c0340d052100380c2c0c440090090074002510456055482400060000140300030460051600c001c00410b1081c44025145000880c81c0e20191481c0c21080c2804204402085603000b6000300390784001d0301c60050340004084140314420702d980d5468007951040e001c2841c911130380c695040200080d0b204c0b840500004e40d1100d00b481d915000c01d884d03540104403480c00180d461414003008160101036030b17404411901400c0c002c2c0800d07040548690b0401c0d859010407080c1c0c0c82503c09803400140c030b00e07403038010001070f030321541d010240002040002d000481e074000020b00602221488540d0303142c86e88164140b41c180c0380301c07480e04514640350310604500c00c200c00078801c461309010b041c45260741e003069074181004141c80030718511a03c02a5046c0025551016245031081c40303e5003030038444240c000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 521741483 1250 521740233 521740237
    0x80f0a1b0b010806060d150903020a1202030304021c0b04080d09120e040c1106060f03070e0703051509060d02101413030302190c0506030c070204090f0501060515070b0c0906 76
    0x108407000c0c0d40070001030050034800c00c101648028112802100c902243d101d5200140203205801501a01d13a45e408080c0341c020420452400c1c0e103d280f10103a010031140c02510b903041030320128807482c5904a19484a100c0501003c140c540085c0410003c0c7c61740c0d0f8580013140c0c002070301103030159295055140070800c0e81480c406454015101d6140b854010030420088598a803400410301c0102d0020300c18020000070800e0b401070058403001c07030009510b0002840c140b400d03442078150044140402c165180c1c1504424007880c0300c084244089001e000410150b071400311001c82d005003102455001514000c0e0312401c24500740e04140010085c142d80740714459026014031070051580c01c41c20400c0685c1008070020194650283c0b0f1020001707581c840c0152005480f442e8800c0c1c2001c00810341d035409143c1207482c1c544c0c0c024000c1085405501d01820740c0c074000342003a90341c1d510780100000c1c3d50030001000c80e0103003c00c1d110680381004554404000c20400380403404000740900c6205543d0301e641e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 521742733 1250 521741483 521741537
    0xb030105070e040507020706021f1401080c211011190201050f010509070f0302030c16030e03060601020303010b09060f1b030414010e01080106030e100213060806060403080f0a 77
    0x56181402c981e410b06000665070301601460466000c2c25040043d180d0200e400b48002041500044100c103550311884050811140d07514581402c510000402e80d40c0000d88444104050f10340034410342000f5031005150107021013581d081d4001d0040d5030451800c0c0e9000d440c0c8440460701e43ea003000040d1550310208203042d120900940c2d903410a01914184220000340100070458080400d8548044000d00341000c101050007815000700105200b198100151608603130f00d1003180c8d15222260030000c0001c180300c60401d000380030b0701d00411415407012013124140c03560f43c8282841c190004050050b40d0340301c440c40c95694070003030040300d410b05c85440c04c1010300505c983c015a00d943c00c0140000c100341144440e181404030420f1180800d9030000c182b42e0441710703030303050005540d40c02140050074110815010444a0720004442481d2507000040c2c905032121640ca240c0b8035941d0780700f0701860344501d01002d0a907280034840f00c1210024080203240c14032407407401800d80524001c003c5000c1103450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 521743983 1250 521742733 521742737
    0x4091412040303080c21040309030b0408070204050f0606030c0c1002280c020904060c0c02100504091404020a150203041e0501030509012a0e0607060b0f0114040501120b03010507 78
    0x1020014154080c0c000b81d000328000d9441d610f0000c00034a850b4500f41140c0720700c4152406d01c40000e05060140580e10021504000f480030355181c02d03c2c04480359800030720100d00c500c4c9401d000c91a03040b9401c0800e882030a010700071502e03648401880c0000c503002110702c103080e07100d03880b41d1516600031030000d8a0301200881449840c032a5411043c06841c0c0e0503030200d41006403c040400142c0d6421049a41054011400040e8028045011100d010816074060341201c0c070001050304c80c50b84500104200d0b4074001c410450760064100302c101901085d01c0103076020313041c2c0030248030020f550200c403a480b43c01401100d18165890305050500700c1c01703030701c00d41101d54801410041540c1501402d035005100304000c100c80b0b403210610b130034200c015505132408042203903419a500c500800b00d5007411400103280540fa841140352490107045080c41250190403111111607030795000b400701024146110b000d581c101400c0000449200d1a101030803102141c40f01418849a00c0a2180500903030a035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 521745233 1250 521743983 521743987
    0xf0f04062003072607050c090703090302060c18030d030209040b0a06050d0f180c0801150602061504152c090a081c15080f0706080604091412 62
    0x2440152100c40910000c0084100d6240400307504180401129503440c2d01400c04000300300c0341013402d04c0308008440b07440c09100300069844103005000848148540f01105c1920196440f44021425141d40920017000b580c40b40000c92004407107000175145007410303090700c00081400d080c0043c0c50017010340102e50102c0d50015003c0740c0c2e800e081c052031400b9501550b0b4203a11510f0010024650302c50303000c080b0f2925640c0d03800d850410182d5003041764031558a080250201d840c41c20241d0302d80c1c00a10403220150300c4c04442e40740f0000451110701c201c0c1c0d42c54001d0450f9582d002c2140800074116035200350b1040c0d41d001022440e54017200680090842005414012007000c4a014003140c01164400151104a81000703a4810005210030003583d01c42580b039242c06202c008204603080692a001d51103041244c841801184a24a001181ca80400b250b500c5400c0a076860307105c01e02401a80009204800001c1042c1016044800100e105030203101e00103c3c1903000c1c904028034440980c440d0040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 521746483 1250 521745233 521745239
    0xc0b0604020c2e0b0604120309030c090f06050a0b0f03090c0a0608010303170603191e08070c092304051c030203010f0b0421080705100b041a090712020f0f04 69
    0x1400701c02500d0f0000102c0c0801502180500160041c0114454644c4460b81c9041403010144509074007401198001c0482151381d0711000e034a0041c08002400500c081c0c0b4001001980b4034041d01e550007201c1c0c604c015903180941d4a6000c00642e40010014811482202d0381d0440c16121081c644004004581d650031041d4154a001411542d0108204140c4440303201070001d80c2d42c1c049032900f8000810303021602506451700e003a02d040a294104d28444c640184010001c5c8401ca40c020450399110303d102c22009500ca000000c21295454503030340c40d00c14291042e00c1084908039000350014080c0c0d04443c1c188000000c0109500d180344002c2c0c000903000f200400a194203244104040c0c6400e0101c68101030030842c88036505040d0071720151061805e8400c940178400c0300ca04035075486402c203040d5a1030040c9081e40c0d4014203510146103015074035050410314031b00401200c5004c2d4800060020107035490b0036108a82c41c94803810544e00d10b641c00c1042c1100e14070208000c0c11407100003c84940c5480c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 521747733 1250 521746483 521746543
    0xc0f0608040201110f07050907031d0309030f0604031202090a0506030a06030303050106022a060f0a05070314070b06040c120903090e0a02120a090602090d050c0406090c0c0b0604020c 80
    0x1c3c81011314015602c03002600d40d12003400300c0d900c0300380c83d016035480c1095901e1040441c0900b601101d5101d29504032216054510b0000c0b0040004e074000780c084070100288184010f623030380c4084502074005200408142200802c5400800c80c1040041440d101c41e0744400001d1aa98426a00300460f00c1eaa01400c0042680500420b0b0040419002504a012007000145a080c1c1c0024010b0102000d00c119042079685403410755802d5212455525110340780c0072409003e070307402150243c001c00e4003e40000e82111114048418071030b40800c0880c80e0b40c9401043c0006054250030050602605404c46009035a0910840c42c4480c081d6849148440c40c1c45c2420004007005001e0800443c010840e90790704400e0000c0440c0c000c0500c1c180022842c0a9040c0b1600a00801d4802c0782d104c00b2141460080c40000903240501017800c4400300021592403a0314005c84441594903000b103070401c0007100209040703844069000710090809858640010402400c051509195600b01c98540c606164149 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 521748983 1250 521747733 521747747
    0x30210170f0c0a080a14070207080c03030406050909100b19110c0a150c060507080108061812070c08010906020c12090a0e04020d051221010f050603040c0f0608040201 73
    0x24040400710205420310210b01001d9100f407800301c200b0300000d0380110321803c00315441014004d92049034140c1e5030500200082d164107046c0b0030114184903000d004141c910b004022a0f08880c0c090300d945240c030700003c05004441d0300051140200c402c40d94000a41220340200801c40e000c4680078001402074021406001c856011010101a50248051002545a0400b40c6007520341c0c107000d220f40e2882030641104c0d0849800740c002c001606150a00140c90f4105107207a050310482002d41d003540e41d41200348aa03500b0043d0800e026580005200e07401c1a05040040444034020100c48a10a8480361502c0c29208025030031141d403680016201d1507048148050350008928682170b03440d1294900000d0000c404900842520b44400c2c00491b0441da82c03c424001c0c0c959102c0251020303150080d40385456908040d40e54030541402c0e2060800d4140d01c040d440303040e6400c40800001050400b0f0500c1045d07007000304100c0380c40d0020b9002160300541991000f005000c10382d600c1d0000d02d8103100050084d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 521750233 1250 521748983 521748991
    0x20102040b040b0304410303090615060409060314070b0301120308071709010b010801080d2a050f0309041107020d021525020901060206071407080403021017 69
    0x5920501062000c0916081140e0445403d07258407070f20303500c4504141620340c0d03001e480300352251105181100c0c83c0b081080e068642000031001c040d681c07680d484074240c803488100d9580d0059000f8000181d449803e861002400075000f50030f680c101a2280800b908a5206400598940300382c9180c02032800c0b400c00031070303016040414a07141107501d0003104211b4140c20040040031f000001e8001848241301c1d58102c0380c0e141d981e000445c06401c200c1c10f0709000307100c1c00c516a030018451400214021400144000303500160340e80307080280102043d141c220b00c07485820032010700c501100d8900411020403c001e5540007410140d65210940002c00040342c072100c0520705568405d1100302d0140e503405110410b0180c045e1141c08861411100340031a51140c140e020100d48001584001d0703440d0346200500c0f41902c20b6841d02c00d940d07222841603913565411284100020300c1244080c0f04800190003418100e0700c2000b425003000c1d00e9500140b950440900482c1c0003c1d0b4490b500c440441c03040c21341a400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 521751483 1250 521750233 521750237
    0x18050709050307031104180b04030e0108061c0512040b0406021603030f03090614090307020103050606030906011e08010507111006031e0203030d05090f1e1005090c1e10 74
    0x406207040702207611100c20340b0016200d100030210303425464450740c00075080c1d2624640c404070400345a00c1c10041103801654160002107100c136440426501449295000f290020600f601c6d811083c1c040c80015841024125000e014108801926150b004003520140212002c0161a0b034241007009107402d0f6000030140e2401482c01080010940150501042030014500481c200ca180e0810a0140c408a03500c1400c42050408020850002101910155100343d905100640390103081003a240816111064942c205000400844041c84020310300c0030804240c0310659951101000d00316241125080085007a070014800844018040d1028003104948200551803e58851005c80e1007142c0c070040e2170310600c20800c1d00359075007001501c0790b00102e01d5040c440c52402491072500c0d44006400b2100340c0c400d40090f080038080081d07030001c10000c544001d0560500105404000d40405020b41816001d070346503080554590301295000105000d86560301c5115520611031006410700400003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 521752733 1250 521751483 521751497
    0xb070f02090c360a03031d04050108030f0c1905060403090b0c0c01050f0c010501090606090e011202100c06050405250602060103060e15010e01180b0f10020c0a180507 73
    0xc0245085000e00c602c0c02508240e9900f03c0c402c000918441c0a042001140d10500c0721000000305644134580c540003007201c2e0201a10301140600740001c0d5030b82809210341d030303030070511480c0b0424245c00c0c0a000040c0c450340c200c0b003002c01520f400305505036808405031030300e4010700100014181c021218100902064002c9890710118051403a200d4204810903410003000040412440c0708000c06d44414240c03c600801081d40e5411110005240c0c81c480d010125149103000aa215282c40825040f9105941c00b00e032042029400c2003660100000c4030818401104840070120b031aa00c1003908c01c601c02c030021308003541c0103030055800030040044200c0b1442001c0003840055800b01d01c290441764400d2021902c05001c81000e070504619480e00c0c440c0c010352200010309040381061940c12036203a48006011245200710009c155070303c5904c1c0d00e422401c0449090800d04022010701d01c0c440c00e61043d90044100c0000007031001840e580590442c01100e100003520220500c503d0b904007243d42810f00f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 521753983 1250 521752733 521752747
    0x30b0a14010605190e0609040e1e0313030b0717040609020915010c140102220311041b1808010c2606100f0201110406120f05071d0a0b070f02090c 64
    0x203150a031130a541010001c110310b145442e0381b641003d445105100400500911480340e1100f0750f9222070025036009500746201100034240040f0448603281c2001880036407503402c6403109004014050540400c2068000f5140348606042d8003190141e031058002180944803801002200030b00544190030540c0c0c0c0f400510760756030b04441ca0150096000f001c070f040715a20144568020f005415075024030300c003004460058155544200740c1641d1182c1d0b4458115040142804100c84854103440c20b90600000000086406405c4171560504a0054040c5990700c8810182c00e6429a40a1401140729040c0207221800c03410500c2c4d440314403081ca0f900300ca00d8448009017000c540400840148072540810a1a99200f900296616507d48540a03540c681c0d40000414500d16001c48412261629502018101c120b005060043c050756440c50801110010300c446e007884010641544802c855000040b003901c00e10140c54894028161602814030500600c94415002401207880180420101c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 521755233 1250 521753983 521754007
    0x70605180d1202101523040905010c081305031e28030608010207020306061c0605010305100614130b0303040e1e060d1515030b0f04030201060f03080414010207030b0a14010605 77
    0x1190845458541c006c4039001c4151455500d0a280128190040e00b040740700018010150811513160301c03daa41c7c43d030f490351802c0c01c5910322110320750010202e4208100040c604071008100701c41c5280d038604441d00d0040218103089203040100d002c2180100c1e6030b0705450489806204810083c0b007007800940c41e100265002130303190000280200e1003029580034640c243e21140412480066008208203e156141d08209654203c550900c22086040980100c0c000d010541c90a490020143c48419a05082c5210340007a184010039140c152205000c0000c524403541c000703501810000d05482558000310380c0c10040360800614a5000392008402c2c200052101001101400f0070500c000440c40e03030158403d448400c484c0c0c00900b94005904c01c0c421104201c40d44d0601691082c3c008001c03da59420344800c1000c0c8a00c006003ca00d003c3c8420040815000c10152600f5014030603103040d244c9950701e415400b1015130700701c603010780e842254501102e003802040380582500e04101d81003000caa015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 521756483 1250 521755233 521755271
    0xa0606090504020d0207080408152d040521030402040c051c0525120b1c0303020c10020301031a070216050d0201020703080a0e1809070605180d120210 66
    0x2402d0080350300040c2004816501e41c150345c80390f580b145510f80c0c1c85680d89412a0b0303460f04000c0050f01286c0103004201580c820481080407000d403110440c40c990103828400d00e084600403c01c2d5031030300590948022407085031b040c3c4840046003003905616800d00740103010443d00c0003038020080c8902041452031400700800c28490070300004901007041e55403003040e00900011403440503075524110400381d500341d802c2a001080c00710550020401c840040d0100b1404140d204616030708200000001c00200784a07400900d40401e545084034040d90106000740100e0740300343e0041c0c460089101c50f00c0c0c0411855588150440050302c0205a8150740120000700401c40d44106407268102d519060216402440103078011500050030640310a008000078081280800c1054802e602300d02449160321203060308103000c0c20801c0002d0000030b081400070303130340d80d40140121901d00341c80c109100d10660300e20345204000c910905891b007061100102c044c7c600886217000e0710401d0b0900b150380b4030320000491 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 521757733 1250 521756483 521756489
    0xa090507050a0e0f070201020906070b040b10030c06120605120706020d0305090715020a02190801061d0c09010c0c23091509150607050a1403070c05220e060109050a060609 75
    0x4940390345912400400e1f4028030a1000c0c854205902044100602c4110703010f0728815406064242d46039510400400b0b002107290200070a501100c0909000445c031031402112010049000001c1c03141c0c44100146404020400d80300317050380b000d8810b2000710360602c1651140c02c440c1c00d0074462810300e119030b82e40780d20585c0140020b8814078544180d50344e00c200408251990090104024114144408003c01200f07004480080d0300700400043d482c03000d20031114842541000300d6215880c0d0018509441e07004000d024104190003440a010030040003021004201300303140b06141c03201c00f40321010650000c001441c40368071100204060001c1d45a00c0b0301d034003402200c403050190395052400300b42d80392070358140303070400740101380700c0c0c01c0010000328501c025004500141c02c04441c0c4d0905903a92045010041118400078002c215030b01346040f40c41c82d01c03a000c0200c0c4540d0700e094100c007002c5904100301000c450740301d80010840d460345481240d030000340c214414000c503400d014029011400d144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 521758983 1250 521757733 521757751
    0xb090a08151e0f01181d0f0d021b1c08180a0e010e041502040807080a050106140121060306090b06091012080c0708011410050108040c23090a090507050a0e 68
    0x6245541e40310360b8401c009201464811042c06c01c00350013116544e141c203070380c00c00d96407190510b1a4030303940c0000b0301404940b09543c0314107241c4481405009244100c807100c074290100809a1100040b03085010300110301640e8401c0d065a4200030070401c2442d010381c0f0017091200c07a08010302020301c034031008907486504079008802001200320018020722540d0b202c40014050507a003c1081c88001c0f4005034110b010f08020300900c0d89a0b20442d00d5210078540d940c0c00f260050240d0080c0d0000460340c5860803c601d0170008000b44c0c0c0341c071106c007a2440700008803900c10186007080700600c0c0c003440007a00480255100c4184504000000500c1c5100800c00782a10b103020403001021482000f8040180550300c000707005456015440940200e0f080c3d0b00011054104200441d46502c80e0082d54483e640240304409554503000c5490140d040c2200600580209003080031103070384030880514020700c1e01103000035081c80c0d107041860a08085812070384c0700381285c030800c1005404081e01c007900850380c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 521760233 1250 521758983 521759009
    0xa151202040c27080f06060a3b04060c0801032307080d0c141204030204050a021e030a06060e03071403070305060709050112150b090a08151e0f01 64
    0x194001d880071150000384840380f12500d00541d02031921060300c00c0440d11008200e810401042d81e0540c0c4402040760426000410b080c0100400380070300e80402c0e500d0b0880c00001c0120000819214401e034000d44120703a059001ca0180820802a4881c8040101e440c4c5442840c40d4110355807024050f4802c0c0c610b540c4000c00104c0940d40301001e000704401403100c8001c4072640070308058050031981841205130741c8044551440380e1548408181018164481a8218501401d66007004000d1602030200d1b0415542446104142d50700050001461642225440d07140d1a002410700300340c0708281c000710b0402030300c282c00d80f5243e10300050345001d841c0c50004c00601000402c0c0407c0c0350900e00e41c4050201c0c440d804c01e20241a030081e02c1c8405940083c0d07544c055549822a5410568107500070024044403590000c01091403e14040c002080c001403618074074642c2c0d00360b0345d85416103003180441203028240c103111810a521b1002903d1441000d00d0f82994030700900490744046051103520381021305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 521761483 1250 521760233 521760251
    0x103020f0c07170106210b100e090c090112022b083906040b0603010216140615060403150207020d0b0402030c04110f07080d020a080a15120204 63
    0x118000740c03890510020100d6180a0f43e5800410003011144403801c060752a02c24045550b00441c405200b401541c4800c0820864440c0d90316401714800030300c074840a90408002245500d01d00080e0390040c40ea10008016114020041102050041c0e02c951610380d00c1080840040e110a0380d14200e151099200c0d03001c420640c0a03805441002150040070348000280d1408144500c45107455a40c0c5100000c0c1070210451030202d00e0901d1640c00003030a5404500080e002074200c00c1c41c0d41e80094050b0002d4144065030740c0001030743e8180401100c04103005a01d542540300100006980b0071342220305d451040c0c0a21001c41c07240c0c411804082c040c41070420044080030b2441c0c048a5010380c3c050501e100d151a1814489142c19080e9000c074800d0103407201244003031800340680b0b016500c40804540c541031484864000540c44404100d60581060200002c40d140d244081c01b0b035101542c4a0300400c0c030342807048004990204040302c07489240ea400c02c0c80450802c209401c091503060b10700280c03000c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 521762589 1106 521761483 521761507
    0x161805040818010c05030f040608090a0809060a0c150b0103050901050601080114010c020306010b030726270f07050102010c0306050f0d030c05150115030c0e010302 72
    0x20310220440303199403800c2c1c80140005040c45180d94a90b0740c1c699043d030f000300002c3e008000e00803c2c10017026800401c070075030001501014040c8030302d466072640d000d809a500e529009940100310918038034001c1d50b5851040d44c1103c03452180a09a034013800203800c04044241c0040d0800740030401e03071001401403a0058905031901d00c02a03003416251444549417021030340c10004104200005a182427005a001e082d9440d000303552031402c0035014015403104c10206420107040e00784001411415803110703030425103000410b0104640d03492801860691940b0b84000360180c04148040381c00005410b208440b400e0b0001d000101c001c50741603046480750301c41c054221010030307100702c181d00d441c1100031029882410441002007058a4a52804501c0d100600b4580c200e82c0c0188131400021042010401c0e440c541882298007c2000030040888102c2c403506054000c00e400040807 = true := by decide +kernel

theorem cover : BRFrame.Cov 521582733 521762589 := by
  have h0 := BRFrame.cov_init 521582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 521582733 ≤ n) (h2 : n < 521762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
