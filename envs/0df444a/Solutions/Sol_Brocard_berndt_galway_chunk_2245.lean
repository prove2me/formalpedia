-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2245
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:21.682982+00:00
-- url     : https://prove2.me/submissions/a2b36066-733d-437f-af75-f9d0d5f35a46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 403597122 ≤ n < 403776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 403598372 1250 403597122 403597151
    0x23161703102103050c100e070f140a09020c0307140d090b0a0e0f010519031406180406020307030b10020304050a0f08030307110f0d09091808070f0c0506030a 69
    0x80c10707008500001c602666128684455110080b03056505050007501c41c1101c1c9441840c0c1108100f104c0032090502c0a04160400081145c0702036031213801030b0fa0035a81c0c840c04c803d080c2012420101d90040d0200030b040000b082c2a034064540141c0c40d000340d070b19000468407086001c0600280200c1c45030443d480e42d0110a41028980f4014a00441d01c581025103003000608141e804200d140d01824064004280c10382c410700461b0030711002810a0080c0321500310004004140d60507040003850003010104441e868403607400740e2214801c172690021a070b182c1c0d07079031000781d00080c0446060540320b0740c0400507665079001c4424060f409074003c2d9199031a0800b0480f100810f0381c40317503102c011480700c00d100074000801200d5000b4840d08259110f080d580c000d1a1030300c40d41f80c0300d80d40a400384494001c40a03500c0103010045600c0712100784044401182c007600c6c01050803400034510321040111000103510b952503c0780e410301506500c2c8240380d4070360102c1d04c079030302c1100d4020650759110003481b10003c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 403599622 1250 403598372 403598401
    0x60c03180d030f0305060d150e0f071a0f0405030303090a06050a050f0c07020102120a0306061101020f03010303081003050307060e160503030f1803010e071523161703 73
    0x10300440703280c0d0840e42180c070042c1c031421042d00e203002016200c9000400e592250360800c2d10059011113400701724400c04079400d000348405241402e42d400740607a0390000c1580098544266074081105100c0440003d6403860141c0c05883e050480031418000040c06a40610103584201e2161000d09100710a0b46003207000c43d50001c210074030b4a850402407001c09425011502c0d03000b41881c00503607590703145e800142d10b80b41b65a0b4140340000000a400744c4070303e5154000d4001c4400c5070300c541c000382c55010041400d0380a1a8000c140b564005c0c401000401d220307070038894004e00c0300a01c0700d164580301d4950600b103520404050740c400c1c1c0c9424100d4140032080210310240400e10000c0341103142040c000948a10600404071368540011a4028011002c6404a04801c8008008010018003110383c3d5442d034150740b1078541451214401d00401d24040da00c4880300820980c280704030a499281040543d401110300015038801384012580001d081c4420a01080720075580340b40c07240f4049042e0031100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 403600872 1250 403599622 403599667
    0x19030201151a04050609040b04050126030705100b0105190906080c030708060103020a11060108071a040e160c150b09062409010c12050c060a0c05091e060c03 69
    0xe40c0d05070b0000741e840d856102034505075002299000d90326504c940004001c0c1000003082640507103020000200e8441411320703903020480350ba1004460701e0200420075100c1c00741c09c4000e8107a402103060307180e0040c901d900003c40c84505042c0b06003480081407906084110211501d00400c9880c04103006440e04020312640c0300f41c0700c0b1030042c51464100030007882c075080174203410306140e000302d24138001b6401a010002e2040d00d2004071805903940f01880c6d44e8400661080414025225040c3c41c0181c00d000c0444081c1d4541d454482242d4680020304143c2c00d21240009081204104014001450390040c400004000e00c401048a800640400440348400b40074548140c2054200e20b107403024502d184414101c00701d4030aa00c8114042c0181c881c0001e0303c40060404c0c0050072043d20164025018203504800501203508036900d0039110000c544400c0b00e0280800d0090000d00140c0c034200c80b4041012804020010380700700701201050b01d681020707071980401d030400b150a01580c00c210208a080c0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 403602122 1250 403600872 403600889
    0x3081305040b010e0d060617071701050f15150309030901200d111e0303040605150904150b06030709050420030606180d0c05011e140c1903020115 64
    0x540c03030b400207000380461813001806020440e0202085c00b80f41d50040b0000d10070b007801c200c100070031844003c2d1101040e0140b000103c01e442c6803500190014072070644500c035281d10030340090b250383e00610042c44070b1880d0720782d11140d0000304039010b0801902540c0141c81400040d034941d1080000503104003c02c00414a00400307a09c4001182a00026202d0580059040048a54807c80112814014660010803c03540081c103d03008031a4008015032046011710301c1045035484800e4940500d66600310a10b0f413002c4800081000305081d078808507c2f10280080008825504c07101081654004660a0020822080080083e800c0c180640e02e81c001c0c02907054548100e07014445031050001030300c804e01586000c03404000f44114a202203195910040c51034101508615180c144012203005203400034040d440701c800c5c118100c91860095079080d4407007010840c46000500b0b25900400f071100e11601c0b9003044106841415422000d50038000e0380080759100b0074640841c501110341e40300000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 403603372 1250 403602122 403602131
    0x100306031101080c030a090206091f110d020a120201021209070f0602010b0603010312120f02071e03080402040b0a0e0a0f0c14040b03060103062102030705011d04050c040e010308130504 81
    0x4400e41c4e260708580d0b00000902d00000c1c140c01600108001e0301851910782d170891460b891901c0009075a807e8030a040c1d20959840406c3c29010f0251512020341040d081d003d6400601303000001010070a80c075649c0040c5100050411500034960804800182c41541d4190440301c014440c0b1013140e0600c00207460240004d100d68040ca101217142c503c014030001c0e0400a182140e110210b204001441d0304001045081c0f21060000d26880008c2d071044a0468407081c60003400142000d841c01c56280c5160075441c0c00f030312a6210b13002d000c00b0708000b5117556881000c880d80820340d00340c08402d0b14001d40c00c042c1c0000c1c2109041c1c14102c1120006040c80c0103020259042290002d1080100e0f401d440503405603640366120b0350010f80180603aa042703c60420081414180d030666060b14401503030703000b00d04486140744e0f503400540d4035840480380c01181030303007002d403c007201e00301a003103d60007805d28642545459a182207005181c00c0070303041256002310000b5899482030002e070010f406010111000c21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 403604622 1250 403603372 403603381
    0x110a210504081b01090b0c0607030c0f08060f031c0c06060501020c03070b0c0c0904060f1419050402120a1209080c0a18060513021312170c0c10030603110108 69
    0x1d07903a56240d01800751010340004070583c2a48149802d4005000700000680ca54016580b019141c000803280507000030326220300c0b9105640b0034038005a4804041d10740c400c060300d600080c440e1b1403454500d5241c0510a008003054480c40b80d10905090b00c805a490b00d04054061031f2501c15100030354441411540844c2c024032440e03500ac0b079a60110703440102d00e55510910050307041c0c00c03c00007440090707120400f94100010b01805800804a12100310010400203559030110750440400340c0d01142060b0180c10001e0185403550301c01900140010f1600468100030700d0540d1604c83e140c1000c8604060040c1d0008000d0340042c0c2000c05054100041e0621002c8040030945100b0f00788501030281400c0b401e1803c1d280400e51005c000f41c9006071981003017989264011000c0d610015840e0310087c030500d000590907803a06002010780b0b038054814003e0b900e408540d0782541e045460484214050009240341ca42e543ea260944a21520340380403614500e58241a0980317001400068180b041540811 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 403605872 1250 403604622 403604639
    0x806030a0305030f130501050f010302011116050607050a080304111801050d080306010e0307150e04060510030c12020409091e0c0e15030105102d060807110a210504 72
    0xc91340704480c038204152556428080d4940000c0d10380025011754030305828054601c80d800599410789000fa00c440c20541d880e4494140e0300c5030117802041044403500c0b0140101e01d42400100b4041d8091012929000c54a480c0d81d0740710340c4262402c817241c0400302c3c001d840d14140f07102400003492001d403085060b036240001064030060041001003101c600040010f01ca0b80c003c01b120081d030100501250000c0b40c444010540880b103107140200444c2100c01c406e201454580208420384070040c01c0c403101c03004410019000b5085000600040c44000c40c03e04c807040744144040c000402e81103030085005d41c10740c1800560700000d611605141a80b0707081242c041040c0c1c42a0904450a00192101700d07a03650603445810070080744c0080d415401c0c00c040c008440c025000c260b0540b4040200000c40f200c0302400c0c20b10040b4192004054828102d10070007409000705540c641c481d80f24180410301c019169402070400301450400c4440c030f49440000540b0042c0c05000d4502c440c118244117242c00e0600c07948 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 403607122 1250 403605872 403605877
    0xf030d080601050f0d0504150f0c0e130227091e0402150d02070b010819020a06031130010f050f090a0207021008010e0c0a050901081f14010806030a0305 67
    0x4070380c140103001605100c00040c0070125205421006402c00c1141003504e01240548050200b01c10300609017212100411418072640101c0b01c141e031544031a03032480000740b200e41400d210884003019424810310351a101107085907203a803510300800801c111141030804c80b8200010b040e000b15030181c4204020505501075503203800035012105496594407800010030513109011030140f055002040140800160200b014107a800340c2003580c660410711025150780c47d01190000e0740c081d041510401280e8088d610a414080c64241441e10380b90306031401c0e80a01b10001c1c501f14291100e0120b41902c1d00071000b04074054010503000b5001e0310314100004051107900b0821501c1a083c0c1804140c100060b42d044072380d03040d400360903105004510f4201070101e00d070034401c0c00d6814040e80001516513104504413102c2240f075449190801d40300200450b200c0800800528000e450a44002c0b08041c003016050028200c4424505149018a0004110030710250969000b5405004040000703a007210a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 403608372 1250 403607122 403607131
    0x30705190b0f0c0414030c0a1e0e09031b07080a0b04030f111f02120408030702100c120b010e030f03030603070518010509040206070c030c14100f08060d1a060f030d08 73
    0x15000132101170b0300024100b07800c00703c2c45544030858070000140300c1220b4241c0d006007203030580718480007503441c540e1404280003111105ca0542003040240c0c034403010181701c0032003100d01c10100e50309542c50300d03826803810010388000d0350900c00f0311080004055200404051a40180c038241885608031920a6582c2440c0c104880404407800400000a000d0b41d0583c1ca00e131a51802c0c801140c00d00f41031010341680196400070050040c0d0084c4410400f403400380d056019807503038070440b03841f2080b940e400091445212050400400280d50516030b030781002001840c840c10006550b90f824040c1c101450040c0c5a440f40340695191401c084000e64105030050445034113031841c81541e0303224800601d2901c900e500045c20404105004811300c610001c2503401e13501d8400001c65114884800c00c0080c040c0351029a000816070005400c442f4401c11015401110207010802c01c69116a90300d4010000e0151030701000100c042007013400d142032800040c000343d00350050210080c5008004081040090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 403609622 1250 403608372 403608389
    0x50307060209100f08063319081902090103020714010501080c010c02010522050d0b0106030606091202010c150204030f0213050c0d0e0c040501150305090102090d02090405030705190b0f0c04 83
    0x85041c010a0352081c410150000c0004006c9200c00008241800070340048c145221502c07040c4030300180e0075004200d15802003041d00e01480340c11100001080c043e51014035207e0405070240710341300001c0c980300c80c021b0b914407000001140e00e604100b412454007180c00d112504000340048024050703604803088a0384401d49031410060780c0403d024241071004298441c0c0c1c0c000404220801c2408250cc50950507200c0030f0b9000e01c40d02d941c401741200c180303446006121110080152410056025030402402c2d2445505c2d0051714084110260b812038000f5070060b02d00c0803202410784c0452410045490155072104010480c5050031482d0f80424020181d2500403542d85902d0300c050340d00300304002c1040031b0006000344815a101d00030620391602c01800240440e0900b8086400c801d018002d8403800d480107040350144801a40030812409405003041daa03a00003003081c6004104203200030301802114800209840d01c2c94135004c01203031300c000c0c40e0f0b41d011800b81c000d0000098100c403c982c111501c03807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 403610872 1250 403609622 403609639
    0x715290d060603020607050307050f0304150c020f090108010c03050610350106210b060d0b010504030507060807020d0e01080103020906061c1e091208090a050307060209100f0806 78
    0x280380c8000103000b40d0b000a5402800440c03260308011000008080031441182565043d070210340036240c2c1d0307000f14025004500c45403580b0b41380140c032075040b0b0304850303000400b20f07201c20510f080400d00030107003a0445d8600340d4541e42004002c540601510747c000506983c48203d03807030b50250040c070b41c801e903c0c1490140c0090100107005200c00ba0111000c20090300c403100d0b500e59441c07002801c410032420500c0f00701d26105400070314140080c4948810a58043c0c00989001c3c01c100d0140002c020313190065040c85010712010000c52010002000900540c0d1508031140c00c100002a141210440c1c2c1c4d0010040b602c1218013482c0d9104041c01d04481d8151090320701c5c0c0c1c8492001035501c0c05640d540552040c808a04818030703400503044206405120018607883c0840c0a101c1c4054880c40100a040c40d000c2d6843e1805c1c052041065030b078454000d4043d40d0341d1711480e40d2142d0850707016440c00c0d241590045242c100e2440d100d100c600e13646c662400c0c0700301d803401003000291235403600a08061042c02d01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 403612122 1250 403610872 403610899
    0x1051f020a06110a140c07140a0305031b070e2a0912070510030c090e15030304090b090c04080a0605040c170303090f060f010920071529 60
    0x208070764140d4070761011041c0100d29030148207a10740c1d0400480c05000509909961030b01e07000308001c071303620b03102110003410b1040d00b0820180c03441c8201641294100001510001c040f035410b10241c1036807140c00550381d024483c4907482610341001c0d9002416004000c40510480700c51a541008902d04c1002c0a950903080d03001c5084400e01500701d01c66000f440882148a07541d002103980c01c10ba8508880340c1c1402d003180c01c2c0480844108110301e4001c0fa859210034403e081105100a41c4842da02500c0c810030223002011908681007540b1084d032241d116180c0b15218584040030551100000e519642002e140c002d0259480312416000b500d03181ea900e0214040c09104003488001d0a400401c0f0304035510402c0301c0d69030f6540202c5094960b4003d41c00c3c01c425410000c21024001e600f904818041c0d03909004003e4011b107429598004240703c4603019400c08107803000903000e49400303016250790085100a01c40e06076284ea56a24804030300240c03880240703245403000310900b0001608c108504950303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 403613372 1250 403612122 403612127
    0x80715050316120b0901080d080702010515120a0f080c010b0409110d0609050d0207080c0402032a19090302180919080d02041e120203030306010f0e0901081e030301051f 74
    0x51030700740c8a401c0144a000480c00560000b60402510941e41e04c120741e62b030716400308074201e840503241150040d040341980e43ca540703081d40c200710381c506000c4113840500465566070f912955240c041114503400c0440c02100c00b01080c451030403004015103060020a201c1e03074071100204620030308144260071058201040c004194040c0804070b81c044121000f00c91141e0010795611060b1007031505a1180e1101e50580d800d04c4e00034bc03801588016040482c1d005803505001020100103244001060203018655403400032502c0c04030180c0458480710401d0741980144114411000510000f00c10340601b406a0004005030a0030540c40201071910402014130300a140c038450300895202403400070402007107141e03443d00601e05003400c50159122480d42c40c11a4105028190b4002e94150018000580b541d4051410103d04120b2032422480080311400006c4000d00b02781c000e118144e0010040750300c00400790f64800c441d605070200841c02c42d032402000408000115a15160785d8890300d0070700c5010750 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 403614622 1250 403613372 403613381
    0x2160b1006120c200105060301060506070816050f100504030e060304031d0303120103050309190b0703030213090516271811030f10050a06050a08071808071505031612 73
    0x44c01d04070000c80c0184901c1a5001c1c0c0402d0322030380d21a500c0d22100007403030318045085035003c50340000f180d41409400c01008410201407003042e14680560134048101c27a006001b040300d0100905000203042c141801c0003040303c160300503101e00808041007840082074111000c0d442d0400e02c0c111005030311501901080c15406261030485154100030004020030201202070611080c0503110000103864610b28007180c480c00d40304041510030104000b0011034860340090401041e0b03440c00440c180e41c0c8840ca8411910300301c1d00c1c41d44843c4803110209003a9440030600c681100720b07a40c81751030180c005040ea04500300b148558051060303201d00b030086600141d0001e10642030040d40b129141e18082801c0c222000003140c240c00b540950110100d0a8580001c00300300352181c0d595a00e0074000340307007001e460105c0098251b40920140a42d010381c10124108590b000d001c1a0010300322040c5451400c0d0303c0310500e0308500e010700c0000c1c010001103141c1c0403160810703016149000001d044640200380002c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 403615872 1250 403614622 403614647
    0xf04022a1005010e220213021b010e0304120f0804051201051f08120c0106030b0709030302010608010632060301060e09090609030702010c030e0402070f0b090105061e0a050402160b1006120c 83
    0x203170300205a40f049c044650040c99202402d43c4000d010486111410a80703a1140c0d0081d1368140c0c2011242d000030840340c00c21b49058901c61203007145456160400102100705000c2c400085039150010040404174450800090701c5940b0b8100790400d06142d0100d0300c03800c6042d0b80d05c030280004580100c950000350801b80086401c044105154200001c0007001d0348068001a000f541c01c240d40021200700511400c021259180c812081524404491910440c074035503c1d40c2201e03608100407045a43c45500450003041380c0c1e03c401760354840007810b206031a44010f001c0c1c0c10540102d810400c1214001c012a029681e09103441ea9440d0b0700391a080d03a1100c4039043d00d68005d0310201c0e8043c200141c080c44c04408600482c01c41c50155200c0700440c1c2650801c0320000c0e088500e15800b1603403042c107404001c0c60124010302100304c0c9600e40e80030404a810503000322031551040c000c1d010500c10781c0c4000c2c0d034020040056400143d414940c4c06001c1c411882c0c120b00c192030751f65042505440c0b003003aa01d50707079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 403617122 1250 403615872 403615909
    0x60901030c021c0215100b0901081512060a1401080c0f030a061407080c0903071512050a0f0b03072d03020907020d0f030b0f04022a1005010e2202 64
    0xb811035140c02580c912040302c01110003514500030a6901c001b2200f800c00326000151410f00d44490500119861480581007100f49007510321802c04958684400701c01004003240105501c0c034014552409403100c031a8240c14070014500140301010004c034a900c00b411050301c04c18000303852500420320301f003810f43d4068070301c1e8038004a5090081803202035601a03041a55580311903102c0c00c0319050944548050b450385907001c02810050007104044800c3e09000791704166000c0000c0b03c00d0401030301c608541e24006d083d5607000306946429203101c0d85050349000c0d401485241d0501c075a11041e003040d440c2a0440144001005100e0b208134849407028540c05030400c1020304040c0c102035541c100310004040030a00e4070007020700c0b0b18801c2c869060070b1003000300401d5040031107209000c025408540305408030000110745078a400c6000480500741c814100040031051499480a0101e89040e00711000c444544401e10205c0703680380203130040c4010403c104402440c01880090203076600700051808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 403618372 1250 403617122 403617163
    0x215090109050a0801091b1410110f03030405120702060301030308060406050a240f091a12010b0a08070201020405061b1c020106080115032607330b060901030c02 71
    0x20b8109040d044001003038400c20b00030100c20b82007d21051003906500070b184541c6404150090680f80091042c40091103030304080340e2500180201d81e0a01041c0d89904525500c00018041000401c21040c4000115840c043c2c4c00c180e030030b0303000a80600c018480581080744400c0864166a82ea500840c02070000601e070062607540d4810a18000400c1000001d0302c10520040745556802210700804100d500c0d55440302a5080c5007074610340c6440c0c0e0344503490001c001d2044100c0000300b103441c1e50103081150000b54449015000003842620010305440440e40184401c01c0340380c1301c480c25509c145101c801800c07040b030480c1020520300342e4107102c0c144c0035451442d601148290194407040c29241200002d001c01c8902d004244e940003220320008144804811002e180032448101001006000c011428900500c98803012034500d22031801d81e99001ea010504000b00e032003c6803c0200f0071043c0e0080c000071003888005003440c0181741c881414542c07115030143c8064420303c0565000d140e103000c83c42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 403619622 1250 403618372 403618379
    0x6030506272d1b040f200c0d1e1d032a0f0f06070311030304030f110c010906050d020912060907061b0204090f05150a05010f030215090109050a 63
    0x140300058a0000918031204806500c501c250007068150404161403c00c06020501c1e074107000080010383d0541e040507503504094060041620750301d50a5070218480c0580b102c814102c07040c24101d83c4c50071401449610300c5001c00c46140ea28880320714044600f40130107a0450002c000f900c2d0508100c3c03055260150708a01c0b40c43c03020443c08901e40521210070400306000d07050a12000441112009074092a024003040c8103103000e1004151a0788a0b1030030b074103101c0310351200394035581041c0c81c2107002c0340b104912109084d5008210f55100340050004061018030382c40081e040014034001d01d0708104000501544941321501162940d0001400724491002581d84858030b81000359840030b100d028084000882901c5080c1d059984c1103944800c400350220b40d402c010040285400c200d0b42d4001880342100403c074107011240003c07500f0310403e141440d02d07113410022110141c001004448400000f44056110150310000418410030b019503224010300059030700f804507a0000d0740c800c0200d407011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 403620872 1250 403619622 403619653
    0x60e01090507091503061a09040302010902030c2b0c0506041d010b0301061d041b0c0507050102030c0a2409150c1d0402030403030906050108070501020c03010603050627 74
    0x291046000e5800d490340703070b5160b02d41c203c20383d50710842220010040b52010f001240080d8855a203100c0002014a100701d1040042414203604540550140c0d56880701a001c0d800e052244080055084031031190b450518600ea480100203055410003514100c0d00310300400c5210f203035040c050b01d402800700c4c1d25241d4070940c9444810013082c8181d1103100700000012002a258183ca040c0d60f006d0720344005000c40440010702c1c0c1180b174280307175901c140c581032810701050148103c1009400a503840610185841c02c016280c070101ea40014115802006001c00009012901c3c040e01ca5022600c003184003009034040240326540c064041030746103041200410020b614107000300a4030b103184280800100d01105444400400e00c0740070f0408500d00f0300c080d8074580f5500541d40544681030000342c0440e161030701d41c100d600980084038103a000603814090303036804100030b42790350344101c000307220301030866942c95152003001e045041c420104c0c41000c41004541e6401d00c0b11070110724211601140c0c6240e0b00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 403622122 1250 403620872 403620881
    0x60d0218043306020307080c01020405040f020408010b0901050913050109080a050304030909110906070302160305060105010207050d11012105160e121f060308120403020610080a021c060e01 83
    0x2c004105140c1c540c000030707800c10038108503410780d0081c50401e0302585806000c2d52003030800b03c4c00c0f03550801000c500d40d5210312640808440c101c000507221800c0019044c02c4031001004188207000c4240100301564840b4503480d48121110030707c0014014a291544c09026400c0d801000c42c0b101284d840c698940c04409584a580265505040d07aa03440c140b6400316818203016000200701040f00410506081e801040014484e03c12034800c40c500001d0700078503890355002203e950300840010085503a041107440049c040480308050143c80d595905c942d518a200c1d6000e0601008144900d004892002051080d01c0d0304c0c0020300c418507014924034480c0501d180c444010a404070700380000b604105800c0198820307110024030700205900c0b4022410030003400314002e0f154448601100144c40c5002405442440b181170142e141028a800780c104200103061900100e82140204981c090004105800c140c0540f00600558440c943c3d41e0341207030440a02800150400d01780d50307800b0304150300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 403623372 1250 403622122 403622171
    0xb15160501061d0f091510080102030a06090614091305010b150409140405060f0a0e030a17010909020d060b01050d051f080f100f02040f0e0f01080c060d021804 70
    0x5107080c40d42e54607981c9130048400e6074480c1842e031000d0036010114201c44021500704000c2014004815511440e20f801e81c3d1003201c90b0741c442516104208030b1401039001d01c0000c1c000352540e050540d409a00803440c188402404100c4048100078801c003400800e5100c0040c041c0c4c0541021784148840d41100e0091340a0311807240914508108001d2040c88285c0c0d55000d1079100014010700d031a41d4030b2500c3c140702c01421062440b942d8040301540c4d010100003c0001041e0f90300da044a601170490b8030364441c201640114025410b1076502c4006a980120824900303500075000590701c0c6c03180004076024052112181e2125280200b0b00c5002d0501c41c2070480008083c0c01c55a034429240d00103940c8900c0c1d03280c00d03104147d1000c022140380c0e010720b800840080081c06401402c0c20f030f4410b4400200c07003e980c00004a41c61f0841031210100c1801880c5000d41081e03401800f00c1905c0c0c4010a10364030804c806e94507890b6010803400080c0b015000900c0d0070070b80041041c40341c3c5001080f80c5200e0940500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 403624622 1250 403623372 403623419
    0x40504061d0705040e2a0a030606110d020309060304030c0807060605210607030e240108100902011713060e030a0f030605180615040e0601120b1516050106 68
    0x140050042c0d80301d64101d0702511140c44000c8200d454410700b9401c00e014402c0c2c10810141218a403d080300b0707916000d0550100d8a40d404200c076403801c20f0107400c1920503042c0103007a400c00c11440600f00c0d000402c51341c0d000ba041e18000e41e41e59a500301102e0441ca5104020959980069040c00340720403a00040141e030703011200e0750008014400042d90145514a1644264000a0000c1e0344035010742e21445481c10144151490742c28202200ea001071180c1105c4880d24500800500580e4000c21402c580100c00641c20005100703035400180600710071902018407961400005641c801c5191159042c41c0e90040c42401002201004d0688035000707220101e00141e111280c90b68103d119020758000c44101424541c840b40100e85807541c00c100041c600d540120f41c8008443c2100c00d0500108001d02001550100c282030280c0010900c0020b4940e0f000907508102029485176100c01350269010300c484c4401d561440d09052041d880008050003418551801c0c1d0300003208120300e4413586034081e020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 403625872 1250 403624622 403624679
    0x1e040e091006060201090f02100c05030319050105010f210b060706090b07050403020f0603060f2716080a150b07030207050f04050f040f031803030e031612030e040204050406 76
    0x3c44040382265000e036005000603d00d111044003506003072140409070742c405d140000302640552211032456109952500c030750000f091050b0b413207804034482c060240909203085c811040251030010025020b42c0c1308841d0103106061614000c180035072011105220250400e03440341c006003818001000c11003002c4c0c1c2d158407600300040060344110110b5040d207a000300142c155501000c1802103542006000642140c145c0083c2c100998038151409680c20a580800c450b00700b4145042442d0400a86041c454141c421100151103030403119403a4480340300300c030016a4a00910401502c40c07a41c1d40070385e054500c001943c2c81415800305a1406a550548030350f284000c00324107000c21141e00721111054502d003100401c000031404584d1403000c90092601d10007005615520401c18019580708401003403059500c2035450405002c01410901607080610602e0301d0418a4a6418032052000b403c00c40e2660a81e0103a95456050314003410300903000b00301c00f64a031070590301101c1704055a0300b1074090a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 403627122 1250 403625872 403625879
    0x9153902011b02030a1d0a12120318020f15030a15080a0305030402060703050d290415051002030403060e0f070b090a09050c0720130b061e040e091006 66
    0x40e1905030003000c0702c079402186007410034401202e1a2940090740103a804c0c08031044da106565119690f03000c0c0c4040201c400e00ba69062622480c0180034802e040107160409080c0701c04030505a901c0001c040e01901d640c00c22044540014140000f601c45041c0f0218020090002420303040d07110104032800514841e11007520340e102159204450040100005c008000040050510707201404056219041a07420856a040b104c03080e60b1090084404100448660744050a06c02845003c481000d8804101c0d401e803000c044000c1e24800e0103400d000c2d11414216021907032080080301c0080d60031000c10000d800b10500c075a511024040c4d0003004038451020f000c0381d55845442240c0d00d1030b00c0140b840c2d101a103084a0b0720080e000091840a8011007800f06001203008901307000440e0140150084410b0280f6041003642d0443c0800c00c141e403440c2c250070210540340d0b5011105044d10307607140a003000c9000c0b601c0c03038210300c82d13a002280c40e00d18001c103100e45c00400180300c15094010b444144040342e02c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 403628372 1250 403627122 403627151
    0x210a0c020712031404030c031506051801091d01020d0b0a0515120408040306180c0b0c0604060e0c1008060406141e030c040c05030f0108010915390201 66
    0x70340c0101c0c0c0e040c800900c014800280107000d060202c090700300899013003a03030721344030003542401c1940300381c82409680619600b01c10842c4504000b520040b280072143d00c0c1c11003440001f0350014000d42401541ea11144200100c1685203000720701c403590001d558980b0b00040640240900c0c1c6002e070300400c2c0400000c5050b2031b00c817441c0110071b0341ca5545517040c10a607400031101c07040054070035a0031040c00c0202001003071275030084070100349042c22440e40f840c1c028a8424084840c41d8003103801c90400303201e0648401c20109203550800d400540c00b00703401004111440c10001c5038010203600206082451103020b421060140c45032904483c200445a52121100740c0f05002d1008268010b2202100d00e06402c2c105441c83c408080150454503a0f59040e40850115182000400082003011040040070680800482d003d4440301c030003808071840b603503204104500e4005089600c591143c42040d00c4000c00c009000c841464103582050b0b030395805180780d001c00381600750700c00194240f5044144400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 403629622 1250 403628372 403628383
    0x50601050309031608040f140a05120a030305040212030301180e0604170703120c0903020a05120a0b0910060b070b0f0402010f110c0303040303030617060118090305210a0c02 76
    0x45100c2c01a51034a0a031a04442c03c60200328402c8640031018480170692060702030900024000751820112000407410410009500c45e038461480f4520040e601c108010f40403803005c03102e0b54541408220754440344009055080b82022803480761101000014441000b1054a6110090361108211140c00b2a40b4035031180c03412180540404600510b5001504408000b840c15502901d0051244c1d0b0342e0744614010344141c1c44890780011b01038503003030003540740464031107008040480c1d4101ca22140200d090b034884030b101d18054011122040018810b90051050484a4010784403c10945031503030b80c1400c464001d00c1054403901490800540f15090410301140144e40503140c06a003103440711421642094030b2405096540a00c42c00c441c101c2d141007010704003451007920042845420000007582e81528035810b0750855100e800100203407180304c00d44101d1a00301c12000704485101d424151528803032450941d6402d54a0080c0d266010300c1c4504041c01203100e07030801d00c2001c501010481e500d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 403630872 1250 403629622 403629631
    0x109090b040206070809090103060c090b03090c04020c07030503030c070c050f2d041406040c0512160c050d0801031106040b181c08071205030415090201020102090607060207060506010503 82
    0x2101280108016140007405403007403605c20081c80d880d001680c0c1c08034070030b0542a40110b40c016290410030643e6604100400080d0012610050551074482c465030347d60b002c000600f45c0280d07800110480380000034445a4080c2d41c20908070380d640d0a0002c80c050352584550401d451080320301030007182501e00581003000c40b000080c10100c00f50a0b075106c09150b203a0a80340b12003001c0452041c2004da803101d010350001030b2580d94507180d00c4c2c034000c170900003510a40e40f0480c0400804000401d001e0714010403040d00015618000604121803503001c5e9001015900c5c00342c40342c800e200811000365844041c80d0705891143c80c0444100d0403080130310007107010310300132000c684606000e0307103014959118078214500360050003520001218551000a80c141c618140c8001000043c400103004280000030801105450300d98030714a001d8440311109104414400e0101d511209168250780c402d40507103045c0e07500141003d5866030b03030303241c01c000075803004104075a59803c0c5000a1410344c001e1098a100c3d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 403632122 1250 403630872 403630883
    0xc020a0201031e09030e030115050d0809062104140d1205060a030602220501020a1104020a18060c0c050906150f04090c05030f10230406150215010909 66
    0x2441594015005443ea801c1c003001c42d0746200314903104503035541c051411182d0182d19409007500d4044145800e40d06079035a5924803441e002e80800c9652914420001010380100300d494841046000081d40340c80360f1554160303280c00040302c0c140100032004005000754805c3c0850810340307107610b401c191908541059100030034440740398980151031541009610010051408158946070f0359240101c1c6c0080740710380340c80718181c54044216504040060081e01007400200071a441d10394440405544151120780166008034603509901d00452980307500f000d459000448240d11030314011718545240340c003940c40881441c8005807038280040101d00605014207140580031a20b00f03401c40c546e206580600a90b01d04000004903c400d510070580700021940d50940e40703061042c17031507460000140c0344c40d90400c485002001740d9110300802440171110320300200c80c3d614042000400410481c0e00c85e44007081904d11580c400c582c0032036841445d40500b040482c1690300c507000f020480705200c500400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 403633372 1250 403632122 403632133
    0x405010e06130f0c020a0b180a121b15061703030403050a0c0c0b0720030c0103151d04060509060403090b1e0c06100b090a0905040c0b0a050a120c02 65
    0x380c2c00c10304006080c0c012482404101250140c078800200c0d01280102c0c2c005030000346a9000f0400b480390741c1a0031640086c140e03000700700c0e8111307500e1f1514851071006180841c40b048032110f403030040800c92301402e503061108401c085039041c01c0e4015003007085003d60092901401042007445480101d540700710110095040d80d896a805a0b055848002c0b0107090010403071600c00000c00380000400901104012039442d0a11403400e40c1080c036000e4031075590724480001180c5c45450000d40c00209440900c0c012819880304013590b0214065074012a205140241e28101000e00083d141401544964030400041d501c16901c25141e034421b8070001e001840d00704041150b03072003000252010b00d44d082c07a0445042014000c140055215003802d0300590401d00030080403040c01c0341d0070700041c01540c0501c1d150482007000256101c81c00c0c0290300302603a854001c602440304034404030001c1d00c507001c011039031340140c4200986540c04c486505800107000c0105220f80043c50300880110300f089400500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 403634622 1250 403633372 403633381
    0x30b15120c03180f031806040b09040504020f0a03082104120309170c15070905060f1803010e0a1b0609060e0f0a0f0612090b060d050c100e09060405010e 67
    0x202940080c1000750320f0360b0220000e4200500a1011000e901c01c3c1000441c1c0c0e5248a044401c2c0440035200c00034451403051008100d030941183c211000c692084400103005d030703501d1001038252170040b4001a082084000c2c08000c0005076001032504642c8001030700c2105e11868818100c0c9a0220f40040c01c2d00311a80300c81104a0183e0422644103200d00e94144640c00e180d1500c59503504085130805880e800740036130501c2681c51080f195008409842d18402e0103003414081505485144148201c4680000751620784140c3c0f41550b02c45644001c00a0020980c044045641d50050b2030040d58174007000131003040301003070403000d84044484545444c0c690a203440029100c16665010040e0484410701034000b20381e441450304030141000c501c2c1c041c015410180000c0c0903150b986410003a1600d03040e01c4070b000caa0100e42050740460100c600c0040c007003491030710034140140b052500b80c001c04a00441d5680715048802c031202c000064401031010750b00d1204100603904c01b03104041c030902118020a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 403635872 1250 403634622 403634641
    0x90c09020406140d0e0109230d0206160c05070920041d04060b10030f0b01020a0f08030603030d09051f1b0e061b010204092901030b040905030a030b1512 67
    0x1082c442e080070340300090131285e5a0081d801e580080c04212208040505024940d68100c05200000000e68004000f10a40b07024065500c4401605100c003445080c01044c42e450310540d032210042c0d50020680301d0155980041c0b0002e0034006858501010401c2030588452400e041660200c1d12004c22200384c412a00c21240b4049802500548050781c075011511440d40301c0940c004e00c00d002941c2c0004c1c2480403445100219041e04c0132950464011010541c0131a03103d1f04491041508400b081c1d0b507a1b2582400245140f0031012000040c45c2032144400a10401003002200c08945882c050040311b040c002c0e0904030703825101a58030700005a0501c010703c0c0e200303081003051048060480340c82e00f000c120005140700101141420700d0f03900018103001020082c010050303a0103040c03d641603806a951030070124500d05c445c442d4109603441c014451180e58a4002803000381c0c1010036640d5520403490020f000e8224005411302410100c204092a0449081100c0007401e01b040080b00ea9110750060303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 403637122 1250 403635872 403635877
    0x206070f03091a0711010b181605090307080f0c0103020a0c2d0f050c0108070206150105042103090e09030d0506030c0603071e02070608150102010e010f090c0902040614 74
    0x1038982c0040c070140c0601c0d51810008a9014808540380c0310790f0524188103c44c00e44009680140c001d10300000030030362100b640203223940c2003241e0480000030700700d280344200c2d00390061803880341d898416103070300050f0424040340c1c00c0c80954107002070b00c0c8158150001581a48110400c40d070000d201d5030104004a00605034214041060070404054140542c2c8078045843d0760325801c4c1c401c1d64020807048d0812900b0020201610b6003802d0400c0b8034640f80d18040e480e140d0042c08101c0030b03496a00c00106036845403003218003400e40358800d0401000020095145032400800072800318091110110799101c2c4020030303912412031a0011484d00100388490805400c0142c0103135018492688844459560400518070411450b035501d803059a05001e003142500b0034000500c20340d00402d03407c0c010540d22007910340d4000a030848801901d144000101e00401504040c4003080d403801100d004e070005940c20002030203001d8400c0012090311045070130304a2007a0300c29840482c440880100092441c07902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 403638372 1250 403637122 403637141
    0x8160e1f0305070914090601031a071b032a052802060408161202030d0804110d05030406030f020405061603110715030c0503040b07120e030c030a0f0206070f03 70
    0x51000c14265a655900e14180f00da130000300c1071035203c0841a2484d00e034001280c2d071064020000b01001c5d45551114001903080c1210310031031501c1d00c0f0028280c00d010321082c8118400115128817021000d050091003055411244030584030602c602c640310312412000d00c2d0074207400002030b050785820211900d0b004d80704a002d0030141200055240050b9580c0e00180004040ca0f4000e0090302d14801c2d811408100b0b1904410440201c403d030700d80150320001011030300104e850900d0b10071903c440c00c040c0354014a070340721140c2c40784036801d4000c108132000c00580308550054906200a176120307002c10050b40114000c2d19003009081c400582e0380d012411aa14146019080c00c40700c0c2c20000a00741e0030f003601d42d0844082c00e011030a480300c1c026414401c01401009504c1d0030303411401d2030b5440d07403521140600410100006c0d411401c01a40301c03a806a41c44403c0c1e0021281c1c1c8198040c0881c0d2650003091001d008541c0030341d041c48442d4004200b00307110304c0740390b0b03124801c802400348194000c100044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 403639622 1250 403638372 403638421
    0x114030c060307021f02130b1303080304060b0d140f0a0503031b040305190b0c040b09010e06130e040203061b0409050c04090504030309020a08010e07031713030c08160e 74
    0x110b9400d500c00949480c01d0000703505c050ba4031000f500da07200c2c0e011442d600034401e4903810010140a84045c100c10030681e07034000d50150303030b0b5141da00341900a0a143c044540d03001d604100000108801010f900041c0c0d85586c042e1990f100040c880d0548400446002174881c1d0410400220301070381280c00312002d24501d010460405032662640c034601100c1140c0a880182c5440d844001e1001ca00d015950060200380e107a40f8150034044141c181d40114008541440100803650341c03070750b8814040e03031001c5508070307448032559603a6404000d05080980341603000e402400b000c07820040e07000300d0010b80319100101003441e0074038020030440240001050f1a940303882c14480460300b400b10b40034107030060380a5540401c21524900400c1007400d810340c00a8540da02d0320100422103040401d81c042203d8200300c0610030300140000d00d070518811344c0c0c2496a2005540e40200030042025400707411784649a00322080e90108810000610000c0d00070f4000c2241400002a88510241c1183c0b641c400c401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 403640872 1250 403639622 403639633
    0x40216080d240e090304050d020f030106090f0c030506040b030a02190e0a0c0e0f2223090d0f080c1c1104090b01030908070b0c04081902090114030c06030702 69
    0x8200b400002c101c1e10404001c2074045010421144210142c02500403207020060761400d417400d00080c058940880d002401a03107040c401000b10f036401e60000d40145025541401007444407583c02004044000c0040b003c246400049015030070680315000c440304001e401032111900a40070003410010448002d9848a80b041000c80c2041c1000455401001503440110300035240103001b4288400000d5181c0c050301d12a9207c141d06d80da92000300899441814401058220211070040900b881112030600041c1000541a40b0346001620b20b01c2801003400f80c6d42010070031007046400108200000c0c0007d8101404103a5001000000b4003941d40c4203504a440e40100c0c4040405031070b00c440c0004840321021600704040e032094014031417001424641009041e50b40d41d5002454082d10002a0694500b500003907c4d040b4200222009088000101c0380743e460aa251903044401e41c200c104d0244240e07100000d5500d85400d0030744800340c1c004024140c2200b00b40d043c405983c1000b0a54021403142 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 403642122 1250 403640872 403640891
    0xa0216050d170d180c0b030405104808010f030b060d021008060a1e1503060305250b030621030d1503020306070206190b060403020402040b0d0b040216080d 68
    0x144514030210440c4c240030340390490b56003007281302070f00c01d54413a2120401c10010400098000b0600c0c2e021100c2e402e00028a89a80300e40756031703186010304c805422455034003142c41c0d90b030644c00d40002001e801003002040408680c06046070000000e114480248c03903480002c1c80010850540c40b5840034001d4080515030003d038000881c0700d1401c1c0006000701e00300c101030142030b04108016501038030301c1d41514401040b81c54151200c011140c450b07285c3d011a0740d041c4000780e51080e00710740003c603004000c1303884010350078203010b5a0396000845500c5188844030000303980d680030343c152882400001c01c05410611781e4440307400011070130052500313240010040c6448550041c4680c8140700310301c090841c0542d0440c0305040c80d004000c0c204406645c850300801c024480409015200168964004102c3c4085d00c1c001c03a9131401240c200952050000c00c010030145824009042007640c00041406194082001d001c00c9200c1d64542d40c202d0007903c01040b012403001c3d0000e00d0310080451001406109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 403643372 1250 403642122 403642147
    0x30212040b2715060303091207081902010e0609010e04110c010e0102120106051c051602011506080a0b0d0209090a03020d02010c0807141b030a0216050d17 68
    0x1021141120000440700a1201010741c4140d40007803959000d00c451000469249107980c1c8000091030500b440201c040003414644040c001d407184444043c1a40300105110400940c403202c4034041c29201e441604d610344889c0180400c85085150187c4544201c1182c03001803002584c00302c0800d0341840007001011074940c40314850f004aa5040001043d129895010180c0c00c0d200441100f1b0072680c010310460500d8000280070b06c0c1142e10508186950350001075169540d882d0154132840300d02c1c901000c21803000750065031001420381d00da000b00103034070040281c0161480c0c3c1d80a160001409800014041560303039100c0316840c00000c100c80740041c500d038005002c0040817148000340e80c000e00e00c1e89081503010000109500c0d01030000744034100d944c65008280c0d04008042710100203800e140200310241d06422038414000c00e4039200c0784e245084c04016625440702c2c400c0d0004cc0f1901c2e4450400c51040200c0364141d0364000c00c0080b880d0240d844d4500c40c2c00080103090000740f000c1203403803003040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 403644622 1250 403643372 403643407
    0x30619030507061205090705040b1306080105040b06010f020d080a11070c050103230604020a031b173d0807030b09060f061810050303040906090632010302 68
    0x1403168005080071820000014030707400d584811521300034201800d00c10b2541c000f181c03c800b0b8560507180000c1012080c00058180b022004a0f03101e00c915040e4045072070030341034004602c40c5000340f04000f40703916980011284100344045080040c0c02c04520304030781c5481400c103590000c60452001c44c405d0304080403d4600e074840d680031100c2d90a800c0f1708020320f5800d070180500800c2040428136905520407003404c60f58070020240c82c803656001814001039401b03030b840910448000e1064401e4002d16403400751541440e0b0700c40000e0907290303900140d000c200c168810b07010040000742c081d00d10b0795103400c03250002c0d120710a1511100c502d04004502d41a00f008580010360181b503084a2034241640c10705c1c1000d001408801c110707855070082000d5500c03003180445032200c020520050f642d460507120344c42180d803a040076500d0f0000040029681c90550041d000fa00c202c01000c000032961290100040d03d4503c04c0707096907940314440400e2184501c3c104010201c41030401510300300100d02400441c0d07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 403645872 1250 403644622 403644629
    0x605060a1502010e0c01030b01050301030308042301090b0c130612020c0312180105160c020301091e02040e010614090406020f0d020703030e06070525020607110909030a14030619 78
    0x43c0e640d4084d00165080400c440c4a0820083c20304104500000d40003e045200c140009000e02c000075001c2020811400e194221445443e8040d0307a400d003403503164034081d00700d0718000c1d5404c0480d40081681d502e17030740081f00c0001c4088480090020724110064415524040d445100c407a400d02880348400300920003040401031441d150704c0d2a00e481e2143e8001d40b042180d01003002ea00d8801000400c1550803482c80030780d000c0e41010301c0c0c44900d500c0040c1c0500107a000c01400303440da0070314000240d000c0314800385060348220740c180402c2140030110b90032160b941c450b20200b4482c0d04840301d0242031a5a503030360083e00614015140243e014140d02d03080d80b1060221700801d5000440a00f459811b21810f0b401c144503030043e04d114240b1a030300034458040d000500103a1400110858404800004010072a41e030140a0948070600e03400c00941c1500d121400303e001c0c0e5820301c000381c25104044129640e0303180c130391208155010900c5003d101c03074100402894021520400f081002141c280008005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 403647122 1250 403645872 403645877
    0xf0907120201120f061a0403030509060903190507050a0806100501051b0d021f1509180203011409070b0705030f091206040605090d020d14030604020405120307020f011b0605060a15 79
    0x24980f004024070740040c1c07100081c21b0001030000b480001d40c801c04441d0107200840c0e104c1d444801c040006400c00503d502e03c0c0c090703030b44142d5a0200f001004aa01c004945003141c0c01502e260f03880c5007450320f03410100e42000b03507008640410b114540c0200d002e031a0f22003590380164049611001d92602e00320301c8020b0580543d0110704442c006c602c24000075510100018020310400658880440920400b0b0180b9401c854560500034008180116103005081e0001e0090201c415106103008610b50140c50001441c019994041443c1d1429421070700c1550b40200250b29150552448081c503801002030690300c50b20018012403a040c2c2004020301881c09070f18000b0b034074140800317800d1a28605400e62001d6410111142c291960801c81c1a484880061a0641c3d00e580c1c0400040080c400c94121a40c0b010828490a50889000010300003081c400d542c058802c071101c200648440c001c0d0101c0c02d0b101d20340c0340c0709440054882d030465500140050030b2014195150f0801103840c100700302ca507100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 403648372 1250 403647122 403647131
    0x70806011509030f1713180c030608060703020c12030c031f06050702210102070f0308010e0f040f0c0302040f0c080606090a03080f130314060f0907120201120f 70
    0x11650054210990719124184418440e2841e65041c0100e02d10803070141c81c68000c21000c8042c280700c0000c58103040e5000a000302d02c0350319a034210262400e0941c900210b01d05d0003c0440880303000b480703124103440345d000052a0070381c1c80c641e04a01035845501c1e0050789015101106d501140048091401125445000b03030301d0303107030140e0088080c0c0c2100c0d90b40340004899442c1005007a80020480303105680540b031400c590341d07031005440300c500311081c1c03000d86030349c80040c2079001d000441c440207448510a644992183e43d031020034201c5c1032803e172400b80c070f1038602901090004900b54210034485104910314059184e1300c3d000136040b1401c101d20144695205c0104030f01040e807002c00264003000c01c8901d28248038014021a059044c80e020003404100b001914230390900d15101030320f800300c03005004106842d841b4541070081f03207110b00303040d001440f400000c1030000346801d0b14103104da40303071200800d80781e4a0f0580304156000381000903410300c001264800c0e50b5a545004c2c4119030b9500c40340104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 403649622 1250 403648372 403648379
    0x1e070b150f030c01090911070b010338060409060b100e030c010809060a0504020d0f03090f0b07210e1320031e07120c03050a0c030c120c05070507080601 67
    0x50307210700d58107640e07100c0c0d0000020181c1a85e0421282c07015296105030010343c184412440c00c1003481410000f03031404400b40c3c000020044009a00300c64047d001d02410194080c610000c110f442680d066007046610303450000b6406e003000d9000c4104203004d01c8011480781b02d59004a405c80c070b20980030f01c0c00103400400c00d01840c2801c00684002c2c6100703181501c902e1400c0b130030300c03a111030b00504080000380c0c071a00400c1c00d560b5241031880c80c032600190901d00c00040f926003e40803104621030504140102100010f02088442c2600c4500740c00c03c64206514504030021000008108140000c1c00081848241c50b511911406402e0b9482a20300080122a800e0040e01d808004280d003842d201e010000c00809603100e10017500c90941d0b4035030907a0251a83d0805440b0115404140b0703500300d15000110725807550540150340540300d180e000300302d030812031079080b000d4075007070907070503000c900010422444d41440390320100f060b040c2d91901030300b0080c0c20780d80c180c100000c690101c50b50394828001071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 403650872 1250 403649622 403649629
    0xe0708040203071a0d0209060c10020a030c0912030f050f0414120c0a0b0d0b22060503120f0c1212011404150608190509070303110f031e070b15 63
    0x8400b03008001036040900084d100300e040244102032040c0440368005c41c1d070b0800c54840e50251803143c05100c0940d484116111103c10080d040b0f07044010009003410048084d05014080c80d105560b001103105059a149032815a01c201d4110703070840401908005072080380c2c078040c01600203015051103010303481101d20104005d541300080141e4868201c154680103603965030310160100c0708525105500c4030051951880204160700c03510390040c00c00c0522030800c0d03152400310082c4000004040042075281c0701411350391071100804a8451804000f903425400c18480074099040da20021a40c001d444950f0a100d9034104440c00c14522800c0d1006019580d04603061012804081d14200900c07201e48005488007010f62081c0b030240590000840c0c0d540859600d000140c145401c002d019a00348a1801d80d030720191072100707034001070f04055426118107001c00c0714003003051400010742c102440302d0844520400c404920b1001d8070000c000c00ca000868040c2d0703040c400c41c107141c14200741000c5403090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 403652122 1250 403650872 403650883
    0x40210120c0e04110a09122a03020913050c0f0411041d07110a1707210306050105030f150109090c0e0915032d011a010e0306090a110a0e0708040203 65
    0x740201075003d0010f008040d41c1b255403201100c80d03881c0078204130110782c2041c100b035400c1841d0307174519020f144042c2003c006182d02d1510480b4400d80c1c10b03d150b5607135403c1005000c0060741d8003c3c8540c000b150309181600c0c4c030091005015000400006e121841100020352540c002d03400403800c29030007007014891100c00344155074000c03481d04202071a0707181800e4464035207599400090509000804a400d0101000c065070001a0300401020401520030107590440404a91150000e07081c180003007915441344007545e01924540c00004065128001c0340c86494109400a038108224a034000506410074095841710320540d407030742c0a112400e20207021007000001c191219001d0016101c80e40c0d40c8000030340550100344060314400c0b2030784c40102c02000c1081386003000110b43c28250315081c0080b140341c1c04005007000362148a91000300f082450b480e41c3c0c1c211500c40040d0498904040403901d070301c140e28018034004240c8400c084e100d90418400340e03015078078140000c1c0d09100300011820100070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 403653372 1250 403652122 403652141
    0x60f09010b01020610120809100306030203010c020d0503060f06070b0a14060a06020a030807051309020c1005040203030403030e0f042c06161805030105070503071b0209040210120c0e04 81
    0x84c00c81803030b10420041a041003442040150b0341325500850500031018151880c6400081c0002c080180061009015000a00080c0d200303510b04080340c0d0a8500000310040c414406459860656584808021204540180c01900640c08000820016082c920446e110300480302c000501c41003006003404510000900031409100d80319801e000058000802c0d01340960f0610380300c9c21715562000101d4171400740310840040100240c0d801300e4402c88503006448540164800c07030303c0c0203802e0425a801e54009880194058004010500c0464400c3c3c0e10280c12007405801d49140c1c004140211f011180c06030401c0c0f040c40034820800603000c0e000c9075000c4400d0380003402040039050601000400c4015240c4640501a0a88011803c03c1701e01c07030003400030040203008008502d460341002d0700c20f80c02203816100003151440c043c00b0b42e4004540d04002c00790050400800c1c0c2c1ea40340d00b404140144200090280510218040d2210b503040c010000781d2045075a90070b00d0011a1710500050310891030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 403654622 1250 403653372 403653377
    0x40309080d020601050105031801090506100303121a1302040333111b070e070806011e0f031a040e010209030c0405060d0f170406080105010e0105070c26060f09010b01 73
    0xf030041050f603a221059036003140743d150b0801c3d1446015840c1600600040e80020f215004402c100460701c81c040081c901121b0107502d0f0310381501f50240a11089800d034106444801a03441660b03129400c28060301c88038042201401450544c80ba16a00301c1d00745803000c1d6010307488080b070b191580080c100120040d0103680307507000d218410030ba440441c0a0301030f02700340050b8540800201240c000c410401d43d03000702900070340d2640714104200e00074803e03002201c03c2404582200d9061100c09150b00a0010300072a681d11640c410340c010500310050700044085541041403003046140654540c4038808100d2080000140e4940c0910149400c000031183c000e441146003004015840c0c85401440c0f060036841600c51040080501d01034280314200944000f410002140106001c6e400c065040d0507a070090302c03428000540072004407514418018003c1900e0030f111003c014804c4004401040002c07143d450461060954564503c0d140045460310222400d08040c032004c10400e03c2452110b01007803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 403655872 1250 403654622 403654633
    0xc0310080a1214071104020f1e040302010e010203120a1109031f1d06040807140601030f020906060f0a030903020f0f0304090b0402090303180a05090c03191b0c0804050306040309080d02 81
    0x1600e601420f20102c00c21503010340e800007007005c0500d0991040b544c101c405042d0a8074002043c400003100ae400c80d000c201d01050141818080c298000406e5814041c10504540710321759514134100060080c05010701c1e1804001d001401c40c035501801030070642e402800c80c00031190807000c0c00b281a50848810042d81d803c070f40840ea0184030300800d00b5640680c01c4007245035100c0043c03a103030400e1380c4a5080114a401210008004c001c00c0c1199000c0302802150464021b4851804008052044000c10000f008040280100313090080e0020703041d0500900684100001c28680141402c2c01c3c5890068541c000003001e0010303a00920a0b00031900040d90218200300311500460380c0d901c5001901e001b00d820030b0001300c03002c0c2c0d15415480040c1001604240360741c1440c10005003250030948864003849540040d0902484483c89800c8580d03001d035180e07a99029885c0c000b514074030143d00d000e880c0503604000101c2c00b91001c22200780640d2017550b810718043d107490b04007406c02c404003012a0854011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 403657122 1250 403655872 403655887
    0x305070203091c0b1e0a11071b0e0114030709151a040f030b090c011e110a060c0206011e080709020c0102070b0a020a09090b090c0310080a1214 63
    0x8240c03682c41d03038140c6410702400d03510300c0c407004540e44054009040356031640c10010660340c2c840c1401034161150740d0104003030301d60740d18050544082c081e220901d40c90038800302c4c0c08100c400481c002c007440c4403000c3c82481511b80580c030741617550907005961070800500d1280c10b2070600700015001404048400c0000007490440d99200030041d1061071800c0e01040c1c01c0300720b03145440d01198010502e00c00300c000001d5480c50a40700c8076100b101c0c0c028182c064100200c00550103501424160455110010030318201c0000640e940b4088895402c107620480c510f40300007074164491880b5281040c0c005142940c500005d000016065090f00903424510420422403401d0014031542511503116000d80c07542d2002c030400d40203004451000d031003c0b10910603c412142c06900410303498403107580d1120703c030b03803510201300a032401c4e0b6102c030b904111400d0009240c825108041c580101112403542140c5a8035101c0c03d2601e03038021000d45d0380781c00b898901806541c0000f425416031b1182142c09040024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 403658372 1250 403657122 403657127
    0x303040608180d0e0f0405131401021308161a03061c08070c030303061e03020d0303020c060705040510080601020a030309110a09090204150b0315030109080a02030a020c01030507 78
    0x15441040140604039002c1182490764a601c2c2000120850488010414502d001462440112085801420381c040c501c051400e0034004d6500c112080110200d120b0740d075503101003c0d8110301681e02c019550904c002c00c904032041c181a00101841350082110540f1084a180d03052440d0384244000307866402165032200ea01d0707040d071381e01801c2122284405801d404000880c043d800000505100740060003404001158a150b000c0e030703009171303000c101281e107034a0140620428540b5030003800c2c0c00c00108000500c2c001c8640380003c1d02c28a00503050842030f04843c2d14046041e42c201c0003064011406000f14181001c4c94880e01c4064500200d0750300701000040e403204010301001c3c0801d84c86030180c9042c0065500e41e4444000041c0080d00190750300d048400080c14440030403842507040003418148040880a840700391800544114516100c2c5154100000070181c4250780554841b100070002c1542c0b080984500c010700d80107190341c3c20304420004c1c1801c2e4a008080e06041c036090501044a6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 403659622 1250 403658372 403658377
    0x4050c0310031b091d010605060c07140402090402030f0702010b0f15031f0b070203010e010207020609271e0601030921030204090f060f0803030402010c060504060b090405070602070f03020303 84
    0x760411454000c03410305040c880240a02504884081380c10003660031089165035107001d0700b00003000007c00030341d5159401c11280744200c0320460482c0d0702240d424001c65244058000d0b50780130007400140380816000202e000e0380c000710741900d40c40c142241000780c1c2c42d4081c001c034100c190f8229150441c81c1c081c0f00015401d000641c82c600b000c40d102100040300c21032415641e03111810024188041c0ca580c843c036280f1240d0100d0000c83c02942008400c42c41d540c014000d440c0c00640c020002c9040509540030b1009581c03200e1401d08440f080344591a003528101c2031042c0c05504c0070f9603d0407940d00e48410080351081c0c003400c141c1c1011310300440c41d40880d00c05401c00c4044000d9205021a101c2690340440c007a0043d80c200e664642e1915020b4100f9040d154481070440d0b018904610080d5614880142c407400300301c501a0214035054580c81c00940d2561003203074000c2c030a6000040c0c21074403801182100c00120740447c1c26a02c01001407004940400c1a00001d1a04801007d080c90469010a40340e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 403660872 1250 403659622 403659629
    0x60105011b0b040f0602160506060a09020f0405040c090e040c06140304172d0c060115090b130e10030c0812071101030603080705010204090b0406081527030904050c0310 74
    0xa084608140200200303501120f10547c0303e0760185400071003509040740c030b4030300640d07070345105146981c00080e50303920500aa0b60400080032603e03042500d0207042c04041c1c15400d454404101146c40c0101d5503071aa01c2c0d00c2e901036401200000c600604244002d080e6680402a489100405004110000700e194048982000740f001c906d03034998200200081010f000100c0011107205140114070829107814040c0600e503480400305c0719180d80e1000b2510b51940340042550008542c494144130081401d401800f9401d481e45464078120b03940d50801c2e501210030703a401c01e0106142d44041013071003060480c1a002e0700601016044468124000060520070220000c1c42a40c007140700041c142e0181c4e00100086d5044580c941ea14800d034608107000354458020104d0040c5410407541c0035040a12a40080d12140001013000c008a4684078000313460040c80d0a101500050341c1302049c12a84c0707282c0d8003c501c010b0046468522103410401a10402040171401100900c1001030100c00080340c135007107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 403662122 1250 403660872 403660883
    0x1b01020a3c121805030a0b0609070306031716080d09020a150207030f060b09280c090e090c15070501051b090d14061003030f0c0b070e030a0f05060105011b0b04 70
    0x1601043c0c440700c42c2c0c00c90654415a45030081d082c044080c021110100d900c245000c0b01c00700440d95440c1429811183c05020242036070031040d0b140411940d80e84001c4c289a02ca010514502d071296507203075040d035880400403c1d005502c0c1c0711051300310704000360741901910a070340b1483c8203121a102c0007940c58049201c05811003a10706007105c00d1100d00d500802440c2c4010345014107900c6c204c8040e408024440c0c00e4138890b04081f4802c132050000b148500c00b852a183c3d40d501310b80510b030446161078014040d01d0031000f070194440c1c880042c1d441c0074016424054054085481d5403803801c0240c00c50f50002c12940c050744805940650020b441c00803a07010603000c64056841c03102c00e0408064504c0726419420180c8161401d211500060010380342c01c0384d1180c1e695080350b2903846000c0350b4002011100402e0246031401145c41c15001d03500450310500040c0c110340e4030002c66103400040d190402c50980340d980105006100a582c0100d03401d42a8900d40300d00c104c98260b03952059032036040100301514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 403663372 1250 403662122 403662137
    0xd091401030f02090405040c0f0801090305041401020c0904030e01090905010503060408071502160c0501031b05030a0e03070b180304081005070504030f05060a05010501020c031b01020a3c12 83
    0xc0b5809107506607030186402920401c05441c0500d0b12904060041c01000c014444c0c80d2000101c8410501440543c0d55055440d14141860540f2600700504085c0d03038103041d4001c3e8002074100b521440c80f403e100c1c5001e0b035500001c0795012000900090001e410005010741000014031490310005081c2e50000c1d0303c000c2032a50780d00c6170700700705801156541100b0344440c00050300c3d40304082c107540101d844034000c040204035107070344c2c40043d0216000c500c1402c10020190700c0c000701d1103009070080c59011003003000102d6142220340156003140c1c0a00021101001e400d010711003025119210300c800c03420050011031030b00f42000c00013952010310703059040b4000d85030350004140c80d10a10503034000359400b20070001d000380b91345401519040b003251f0388980710345041c000040320341c40000c1c00c000409010b400307811104007000c40030218510300c0c81c226055101d02140301e0006101c40c005d40a01c500c860049440303040554400044241c2e4038021201c00708081528407001c642018045d1005000c81d040c03809 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 403664622 1250 403663372 403663391
    0x307051509060f030702210315090604020c010e10060e010308070b07020c09090a110301020a0c02090405011d0a120903020a170f0f030723060c0703030f020a030e0d09140103 76
    0x3000340c8106011981103ca022081c440d0031a000208121000301203070340542c142c1000b0880c240070380030803a00d11004103440c041070900c90400030580d82e0481d0015102518284070f41900130309560234000310002e20b500c40501e61f01034024512a00c0c01030708451602a440354555169a401402000b1002e06500d20200104009a0080041031282030018083c0105441d05031100307500c501005100780c80300e1200c115180f0007841c040c8229101000c0c0c9490355240d45005409000814100420440e034030342d41c801081405a0742145e042c04034039451402860686114a030580c1c0601204803510700740040c48100b80010b035103014482007a03c14001c2041581919444070301d2a00703030024481001405003112802c14400c000c40100400e03409a60882030721841d821100f658440150401405900440086080d080302107006000180c0240b03408103004800c41c4c940d00c00c990200d9481c5001c80c0d510040a540b5110901000c0301050950400003605450a0034945146000400c4c240c101584c0d840c550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 403665872 1250 403664622 403664629
    0x8010315141006080915071112030c04030c06050f0313060902130e010606050f2d0d0b0a121a100e0f06030f0a080a0806010905060a03060e060307051509 67
    0x1100841d01d020030120382c2421a400d18410740a8064000042c10f0600002c0411500084210342d00400500701d103643c0d41d401604030346048050388a45068029030304000c00d0038600c103028602038280c0d0703100269203e286190804e45001036600050500400f44401c5001d14080030540c1d6002a01c280e10119090706032500350000c6c0050a0003e501002c50b184c04010039185034480002045400000c10565480340c2046c4c60300d024003280c0c2440800d007003040d4075100490207040030112510b41c4102c1c42140e180c6040d114a0b80010001440290380c0c0d80440103a8500508801c00030546918031582a52203030320703920000422229000c0da04080c110200d0709205003030804800a00340c3e42035240042c20044141402410142c0c2d0051081c07040290382202c266001c41c0741090194080455890300c014500c0039165103a005003400e040c400303060800200750b02d0b070000400a2540940d40000c500b81442c10009050030081c19044c02540b10401c28004d50321210f14a070440c40096480729151641d20001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 403667122 1250 403665872 403665881
    0xc1806090303031d0109050f072702070804150201020a1409010c0f14030703020102130e010e16050904110901021e100e0f0d020d02060c0a1202070501151d0a0c08010315 74
    0x70040740390b203015006c5050140c080351504503000160240c03044c0a9a0702c1180c0e1020302d0950a0908401700304480e0304980066034020400350344501005814507a4912000c1c41035003030121a07801503500069031884003a0f020102c900701c098203092640c01e0804c01c400003040900032000041c0305440501880090103041507602c00401072100469a803a05246802400307034210707000711010201c01100118104080307403981d070f05035413199104280d2950382844480e2103407181803400007408801c0011154540712400340c01c2c0f401806102c1540e90f056020002450000c1090881c54029030038241e0040200d0045034150340c0c0a4031203c046800140c609403281030900c2044007c402d4403c42c6100180340b6004110048109183d40a848084d501c01c0d002d1112440340d1140d0724002000c8100610b43c003001503020b003103410301030000003c403400c8a821006114215030800c018003001c2c900003034a0001c0e84450240c1c08140b60b082071107101000c04000d0301c560b4060000400c0070340b40340c00400030100325510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 403668372 1250 403667122 403667171
    0x80c1605010618090b0907080606060304140d0323010b0a0f0219050106030213093306080618010b090f0619030c05130207030c0b0901020c0601090c180609030303 71
    0x41e0303070840b1443c04400d80c0040980782c00488640004034001800b014012550a04444d0144041c28059495008202003988000d0044450700800119000035107030070003104c01c1d800348641700051001c80800404001c82c075149040e01c0c1010003c001071101d02c0c4480141c80795925282044480000800420390802e81c008440025402040307480a06002d415000441224001e440380180d8041404841c2d003501d40a901c09400d41e5610520a0600c00d0321000c0400c60814108a0141d00c0440f01c0c00c290582c0c0c1154049001984004103108000700c5101e450303a82d010841008002c80074115010410480004150040f0319115400103031854940c01c00d03400a01c1084546d841c0081d4903850810700006003801164021405407485131906030705407085a9410f80c0688644401d4441507684008040c0c00038181c5000d55000e000740503800000700102400391807109d40110b9410750036407000f454403401d2400c17500328a191100c1085000e4000501106a9030035141c00314403080701d1030701f42000300c20469 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 403669622 1250 403668372 403668389
    0x31321060f021c091106121b07021f1805180601020f030d0204080d080603030d0b190f14041103010b07080403080a0c0b090606030d03150306140403020d080c16050106 73
    0x3103016000141070b400581114805d44802c1501105070040c00300c41d008a0190203180705903c0701041151030607030451482a000c2d00300492902c00a0307404540388410503043d0291602c00401c0c44403200c0d4004103001d040864130788181405034588800070b0484545824002c05c008401d0700440e050703901c02d1000e0318030b154400048954032030b02220f4a80c001d5005120f00c40700c80c06041c0f203080b540d504c01c0854500030140200154101101c90580c01c00404030245030740e0740181481c0004800056000b00301006016140c40b003106e007850201c1030103078101c04804091040d4540451025030188400c2903906442880d200e1030b4440980c0c2c0f070712a100307118540000e4a407107004a15104039550010100c1c0741c41e480340d100b0650584440710055610711080d21120fa00d60800442010120b100364041909011040303021400d0350341c0d0751648011640c00703840002d0702040c10b80c1000141a01000302160505152610308024641051080c520b8003a01b16102800c0d4100799440d000d0003000d4012001030001c21 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 403670872 1250 403669622 403669657
    0xe0f0a0e010b040608130c03060513020411130e04020105030112080d1409010c020c090112210804021002070e01050d321504170c030c070305031321060f02 68
    0x2c112a15564100384581c50024a4810004035055100025008500c0d402204140c40d5400c541d03400001d014001d1024500301518468840075a90328061b6101c10f810954805681e42c1e140580300c2c0400e41c850300850328515001050000617681300d000c5a04584030804412400000d40c90469003e03c0f8904102504c203042201d1122913461111140e402030802800800006500b68800d170b80740e5480f010f059078021825001008a4854410558145c0e84180c05078210000c0d11884240483d00c825468070014070070808100c11400c0078200c207050400c02d40000c107083d038682380030b4041032101405401d020301d40f0900180d04101c4460950310003007030000000f070034004242c440c01e841004c007140108540d01c80c0002e0100c40050080c4158012030b0004c0f0000340b6048100815245507004224400d02c0b8442007215040010007801020061841a4065983c41d0000006098420b040f6000004c01e160340b1121034180354586a00825002d5000e1000b055a6442d861008000d000b110045441005207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 403672122 1250 403670872 403670879
    0x601110d05130e07020a06020c010b03150402040b06070c03060209041d0c130903050906090607120807030b060301080c01080601121802040c0504060c140a060903030207060b03010c0e0f0a0e01 84
    0x1c203000d449900d01c482c00464005035541a0000d581200340d4105000d07070424241c2c079010070740607001008002404400412242c070f00101092810088440c0940410506c41c02d000451520b800f0700070240710202c5d0303080d080005c80c0d1940c0030244800e00c0010401a030009214071903450300c0d00400100300321540966904001d00102944403072881224602c120068510740300003940718030404002a415565260502c8000c40910442e41c3c00075221641c41030b8284603440c006060340c0360441159402e41c1c1c8820950a200c88013805a80d2a5442640f10b00420300060090350740c00100000c04450911b001c00303064550700d0050700d525103082d05100a01d824591464541c00d44403c04400441c070035602040b564084034401c580764003583c003454000507284001c2c10045100c1845200d80903441406442030010681d41c3c020407181d44940441c0030075000320360f84060045600c1001d2a0310070641c0240306e01e5216280042644004108185c49034035103101003000e40d100c180941003c2c2000e41000c03201943c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 403673372 1250 403672122 403672127
    0x803040f050609010203520806030106050105090f01030b0616031707020a030c060f051005030d180618090e0a1506051c03030b090711010614090606030601110d 70
    0x441203825540d0703100340c0000c146442c40504c201da104210000b21848180328070340c41d244142c40e02c14651130701040f81101c060350aa03500038142c0c03004401780103489221134000401811030100141014443d0349001c0003048181d8000045686d42030301298402005809140141d004190f0f035408903401102c0400c5205401c046000c00b00400d40c000d03102d060302455107032070303034540248100da01200603000402e100c80040d02490182d206c7c10f03c94000403803071700000c100f21012210120b584607040400d41c40104854182405103a0041c052854010035132140a00d11150503d1076105034802c110508001100540e030031202c1201902d00c1e100c06010141240c507005596825925081e501000b4081041d492180707244164411100c0284c8440044000344581c08c0201140c071505405140d02d964a40c0052365612480500c03d50f0309841d00500055050015404c4428940041e1600302446003071104a69641c0d103000c1c2d1003142200d0301d0341e232503031050f004030b83e02040c52403640c51900c501c04640d8040c54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 403674622 1250 403673372 403673393
    0x1807060e040f1a04150312050306120a05070e0a0903080f060f03061906290a03060e0f010f09020a1d0d02030d0e04140106080a1d030708071502030c25080304 69
    0x802c00c85080c130040c0b00c0b45c1a840f140c0b0312240300040072458081c441401d0180a60050b65100310700404048080c0f0810702d000341030003114507080b80c3c0340e08084800d100e40d40044007015080100c2001c1081110402c1d0b6000d02001405403141c0184840200040c0c000e980d07103412505480030207820340b40b141c100708104c0c1c181900c5010501200c00d0514102084441c1541c10620b29501c0107001e02d0303050075460510380c059034089021082016105c00d800f086030b0003007004060180060301c03d12881585411441c8411800030340002c04000d00400c48110007551020703032020904000728141d080c20308400000b03043d100c0300f03050081d013500070b80a02d080441d410203007842c0e00f0385e0300b40c0f010710071140d24841034a402c01c02405682c0c007060004001c40c0910280b640410742200c5d064440c0d0001c9640c10100718555003258900305d40040300003416008001d41191007010307030040d0000541c1541002201d250884c0291101c500505c041050440010714807611351100c5182c00002e61039480c00c05083c801d5461 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 403675872 1250 403674622 403674671
    0xe06210c13140a15090221070503040b06041505061c110307020d45170c030703030503010e0721060503160b1602061b0c01081807060e040f 61
    0x22a8504005241c10006004c1e00010031103080c0b400480c2c50503d41310000035048115150000100f070680154540160450203005040d50b4603a50f480303150901e810801500b0042c0203500039801d14244c5074010080031040300a0b01c0045513080d8807200d81c042e0400b01c0e0720141c003214200c207041910310480c00c1b81680045008030900c7e8207890070510035030420f44031410101f02015049050f48080040c05080303800c480110355040084601410800b055264001c102d038200403503d50301517130164100760003001131f000350000940151103601d02c1c54602034440d020501c229040280054000750216101e0200030301c07003006421102c2c0603451055190001130140b0b00440c0e0292080c11402040d00f84401200001c43c3c4023000d11a142c10511544605680c42c2010101d811000034001080c540143c0710034002605d15400c010700c0c0710940301c0c00041c01c4910180c801e00c0c5140003002c3d074000858021a4081c241d51942c200540000d40241c081401813440b007601c3c416003032400c00e0244810034401c40740004ac = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 403677122 1250 403675872 403675901
    0x212070906091205120703050d060311040b0909120c03040f0308030105131a010302090d050312150109030b040201030c0c0516080f03090d020907020307020a03050c0a0e06210c13 78
    0x603e0300c81482c0e403c5644010009040307a403096044800720001c2d100140700f1b40d40301c0d192450074240240c5a02d400c1e9070003a0021144450701c1301505d016420144214502400126010242814040c41050b2600443c0345448002c2d58005400411440c041080b50001c20340c1c3d8505c0c9003d01d541c2d080c401e031281c10a000d2207205030901e030b041214072809401840d00c20003640000f0000c07499240c1c015402540708001003a000f10181c8010343c04544148082e02071150026140944d524207591100c02c1180040030550500c010140e062010480021255a100da4203003000103044980600c11345603420307220307402000c0348154920040103018a4902d40b0403103007000d00b00c542020104901070b849020b0110b00c2a0080c001c89100c030050300d889140150051114015a4901034840e0045802c1b01020b41041e1120751141d81071030070505040c2c911308010000805041954145280018444061400c2c060b0481501c240c1c020030008050114941c00b190040c00c3c070a84030303850a1034802505420592694 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 403678372 1250 403677122 403677137
    0x90a03050a031803030f1107090e01090212030a080f0a0f0509030a020c030c06120c09040e070f090204061704020301111801030e190803090c0d080c0d030e031c0212070906 75
    0x14400c468108101341c0c0d502d070310b402904130303031003541211100800201c0d040d0740d100700c080025110481e0b02c41c000c800c141071b00012a4407902d90051298a52020059800725841003200850603a840b00170160401456004900661200242d20024200040d04401710ba86020188503a14000100030006081e15400fa664030790400b208258840000c004403a8200104102210080a0301c808942d0301511400d94181020f0240011030205c9244010301011540301840510071107811600c40001442c1820047d403030300b800d03c00000c01e400d4200440901f02d0f022400440d0443d60207400c58030100034a14802d58640c5100f18a8140840700b040c51940420b2030304889011641c2c01180d0740380c402c5101c009840c0900c3c03003651032003080d1b84020451010f501400108091658076403001c0714142d40604c141540300d00c4007081e2070b4100040c2485002c02d140c03520007901c0c0c440b03401005903428140d034482840080c044600710031029111300c0903d242a00510010003110540001004003036272015034a225 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 403679622 1250 403678372 403678397
    0x706140705041e051e0103180302060f16020a02220507120605010203030412050c2103010e060904030c11030102090a120b1308030a38090c0f09060a05090a03050a03 72
    0x31a041010700940e44c10003401c960024003c061900c40e00354505e418035000075a44121200d0003071a154007842100160090b400340b00161605d0035400e904410250700041482404400182d5a80701d121002409444407402149401300661040d10015120a0060005291070400181000300f014115040c0c545400b002142e01e510010949105030b034011201c00070306500310003c1e5020303000301c00400c0c3c56104c1c0765059400381014501680c807913800b8205950f100d50412040302211540101501d02030340e00d44d010072002c258448a0003120680100031006402d10240110740644a1040800d8001d40f58181c00600c2d41010764454078154080c812903081c40e20b544101003041910b1600c0074041001c24004103942d02c0d070a601078550b40b41d01c180900f510981d25840c5481c45210303190701d0b0b050440010155882d0303080ca150481d40c4040c80c00002c62500c0c2d18846c0201c120701407108458000e100105180d0042801002100e100c400000d05c407503070700e640e28684503598051611003180094818003591 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 403680872 1250 403679622 403679669
    0x30314190c0906050f03180f011a090c0a031d1f0e010504200a030212030a17010803040915030204111809062b0209070c02010e060c07050105070614070504 68
    0x50003a20155604c2034542500c0c07100c500d5043c0c1004d09800c5655000b10070100000000b0442c0c1c0190018001c0081540d5000400c0a1602340c034402c01e450141d80000704001c1242403050071180d4071300d81400c0000d03107045031241c01d81480313170042405c2d065481040f1915042c2c484002d02d000b0400410310701800302c141242c44560030b0700c0c2c0940f8000c2c0944081c80088400c02219503400c00d42d5500540b1803404541d8a40000d0920000c4050480307072904005040554175620140486140300d410f4003104403940b4001615559205502c070315841260380b1030f1640703003010700d14440800841d001041801031041c1e0b200d000180d03922115006904400e0802440480e0510004b090701c43c0d0002803107041001700d1000c055552001c080c0000d040d000c81d0f924110016920010b81c54040d2001e0355980c280c00802c2e10000d000104000180c1c2d11070034090112a048110005007142038074400e1030441d03152003c40ca40003002e0540e007000845000310000c01c1002940d442005002103c00b51882c86181d801003540b0b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 403682122 1250 403680872 403680887
    0x5130801200a1806050c0c01020a0209061314010303110d0c050703111306080313090902060d0c02030c03030c0306040614030a0809010903050304170631030314190c 72
    0x70040c4007100d80c01110340c60440050711038018182040c0b40c4180d400303d00922044590740052000c100701140b030b800071800030000010440801c0c0001d001c500b50540014064440041050b441660301c0308910a0801c4560800e203480c41c952154100d5550310381c900a80240d907401c80050705445684000d840c3c1c1442040f0400600307130054043c001c8241192150345055000c01d0065401c00d50041d40c64240c0140f42c4541001040d0f43d002442c0c55480d034880040c40d816459004003c0343c2c0c107203c90031000d039640134102e9086004600c0001078110300c50700181e05500030a0340141150001000b0084080a0240210312911080702e0401c4400c0c3c50762010542920240c5141d078055229030b4510001646000003000602814105440d40e2544ca50305c0c0707031455025802894004080d80b648648244040249503049000a601190388011355102100f503a0a1800c04090000341a402082418006c1e03012003941603c061244415140450b0410307009451900758070b01d00d030700c0c0076106146680305080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 403683372 1250 403682122 403682141
    0x10b011106010f0e04111c02100203040e15210105060307050607030828020d060e150607030f0e120c210d08060f0a0f0905060f0609060d0b04060605130801 68
    0x40f0811041d04001d200440a500100216400c0c2c10602c03c600544d6a80c0341c0824806084101c0700c804940c00c0e10500810a000301c100900303650003031205100c00f010044140303520040320b200b81c4101c0d10800000500860141c0180c088416120140c0290481d041d04420b03c101d80550407620707080c0c2d0fa042802245d100b4414050300147d100c60110703114044400700d440b00c0140950074400045908008031040b039201842695103940d8030601041408481074446502081403644844101042d03000300324244140350004040200c18000c04103040d010708202c7c0e01680d009442d246442c203025003803a94603898410310701d01c21a184100c1c00360fa450310300000b0f0090050040500f0340301007003010542d19036101900d4183d018544141000c13240e143c99030880000c00601913411050341c6403060110131143e0140141d4007400c1c00b000c15115585071401100c0c02e101c001d8484680e1240c0100300f0740c1c0201800d2a980e54800e003000000504c6544c010043c0907070501d036094920b200c83d43d07907106500301d421020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 403684622 1250 403683372 403683389
    0x31f080a02012f240901050601020304120314120403031409030a0c0f051c090807081518060c0405180405070311010c0b010f060306060507030e092205010b01110601 72
    0x1401d0314a00301c0e05500200c0355900400e5445900d900402890f800c0c905407424680d0000401410000707113052084100d5013240c0c20f80020451400d00b800000d46034441d0740214007036201c0318000c81041502c42c10286802c041c19013021780e183d921070141c0200103c0300383e030b090380001d0400d008468a040f5001000c1d0050604c00002c518010301c4c0482614801c0c3d401e401030764a1549103c0801c0421418812007503012900c01d221164591800005003101209810509082e8040720050080460000e0050034003180c450030340c440c0d56194a0300912a1030490522a6280236007811f0001c52011030b409402650012203080c104030a80b08404a0304600454004d082544101020400b00304400d201100c642e8041c0340001c480c4245803142030340fa0000303034446c1101e8154030300100059985845508041d100d6032401d5032078949991002021b0100f03541c121441064004007081028008942d20ad686030072000043c1c0c4448864184140240440703031001717020460328022940d1800d4041a002d050381c0006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 403685872 1250 403684622 403684637
    0x20703350f0a02040b070c030203010c08010f062f15130506010b03091204080d02070501030204080c0111010608010c020102131d040b0901020706050108160608071b060f02031f080a0201 81
    0x6000e01501c0581002c0c0e100780d0070800850b60f40d80082c01805158011300f41c00491514600c1850700715411180c0000c01c100100c0700500280389420740b10320450f541482c0c020310b052a4840a41813500064001c0c40c0c028656180107280440c01186e1240d408054070b0940c1199031300e401c0c82c106a03503c25400102079401c00030040c440318a220000e9174010b0080412544810090303100d100b425071098201c0d0010342e0040b02d0501c80c2d164100840c4000e081c080c40c0540c289031510501e03542d11680c5204490611a02d07101340203040009600140051052000a00100c00c0c0090f01074000c0d8030007500c030130307030b0034021751703003c00c6103100343ca0182c0d8004550b203542c6c41141d59075102c6648159000c1d01c004000d540070407081c808900c1c20b0040501034002ca0000c0c04000040f00c450504188840d403082007071081034000c000681c1e81001c41908030032041541c181c0c10440c0f81c41e220001303160703442d40c1c1300c03d440c80803041c0000c4407070041c0040300c26444084103810254503410310640e85c0f600010000d0012300034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 403687122 1250 403685872 403685881
    0x60501050d0e150f091009021c02150a03020a021e1510050901090605130507020c06090301060321120608100e010b0301060303081509040c0b0a110102070335 69
    0x1ea07482100a20384500640c1c03920114078140b0001000e094030300300103810b003420900809400a005049803118055410080c1c0a41a4082907920840320f081042c00e40c00300700007005546809414080b001d4046040070f42d41c1418071000b4000f0f401007500f02c001442190041c003005400340003030748007c108002c0200301001c009900a4502800200726103804140840d000815494041680e8042d0040301e0b1f0216038203040106101d0801820b90740031441c64201014041d079030350085080da104e907400307844003030f92030b043c1c05d0100e80501950360005050561032808041881c100c01d08000c0c80d6101651440d8800c142e074007902080c1c0e005801030b40c039076802294008020102d02c1d4081050f12003200004603400640b200045d00f1203017103910550104440320100312181c041107441110a800494040707519041546441031100e405008086010a00007684110203000354004184024810003d55582d0310a18000740514404034580c3e50312040710741c65040901d5800316582c1201001d00a00b9480d40d90f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 403688372 1250 403687122 403687147
    0xb060c070e0606130608012c07080a0b030f061614030c09011e021b06040303090513020c0d0c0204050a0606081315090b01050f1c0f0302160e040b070306050105 70
    0xc1c054030a0f81e00c800104922041c005440c0f25481c014140d0b500d64013800c2d8505801d4480b101082000e4018103591042e86803400402040303003642290583c5410203035903540c2c079900d500505190310f10725403511550f4100c51922000240f43c510440e050f20315915a11912807059486010480159446000034000127885c111034002409600c20140340a0103081c103400070010059060504540050300000300030540c0d400b1058681d03507020410b4031072a15003407458400814803481809906d00c5036007140402c0c40340380d004d0707019501b511844405070b40c0c181410480150901300d10450880c002d908040000303a000c082449a0012900305456506490b0b542101c80100103600103402c0b190310a000c10b150a01103101d110762040326104043c2c0c0e180c254180760030890720000400e2910300c00d06044060070805d85001c4003484030340390302105003460080c06250981c10050b44d1440c405103207407003060000d034202d082c001e0f60340124010b045c07215050b2100701045055810501403280410400c12111a1607035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 403689622 1250 403688372 403688399
    0x901091109040606020d0810060c0303050a0605030715080901090b0c130f080a02030114060d030813060218040c03063f03020106031b0f0e070c12020f010b060c07 71
    0x10000d2003018645140d200000302269240c1d0810340060b03101c4039a0f8024240c00c01c40d84e50300200710b4190640d61a00e80309004001070034201009040645401c040740402c40b00e50001805044001d00b542d0000761115410850040c81000100c001448d0b41d0201d03076210018460139500c103800ca036a0f080c6507600c0c010382010310b5003c403d4007030900c4054a4006182401d0448482c042c1c9801d1028181104075070040500355402c100302001c00512900c00d10541e66501d120090420340d240c24210801e503200b4a400103c0001e039400600000e000003041c1c086601e10307843c103040c0002c0407901040440040201182100c846001c1c89426610704002c402c01800d4080754020829801d41805100c0d0550112080c0c0c410b14099048015070346406040c01001185010b10160550981400d41e00615040d4610080b0b20148100741c0b03c03c00e00b0b0003240d6642c0c03040c114803181d20382000c2d00c0d002d0410a1840250f0722106e22403141030b2540f820201c402189404007c4803203076a1040300424205040c1a40c0700040c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 403690872 1250 403689622 403689641
    0x240c090d05030c0114090f1b01030903120504080723070e10080109050d02061803040902090a122303070b060603070207030b010f0e06060f0d050907050618120309090109 74
    0x10b00c4140401d2030b50718000d025010141e800c04d4030044a904151940e10715021301c201c1c04020940029000705030303040ca41200040e06000919002c10420300c04d00701580c10010408070086000e007850100700071301c0011002030406c40e124850b4000c0401a0759507150224a03030210509040e00046010055420801c0c0c01540203142d101c841000b407580d404040b42140d0040104880c0e50f00103000c0d041510b1340500070705903c8441d041c800c20455002200300da880344a5806a014101c4d40403d452100d6202c09500360090301000d00c0c451101d41540c1005040d4400c54464680c00354003071010141d2210b0040251a10b8030ba1000c0080070544a4804020894000400c8001103100750075000000c1003529201c20b0080c0a403118403005141401c038001d01003213000300b21a0180703604101c0140000540310071105010416000010142c8900001d1402e0a00c2ca0340038580c008c0004c21251800e5094100c00c3c40002c0d400c0344c0140c100b02803040b41503120b0051121690740300260800421010304140c01c10303d105c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 403692122 1250 403690872 403690883
    0x200f0a081e041b082a04060510110709050f240102120c120a180608070c020424080706110d170a0204080105070504050907141e041205240c090d 63
    0xc113138490b9503007403608851048062400700c0725214500407170402050350117460000d440510a20b8240008103545a41081c407403000c0017100d00000318001800d00c4110098480000c003840b890070109811380d070701c800544100c1d0042050380c5080354101e0081c508882c4d85401a0054a558440740c2c01038070190300f000b040c4100314024a0528040e0200d840300800e171a41090315542c0c2d9070401314082c0c40c040b0f10581c0103c424491a0000d110000343c00c8110020020343c1203c02251103101d03024001c1100ca02420031018030080d816000c1801d02c008148882034444550380d40501044501c2a82c0c0c1c1c03007001035200f1011415002d14401d1145d400d07041a0b5210f44004e1000d45050f036615074090858408950500005402107800c0c80b0501d030040200e40c0110003803034164582e03c054402c5101c1c510030600300000c891035501c1c40410301041c0505480060405800741000c50316a400e190341c071a0b090109a04060401804c2c24508002c6a01d0340740c05100c6141c0041d060a81100522011a62251040e2903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 403693372 1250 403692122 403692173
    0x11030a051e0f0303090703031416020906010203190e0415050f0f0a0317070c0905040b070503071107240810180b060309010902090a020f0904200f0a081e04 68
    0x40c21000c100540c01003c01701c00600300c00340b40d802c0042501c9402c85180300c8003a400c00c8036a401202c2c42c001c4403c00790f0102e60724101e80e00d941c1c0060b403540c07061300d0104000c4002e42000c810301a402140c1106082001c0d81c051140701040d12101d103120301c0e14050a035110080b03045040b40c500304019144801ea901806c0b0f006559103d03151000c00e0303150032a0300204c078080010301101300010041074a006000d03d004c02c0c17040d03080c290b03161011404010041d070200400400001d0290344074140629202003283e00303403002d1584400030700c014100039107401d180558448604408030740c883d40038944245855810000411300b0400000c400100380b5101c03030b881e07507281c102120041d1b88041c0110b000d0b400100002414034004e1040c008443d00007040c12003960b00c1070200d1540c903801740d0100c50082000300c600180a9219640e001c0450b08110b10f0400340104c003041c041040081c20000382a902d21588400f03059030344086550001410242a0f044a058544041400903031051907420344444165007680 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 403694622 1250 403693372 403693393
    0x8160c05150a060b0a0e13020904060902030a05061813030e1003020a0801140d0f05010204030605040302030a091401120e07030503160204050f0f060d050a06050a0911030a051e 77
    0x280340a01d21003540038841c50000a01014520500c50040102400c041d120b0505d210040003524000c5540e00b000e001e40e5441c080212071002a038116800391400038010802c1d152a20180300094004491100419282c0004104189041c824031480c40c401402d0205256642c100343c61400e04002d88100c2c28040340342540c6040340d50b03807655581000e103030f035030b00585500028000a105c04070681c4101481c1d008400d81c64010745030b521040b0351140d042148a003020045262250081c8a01e07800544400d1034a0709110070035038040000c11800420b0703583c448401d5151140c9181c5400310101032400303d464501584240b42581e00300c030785181345c9401540c4009a40b51a25819039100c4030032000d40d8440c00700480e0840c80c0601c1807a82060400502101d5071400d030818402c40d280141c09903220b0100001c0b8001045400c0003c108155441350050080e810b00d40501c1c4080d1081c000100c805141008600c02c4074100041c00550440d00310004210b1303200d590b042c003040d0008503501e11007680104468034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 403695872 1250 403694622 403694633
    0x10170f0402210613020105121e0c0a0c02040504030e0a060201020a110703020d021c06060b07060609360b010f0609050a0806010b130509040b06010318020108160c 71
    0x124821024511111040d14151040007101400e1903050303809a46a071201210200c0700041241c1e0015080c2405001c100d054001a20140608900d15422030302c18003c1100100c0320560106060101d080c500c68113031256407241155028504441c2c00040340c00b000d1902620342a0030040e00302f8001d00b0142e441c014a42d001c508200b46c070341c10020150b9000185e5030b05e2680c2c840304040308966208050809541145e00107012400a03000191090f00d2078107070046d0311200800241d03031306a071244c0d0400c2103613681c00c0c02503038540010f48181c880718500100004c042043e0f006041c810f10301c0c1d801415101004210400080200c9081480000905505072000032001031010b800f9085111403402a186040d0b4018072500403504228012180108100824800084c0542c1034030302c5c0c0c91503240c171040c1c4680d07050411044c5d44e004551124a110a1100740540003408a005107001e136000d1110540342c40c00d501301da118500c0004d0001d035030880001d06c2c0786510007801e02c1c030a86034581129030b580d03180ca84 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 403697122 1250 403695872 403695917
    0x4020d021c1b0308070b070314090c01090b04241112070204110a12050a0b10080405010f05010f0b070212070e15030a120c1110020106180e0a0210 64
    0x52421180360940000c1c00e00881c9000b4140100c02200c88141250a42c1e46a046600070588020550134680007c185558081e401c4002104503008104a15240190711255151944849540403c8054030081030300c0b84148202d60075a0005843c0b0004d600b03032070031401084803140d103009040004031400020f540100b072101060340d03442c17000b4882d100c0d0211300400086641c000b04440e5515810490341098680048205800e03104002e40000d031584e404942102801e141c0700c000e0f9220700c4c00c1280d854099005a6100d000303502603402008603420703120300c501c110b0780700303004284040c0e00c03a0b1800c00144025030014506507202401410391050398038442460003116410031301c12083c140c410408255404c1c40c0d4500082400c070001c101d0005103459120000c130305a50307041e041003650f0051501b0312018020018103540083d2103600c8403012101d000b4000c2481d8020741c0000001d032078001c00040703400e004003222051440003804110745583c0c208051001513a090303e0500c041d00a80d5010548000700c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 403698372 1250 403697122 403697149
    0xb04050c040305061510050a03091e0b0708060a050409020f0901080604030206150108070309020d0506040302030432040b15041404112b060e01080c01090b0304110904020d02 76
    0x40107512a4150f20f449401c01034010321910704203d0545c04040380e582c0e4500091900e030600c0c18815074821f0035581c2140604a00b280c0a0700d4030428400c8030410b40c0f00c0b0f51000b41c46d1070040c0d003c01c0c802d480e2070604441c0d0700d0082d54903a52001c0001000d100c1e070300e401d0f40701400d0307188020400a8820302c000042040c2e000268494502c40d0070500400080c950180714081e8031040641c00c0100c3d0382802c40010700030000151669042658a801100c1113441e1192004030325900030040700c009191501d0000e41d05da10502807040030280c421f5041110840001440400d400041c03042c0300c00c1b003805400e000c02040d0040f401a48640c403424003015882d241c03c01000501800c00c1389410400c608020302081d10303541001c501c0741310380400186200c1c1a00100c0841d450001206007074031204690b08020282c60a07400981e80c1021351800007851150000700c1580b03001302030300c030144c1003943c1d0002c0400340c3c041228050810321800c00307404d91529180583c90b5000b4801051000c2540340d640108400c80c03450907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 403699622 1250 403698372 403698391
    0x5010308070501110f0d0533100207051e030a15020301051005030105060a0f11010f0509160303020d050a140423150708090a120c03300c0302010b0405 66
    0x80c807002800800c0c090f00c1c083c596840441407a0414a0f02d80340c4641c410034240102c0c007680d902c041000d0703019108540982000300f40074008a100c02006504510058464813442400b20048092002d40007091070f0007201c000401103200040e403070a68500c0e4104000c0d0480c1e06004050402c0001103500034103c00070041c40c44016146d41c10181801040b20b10510f004c420b0100c144010003481d5034000c103c84a01c681440c1903452010745400c01e0b11384040b00800b4010f42c3d400c1c0701194002000c1a40b00d507101d8003d050485191160074400ea840182640c04080c0c016003001c5120b200e80d0b402140144101c00207840c16142018980411001e2038121340c106148510016089000c02100e0740042c0300b151104a030750008001217440d240c0604e1162080050060001041040b1a41d0790000740c3c20050038250200105c440ca50f1400301400092400100d84860455404a103400203031251443d8914201e03441c0c442c0814124002d84411a840208504640d00c4500320910b40c0c0f16401014003803040c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 403700872 1250 403699622 403699627
    0x3040506042d1407030b0a0906140915280608010b03070e0610051201080d020f0a030e06090d0c0806161b0303090f0614150118030204150905010308 65
    0x34501000006058008400080d40b181c10010001c8855980e5142060f80808000c2d20049201046410203000d903001406080e008001c014507100c15421031600240304240401520442140e44820350000f940c00e070340d40b58440e861132081a060203141e41e400140034035055104000c2e4210000c5158002100d064039503864490400004400340245208040100c001d4800f03642425814148400010a0b0500c0b59481e1034140500b03502031400c80e0b84800900c00092011340e124484650364210000c00d00c1c0c018070841ea281000c40501164400c041c0d030340344d59140c2004030f00704104002c0c0d400510b00309921040c036804500c0040c000808003401400701d80080e003914902502c840c21414800040442070001d28401031010400150031003640907450305000840d01d5071030405001c20b03609150001c080c0c034034141346070741107030507103440c0520030003c608254000892440046999012048400b00920340b00c3c5014001407600e504850700b00c03c100032100219968407181041034610030781c81030300c114500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 403702122 1250 403700872 403700881
    0x2a080a0312060608070807230c1b060c0c0d0206091c26041211120a110d02090a050c16030e1504120f030207031205120f01050102030a110a0803040506 66
    0x102d0046500400c07460520780c9440c58580c0c40940840d40c0144424200018a6042c0c0001c85503e01c600d2074010507000c1850f02da90070829055a1808500304511310f11620f04444c0c521450820704445200c1702c190003802d00a00c0071010b10110703c1d0000012640040244080a03403a1511049014070030704040c03036140600315500f0314410820614030031541d40114583c2540044202034100d400700c800c2c2000349032896017242440380403482543d4072140e020280c0c400d051070b10900003818030b500501070550b0481d4000241c08100100c032040400035004110071002541c040904da0240d0b5002c801488001c0c90085c024801d16569904403c0c1100841c503201304c50807290030b1003122003540750104480149030900382503040c0c015410300320b0f00504110040340c000003010300c01c1c01303000029544401c448207081895a0050000e41112024003086543d10000841e507140d0309409034102d80068002e14942294420304848008520314610001d204540c0001c0014180703030011446640502c0103070549040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 403703372 1250 403702122 403702157
    0x109151104050d080901030e030c07140a0f240c030801060302031e28060302010903080724020903012306062505030c07080106030b1303170c1e072a080a03 68
    0x100d01c000005c08e0780c0300340410f41c0d91800000f038032400e55a4412642180010030303400507030700075130744d23045012080b118003400580720f003544030b42050005005121643c400c0c0021070451340821001c3e40540002d100400400c0450301030303030095801441c1e070305000410408001d010131500109580142520305106441600300c048103040703114820002c0c0041c00723120320b0b64000038505076a600020b000d94000145034000c2111401003190101c042656210b01c0c81d008050443c000d41220b040740e070295092040000c820540b0f519000d041c80d107072444107401c6e0b407160824080280c210707140184400c40010006e0740d98000e80d070342d1600e0b4140701e01e00841d03560456224a80c18070b00ca070f42c0706c01c4150381040410f10001ea41426282c0e0301c0300710980d11044140103802c0c2280c24403240030030360304080c03420302c1480f1080003068028400b2004400204030000c5064104402620481d0343c09840740c005092021640c2112003651421400c50040c800040c5484588450424521010860102d400030319420b00400c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 403704622 1250 403703372 403703381
    0x624060323090f0d030605010f0f140a051201030c0f050604031a0601052107020d0e031b0d230705040c0e090603012309010501080109151104050d08090103 68
    0x4061600303000104200d81129524071042010501c424203690008144480801c264103074411180101c0300c50303010000002e00204103500826000941510122050714004d2079000015482a600c5010365101d001082406400282007070042200800c40d80444100307104c04640694010605a9011881d00d0150025144243d0000e0b024940600040001c40c0b20429003c0078442d0302084c01c22070350380d8840100c405204841105030503018a941c40364602618500c0741d4400c0c823a0350201d420382150b0a809940c0013488502c05a8140e2001000c01c039483c90340303000c245100034081c007140201e0640b41e44105000e1401050b03041c100b141c14114045540040056400800d0300351010044c40780544001010390400c4d205040c0501585000315005d07031401d5100880c0e032411f9549006180c03041f0303184080c2d80041611005030642c00c0c0300000c03a407801c0c1886101d0216502121045648800360601400352400c1600002415001c0c040000d55440d5000240481c0b44103003e22a076554036140050200c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 403705872 1250 403704622 403704629
    0xa020f100608030d090c050a23030304260102120c070309050f010503070518060408010207023a0c0510030204090c080105011b0f02060c0c01081e0c0904090624 70
    0x50906800700b19080b030100403107409160f4102c01084908160500314514552a4400ca411012802d0300003400607403c045407030041a85c80d00440c901005008250b6031b800b4a014061070080f01d000c0b411899000b5800005009007490005418150b03d9003400300ca4083c00c0b0366040700d04c10009000000c142e44016510041c1c50222203d0030041ca00700002802800000e0900003801000038448107005c4030b41800101700480208001d0b5a50740318100d41d8080d4100246c02ca01601100c000c20b20001c0e29140703c41620f110140c65500040b0002681003c04204848295600183c100c5c0c0824517866010605482141981b40565a03c1c0b401a41400301e0b6150b1508404202440d8010f00146c2e92100c61140740700d044045008030010030f400e240f0185c03002c08600a60100300003e00c55550030300810540b4050030242c031140402d0f90b0741204031115440d41118021034016607000104030110541c050024240d01610001c0c1506165540c002181c5403105210030800350448004c41e074102c040480000b8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 403707122 1250 403705872 403705903
    0x10e01140115090b0d020306030c0d05010225020603070507020a120f0b01080c01020a02010f03020f040311030d0c050d03020315030a0b01030605061002070e06062b05160804020108070e04020a020f 86
    0x6441c076041c10100c1300d014030625025126000000301e00b1654003004070b2401c100740240207000740109458441d00075070114280292445c0039007992115246c0d0600310244154001e02420315559841c01d0442d400d60208030b00f02e0340220000030120300c4219210103000b9031071240c94180611040703402c0c25141440b050344100305540c0308102c00d110a036070210390001026820b080c141c0c0b0f100d25140c1d0a84c0a405014000c3e20380d1480850000180044a15040e0b0701240903401d40b504620100700889800090a030301a107640d0125900c041121705c00d6008507840384c01e03d6541460032054000207420014683d8003515000c80c01401070060203480d01c02c3d5034200307004613580c40109203001c0029489054a104008505d14000001283c40e1900d81c2107403041c0403601c1400194136820080440c05001c203007480741c591403038000081c8103640d40e0b0080781a0008582c407454020350f210380c01110011b0004140307504210080c0010311181c0c645002618041d00f041c0c001c0c002d440054401039203010320600b0004503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 403708372 1250 403707122 403707137
    0x71a10080d08190e0102071a090d1409060c06070e01180512210703181d0901060905090d1107060801180209031b04151a0c010e01140115 60
    0x9001858501081e080d0404032040d40d01c0320007411031500106000e41032603003889280825484194010501e00348244c103c22550240755004070b051400451f82861541c5c482100007179298050340d0150882840c01c40c803280b600351800085842c4c1e42142e41603d030330390312000900290f15004280d0011001d020700c2d0031002c0110946c1c403075074038000c0752241d2406410705100f82c0030008418490300c6020a5a03d180e402c280d01c003240c65000952140805030000745884d00300301c800c511114001400c40309810070720006d03801041d40d116280b60029003800a590b42e00c8400141c8800d082c02028840e01c130440180814280801d0090407082c410216001c06811091040c0001608a817070241510100f242900c41e00c1e140c0541c02d40288142c1038907035410305c150042710b45001c1d007c02c8900340d8280143d804ac040c1013581c1e030300003000549601444c078118810450700114000d0751400380261600d004004a606007546203240e00b150440b00c1080780040c003020040c01926020408800a44c640d031a1501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 403709622 1250 403708372 403708379
    0x1b0c0303090d0f0606060f1103030708011503090f03030209030c041407081803120a0f051b03071206030501020a031404080306010c0201140a180510020c040506040908071a10 76
    0x29100d1040c0201c00d4456001c0c1e81021041c020503000031442240d1011040100c60380302c660107031500c0c1503059200d0008052100c4404015404403d27a8043c414540303920045909003c941d281c01c261041d1198205503903502035002041001419030040e6011781c8006986004101c10304d0b00300341d45120303183c0c0501d080007201c01c142c05100311030584c4a190b0f8504110b01c0c2c4c54070394441c0c4160320007583c000c02e02c0c4800303c0c00068000b400c0714602d0040d03440707003010024150711110040c140d1b40121452000200d01d140855500750750400113541c010701c90b191071808140003907070700e0080300c00d29082130720981c1d0702190a0a126030980704102e4140d5521a40310000e181c01c1c0c1e0b80c0e414074400248840e04010060a20000310390180350420031652883e1986519004940d02c002c01021803000580039400c0d154000050380d003812004034a1102507580a402950500c606020240c01d01030705450308142d07500107280204003050081e040329803203400c0c4007402c24503000340768000c0304000d0900b440300320b0404804c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 403710872 1250 403709622 403709629
    0xc0506161d060d020c03040b122d0f040c0f080c18060915180a020a030605060423121912080114120f030406031401090e2113030303021b0c 61
    0x42d2140f0440c0f0f440560741d208024038450550085600130906e003075011410749940140485200d2003039004048c0c44040e005105d103021008441311116140d03404800012400e2988180c0711580c0c000c0c060542c90140654480d40c900340c00001c1d512411164000e184650001e1800c04040142018552031740c588030309081c030000760b0710071001c0e043c400401c100d1000300350180c440190701c1450b503010792030200480c076000126101960011400f200043c0c544003010a042c034001c801d45050f58502151000f890b0760701e0450409aa03400103410f42e10441d146411600c411080000305072a014051038584100c1003850400d5810401d1358820f001c0c803a0020060141468000300310311510012228203c10701d080f994041e052180d00384000005000014012403c203805400c6045030007824a9100110703a07031048000c0841d0340081405c0c03561f4100c148040030b0b076802640a02e601542901907070b4900060034600355415043c5a20880120f0740124643c1101c0554140c505020705d0981c001d049000070b0030000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 403712122 1250 403710872 403710877
    0x21002030c0111090627060d09330b181e0c03091906090b011401090512030909070908010c170604020702010210021c05040804030b0619060c030c0506161d06 69
    0xc00308801c6e80265030f0180001061100f0794952006041142d5600c414100c1314090404640c6c181c450004a91200c01e0b0681c1c039908a190700c5a56000805880401c4540e12005d0a608284603600c00c68400a0724038a40d03044203480c1c01990000e031401c882100e0307900c0c1032510502c020154000c1d80818400c003c041c1c4001b24451a9031a900b240248104032180740a10052203690805842c0d65030a400204030918078030240c02e190311090320748440039940c50f42000002681c0c1d90440c9000c0e0000e0041c18240e04100711410f800c502d0702c0c00c00440441c0c940e80e102e03085a40c0c107503865000401c48100500d03155104801141c11142c1600c0c2545014040d400103580c9640c840500b5080035800030301c0e402840c82c646c060995621500409014506190510400310340003030209855080604020840501e00018450041c0c50900701a8034558900002620318040d42101941485030241c0c030080000c20500c001d61080c1d241c61300d44102d228846900814072501d00c0301d10043c8110051600c5150341ea081c0c00e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 403713372 1250 403712122 403712137
    0x121b0308040608280f05010f0b070b06030c0319030315031a10090606261b030a020f03091b031b0415090e1b0f090a020c0a021002030c01110906 63
    0x904400c03940340d04d00c203036980e1180c012264114030b04581e501c120140c42c0381c000c4648041045000c0c451a43c803818840401d442912468030003081c2004840c4c0055046c0e01a6607000c1d0f070040503690b00c000c58001182c01c0101050003c81c01160703540ca05000c049d018451943e49960102c203c20800c1c1c00d59403003403c44010000c61001030079031400000c0c844446a40c80c480601403c0f0b20901c03004d80c1e5441c0141120f10b856403001d00c51000c9001e1541950242c2c00380512600c00f0b4001e07440d00d01c400d002c01120a40c005000151100d400300300e00e00151007040c008500540020b8000c01c2c980c44500100e2900600c880084c501c03a03003100000b91b1100e000040010240c1404a03000505400a40204040d0170859800402100d0900110070034281d004211403d0070a40c1c050241886441841040004022820303065403100c1104049856203040380d024214007400f20b001c07a01c0800d10f075000583d40c01e009461801c01640300044031039100c1c7c2d0a0007880d20001541c1682c904155068001a005000b1032a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 403714622 1250 403713372 403713377
    0x60203091518060c150906060f01050a0903170d0c1103180a080f010203090f16030303050c07060905030c0f012903100c021c11070e0a0b0a121b03080406 67
    0x650b9071025607460000340e11499000380650703500c290411a094807410840d4900d6400414100090303205140400e5403446000000c04c600714241e080c00040d9504e030820486076007004060580480001c40704042014401030b4a008640c44500c440c0c580030985083c416481d04006201001d1455038200000f03a419402c0181c403000e600030342c12030100d002c03103400c0da01c50300d264810fa41c454000c0a0040d401140036586038000d0b41e4401c502802401c1d41c2d82c0240790100286e88907100d0030400300b8440c0e800303150403050220303a807898000203803110740a48001440944040d0800200c1702241d03d0b0401c10294222840c1e0000e01070383c5128081407040095012044a408038595840002a40e0030300c816140c0c140801030810003d44600c40003955031b03000c92160074105055881c00710703a16000d0301500204c0c0d0064001404403c0c145040c0c45664580600b070134044a03112043d10f001369907038000030805851079540440692510341040880c205a41440c002c400700ea013102807021a0203a01240d0540b480c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 403715872 1250 403714622 403714627
    0x10b0108061027080105061f0f030204030f0302060f0a0e061303030207020d12080105310204050604031b150c060e160303050703090801150501030e07050423010602030915 75
    0x941aa91018491158401505035080c1021030f040ba03074100c501501e002c540200181e80c1c2d1030301488125000c0c10000c10404801e042400d000e00d2241c0030403401809146400b50429640390789500a070141c8078012005030700700204124090a01e0084036900581c0c0400c180b000c0c0c0310030100c0b00d840300c5000d02944c0c4028000301001e018103000381c049408a660181145c18140e0250401042d40c025200c11400021501d800000b010714100610b0961010140b41d6407403800c40c807072009420106080d404031f600680a000025040e91154003600c021070084140c2e2050f03911041144441040642040f21812900c1040c800365a40c0300c80312000d110b43c0030070009030380603034000e00c241b40c60b00383ea5201000707040502c00802055803100141040500c280c407410035407500c41800e14240c6041c0e050350030f140d582a001c01c004561098001c02d41c041059402c2c0c03020107840b0703008182610403d0601141c040d5502414a201200c801c5509004100c00e1000c0c505240360540020003d00071801040c0b140c6402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 403717122 1250 403715872 403715899
    0x9010c0204060f0b0304061803081f0308040f06021207030f0c060b06030106110d030504031e0302040915031205090108062205091b09270f0a05100c02010b010806 71
    0x660348241c0281520501c840c0c0f02c9070382d40b13010000551080b00e0480c1c0c03190038050781050308422420309144e0651300d51103640c0540e175a42451503017200e030402d61201d0004603140020202d40c581000780007a14120b1050b030302e4a0304010003c0e141c10301d03807920390103030784400c100c4078022a03401115a18050702c0341c0750a4010b0b8100b4104000034001001015501800010002a495401018030012040c551083e05d50b0583d00d1101981122801c56018001c200c0140c208038030f040a84955046012842c140141402e031912075131000c039914501400750302d4010f070341d0501c18060300c80300084060318a4640306280c5024071000910146007d48840e010b10040c416180c02d00c09020031007030340301c282d804040000780f0748031042c07541e2003200500c4007d4451030486104003a00300001d04070701c64040b8210881c0300c5400c0007000c0182480b1104401d11a0103004112113166105001494806004000400707060b00c040683d2005c4a8454904409580c03500049045c80d907000b5285d164032038002ca41d14400340c8135 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 403718372 1250 403717122 403717129
    0x51e01090803040810060506070c05060f070507031101172401111b1207031703090708060112061a0913020609040227010903050a1433060406050609010c02 68
    0x54105421030b01000c0341c041050100001e8240f898191602c080c81243d41d104180716541c0b10f066000f0700840d80a000500c60f0b402e083c0003c140040e0401c514924220b2581c44841c03c2c1320b00c1d80c10131243c45002c141c0310f004542e400942d4030003098100d070200c2403500b40400d880038482c0250311000101220f08000704000ea010fa440d0781c85802800707065034281c80c081c89200c50054040c00541c0d10940300032000a20f0042c0002d1900c2c140d03644882c0994540c5202e24084480d504024a0901a885500b02c0890100000d0101d14000c16071606a85441c0183e880d0000648495400b40314070b5807240d481005041c0d5603c400f06070081040da0f000c490440301c50010828030300c075442240740c0150000507040e1008a00840e5a121440c00c1e4018619242c1c190004440d03069003840007802e15801155800041052200791000403c007401c01c42e076918040b190851540f4030303d49403060707a40015112844940c040070a0a43d400794080350b0400002d0308040c00102d8a020b0301c1e1510381040381e484070000841d00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 403719622 1250 403718372 403718387
    0x5160c021305090606210307060b0d050f0f0c010203031302010f0c2018010b0a080c0405091e0a0525200f070812040330080a060b04051e01 61
    0x620703801400b151602400a90f6907400581e407403409441c9040e00d201d03003454904d80124410700300d240614508203064a408000d4203582e5a80c0741d110703201c2c040e03000010310200010b414045114015003942c2072207a8016041c4080d55280d54155007040040180c62002a410203000381e41c2400c0c100102e0640540c215000304030034030010045000600d00150083c0085a0005502c5045441b09408030103065000d04a040a00c12128004028404c0c540080c0c0a184143d50000d51000000d043c0750ba20400984c080d031007554420802c1c1a07240c41d228038030b42c00410107540100b032000103024500300209030350300107025001d651a07039207001300b480c5000d01e10620003408103000480789411003080c0c5102d5140c98545401d1410810b114130040013038200e00c00726500070f800304041001e0b03052034503580b07032041215a040c545c80f00400a030700411003d10000c288050700140141d07290a0581f41c0240030740d046540301d42045002035070510023008180d6a108448c8520440180c4034401680a040140c4005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 403720872 1250 403719622 403719649
    0x2a0b1909030801050a0501020a2d0b010f030b010e070210050601050c0703051507090602060705090d2306010b0f0708091c1401112115120303010509010905160c02 71
    0x403810510321005060780444894140c60007101c02c1241c817903075000160b0b56107a2400c0b0042508041441c442d1110702c004042038820102108807500c410000c0e03882104000090300403840581002d0400d0081c0401060307090b0141c00f00c0d2908800f141058034003c0e5a0b50f0841902e15009070711100000e00c0340c1d11810581d24200084000c89001c2e50700c031701d07291f501c418005100240b840c1c0f00302d0025101c240309036104001c5808a80250074161245c550448095202600d100c0c2c1204548840000086400c4521610250507200004031040e01c0e981541c103000040e0f009284d034420030705c0106400c901207000c582c24598004199030355400340e40c1c04200d034491048100903810002c40662401e01000c81022a02100003400812150401c40320044007405500341100c1c45510500e444050300d0210441d207600001c1e800b502c10f40c40c0c0d0000300013490318071416110700481e41010004010234205002010b02402031030800380614600010400000e030b0844c82c44004101d40c2c4050b030000d54844841d0304011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 403722122 1250 403720872 403720921
    0x6040e0118020c060f06040b040903051206060406140309160801050405070f05030c040e150c0a080121030f030b0a0906060e150f070f05120301030b1308030a0f11192a0b 74
    0x90f1240c032f040140c40c0f90080040309134142c0c080000074505280c22000c0b0b03025540e950320782044200d41a1443c003803581000f84188541e200708a00e5441c125105103d840082007000004203091030180303800d608040c5164484e42c0300020250b800d003d40d640c0461603000410081d20000781041211040504d840402060210283c50b100d041c45101c481450041c03540f00800e489544c5141d90b100208912420000720388402c242c01d0440010001c0d00c03030702805000c51107a20380800c001044c000001d0030a5200d078800c606040d5a04c2040240300d80141482e91a076404662040111021406e151a2403040c007569403c04540010385008000183d0305618200740c22400b19500c000e8040151000c943c02800b0982e0803484800c00241400c2d4014040c5400c20751010825007140c503013070b101d00058481041407080e016120025031100d00320003400380000d109040245911004e0b1644090302403085820314003910b0301030251002d0700c0c00c10305171100b0344c50364018030707803100e66403025482c00c0950044c00c0e143e0389 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 403723372 1250 403722122 403722131
    0x90c0e0a060509010801121106030601030e060f100e1902090d0b0f180105190e0f030c0105010e060d0c03030525050f0706051201120f0206040e0118020c060f06040b04 73
    0x140a68003001800701c3e10001e881d602400d98070342c0c4a500300c03c0700d03100b03008056210f141240922405d081002c4e40d0400410304000c00c2c0e40e1a15040c060403c001169004101c0032800c00300003107020b60150900081c0302d411190000c03420510030303032201355001c3e45072000c069400003500300507615550102c0c840e00381c1104408000e4140b00c1000403c3d40400e4071000c00090054866168411703042c41401d015040c51281c42c070000d130044135141c000e4603940c00340c100fa81c0580c0824800e4003500f440204a03c16107403000103415030400c00c4005c881036005c1c000324090200320040700c0005040710140000d803a0103040071500c0d1494031107096051810541c3d4000800300508113642044070014140d84040546825503c000e51150380860301c600a200701c0c004a03c041000401884224844d880b00f41405000c03c054845c0154004c203007654061b5120707280140003100104109010081c01280e2258088000e518203154030302d45559966018012085c100e0203000810030b90f80c0d4560003107400c104c01500030300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 403724622 1250 403723372 403723379
    0x506030405031e03010305010c030c0f12020c010603061b14120901022a072c15040212011a0406050f0d1b030906050a20073210090c090c0e0a 62
    0xf54290402e00c002c03660396080440101407070b8003034090401c001078990360300c07030031000300c03000c200c600d02081300d89452025420010960042400e01030100a0350040b5000b01e00e0030040307103265120207400499601004a0a1200605802007400712080301c00320044000890300e400c2410760080c414003c01c44411068589044e038441c3c541d002940404000c08240c03420641e940b2001c0b4041c004007410740401c2c018070503d90590311840a2a03e8102103a4050304100710031500c045801c0380c0c01110124060900e45004200003a0344824880750ac64040003514201031038243d0141c818010603821100d50f0f540460b00e8803842e01d50368051011103d0740c12120400e110b2080d0090000d20b030710001514000d003444000761030f40301d16004100307801d0080c419860340400c1030141041c403038000b070104407540010340409106e18412503075914002c05166981001207507a420341245890703840310031052118100b40c108070120b641c510b8541c003100e82c017010100f6612441030b000c81e03001301da0900e280e601000021010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 403725872 1250 403724622 403724677
    0x102090a0f170c0109061d130b091003030c141501060302270a030803220804050f03011a150d021c150305060402060a12090f0204050a090b01050603040503 68
    0x68044900c0c9400540544071811009a214044103100f98007054002c80108603403441070110400304882d85402d0764204201000085078110b03e00500c544154031000031003043c0c40d02250554104084102441000303140d41c0c0c024008a520b41c2c03003c1c0c400400250b40c8041c4a00500100455810b5480c0d82c0b059517031580000b50080d0060210600d003080012500d41a00015603000224100001e14260740c491642c0e440c002c050f4001003910001040c442225180c580b4210381c4094034070b1042d00c100362118142400d009000c5006c005140c480e03814118012020b0282e103081c400340d404240c54080144a581142c02d40d54800d010350f01048030f200284813141c100d06054030780c1c20690700301000d00001c0311500710540c0c0c040b2540009002ca421401c00b0400514002c8014110f00416080c042820301e02c2d501100c040b60b6900a090301c084510f01000b50452030240306d1140d1007080b4500421034240d55845034600000140181409450004041030600508000345e914030220100d034540c200784507004c0d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 403727122 1250 403725872 403725899
    0x310050702010605030703030516080405030708030901080609010501050306120705031923030d0f0f0f05090d030216112814150a03050402120715090e06091303020102090a 75
    0xc40154a05a4046010300e0003007102d60031280c040c0e84103801c11014000140000d01d44a108840456003088005180d85003032010301d00605c2130320055a1500b6100300003510720000200b00911440309540180001c0c6e80000940742c008006039110007520140d441030500e402d4890304502e03814071911990341c600a00201762a40c04900c0342004c0f29052800c1000081c000381030361340d038030b5083e001030102925517030742d1b070b03100d6902c02080c201d020540f400c0c05a180c00489980000c0c0403681900d07a01000303007403c000c02c00e400a030403062030114a0902e082d82100d40a240c2410010211aa079007401035043c1e850b540342e82011891103071698040d503440c100d41100101540305140c80f040710070003540314524001c490b114a00e0384503603419140c421081c2084006140c0108102c3e8071a201a4601d441c0310010400b08024180b02c01046846243e0060094400c0c0311682c09011112a10420030a07240c441d08950358102d0f020101c050701900562400340c2c0a4060140c4a60300b043c4484000101c1e1000700c1003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 403728372 1250 403727122 403727131
    0x1605061305100603020607080d140414060601020c0a050609060418090528140f010f0204080c0409021021090803010614090d080c1f0b030f150123031005 67
    0x3110196440d4141103000d450051102950000c001d0103a030002c514082300a18030b15031140300016044007405040360007500c064a0980380d5082c010020452880f040003459040f00c1300b40004e00e4901d0310391000030301c40c0c03030740d80a45401114003095018140d02c4200542d006855540449281000e0a040150082500c03040c2a500c0380315189941d46802c005090300c004101281c04040d0542080b13440b40940c00000700c00c140b10314840d00f108914030460a01c6105481401d42c00c000d40e07124a004103103403424040a0240348603524000426005a03501d140b101102ca400741002c241d800c8041c2d406828801290781c402040509004104042019000003541a00c3c0280c9604004404902c1209050b003c0c3c070748103a400001c80010f020204946902425200010008135403080c40c06a030440c10752129201104185a03c4d8440c00101e450244a00040c00d2010700040c070030380362014907126070414107201c0c40d680704074104100440340c404042001c140c40d03006411111044420781940c030080c501105d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 403729622 1250 403728372 403728383
    0xc1e030102210609191a060c0a21090312020a0c0608101406160203030f1308060f04051005040516062d0507021207080717010606020d120216050613 65
    0x28005212442d081100c83e003c0c25001c80d034004948442c100100c014030703a070300c290b0b0410030f4902e0495513141c0d101d07c0108104001c10340130b003058542c40c6c5003400014002603232030310b462000865200000e581c0113058030b04a0b60424031441d403901049505905291904201801c01303200024045800354100000c507000d081e441100032a6565140303800000d201c60340d0f5600380e00c20400c200702000003428211141e03d050005055a242c20001c900d140401d03070001000c0503022001c40d03001c010401e0700303200030f40d0b108200021552503843c00b55640c07926844c00c2c208006074259903001003000c2c03200c204888290703400c42ca07540d0060107449840203400251081c503100c01c002000081000300b00743d00c1d102d041c0c54442c103443d0107003041025802c00807400003145500103503204080f0700044201080201c40020300c454a0b00911036031021000d2400d5a001e0f402c11401d662040c645181081e42c0903182514441c0070400060b00e40400d100481a0800c0302c000c0036045100704814054456048031200c0d4841d071090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 403730872 1250 403729622 403729687
    0x300804030806030718090303060b040f030c0803090604051e0411030a0e07060203090105092202031902270d06062601060311040e07030807030e010e0306090c1e030102 73
    0x4004040d5550740c140502003101129442e22900d01701c01360070108510b4442e04010031502d4440a0803040ca030020780c801090140188010424031420b8006040a0154103001e075181c001580080b4980d8803c61181c3e42c007921244461084041e05000c2401980c3e00081080c17022881030403010410341c20940c0d191881501d84409102c00700d8000502404072041d0760095800d0504403001500d5580081d0b9080707030403410000d4010b10360642e10200550400e5a8080183c40e0705050b080943c0302c03411541940c405500c1001004200d140c21601c02c0310003030024a005083c8100500494041620500f004100030304105012851304d407950400400e1014000f0200320551031255098261456444040c28600e241e55003200c0d81d08094200d060550402411204400d03500d5a45041d640e1003004103400003a40300b05007902c2d0350391182c0c2e0302085010890040c240d604281d20304c20780360703600c140c4560301c82d4032400c05056042103030031700000100038014021521101070043c0c40000343c40301540c03151140040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 403732122 1250 403730872 403730881
    0x9160c15020a0816080406051504090c03050c01050f0403080315090a140c040b0301090b03070305030309030418090b0f04141204050a0608090a082203030314010b0c0a3008040308 78
    0xa4402e801204c3c0310703992000b0f251225200d100040102400ca4040040080d0101c5650303280c90080d40c0c0f50324460b0f41c0314022689141840f83c140b220501c1c020b41044410405605218a04015103003540d030000000c50380e039110a42e40e50640d544100d110f6400c10b0840c2c1c02c02c0070201c040d50050a4868440c200f00b01c840c0c0c1d50b01c40e03451b01481346000781c102e903440130320050000341c00e542d010400903171000d000c6480b81516911010314680040741e40240355400003038284a01d8040d02c218040540d00a0b0050180507250780d1002c1260780b000700b140403c1201ca0000406201d001d000700c15500c0c222100342c590404010040d00c015611070700034103006101c243e1000600034800c0d800240f00394050400390030414000c5c2d96030f8000e03a10200d145800100003030b2018080e4101c0c40c80c0140114486d850018110700c00c120b43ca0440d101c16880f603454a141030021050030900803400703c010a501c04080c40720100b28030000c8014010301440b1600d204409490784200c290011300c0c20b80501c3c06030b22503440d15502e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 403733372 1250 403732122 403732141
    0x6030a061e060b0c15100b1b07081f05151c050f06040b041b0b040e04031707230d09050109050f0a05151e090705040f05010509160c15020a08 62
    0x140c0d0840c6645513004c2c041c000c1100f905c60b03109641150b19000d44200460365021003000e25005052549074540b0702e445074150060b020840400148043c002808030010b04034440b04110a03032500468001e600e460006a84143c600310605628000501d18902a003008500304151052070008032418400c8108c01c8804060010745113100d580e00c209010080d984a980d010524160030340d84404410344540c02141031128440504043c0c4890207400e4010f01c1c0c070f828020032203220101c20f0b004c124180c0c018480719581c0321440006458a2a10300064004100c200311154810003050b01c850034a405508820050306401a0308614040d008803800100b0010030b5540b500c440c480700500d15441055028a82801e540036542d00280d0355611003030306180201c0e139200740d0108488402081d005800c0902c40d41c542480b400c1055180c10004220700d43c14500460501480502100c030410030f42401c81d143c0720320402805102607441642d0791508400180550007070340083d1300d404089903442c000101c6011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 403734622 1250 403733372 403733377
    0x30d091a12010323060f04020918070b1608160c0503032107050705010905060901050702070513020706060b1204020a0b0f0732070e0703020a0903060506030a061e060b 73
    0x1011040322612607403031559207030804130589030300360742c10b10003040003010145007070041a100d030145c4407403900d4134039240c8100f00071148024104a210788891103208840080014000142c95241601595400100e5035280d42040c0c151802071041e1400175402010b1280c03803030810f55051103454012000c0782c840d8105030326401018440080c02462000381000da000d818216034110b201800d03d146050040d444032802e441846c00305a0b0715a101070203000703100c0d00034070034207030b016a287c400f0342055403c041c00500200100301402c21541d4000ca10b50087c0500e55001c480148000b84402c0d55031a030840c0e413541c10401c1110140c1c03080d01c001000141c0703210306001b00c1d8902d02d0484003e0303150440300e541d1405410300d0003030014540d440c00701140e01849018405100c1011550004010407031805a0501d4a0040100307640205070060010024140d00402d420b002c2c0c0b070703000c0e8003c292940c601010918105d41c40902030003160034038107144070707109c9070110607030840342d01150900449459484c05803061 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 403735872 1250 403734622 403734637
    0x110715050f03101203050a0e010908070506030c0d06060f03150506070204090f080d1d070302010c0209180303010312080702150a0c0c06021206210a03031109030d091a 73
    0xa0301003000d855111104401181c0c0490301048030b000094541c080940703050705800d011030105070002640b148a54021400259402091034408140d40c102010035848091501c1502d01910740440816201003000040d01c10780882440100b00559807444c000308a050842c40c030801082c54001024601e00c060b515143c1a59000303018a8030300300782c0380c3c02e20000380380404042d50603070000541d81c000204400003c15003c030842c80c010494100381c010b90a404050f904004a4981c04200f00b000140d0304640c4407546541c040729551119601d401400040b11000040c600341c0f4000000007100b0000f070365503004140c03c0103940345180c075915240103a80d641c1045d40c080001ca140c07200012949511074000f4800503d0f2498680f0400b55079176030310030a076007100080003d03900507201040350300d04202400314030500c0480c10404689040d1441c01e5100c081000300074041513101c681120019201100710788002c13502904440f82885100f500500241450042001e0b800c6aa80c1a50002401d074007598400d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 403737122 1250 403735872 403735877
    0x170a02071a0405010902100315080f0c10020a140a060c03142208070b0610050f07020913020d060c0e030703050316031403010e0a0c0c11150c0d110715 66
    0x7040036a40740d0140c41c0e840140201c40b650748034604a8016220b90750489001101c5440c003141c64042d11300d01c82078540882d00020000c0d807099001d110112070001d2440e5045100707682c9080d580306407e004a080001e4000050521215011601c6984100080019885000708003c00983d02d201104800341c0301501a40000c8151031008501c0d2442c00440c0c80710f00c800800310001d01482d060b59140d400d43c21a010680d014034003842000190f0400a110203a80c240c54034066290003070540b1901081c4c00b0300080170b8014041c1800003011801030030b0b0142c8403680c009003600303100c01052400002614402c01c0e0000003078180d48031383c022802d00141403800c0d01d42c0b04000e5414508180e80000b200142003400f0b804020f84101400b442d0005080111b019101c0902d00c1c50041c0b92070581c00003600d043c1c40c40130040014460201000c0313428019640c0c902141203928150a0802d192043c0c50750080d010500160b010ba082221011743d0807078628429010300c041a1006603a4070080b85081b0b2000403a110302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 403738372 1250 403737122 403737143
    0x173402060612011d0c0a1401020304060507020a05040e0f071a0909101a0406020705060304170313020402130918020105072301021819080304050d03020c060a170a0207 73
    0x2038500b9160300d12421840000004040f012020304042420040e0341c0c43d101030f000900641940d040c0441c001c0083c1054030000022544034400003950382c490f43c45028200a030210f034071401c642d60b454007040103180040003482030f032010700401919000c0201030940d0504c00e8130000500d09024036000e07101404041105410300b06c0c90814030020f600010030a01191204003400703c0d8404102c5540c000b90032000603031580b91414820007030314002661b00814421803084c001c20001405076201c5060341c60b000d41030305032284c407041d910105500c207200d0020740c8180045548003075043c5655070f0004031b42100000340300843d0b813070304980c1110300080000303400104100071100c0820444d01078001100c41c00ba0100074058004c013030581c2241c00004c125129225440041e6a091410080d4204214416959105202d01d8050341682c2d0307225900c6034074011400500c0840c2407500a000980c4414006044591b898040f55802020280d40000c1205650111000700324000c001d4401d6401985c0d00c0b144540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 403739622 1250 403738372 403738381
    0x405011103070e012d050d0e060103080405090a060b1605031c050915040b07032d2903100e070e04080301050109080f0604030e0616050c0901090903080a0b0117340206 73
    0x1c403203071f02c0101c0005069031111403800303c001040200c58021409038490030380721810001000405c01c0301810310b449060070001b05004014044040740c0100c0f035040810320280b005460030314298002d50100c2d101d010100701414409001c10b40100b071103486088255103800702041d001c1420501b007543d001c2c02a4030428001030703442c2c0c000d501510b690340030058005c0c0b407099000d44050800c0003288a4000031a291070004400d0300340d01d480241000c2c214070644055030b80903400304c0d5550b0b0041100340102c90f2980800d01c03480401344507841c058440d040d1366000901e070600f041102c3d90300c03e118090000f810610300041d5505c01254000c4d203001c54201800e040d4990b51070880e0070100980440b0b911020400142001184aa102c0300c0403a1040014080d00c40000c0204002850140c1c011105c541c2843d00000c0020350019440741c0c0414420030010b413103100c4100480c3c00300004405180302070445824030603101c2c02122401103220041d80728043e003032000c1624095001e061078030000564003800124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 403740872 1250 403739622 403739627
    0x20316020402040e01090213120b0601080c0f0c070e01050109030804090203073506030c0a0b03220f05010b060f0a0507050c132c0c090405011103070e012d 68
    0x481940001c01c0075003496110368211405800a030b1011060030303400103a00111504080380d030700c0204401d1002c0d0800e04907503111558041e0b4020b09032070400ca80500008c0800560900361444040c0c003004035038032000300d00c1040d0317034450141c05040502d80044000140d17546c451140b401c20340b907109241a041901d0b124920018bd040907140c64103000030109010002c0102d1000410054081d007014903401203500003091907200e01409841c001e8008141d920f015840702c40700d40701210303141c0354900e03980d584640c8500d0146080074016003490320880d41040078003d107c0b549039641402103008008030101705041042510581007100f110800c02d0054446203409040500b6100e070140c2d007a20011005400014041d000040321440100d030f441c00540004521049910300c090041e4940509a5030038000046c0e5803110b07104518410302d0300380c00060400ca402e400ca80040d1000000a1707441c0e04000074041c007201c1d05000382d03034002440c0201e0b070f020008170079480c107441c5803040c00016090326404108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 403742122 1250 403740872 403740907
    0xf060810210606090507030f290607020a12050129030703020603092e06080c0a210b0405031801170a021b0304030506010602060601081b1b060f04060e0a030203 70
    0x42c0c92082e960000080c1401ca10b002d502d1251320386a40000b143d12100041d041124061110441c3d00750000741500c10901c3c40c14099204024101d03500381e05c8050503c0041d03001e0150b80c00100e0080d0f0750348011010820150890032034141042c2c181684004010780503954802e1541d80e259265018441c10405401c002c8001c640000b030350f009442050b24402e040c9182421594000c1031400e10791140102100014452403000e84900e002406d504860040010a6403415024900701ea1015071080d00b010300488801410041e8000301031642440c3c40c0c02d1044d203a81000541072120303c0048040c5803a580310320031402c030946450503444d881e41c4a50701c00074029042081074030703076528980c0804008460108040c1000b148680014569507043c4000241084000381403d41489892020301845031751880c010100d842005407803d0702e80e840e026210852403007141040520b4000e907014424032850054070140702d240100c1c1e0600407100e440c1520750382c0742050000034005800901c507049504248807071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 403743372 1250 403742122 403742189
    0x7030210050f0a09080d02070501170a091a0103050705060712030519090c050301110f18010e130b0102120f0405041a0603010b0406090801141501090f0f060810 70
    0x34203500305100e90b80b1000b03056020400c464003241100408100890040004e02025041071015001951070100081c4c030340601c403286011007002c43d000086000710325038041519a07400100380a51003024840d20ba040403401e00013035030540502c080100389401c1c10012290407560111610071230032030b2504210000d15014020000d142000041c11a200d0181e0042c881c11f207000d40d606500d40c52800303041501716101620310007650201842072181c407540c060143c0d50420b4190800d028560780c01e40040756468100498290700c02c0ea9285218240c012680c803502203d0f40a0302141d01d8848540894206030017140440a800107042009200a0801c0d8201070382282e10300b410080031070358401c0001d009400980010f00e00780701c0490100a034030780c0481d1190003050550003c102d900e201e031222051200008002a50042140301c14840c0742e440f44c00e08030010140e40540750301041c2c442c00040100b0704144100000200b010002c12a07179071998114001300e9100300c1c07038520205884000c04404181c401e5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 403744622 1250 403743372 403743377
    0xc0b1905090114031018060605040611030d022106011d0114040306050a150b04030803060f060921011a030a1415161b050c0105030604020d0207080304050106150207030210 75
    0x60011403004201001c4d43c05540c0c1d03144055880e5040607a120703410307a410106514a00e051000070031171240c1100440302501c1c06483d04420003582d600384c0900d58480d411040114620026164984071645000b10f03007036071030f46281c10455884000046805141c5041c0b0760f52181a900c0c3e00711b400358012036450081d006a00d4003a41001d580c1d49843c001c4801c02c48419aa903911904040e80d52400b2400d00c2c005459040004d60a00e81540c60b115a5400002d040e18010741004501300941d03a169400d031803d0100052401d1303101107241c02c0181344000d0030603000304d0350760a080301050b19945816071a0480c0364003500a0000764413179220341401c501c100300c0341020b41c01013103085e603159070000310311921034000c080c003140c1c5000c1e4624000707080350042c0701c0718200030f41c00004400020b031022981545820003440d0040c1c032602ca0700d0010300248121280a02a1480000c0c004200034200010b5403007503004074002c1103056540c4c1d00070194040781201040050300704003014001850000241e090780c0c203952 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 403745872 1250 403744622 403744637
    0x901090905090a20030708061006030f091b03020307060c020f0f2107061701140910080a1505100803120a060905070503040c1a0a111204030b040c0b19050901 69
    0x107854241c0400d942044580d0404000303280d202c0d0313034202081030400500610300145124034101020030140e00ca01e008100400d5160350a44220301e500d81c21055010f41c201e0307138405108034441080d003440e030040d02c800c82c0203008003280042c13117901038000a040c15801500c0b034100010098200300c00c0d4000e00c02d200d984001a041c0d0102e91224803c100011507910000810102c0d04001d400741640f141101540c03039000b40c55005003c07041048400c00490001910385034072079102c028444214050b29006140c143c070030100458148441c1000d20011100103450810080d140d2002201c8176811602802265500420200100040c25031001c2d600c0b1107070304000a400c41d15945000c040e83e1003900c081c070001364040140400c0c840354040540080c0241400f440104d5002c0883c001c03640590042c010a11481d210489620001070050280000e928046d0940c0c4540b01d2074014039110090344c01395400318051201150400c1004102c4106503200646500711601c948000c940703a40c00a45c1c10350401126 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 403747122 1250 403745872 403745893
    0x3090307170c06060415060e012304140f0108061e18010311190b07021f030203040302120a0c02040b2106180a152706020702090c090109090509 63
    0x4050303103140c1c1e850306541e0503540c0e90325001c02d00b480c0c14400f40c41a8400c0d8a001d00b040e8a01c00d1045180703040307601509081c0f201069100c016a540e8200541c40e180c20b2460300c41e40c00c404e400c1440200700351142e29079648624095a014810f034910204d1205020800f1328000ca107440ca0602801c0d11814062010564400896004600500204005404032842000042c02004455004414800750588621281c520302d0b400401e10a1820301c034004800c08000360003420341d11411031540c0405482d2195901c00c0c862179200400962003250290018061074403c0e00c20b0b0b0681608070b0305500f080c1c0e901c00404100540802008111a844059200c500c8540c100032035001054185841d18020000c1e00c0e9618154100140700d081c0c40841079001c4d0407080316200001c068000303001c2841c02e042c200040219100340c89008400a907015032411110000b103140400c00650001d06a0030710a07078001d210b0f074807084100070440c01400005404104aa4814054041c0c03e03400940e1107583d1108a40003d802c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 403748372 1250 403747122 403747133
    0xf030f12130c0303080f0a05152205041a0609011404020a03021b0a060e2404050a0506090601031b0e060d02041503030905270a0f23160f1403090307 65
    0x1c250b4404c0f03001c00c181c0020400040d0361034003400e0340000340940074040703464100d046411544259112a10803940c500c03881821740c05071045804800002039040205043c181080380c0465460101005400b0304207002401c5810440780090403901400134003001454214104006908407040c804101a420301c00c0c1c2034950004e04070b40360105018009041410020b04012098804100c0d0190040d03000d04041580101003490010074080c20410903041616907217405401c103102004090110302c54002031144107000401d5031030480344541940315105a080c0c2886881c0382071403186182521a00002500c1820030200d4515514401840018988100440070004002540040c2d00046250710140f10360708101c1c072000c1075050503002c1d90b1000d05440d041c0003540c18000b083e05206640b41d50500c82810300940204092080c00040311648440f0700310340d17040c0040211141d0f1207030174000100c10343d5240141d003641c221503900d62301e2031100d40210407852065131021b00036002521003000b800340402ca = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 403749622 1250 403748372 403748393
    0xb010909090f2301060f0501050706050a020730030b0d02010503130c09090c09020c06071101020d1d1603030e1212030115080106050a0c120509040e0f0f030f1213 71
    0x49100003080760f1012105021801c4641c25004a0030714445550280000c1c2e8000f01616445607010001040c541e03944802c0e00041d00a03880018140d08031000d40d0442c020912880c1068000814410303c4ca20034400f904800f6079010b20781143e04541c0c10540d45001d944200019a03002d03001d01d0b001c1000d00001c0d61070900e030041c154042c00c155556034400340100706403c040319000780004d14055042070214113601d91504800782c800740070f01003131900d4010183d00c290145c840c28010358101300300c000307818034a8a81056585010b580580650b1907494400303580b00ea5048180d94040d5609001c50f40008280010215840d480385150310030310348403014180a20700154040e210b0255012040396031400c2c042e080d000306070401c00c18400d040c4006c00c04d40b036101020926154020720007034540c24044905503003500ca03000c0c40c0e80d0000c1c00d0142007069248002808a8010040800c0304da4848a0b01401a220300035481d0b13401c80800108151080d260100c000650085401c90405520840d10f41d661007064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 403750872 1250 403749622 403749653
    0x120806060304060b2706030709090507060e0a0905010608060a0b0304501e0d030906020c01180209091203151c0b070e04020403120c03091a030f0603010b010909090f 72
    0x18040304007084013901f0140102c0b40105118481800003000759542d040e12104140588810032035400c02c1e9000b02c1d920200c00200500d11039004000a58469100074040d20044607020b02900740341d880043d0310211101100d10464202040800c80e46e5000a074180d48036504561542e010711407071b420b9031203200551088440301d80d01c3c3c501c07402040c0600c40715820001d0807007d06454118507009200040d40200c0c807044000c0440ca4002404074a078074200b80240940311043c0400d6103060038504154810020500c4464002c0311021a651394035840f8560303c40032805121400c0d14140040382c68540f000040801300c002c0144009442180c0302d1100c0c40c011900c0e1026103454a40c0b00600c8569a0480c101e00721110090302c040d450141036407036110968240000440030094510443c20a1510890034400540042511084820510528241640c006507503240001e001a40441c1152405100f1040402810707110014107500d00451500100701000d0b0503200014403000c00c2c4c00040580086c1e1410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 403752122 1250 403750872 403750939
    0x4020d02071a0f0f13061a03100b13020304052e0f0c050403030f09090203011e0909020a18200307021509070b0c07080d0c120806060304060b 62
    0x485689050180032050110850b00c0d9902d001018054041e0065240a0f030002e81107404403403030b8a90703c0901c201c510a03500c010380b07000c0c900380c0c43c015006000c00134000461421011948900c81d041c04c954112076806c446c40d0b030f1005411198000e031034099005503a016000d041641c000c800c2e40c1003182e200600da1b000c10380c01c1c80c10342c948014000032a4440c0c01800c1c0001c00c01003018041400018242e480707503000c041d091003d040c0b44100f02902c14801c00c000b40060400035500d0356910300d03c1e40f210502a4601e001c1c5142480e070041038000107440b40503d015001404110601d15022031410300c52000b02101008544503078407a080d40d02030344043c031664040d840b0569a41d00c2c001500038101200c41c084070090a404030144090580c0020762031040d69650b1148039075603100902d03418503140c200da106c00d005001d040312074226150815107445156028030300d10110503900040449042d0340880341d003030380001c007030021401051056011140c0214042c040140640e6131045624814201c240440c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 403753372 1250 403752122 403752127
    0xc15060b0417061603020c01020702120c01020f0f03030105060a020a063213060209030a0c0f0305060c03011a09010c021306080d03110714070b0c0d0305070c0201020a0f06060504020d02 81
    0x7180d80e04a400351940c034180c2d001d024181891104181e001c004d401500c401c154020030174501d000b00c02c2d4112483c480d40140b80040302000030340c42c02e1f21105041c4c0ca041c0540070703000c10005900780c0454000300d0b0090243c00b444c0385da801d180030001190008486581144222402000018501c3c860800766030104940040601d089900030f1420900900b110f14517288910305005464030241c1e18054495800100540c0b034901c1103020070703d015680f02c0003402d0300c0010030000489103074030200742007624090b5099400c5583e0303210b103204a03072100f80304048001101c03024448505030144058007034a80c051402d100681079175000641240f0388116520729555950b1410490114100030700712080b681030a09100c50740140350320b00c01074017480c800545a4002c402c1d14581e503070000d014180147c45c80c961541d450f038000407030170f03503940a522009901003450070b0040b5511a008581130096154141d006118420841d42e514000304aa542d080300c1c0703240c4401000c11145c2c1c03030380050408101c03d0200181c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 403754622 1250 403753372 403753379
    0xb0f0903070501050a051611130b0915030709020a032d0b030c1e0612041a06010c0c0306020c010902060d150509010e0117250611120306010c15060b04 66
    0x508203000765006034140001040100d41003a044002d442c0c44140c401c03802c00c1e42c005242001124048001050f6600581c04145d08861070502d03400f044520318180d4400815a4a11540d0501d200704030000c0c41d07142e4051700081041050302c2d002048051103030718001c10411035004c004071f2400d050440c545010700c002d081c0c0d104c0c0c010017442030b00c491200480003804804002d0011681030680b0001100104d1060201303420b454880d4000c503540400340151b690018a03007410030014030009048000380c000030b4800890300da503102d4950b40081c4c0d50000444d0501c60b00c4e40d034460009502020004040d9500c440205002d41e03a07000107441501c5981c48082520022180000b00c1c2c00b4458008038802e10b0f0b03002c018000d10001d000d840707040d86c0455400700110f801035495640707403040c029804a440d03c00041d1a44840380e070700e40400c0c100d60580e102c1e42c4518195454032601d840b041a1040c2c5440014000981198401c0b505140f116000d40020702c17203d404119000c05031442c40d0030040d401c0c00009005c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 403755872 1250 403754622 403754629
    0x2030607120c1805061602090403050301080d08160f03090f0318211202070308040f0501080603030c1011040506040f060e0a180902061c0e0c0406050904080706060b0f09 74
    0x6001c0e040302e529001c2c0b14050300410f058820103c0340510f90050202145541b012000261443d4450380c009200c1100d511b0203140c0100703580d109000e104454003c03404808240c5000398011030103a021a10500c10910354854101e9008540c1040c8504241c0c40742100d00105001d10b4426000b1030103586c0c5c515100751409040e64032810164417582031a01808001c031070900c450240f002c0d6403070b882140d007800b90718003c00c203d182c54020341000c2c203400c0c00001c0c0011126410050a82113900c00c7c3c80c3e1007100d50380c003c00c15460b80240454130605d40c011007102190400507501901000813843c4206040980b5100414010303040b81d000605011070001003400718076000540403409d0142254090440340c01c0401400b50a505543c5080301682c840322560110f50f1a0403d0740d4150108091008003100d080c220600a44a4141d01d10000e004d50081e460403400c09016050660b140035020b10001e454035981d1030381580c0710b15000d550f110340d22840810102005001043c02401c55075900740c8441007030040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 403757122 1250 403755872 403755881
    0x1b070312060f0308070f1406010801091104050c0304020d05100e010905070b0f34031e110a1514010f03050d0504030b1906030c06090906080703030203190201090203060712 75
    0x42c0d00c110030740e0181040010101c0e004c9903a02075004107030702e602d0581c601c0e00074440000075142d0300071ba025000020800b4101544003158641c01303502c4501000721444184011518288e41c1107001d580b04100003009030910814040c80903110701c2c12112203101c8207188100302d469101c2c68030840d0751181d8640f005c0c05030422480001d0200c850329a46400c4440c0140d1441c1e100360032151304d10410b202c200125825000c0b8500030480036801c0c8854a109852a00810000342c1107200e200801d1081e0f4400d200358412a07202900d81160310040103802400c1c0c40d0350344035035283c0c6c00d1a10b4081d19031909070045100b03040304a00a051141070807507420b0079854814140300c44202034104005003888104046100c1c0c1181507000200c00503010504056500b4960140c440750b080600b24002c000b0001034010380c040c1c440e40440712103c900300400f42c0c4401c00291500072610020380143c0c000e0240b0100c11207880e80d6821103200d0380c0000148481c2590200c0d04201c021070f81a400b040c800c0d59031012007040e5000b07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 403758372 1250 403757122 403757129
    0xa0512100b1207090806010306060303020f010606200a021c03020d0e0907030c0e03070f080f010608030a0315080f100b030c0306040b06061e18030a0f03081b07031206 73
    0x66904a1814151245220301a01c1ca42402c228009004601000e01443c10340e005440c1400c107880310303507031a82400c4002c0c01d01c41c40100c00620480d00759804419062140e90195403c0b40c0c0c0d8281103441030b480714903070110703e01500f18040c02007280c1c5c180142e907000070514942920750821072800d01603050103400c083c002080c40c400e0003010b040100302607888030303171865010702113090004410305440c0302161125a0030b8406600f6104410002c55820040107219007111741e06001c880f6211b2010b03105909994591280050940c800c1c006084014062780114105410f0b00e110440303031542d0b4900c2c4518010340b2011444203a0410041c001e11010b2030b0041d030085540550091030300e800d80c0c0000c60760341c000050024100d9825840442c08960300c4200312070480c0d01d541111a03041510040d1500c03e07620650446030703030004070310710001241400300740c0303103512074101012031411816504c05481150005102105540040c0521a200c0342060007414040c1e010b80d517444220b80a100391141110703026003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 403759622 1250 403758372 403758391
    0x2060703051509400b0406062d0b1e030a0b1e18190c1e1107050a061b0201050706020408060a0b04110703050903031308060907090203060d060c12020a0512 68
    0x4548148440000c25030084450740708024035540d65903401c2100051616400100e00c951071032a00d45804810a0201d02514827a140045032090343c070103148441c0d1040b41d90454039480f030803034140340e5031075020095030b404086502d000c03c215a071680001d80d0200f20360041c0030400307411031402620381000003125444c82140c011942e81030900705804a81001c02107000032205895548001c3d0461150302002020f03917451041002d506000388002d00f903070111443ca9102480355080003c3c0e58942514144201e0700241c650282130038018807000c5058403030302801c0c1d0511404026403030018819100410090a100b0058221410000d61540c16240d995011500c00ca00300b80075003505064280454000c00d0341402d145503116403183c0403900318010140b5201304900b000f0f0001903500404210a8400e00800c8281e44440c0d48464a0100b24042910410b030020b4043c4450400281d41c3d501156420b40700b800c00c6148080b442c2d485030305030ba0005120000040c400b191190100c0100c1d0b0310301ea081303207080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 403760872 1250 403759622 403759711
    0x21170c0303180d0c060f060b1305010212030f0402010c11101707090605040b1606020c01050414030a0207060e010513231c020d0c0801050a1b0f02060703051509 70
    0x794001000321410100c0a01406e5a540d000025a221035004100a2200302e020a403038012030042503942c0b400034420702d40540035810b11080c0c0f030020303d42140e101d6400c40b884840503885540044840d4031507205e04a80842c120525524aa5503140d10001004503d6507400203101a00340744094250018043c14148640706805000d2960071030155000e540405040644030100020101c0c80d450914101800765407001400fa140202c064009502c544d004007240102100034841d159680e06c51008500f005070020382061200f90311800ca1482c02160516040b420804494801041c4100c99441b23100d0244604000700302800b0f1400040d403100100711000d07094001100385000e1196030002000703101d1003c850600e02004900c50390007010f0154000200032a180900804c0014021030303c0c05404610350008040304544a80400702a0b01d1069020380841c7c2c848070f44c140c0290801801866540104440d00000c584814809034480e810344145070f454402d888201c034101486809503020200c008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 403762122 1250 403760872 403760893
    0x120f01020a09052e0210330b030402040c1103160c0f0803030a02030a02040b030115120504020f10031b260108031608040b1216050421170c030318 64
    0x1507180c070140c904c01c19600500d82000807022820103d04052a01da800d20f00001c103041000d0b15148082c0090402e114801c1800c441e110401510006101c0c641401d4002c00028005042c6504040c0b01025241051581c4142e1081824107540011b09102c074001900c0000100344480040c0c0c010003081c3e516140c01a450500394142e86a101c0103000d03103511074001012685118041c0e0407034005224003882192a540c449480e114031451026601c400521150203103d0041c08502c40c0c0390080e98001c205035100042c0038244050070b9203101c0504285a0381d51020010941d604047c4038428880380c0d80c00001c0004080290526540d0b10342e103880c4284900014021040c002045030710061600c080c01450540340d00d0121001e20942d0071840c851000402d00e081e0b003544503991940940e42d040c400d12007040255500f10b030b90340503511641c40344e0720850344418030901e00c4591343d00c1514020f83c0e0f103400d04070171004e40340c0c00740d4045003090446900000c100b02e419400c0f00c048009201112019003140203c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 403763372 1250 403762122 403762159
    0x3030f0105100215040c050d050d080c120103020f010309020a0603090209130308040b0408130e0411090405060106050d02090303041e170607032c03090a06020c061602120f01020a0905 80
    0x1c054a640040c0300713500120b0244038040380d10741c0003048001d0203071100c0d154624041d80c0380c0c03040303081c03030b0000c6224840410100c110001c06c1c2c0d038044100c0d201e20b42c06607203160200490204003a00f0181810f030358007102000750b201c00740d101001c0c00c10b54a02189444540c4180003000200421034004503401141400002e41d00100c40e5400030f0700a1500410f989440c2005012489100b10401180c0380c80b45000544c56450b8a0b220710480c0510400c0650504440a011814204460040144e0441d800602c023a0340190040d000c40190000d0050800701e800011034510b40c042e401c800418040c102d1041c2030100d0b140d0f1480050038020101c2c0c0b1890f910b0b1070a0359078610b0040c1c06803042c943c59600c1d40d240c80175840d4041c80c09852700403030710702800c81c01c141480e1682d000d403c215000304040007020500c6400040d00981c0e10b00058000d40c0b07020900744244010314080501280c0c820b440d00c0c644a640c0074100908400341420740001070382d1300c2090308094000602584100d018000485441c00d0204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 403764622 1250 403763372 403763383
    0x904150303270e010608070215090703020a080a031e03060506181c03120903050706090c06020d1704140106181b03140402121905011a0f060f0c120c03030f01051002 72
    0x4c80343d0600ea1b14075101d844003a4100402c0c07180850107041321008100c202200040d010080701e00984500c2e464503103614036075454514044002d40801e40801c3d0007400f505124605000c1700c01380e0b02c1c0003d0301980702c00000b0515800000b09071003486205121120724174041800b440f10200300e40100e1401001c580d8090004628040c038503031481e59403200c000615019008449140783d0004040119000d42c2c98880c2d11400d050082000501c40c01030303028565409020b82000c3e4840550066440703589903524500107030f8401156501d65500d41c0d07000035042c0010920341145064000001c40c071030241c0c442d0505607224145040040509168800d608100900321640c1c00c10f8056406801820003c1e142d10b142032003030a440984800400401c1044c13040660100d20801d4203c110042180a20420082ca081c0384101c425801801005010704001c06030000380201d5100c2c400ba00ca0075409050309a90b103810079941c3c0c0e0b110f07410020070003446282468031203000d03243c125400a40c40d1240c1030001c3d40d41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 403765872 1250 403764622 403764629
    0xa05060d03211401081c020102040f12061b0507051009020901120f0b07020307060b04050c0f070606050607060e0d080f0a0209030703080f040f0f12080904150303270e01 74
    0x800703051140391008a064000d1103038a01c2d0510f40b82565695401310959400c485200c03000924520741d02c410040d0300c18002c450480703890000140030320782082c0071140c0001e074240040f2949a0344d400750041c21860501c10407040940c03501c0e0141c95002070b040c480d0400343c40400b80d000361442d00c561540182d0310400914155044c130100f4501900030b61900a8071b0041902c00030b480c0852010030012000c1c1e001008118480c4030707034030034085001c6417020301c815100b0603165140c409805200202c11600c0c400701400c440740c000c51000c07441941c0e83c80490000d030b100490507151142c40d6404004a0702c1c0c10007060001c003405103003c200501d403251900c40c0c40040031b0151586240c0000b01e2400b580d1b0100042005550081040355540b48102d41050140d0f00c20300c5920300e070115a690000d41c42002880d5002210b148002d00701e908000c6503207514465104c81340659002e036903412000c2d04100c0350754818001e14866241c2610240444502501c0709021510402c1a41984c0500344546d081100c0c146046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 403767122 1250 403765872 403765907
    0x9050106080f060f030109060b0a090b0a0603050718030302030405011418010f0215010905090613081812032208030901050f130509040503030601030f0b0105180a09060b030a05060d03 80
    0x16030b151a0f0006440c400d883c801d06906600340100134051000716030100c0d203042c008a07450540d007552000d04005441020544640c07000224004211550080c4c110a0f8490007a14015440300c110103200c0900c0b10154000760010703030000c1800d2010b540c000d2013040c00c0c0b032140741d88181050f4507410798860110200c01464108034200d801d5182040c000c10045181888008211005684840000000701400c0307851303405500c03a074008500007407660303402e0700764171900080340300d103440e10858821200343d82e01d00482e50045038014000c19101d00c01c3c4081c1c00500440e050140343c4080c5900f1b98115017280d40c121000b0f42e082000040303c01d03a0030038101c41902010040315901d503854090700c00980c1d4182c1e845079030800c3d24003080004014001c4000c501ca0582600d040000d030071804110001c03542d03511485800301b013080041c1385000c6001c40015141060003003020707405540307a0040000743c40381680800d004130404010300c902e072942d50144545c03000c4243c0c0c1d1500511226100180407403d0b004200b01d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 403768372 1250 403767122 403767151
    0x204032910081c090b0c100b090702120c0a0614070e09061305040525080d14040509043e0d0521160c090c140f2b05010608010905010608 60
    0x3d03014003490003403004000c22100e43d9190012418080e496002c0c6c0200c0002e01d03842c0805060f501d2419841f058000c1c1e8980c0d000380f000e07014240d003024656102c18407505403032081800c0c0c3c900180700c42c05420703410703e46d000501000e410050400b50010641ca81503912482d291070402030359898034407034404802001000495180c0312410060300b04002d9446403a0101d0b018403809001203c000408004c40f124001103e22410608004a5101484800140a2030402c010410a511340315881d41c0d0030a000d10406692000d190fa814008040c44502d8900310b00c02d0070301c180e1010f43e40e80c03400b004000c4090700c41c0e81120400780e82d0580c5500300038404031502e01d042c00c402030310140c003907045d1401040d44e100340b00030351009820640a440360904c1a041e00038201280c0403811889580a080060701a00f005820000080c04a43c569008107014880c207a0321010320400c407a84600f2065801c07484440c00080550404000508454058005c10005420000100040766001081035441001c40c0304660 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 403769622 1250 403768372 403768423
    0x906030c0d020a03061a09070305010609170f01060e0a0c020708060627040305031b070c05120312011e151b080f0a031a0411071104020403291008 64
    0x43e984041c0750405407000e450443c0400d95850241c04c01c0003100c8045035405929030303d1002c1202614000d001304000070711f41c07070010480d01d1111043d8001c3c0384128000c3d101d203c45080001401c490309980140300000b0344009000704c115040c8602d2658031458405070120a0070f00204503550307400541428052298440404241e26100000084010200c101c0268505240c10010700c950426580b100642180300c00285c441c40e030810490711659801000d11201c0c601d00410040f0010400d0001c44a03400200990403c620080864501801e00b1071031341d104150200100c0c80f0020760a8100c0300301c0e410301c038208044c23480e00001d4400301c00c1d21860b4404002c42861500d4449401550384100030b900010850507051901508422800c40150003040710303105c4503104100c161041a004240062001c000800114000035185402403101030005803405540b59541485c410120010241c10051201080c80405d90200103580010540c5088030102c0e00303102c403040d1a0200c000110b1924001c018080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 403770872 1250 403769622 403769629
    0x1140c0714180412020c100f1202090d03030f11030c0304060b040b0915100f21150806070e1e0907200a1b0b0412080409050408040302010e0906030c0d02 67
    0xc1090841c94024000c4a0a1038074281070b84c1821441d40c44054012911085507e06044940580c0403015aa40c50317558001c20100ba140c03401a00d4040301d0311034003000801d0a07900c50080f90302006100365400245020701c41da11001300c40c10030401c260040010814030015807008000c1c0c84d0040d0700a040050300454005c0010300800060312915081180a01002604518488010010300c1e050302c96100540d035947c03044621000c00158100401e1504040302c0a50a09004900d414245120002014241a40b0304210203255602414055105031300b0018440d81c4048544101c1c481605c0d01c44ca0018081c681c0743c10990703898142405914100c0c0040c5020303222b51b00031202c81c4c0c1c80034404052406170300045916400d50b03410580303460700121034510400c10005181012910100403180c00d1a040c9981c00116407100c600541d0744032001c0c000400c4c1c100040c894240100d11507002d03655150b24510000d0400212005801d2190074108100121030b24042100d0a48040450381c000c8000c2d42407001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 403772122 1250 403770872 403770889
    0x8160f050a021c08040b0603061b070c0e10061815050304060914010f18020f090402030307081201060908031216050403050f07060318050c010503100e070e01140c0714 73
    0x455640f020782e14032507100d4015041078003540c0242c0c1d807603400313644075428541e6403c000d03181ca91900d4445010968164044d00191148610510b03030010010f69410624404201c2603c0100441d1084d07041040f01c90f030090b10300c15001010f401c0d100b16a61410482c031101e44482040c032018031a0000025040107691b41c80704407007a5003d40d071841806001700b4114004c00941030b00000c0c0798a45601d001c0c680c8002204140059401007080c104580001c0c03e104024002510498151005100310400113080c0405002c7d03464141140b050f140d0706d001c40040014556070302c4880d80390010440c86146c40c82c600340c0d480c2c0c003019405050700940c5040301c0c216410300c21688041d086002c0d240307c40c4564030000c90300404a9115560074010120301c031140c0d018800c2031680082084d4080c011140c010f5004e031001e1070340941d00804013441d2513641d01406203455404c490400c00209174216400c50b035078210750070074030101d8035040329070414080a4950742e0b54030b003070300814140d001601c0906040790b03166800d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 403773372 1250 403772122 403772143
    0x281a07031b0f080a02070b06040903090e1f0506120a0c020c0a0b0408010b0a08030d09020102150f160203041a0702040207060915051518070c02120a0308160f050a02 72
    0x70a200340310340894000d040c001081c0640c03001a0400010850710b03c0c482c0259090f01d03802071035100c591f84a000401004000ea40e00843c2841985400001e010740d0844009100f2015000900d5076454040440e0744881096040b40380705d10070900c0074004841126081c154444450309000071040c1250034141e141c100c0c03c1c0740440c2e100d424405e0100b000b8600d84054402c0355090f10007440726440900820003116050b0043ca1030561060221401452240d00418140303801801624001c2c14201004001c0801c1160140c01186180040c08181803c03000b00c481c8a0741248095402d0900704014031911003e031a015280c440404544141550307580ea045407000340c0e22802c1081941100c0c075102100860200000e6961441d000c00a20094101b03100e98041910003401c1404241240180c1c500e107000142c014010028103160755001600c031f04405244106001e001082c7d00d1541d80307002401c3d02c00040c406400300800c0842c1c1f01e051604494918504c4c0f00f03506100d515a04000c40881c9890074820 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 403774622 1250 403773372 403773401
    0x3080304060e15100911160b10090609060501021c050315031e0c0901060513560702090c0313051b0a050607050c13020702040e281a0703 60
    0x82803091301d0040b074a000c0101d0741101400d0000c180c0125603454103010346103000c111003450311000300004000c184440e501c4001380107403401050f111004003007181c019802c80300036180d0f648410b20156804101c0c44219070072400140e890340141c408010f08900000e000d81641c00d1604003d240503940074028501006600070584075102101d00e6042e581c0c042d070040050040094000102e0b49520460031030742c0400d0f42c1501d04402d18600f210b0200c110f1307506004032141110f10b9100c2e0340110706190000b14560416450410542c00042000386584072114403130104000c100403002c016190000e82d0380d8044024441d240d201c2e40e8000d40c50000d030605000c0208903014090340c10f14104102d00e00c903100202d09a42d0a0103a5491703400740f2105128412014009a00518041d500d518002d0507200c0c0104a0113800b60030005580c1c00704040c0d40c85404924095080750b0034885501000880c40000036042c0350008481107100e03192100080303400901d1032228441c030300020705618040d03080000881c590b10b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 403775872 1250 403774622 403774663
    0x120c0207080f06060a0501021504080d0b10080f071119061503030c1703010815091e0718060f0e0601030207020a1701240909110409240603080304060e 66
    0x400b1003034030b40c18101d03000ca02ca40345d1403074007052951000615400c1401304440f407120382e448548420610345c205200d6900c1140d1134030904000c40c0c848540301c0d208101c00d915482e0941c100031003032801e00c40d40100a00b04001d61442004d00c0507100091464111a1031078000e490200a4103080001d03141d807000054500d0110000082056808188a52000d002c0d9004412044428000c003017144070a1007501c0c00d03903000402020354413903244041500000301c0012038203403034503110001701c3c003241c0d031450000c06030010070080051100c00da00c1040b00c0341c4519010070955040243d402140303d118040e18400e0b10720500002c04a90081c0e0440e000303d0f400a00749104542e4580c0c2150b007070150a50089019400c1c00802e00544074054190680300e150440081c262a040c07401600040802c04c1050f00c451444410700c10f20342d05c440c49040d105074042c0011010b002c0c90851381c03000c2d041c81d1032482024039203080c00410108074044240c07038205a1020000c5101d20080c4003036444e110b143d91000003403881c2c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 403776978 1106 403775872 403775893
    0x709060c0206030a051026011b0512100902040b0702010e01030e1e0102040b0406080115020a11130f1a01020f0a0803040602030702070e090106060915120c020708 71
    0x12044900216666011000741c003205600e007c10080f80c040200c503140070002e005507a0400d02c00311105800c2a00e15800810320b1003400248900300e0104030202c4c10302d001d00342c0c0407002881440000d41d200e646902660f1070355446100101d000c501c0010203c06c295029004000c0c201000d20050700b058110350240e21f2465007240700010465608020220740b1041c0c84001c0c1c0003515095590b1400c66040c055148001c0069500e240c056500242c0c5040000e005880454107000c01035881001c20101161050081d00c610202000035909042c1d403861803600741c08288510220076030860740c070301d8a040320041d107461480401500c0614100300040114203150011a04034800344121160070703540c0e030385011070800c05079507603400c41e5140d02301005404d6210f0f480710040d00401054140701c0310003190250000250f449604561078481d060221a14002d02c1000000c1410b6070036100a900c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 403597122 403776978 := by
  have h0 := BRFrame.cov_init 403597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 403597122 ≤ n) (h2 : n < 403776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
