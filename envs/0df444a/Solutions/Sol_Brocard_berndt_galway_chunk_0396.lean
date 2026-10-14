-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0396
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:36:05.091982+00:00
-- url     : https://prove2.me/submissions/6fc20c9d-e050-471c-b2b3-ef61bc04724b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 71043167 ≤ n < 71223023 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 71044417 1250 71043167 71043191
    0xf0610050301240e041511040306050f1b0c0f0f0a030207090207121416050606280302220603031707170109050a0f090f03020c03030a08070e27040b0109 67
    0x200e20f560081e000b05a52020008090021001c20658500f01006041005100103442000c1c030b90401e000c22280d40b400c0101107451401c140c44000c2c010b00d041588071310b0203102c08502692682c0224140c0c400c5000318000d40f0b82120062100c0c1624007082c0d40a084000081c2c0f900034180031341b5410006a8074414040600483c2010782c001c02107022a06001400411032101c9401502440c200441900f01c0c0340d019804002c00420f81a004200550741e907020f6009001952010b445002290003824403580010009844e20151034106d00e495003501d2a51090300080320f9041e03440700d801c19400305150000c2040302c5481404041e0780724089113480c684e02c6210b14002c3c01000018032a00202c41d850302c010880c044d98a40c05070301c84000310081042001c82c00e00d050102844609019405030081203010360f945c6c140803045886408030b030365035410b8a680700c01050f14548103019600d500004495a40380c2c042d0712010503041c40c551004041001c41ca8145040580018141c1100b4010346c10b000000e1a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 71045667 1250 71044417 71044481
    0xf0703110a0e0f061012090c030606090b010804022e020d090b0901050d0902030f030a03051902070f12020c060f070b01050a0510260f0106080105030d0905010e030f0610050301 77
    0x3008585d20029100c1d1918101d0340c0e920f00602d400e44041c606209141000802020381c01120721030f0a0500129582d8544001180d0708041e080340440c000000080041c50443c4101031205110401d80440d40e4901901940388440000160b000d6070203085d00801107500036005500078000d03041c11514180d10741000801d540100d4200307521054490351440b08541c0d040c00904105e4039200304132503e070030000c0c0e0002c0141c5010f0b54402c040d0064101501e041c1c441c0b034021620415040142000412003d030b0f10039011807054402e9034118040d4218940045c0c0d02c550042504071101c49404d46c0b242e10606003000b03003400c1a4490b5109034440581017241d92107443c0b03680512202410042104a115600d034217a000614100511458101e410801d48811400d0914145c031419982e114080c0e88407028583d59028046482c40490000c0901308025031284040d10702980707018054400590219204510b00001981e10700300082543d01e0038882400c00b489520034044000118100740741940c580012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 71046917 1250 71045667 71045671
    0x25080406020c0a030c030b060409060c030b0a0f1202090903120a1e05010305060105060711040c170c07020a0302090a0b03061501030b01020a0218071b0302010207120c0209010510020f0703110a0e0f 86
    0x3031f0204800148040c0c0d126072200314a540c00031018414443c1c0120010300500c660001c161007600358400c0401c54200509201c0c003910008014090440000e80801c004500d004084411601c020400d80001076140400075008920031880400d5142c04a42c00ca030394001c0d10f100e00340c1e2117480c1100400c0803076000111181142c01c20390361980d032081282800020280b51020301908641800d160350012035000804000c142081c60890425844030070010100f8490080040d500810031901880035181c413102c0740d40c01583c40703000095003204d07400101c1e08055040b07900704101c02100d01c1c43c403c40d582601a1040c1d9403824409004104c070389500140d40c0da82d248801c42029505200000c07001401101c500d0755159061241d00e030762064525000340030f54003038030045509803c0000c204140d58015403884240542c01400d4601e030744e00384801c2c0450a0700c87e0002c00704500c240040760403c0c4030203000c65006140105945104170140c1030512841d010a40d10070105030300a44104141c030303026004065 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 71048167 1250 71046917 71046923
    0x21203270604030507030b01091104080c04110405090f060301051e16020c030a050a03020709050103020f09090c1306050928110904060608180705010203040b25080406020c0a030c03 79
    0xc820004200c00700710a8052070304001c0030b038421150088140200a94202d0481e45880700511100072114083c0c801c500a40c03180d50a9a400601e5086052030a50051003030103000711071131070405548800207074810000f501c495201c0d07090f007800c2c05031900742802101d0b8001d900342e998110448d800103415204034002070860b49440204d1003400682882032140440089004084540c40c5003507091942c4c82d100080f070108d001d0f10815000284405040c003e003030481e5001400440b40ba500501407081008000b4031288903800b800117070350348503610b481c00c1c201c0001d07500d0800104c2a007840c09101c0c0720180a000510280703003041080070104000007915410010310100414101c5990034494114000c0e150001d81c040d00f042c00218000ea8843c0c00300340314403107840c1395819040e00d02c000944c444035030740074881c0140c10402c801d00581d01c80b08002e045409580a44001d9421100c01d6500141c0030b00000302d1b0075070b000140c1009101d90401900781000382c2201e50152251031075807280c00c0b1280f60300c401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 71049417 1250 71048167 71048227
    0xb060d050910110c060a0504020f130f0608031b0304030b16050d1e0507090b030a1509020706050601090f051e03030c1b0a0b030c0a18030f030804021203 67
    0x246a20014000d55502c0c203610b202c2840740640c480c20001c201d4005840c945018821500010080c500301c0c0544e5004070703000b41881d0a14003413401445840024424081c510945404400c045406c540c46100c004200d240003940d12003121000034a40f0029640f90300f4616071040c401440865a25103031141c1200101800b1070729102d103940e040c3d80e14014400c031003150307526100310000211403211108843d42e445003000c0285959201c01690031040754003460700e40e01e4080c000039809110580c060088101c0c02c0c058001120382d17442480703040ea03128203011203005480307209000c580c0d40c21519040103000c01c4006d00c10100d06150109210900340c81031195035081489040c02640c07028811689400d5102094600780310118045500203818880c0039409010281800a03c0c101624180ca0240000720741c506e242c10031249044603c010751100d0002c1201d05503000000090403400507001c01c034829100c0b201c440c54940100103608600d4120303204260000c05c2450383c150005c0d00f1145813007500c84d1017 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 71050667 1250 71049417 71049421
    0x24090d0c0f060c0504050907030903021b0307030b01080a0c1203050904110d020c07081207050c0d020a0503060906090106060f02030306090a060803070803270604080a030912110c01030b060d05 84
    0x400d03003240c0740c00303005400700b450000020030056100d8000c1007590300c20b8030420075540310644120b00300c03000c035000900140c100780d0100300e400c00d940705490f40600004040711201900e98070f40010601003a80a902160b105100c0c860070441c1c07414002c0020400d000443e0714410f425140030b04580f040c00d00340382c800c90740d442410009201401c2907a00d001d50452046455441041c84280c0e00e82c01c0340a1540240b1540340803c0691104038126000e841c0c0c00405440c28811140904c070310034082440c102e920400302da00209040d103041014602c0b401c07140700182103508240c610076003140e41c290070150420a003c074980c40d00c0394000040325000081503402e4109541d030175044a0082401350002004ca0000107600418000a54040c60140c14982d0816240e003614911901c1100d041c01c02c03116080d008800001d000c0b03001039018109000c03c1d42808521100c150343d844072844410701d0018046018102c0804c0c900c08100b00c035441140003800c0811082131207900050780e40c06840c000001c1e40e40c4581c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 71051917 1250 71050667 71050673
    0xc03040318030f05120306060d020c0705030303040f0b0c040f03080310170c031e0601050108070e0414010627170c0303070302060106120501030c0306050402010203190224090d0c 78
    0x20145851584907031a000c0510749900c0c0229089400301c005a4040c0f0411081c125500ba446084900403d00284802d1074003154008201c00f941200d21100e070346016580001409031010310040d4800c1e0f11032203500148510038a4a07000d6940c000c0c100c0c1d40700c1c013070610003032105a0250210205880d0000305040c2c90307a885005142510700c80b50000103030403039000030180d49800002071000300c411088060b41c4040d080e1401040d82a44183c10514480d88903400401c029402014155004056450b000b4062000305001c00e0070f0b80c01403000c484080a0036801044415401513001c5128103140703120b03d058280c030b16008444100c45008a42e407009610b0302c1d0400c03440b0708120100b40c0090141c103407900d603c1182806916000b091107041b000c42e10086c5040c2401e6800d116403416254020b060102d40ea046485190040c0801001241540300400c080028042c4184d8200c02450785c9a0040c0003000e12980e08144808140d08001d8440050100303000000801241c05010174006241001a00701941 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 71053167 1250 71051917 71051927
    0x3071707110a06080703060506090f0105030910090b06040c03020a0206041b08070810110705031c06050913120e0f15040b0c0a0309140f01030518030c0a020a0f0e0c030403 75
    0x700c45603034031108101c00028560340002c034461091403a070710704200060780c13601406403510a5900095000c91116164195503018401558204860104982c0754035100301a0808031b51800d14165810052a803c002042c83d2500800404c01404d107001d600744501c10304040d64034203006d00300034010060f00c00100701404122030035100509001c8200c4094541d01c2d80c016407140c107441c2d800c011140c00c2044150540b10018100c807803490b4400015880c11700b0950388009500341518500c0700084d22030400089540d1012001405010440c40c10042d2841e07038a003891960040e84000d10511110750200710099032074062910000c2810b44030b48a0040d038461042e5190321036504414400302001c5142c0400000004a4200041c400d840e10140913443d9820305903c011040e0005ea8403ca2400300c03141d95511981106410203032904880c003003545070f10449030854001c0400b08049511004402c01546040840e000081064140d80f5410900b40b052081b0b04a130010080d0140d5500080840d08240c821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 71054417 1250 71053167 71053193
    0x6050306211204050f010504050112050606041d0a050601180303030f0905030a1805010c122105070309020f060301050907081009093504151205041406010803071707 72
    0x2101516401400c9080c004a0b03600103008681c020042c0307120002007540500c0c00c403016240140c440194040089114201400c0010102c41d04032005100c001004440034034041e03007411210b4100301c10303480c004150300d048800c0103001504104014051000e01d840f03103500007069981514012a1f01c11030350a100f0301400c42590020400e00c00041c5202c92150b0050044400d0f070480385d410502540d4940c011103600d101c2d50b41c040c107501d10100d0019000c3c1c0c001d0300c0911588400c6400040e1803181042c2820849004a500c0c001080c0c0311882c4104624041840c4004101e04480050442d41407902280384014000c1141061001c08804280d03a071340a52072501c0200703280036062126003814504100103c40c1e80c10b07000d10000160b0a16080207013029a42244d0081403811941014a45590403400300c16007a0743d03200f0b0040c5810070036248143e0b400348520442c041c00c481082000100380300c0746010416402180713260030502c4164000380c240314600811f1041346c50074a86451007402c0912400c071134 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 71055667 1250 71054417 71054479
    0x5090a03060207020307090b0105030f15100e01030c0201020c0703061d0106060e09090303040f080f0c030310060207080f0c060306040e031602040b0a0b0316030b0607030908011506050306 82
    0x128080002003210030303002403070014400d40990710034590b41c0c0d01c42c0050f58140807040d404180140b001441e0317002401701030703039000001d81c00c01450380032514040717400011035007852400030341d0107029000b00396058003445080090074402145030400000040f5161030841c00004d110039242c404100e900304c049039000d00c00c103084500811000c0d5480e00041c0c001112464450b0050800d1000960800000300035684510b80044519881c10040d0341d402243c1c0d88100c010300110442400f180701890742c204003861143c0311108074840540c1c101880a8504040c070b0740030810f190701c5003003070802d01e0301c0c00309010006074030540304140c4036201d5000280141c89a0340d10400342d803002003001100070920185800741c04c0c0c001d031020003440c40e05c0c109100000c51035001d2240304000070000301ea2a104058210355650015280c0010300c01410000214594480d640650014500000510180c00280301d00b05400c410320340740c241d41e5484c104014115010080046101d04a4180500c0001a02510100031101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 71056917 1250 71055667 71055679
    0xf070201061503050402090601050702241603030603021f020d0c05010b0d03020c0a090c051c060f0e01090e010225020a0504060f1e0803091009150c060c0801030206190509 75
    0x10b201d200240141801c5030182e00c500f444c400842c0316940035104840e46d1310f030050414050204880c001c00c085010300e4206000e80030b070800504160244140550b85054842e94000c1041444d500410040326030101c914440c0540e07844c085d540c2e0980000300b000d6000b41d542400b00072807650b400d00038010003540b5841b68005e11120061010503501040c14070506404481f80c444841d282c2c4100c80032290803401d02c20100e101004900f418444c0c4983d0399000c01864003000c10200e0f09e8141d403801010880e400380810140c464018440c00850380125003240d0115802141025604064041140c140818850030060030624031010340d2107d2070201d010300005803040c0b005540c2c031500686051351a110f0000c00a501f086c0301e0321035a0369405605c04803100c0c000254100b007080b604010300c090864006a0034880280c0707000620709084c208152800c045500d4400080e095400d140007079600c4c16054004001c1070400500069440400380d070303c1401c1041c00c80d10242c40441040c0c5040c0b040b248129400300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 71058167 1250 71056917 71056949
    0x3120513170f0703050c0103091e0308010305191a04051501060e01020d0311040b090307080f01090308070e0d0b0c040905090a050c0105040f09020306060f070c0602010501120b0f07020106 82
    0x1050710000001c0c920101254159561200341c41e40b41c031a079000040c031503040b00b00c4410182d842034000c0350700c941c010785030566207406000d4080c200134200d2400304e010405100041041c0308041c003202d030b051014680c0b80d1600e21900da4422500c283da0000540300841c0303c00210303090040401000710010324110701d482d11941c407200050b003c0e5131090586c5006100d0b003650f4803a003910074000c1c814882007004420b414a030901e0340c1107409820080025407d4400c024002a0404023000124401000600005152546420002c0c64180024181c80178014099405c28503619401040c030b100c16044011907505445001d21846ca510070350344070303606850608040c41000d5001080c032840c098401c108643c6800820350054683d40a20700c100707504546540130802c8103e10680055a001c1c5004050b03d16003403060807060031603045903000791038841d403110b07041c06015024460385000d00050300603404121a00d0303441a1001d000140605c5990b02c078130000c00c20490007508004040d0410120802400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 71059417 1250 71058167 71058179
    0xa09060e03071a2809060b030d0302040f09020a0215040525080d020105100303031109040507030b19140f040b0901060203030901151508040f0206130815070903120513 73
    0x5100030214002400900e01003000d0005500c00d8500303201e03800f1341c024a41c00d00c041d58440248940d007810f403041d40c0c0718031088000e69001d01c001c5519010310b440058556003400170750204a0455000044614070420580c110507400041c00210030303030309410b0701e24a03035510b00e8194280b01000e002c10384148410303d08220507e418400104c140ca20b82012101c80b6034480707070220300361502a035044040d030224040500c00b19200c1d410485203903080d40d10b000d1030000c0c00404603044a03811651803000964072500c0d0b8015180160704015403c040288403034205007040510280c1700d9220084900c602020300003101d5684540d01f101c0c40c1000001e0100f4070541c6d4840e8040d480b9030048a03640410352030000410041102e001c852402c3d2000994403078100e00f0006400d0740c3c0011301130419550140e4598902c001642c0b400c000342480002c1004004e0703c6032500c04800e1030580d0700c80124008042401c104001c0c0c1d80d204151004494000c4821545a41d8003c81030b101441141100c8602124142d404140c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 71060667 1250 71059417 71059433
    0x9020a0e031002091206070f121119020d020f0318040b0405040b1006021203010510030b03010e030a030f0618050414010f0b09070e010807050904060f0e090c0a0e0a09060e0307 77
    0x200b48001c0c0c176000c007048454242c1c692560b42c01c0700c0343d00204001111030301c9174900c100d9000d80b4840110300001900c12129040b03080d143c01121038510941da210818020711a0305000c20003001c03c0c1d81c0000d00140c4848a0403a459004140015a210310003005d289aa950749400c03d888500c0041c00800280c201030030007140b007107400c075685034468241d040006401072000030305945010350132142c00d05523424a000c001c0452288030380f0704105070302c4a48501480c0ea0a121388610300e03660000641e03076200110302c00b8041c2c451100c10800c0e0545403102c100180850900350222022122000240b56642c80c9400c00f80c0300d4400c81708540561821000c90282000740d0b0006c1030340349080b650350250350390b600011505807042c610400e002074044400314500c04e00a01c003038140000d0080000c6030b03880d10340003202e10300c00060344401144180d21041c00b003548030900071001c0140d015105100501d0030500c15031904103003e00540d440c40e41d902100b00c20b0198030f0b0b005143c032900c540240da940700d1581c20b00c1780f6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 71061917 1250 71060667 71060677
    0x10020606240715061e03060b0a030218040615060e0d0f0515090105060a03050c0108040203120c06150102010603080403110a0f0306020306090a1803080405100204030b10060507080409020a0e031002 86
    0x20084d203030110208a090380c9444409004692288500c0075606683d2800c0c090300d44a80c0490308080114004401a0f440c0328121628400c40c1d000d403055464682820401c0c0ca1022030420110008420103005059200c078070000c0598051360700003600380c018070f0a0b00c407032526050090005d014945220042c400442d05003401754205400910885d00e941c0100402650300e840f004200368000710040081d5400340c6001a030080c002000d543e2040c0320985880540d52054103a1050340c0c106e0000c200701c1c000c421401e61000740007840200002070440d42c0d0803d061040e40000782599140340b038011803aa65007040311000d0301d442c804d900c8210307a403031800f130001e034206507510340c403031148040010505100ca01c10303019a0b2045101040d5a00e04e80c5e142540c3c00340010b8030a030340c140200c980c5a0004a03c1d40010b0004610440a07850b6920740f040c4940c01415958001038100314040180340c0104180a0030355042c1d6455070001a61103241c40ca05031207144640040c15094007490404000000c29640540 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 71063167 1250 71061917 71061953
    0x7050609160503010c1b0507030b0702010c080a090b0103080c1c0e04140601140702040204120506060109060206071d0105070203070f050a050d020a1412010e0615100206062407 77
    0x1d894640310b9042600f80c8941c200074200142c08106507220280c0b410800c1c11610340100144e40c440e0307459845149418408455540241c1c0d152081c14103120760050003a030b40110103444c1000794224a03503c3c1c1c40748030018400036180000c08103104c00c0300300c070a0005021848c0041c0584005141c0064054045060001458407a520313085072202c030106d200c20700500c2f0702c2c016519041c40c0c07011100300404176003140700f060340c00503401e02011801d0320840c5160000036005400030a074501e400c000040c1290020f03000035086401a006000d0f6003504031401c5400314860b201d185100140100040742c2c940114403020350f240c411010700060080c040140c0109031801958000203075912402405041c1d006014001e400841d800002c0000c0500c0c44050590729000410700583c4901c0d560600303096a100203030584654002c2c40500150220700e400300300716400d058410440800704140065103c030070040503540626112409000c81c88540e880d283c0d5901201e514040d1545040e051410103003108581c02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 71064417 1250 71063167 71063203
    0x30c030c0608090718060506030130170a0c080324010203041404020906090d11040c0804031b0c08030406020f07060509030d0e0402040306020c0109030e0f0a0302120307050609 77
    0x12460301d119002c0c0910a00c90500181180740c40d01c900c0794142403e2448424646964541c0070a0300e03a594030040d07008080c00d038091000110b4103141114110f0107001e01141c9003001009260004250714200c81000f0b182001c269254402030324162004411420000d15508000040240410017a50f2005d040c00383e203658010492200d10040e40d503031040d40a00310160321060300f99441451300b500140300088014150303a0520440501081d001090082d040350902c0d624044008103052a20952004280320700d4201c0c21810a5107014000d0f9030250317100000449901d000c00280650300904c14000e0403000e0803039903260341d03c0500a444000700c0e10490b00714003070709c10005140b510420646202030780c000c020b81b4960b030075407209803040b00b03480e922741d030b0455001e00000002c07a25900c05070002902850001c43d64aa00e40b400400c48204036080d60721a13102a0b040c1d001c00c2e2038402c1c0312400d0381d41c1a0b880d0343c03600c000c420311035186000c2d5a00080040c82100e0801c44445404241640290582451 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 71065667 1250 71064417 71064419
    0xe07020d0f02060105010c0b1803030c040e0c040509010308030426041d040c0e07090320010e010801230310020a0c02011211030f07050d0e010501050111150106051c06030c030c 77
    0xb241c695a00380300f40b60000d40c1c0c07511140b020407030000c80e558019500c0011132200b0f109181d00e1a05580080320b6503100c851010504108081016494592041070712502601d07043c18040029428441808084c3ca0820040000f80812205a20b04205070004417820000040b40784802e01c00c540c02800313500c5c0380195103480100c48802042083e405594045200c80e84142442c0d8030b6611480c0c003e000400b04071a0a4000012540700c0c10072541e40601d0103901c0443d000d0000c009001007008070801c80c1008035003001040f02c0c1c0303021005450b592481480f01c001c8044400006440c21015045042105100003140011540c0050415518900c02c1c0c0b40c021400070f80724095801c40302e82135001510f00008000240e81107804600780c0da84a40e00b410b029040144502d039480c1201e1010609040c0c0d40c5d5160014050b07582c1091801e05c0c3d003c243c40040528a8509905000c20b03a418400c960502102281c814242c0035401c501040c42444d200302007140d15500d00b4600384c580054841503941c7c0805a074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 71066917 1250 71065667 71065697
    0xf05150103111903050615010c080a200c010f030b0102071a0703030c0c0503030103111f090806090f070e0a02070203100605010f05121503030f04090e150106140c070e07020d 76
    0x8800c0b800c1300c1d0410090200c82c1d803884000f0300848280500c040c1003000f80e440181c0013540c9100500f100c0e041c9075031400b11403910b4401700701c48010400c00304c04182e80721012482d15a07a11540c00b014990440c43c0203d2160b120500507440c2101d40e40042c00c1020b2151014268540d80d8005498524069901848048400c2000381d03207440003181e01030255041040180003140c03808074686a06000503041003100d04c126005000030002800b0441d0004100b403104001260f01003001903002154140078005898050b42d41503901d80b0745120751041b005568002608070043c990503580855005400c2c0c0d90450800c01c0c0c400020303c1140651400324007242c00a80c003252040341030f1240640f51041c000c1302c84d103829210073341c0880010500c1e54148800c1081026200041c0c015100601803000085104440c0140301c0f414290150082089185914010021950301100c900c00014442d9842c50340c0d444000780860820b00e00303400060340d00380600c042c0301d01d19a00158100c0701a4040e5690009020100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 71068167 1250 71066917 71066959
    0x302031c0b060301030f080d0f0f0b060f041a0d0c02030a120203040206092107151202070302070515040e161b020f13021308061602010b0306040f0515010311 69
    0x114155070022820b20045c40000c401d81104010340d0300554501e42040b1200350301c3d405491030317614403160054440030a582d00c2805801002418038003201c9480c01c144048084842c903001d20321541d001010b00b40350861041500c0000c50b90740e01c841040500000320300000c065526071143c9074544c00581c140d000092401194400d507405243d0050205207041c010341c08200d0b4111000441c02c5400e146480c1988003d4400c1111000070134410a80102d031000b116000b45c82400c2016071404240e0041017581e000039404914003040c1d410840d1091400300c1c0084400b40c203401540c02401c07160300c9410078007441d59846980661a00c0440d55111008107088108840c2500758041c025000310313451800c180d0600c1e20b090f802c498101030100046c200035030700c2c102c0314103c1e071164002d480d1074014078240140c2c50300e020006503c20185000074090000030344042582c80a00410240100c05074000000801401b03206c0b07908a100003449603081544c40f82800030441580d000d070700703109404152039000901c00b80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 71069417 1250 71068167 71068181
    0x3030a05071b0203030403080705010f061e081501300b0a0e0a030f0806061c0603021c1e02011205240f0105030a0f02040e010902070201081821040902070302031c 71
    0x130300a1400c05295607a8020320703070022401100e86540f10b514400440c1c2080c07060000610740702c4000c550242c48005a000d1028998100b5001600404500e840380c40c040103039141114001100c1c0522146511001b07245007c040d4002c501d031448010601090081d6410380c0383c0030300c9003d40f0820007210584003159682c0781008005004ca810700030040c0d10107000300b88507540720070040c000c50702d8440e61040c0545200c1080f0015048543e0310314040c415804d0a90b10103207007807400c20120f280c51180740c45200320708450850282408020361004811a440b44404014090410206100074200010501c44000b0410001c00203003407003905029007407401c1300c92201c3c00c40c01a1a45031030f5450f00c410880107004500e0030190429002c1100054019218030800d00030003900030016100c160360301c001444d50002400c403504481d0400b041161248010908540c60300785501500341c0b80569810b01413550045a0001101d1780c8040380341e8091540110041000709601203103c05a00310809280c01281d41c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 71070667 1250 71069417 71069419
    0x2030705010c0e130e100e0303010905060405010305190201120c0305160302040b0d0b06070b071706060310050108041515030c0b0a02030304080d06150908010b01080601050a03020901030603020303030a05071b02 92
    0x1075140c85130342000003541700b600c14191a00540352090034140c45402914217500300300196500010041180e000d507407003142c1c0c2020702128140419455030300c0e1240d035a4250400c84201240c111411030440e030052115106203800e188007403201900645028004007021510400300340194030b0500b000b14803070b1003202d080d290103020180c00c010001902000034480a2141904110100101e801040101100c030313100700405d40d9100010000c0524403008264064840e42c0a48403e1003840008141031111105840c02171900c2c2020b03540f281032220310302d03070354101c1190b0151a19114a4400000b0400d80c829640a0300f180307440280c0e20101944e01d807007042c0f060340041e04140003040014208000800343c8564184010894a0700d60104001148182c4d1410300800e4610b403040001d07410a0240c80c00208003401c3c00700700385c031302500003901b82d1046803c003408050780065100d05580c00395202e04042c40d000340c100c0392203180c40a22500200001da441d04045445d0070b0750141c41c5215118a00e20081e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 71071917 1250 71070667 71070679
    0x907020d0503070f0c05060c030619050d02040c1701091a0909061b041503021308010b0a0608060301110304050105060f030601030503090402030a1b03090213090206090613030b0702030705010c0e 85
    0x20b60000219131100e0802070402c1081000151600854820000d60340644000001e65549040403400c0000c482c03080030b1288140c01c684a41000340d5620304070203078235054042c5c0e030115248281000c00c8884041800c012001c0402c020004070f40902036600024002401d40c0c9044141d1661104000b90076808903521815580164001032288940d0900c28a070300038071031142e030706054941ca5901060303458954204c2c0080d40c00304810b4503242070303e84440005c1000900801542209001003005444940507000911034010b001c2809603d0940c40b1581c0c414101140c1903d03428145000c601801007554468814101c0b003100000b00d20300031aa00d4100c3e03901034001c51810740c01806000c065000200b01540c516540d482c8040c913003203171060702c50014240d5a030006440702144100307d0440c0060000c104e1103880c003c00b500c0183c40354000c65043c03c10444105864140141101c00c002420b40c00c02400ca40322603051001c041d4001016043c428405c2c0300038080c0380b000f0482260301c0244031006580c007207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 71073167 1250 71071917 71071921
    0x6010605090a053d020607050322020f0a09060e0c0901200a0f080c061f0303050702060405040207030c11060304030804081303021c05100b10120f050c090907020d0503 73
    0x104d02100d250402c4074001000c3c4085070403058103d41191501807540100800400b204608954140101e0394041d0b05810504d065041020040c895010710001c0400c0003442d448005007507503901c2c420b030000e000d0010507500d0a0381d11417001d10081c219500c5040c1d070038244080442c0424a403001a281200d00603507030311054560315482109480c80707011310709a540c095036080c6004a818002880f6101d4003440209070394282d00c0d0310184c90700303c00402034004d1291011310030403084901030882003242e8240c0f0f03080b6240d9105000284032449a80d01c102c1d8050702c0080d0040426030440c4049140c580201c058032101d002c40c20a01210344030455005001074490000240040c40b08230140001c00312200e8030101603600c90340806d86125401000400e40c0082021030320401508100704400c0e42c08030407045c8208201c10b0040b44401103146006014000f10f920114003244582c0e0192014440b0207005000e42e0801c05086041a406210340c0c1e4060810340000482c2e484c000101c1500540007507486900e1a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 71074417 1250 71073167 71073169
    0x30807050307030e07030c18062306040b120712050705030103080d0905060c0d0e07050607020409171c0e0636010207050d0906090609140d0f050f06010605090a05 71
    0x180e00060846051560b115040c0030007484c1004201c01a602c21280c2d1240c041c10024800800c541d803602071a84c0a041c0710082c00034071891041020529450080450840440d40020b1210302a90f0400e0007100004107580b4043e50034030501d580215029140d20229030f0702048104181da0040700c0400206000f00010000100d5400007011105500c410002d407030096551010706160058070000c21180740800c5210310440a84078130030340c0844200090005901d860042091400b4200c4060312a83e6a8100081840b503441001008032501d4410741d550b0340b03004118810a11840041041c0d00740c0741003d200000036000030340b0f0780180158003140c442029800c10388881908100b8001c00208818104e40d84258400d0014000c5a4801c801800c11514440001401e040341e66004e00b00b08117501504121240c0c11000000903109024078006141c83c00700d01042091b850b002004151600320311084c0c0620901041c2598002c41600541b000c2d40d81e030304001c803498041d246011f980120841810002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 71075667 1250 71074417 71074427
    0xc0f01050f060907092702161b03032007080703030216090e0c21030706050f0c07080a03050901110403050f1006050a0b0306030c040e0307030906020105041e1a010f060e0a03030807 79
    0x1810401072410107401061b418040e41c010070400706080061480110401c01c400d460621050f15074041d1040403403641d00c00130f2641d401c16540c3d0080080c1c0c01d0004088810602a10000c3d107013540455a2441d543d01e8000e64442311b54040f01c2443c1c2c6545804100d1400501070341d11000f20050060034060703484000c110408940241e2000c040302c0d100c0c1c3c815504203080c000740141c03a000b0080001c85192041c05401006e40041001318412402c001c283c00141d44241a03c50942e043e181c0060300350341d04080b1500501403903850381c038056004100002040000503450600c0510a01603072858001d02041c4c8064420318010280c0c030040c400300c1403140c80381c1d6101456001c6c0b0001c1c00c45241c620008082422200350303540200b919007000a000003815002403240b00103040d284000c00040ca41a00d45072079401c03015680320311440081c9101010f0105007444080000140440e6914070350f5030744851815041c0d188202c1d00410881003d12405142c510b40210032030b50192240d100c240e03110081154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 71076917 1250 71075667 71075699
    0x131721030a061509080705030303130807110301060b09010e040504081603030204090f0902030601210204020306010c020306191107020d03050c070308040b07020406050d05070b090102030c0f01050f06090709 90
    0x51240c0d5101c50010300c01d0846080c000f081ca146484076684e040c24500b10310300b40200394110500941c020801d116900c1c0604411780305190700034040e192144540d1503c01c9141d140070404980c11360a1690204007949440024003080e003007629104602d0903510309000543c1c40c11600604018801d1002030609012190031000b240e10038a4014640f90300c9041d04811510900d08000c4040e41d10601401182001c00c6007602504070606031150507900c4d9a116502c205007810024000d07600403020800c01d0f400b807100d140910f43d005080d02d9880c60046c08041018501a62110445040ca480d20040d880103504035006d154010300003407000300302c988090754a17504c811b03e021021311440c0000400f0605540103071003d484030380d00680c0c0d03540d55070040005403040ca820051094010303800c5030002680004010044030603035005503454410110042c2e0450151042c3e08145000b51a070f480d00354401980200e20903801c20101c414941c030327008140181441c0840c0d88101140b030004c0305002d88110010040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 71078167 1250 71076917 71076931
    0x13020a0c02030609241b070303020c1e060114030a12090e09100615050a0f03061d09070b0a02030a0c170705030c0706020c031b0a030813172103 63
    0x2440304015501291420008a8041d62181c2000c030008034900b018402e08031380e94225902c24940c5080c41405c100e81419920700c8645024800201d07070701003500a40507546402a4030307041c0e4082812030841035040c0c2c0c00340140c0b60181d003e50000072403041c806410305100e900f4003034018543c3d644280e0b60001c11000c02e0354200c0900090038030003e01840700a444900c0f4841001c09402c41800d070510b81c0e000e07181207412040301d0701d5000c0030070315406600030113075800385a80345054a00e80092100c01d038010002c58110440070a0012400d515410032030a9250003101c2040441b200203903640483c4509000340c80c1c50340016002042403010162240403004104e07401406044400740d83c00d00c7c07500080d4400c41c400c8034640c10210303410b00721940601c544c0c0003e080500280000c0d40c000340010362105c0e00b08848804509070709010465680303880d14048013a42d401901c151303840440703440c1c01005092038418141a149103800381249140041810650b0f1240180d101081011000082c0c0a07500020592 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 71079417 1250 71078167 71078177
    0x1c1a01081005040908070519030c02042f071401090201080c0c03040b12071b05100c020c1503010e070e0303030f0618070305060a2301050306150301060201020306040608060613020a 79
    0x1042d242d9a611034000c280b13115605260f50340e03007140303022802d281812100080314506290584042a0003400004030664125000640800c0140e000c1200304005688085006800c900f5480e04580c0b590042c007180d0301640d841000f121695009500340c0704003120007030004140c4c8010401c035643c075001400446403204162030600343c54443c40603d50f000124251000f20170340c02441081d80d00302e000601070012580402494070801c1c1c5604d56240001c07030350500d03035a58444040e020103100740703c1014001c000410543d15210031005030000c0d40c000303000e51a01303e408400485c4003a0701442d425000180701902660a59440306d16004890000404454001001801498403162001010707849500789803000140da00345a0184103200081d50080500710310b6196034021019510700610079440360918050760359a80f141d02140707840518444900300d540010001041482c2c041d000340d0b1080e4015242000b100e952030a10661f550001d5985940100b04c0300d4a00d40d20b002c0701c2e002025006800d00345 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 71080667 1250 71079417 71079419
    0x10030f0312020703050d0f020307080403050c1e06150603240402040315050709060201020901020a0b060f03060a1a01090509070c02010315030305090306060d120e0301110d021c1a010810 81
    0x1030401681d011070f60031000604c0006011044984a00c6030b00e00c007030041c150441c158500000c028140e0740307001d00094103005011800001c20742040011600d403070303882042180410b2180701c04aa66880c00d660f605030740b50103da11280702d030500c0c42c01d0b030344030b074404101c0e02100a000101240b43c41d681c0c000000c0d0807940802c400710115102c0408142c040300304100c001810b141c05200286884c1a0342c20240440e40100f12084050703900045400f00039811150030100ca0300c800d070000d42c003842181e01680d0180103038000c103c403110f003e6000c42404150f88007460480e0081c180119150001d0780161036020303410b2804502580e1040d0710710700300c852040c10006504030b02a40e081154030b20641c01280091400900c80300305007414050300790002000d80704101d000f8150396810070700c41010030b0100c1c10080ea80d074004901d580d0035044010701258142c0001c0e0340b1084034603510f0207503001c0003500d6244440c01100c1ca401240d20302c108000144c0d0b401d41c01c1c00b11054a0011a1826806040c40001e5245040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 71081917 1250 71080667 71080697
    0x1060b0304080a0f020303010501050706022104050304060e09160302160204020f040f0e0603030f07031713020108130302100207050a02030d210207020f01030b0103090f1202120310030f03 82
    0x10065000d640642c8038140c0f100d00d1041e00405002c0001c0440c411500309200411003a45c100c03041d0382da0b503688440b0141e00d640540d012000c00300340d5101011070b0b6603000345c03d1009010002c8020019506c4595400c040104100300740011000c00b90f81d80c402400d91600907010041c42540a010b1413103100c2c1c5a540083c00d00c6c2c002900740d1b080700c00a41250400014100a088103c1035000020b001101c441c14107031809100081e207a0180c000e405840c060009024010103104002c00204900542c2c0111880e01f41001404140b407008c2c1d01c200d01264071500803509a483c14440d0000540d4546d009220400034011410040d4001c11000c5078140f0580104e1001a5828403400c00d2070010f40c0e03505104d0000300110b1034440c201c0c0d00102c451540c4100070b65005600c90320203400038000282400300d02d800070800102d00500503040064144d01c408580c420410480005141c034040c0b207603088841440540c0d81540311440156034000d16403034000002c10000c0c004812a01080d0702a05010b01030841c181c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 71083167 1250 71081917 71081939
    0x20307080715091a0c03120103080403030f030203090601050418020a080d02010c0c030503040201050906070f03030e0607090e0609060301020c06010e014b0b0a081e0403020304030b04050106 83
    0x6080490181c01c041000c0c0911101d140c5075140126042c40c01002c014a48a120500c01000042c040c00204000543c0c9150758030820840315003c60b0f5066400c801d60303503400d144400340c20601044000a0b09250b050340100d00c1317402030780d004111080150145910b840c0411006012070007506808400c0260b4401c05a501c5031104c10003404a10301030510790149490080c00c4a6011907650207001c00440c510010980c40744c10780358825420308109544144130b0000031100e0082c02001003070301c400034400c9820154560842202c103e20b050032a0800d84983c00b0503241402c0d0380c01004006024140003070154030b4155042d0741c009901034001032801100054040c1410000d0b0001c98282d56400010044031080243d8042542c1c080c140c1e001804100808010344182c00b562441ca21024600a68100040040d02c00000304002ea00465490041881c050985001103514511090040110703000c0e65940e43c0a0a1080380e15902951429056560b0014a0440903105030f61700c2d9661030000c0b80300703030482c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 71084417 1250 71083167 71083169
    0x509130e010f090605060603100303050306010c080a110105011a12042d0b0703090c090c030b03060a0c0801090533100915180b0c010b040c051b060705030a050a09020307 74
    0x1e00d40c04680c0c84030f103050110903154054102400341d00c0400c200728015500029100a5950510308203a0300d40310f020040703a0424043c00c3c00342031980c0c00104100d282d60044581101c0c2c01c2020005e020b66a80c45c5c0c1703e01041204e02c205003212040801540880c51020070340c91750300c288503155000e0020340c0200c64124030306006916412000c9004030403024410616802503003c0c10510301403011480030f94074602034482501c0b030441aa516880020807881c043d41014000342c002504655041c5482807015000c0d150b08918800410b40500001c692914140102c5114039042581c444924002800711010b4a44103108800013075401c8195284c03940d2a18410940c00d12140d4854981c2c0382000c1a0030801548c04210105100c40a2200740c800c0c40c0d8044a44200d4040c0d04c0c2c410b1300c8505e1080d02da40508065401c1a500914102c00d001540d03400c44e02503c00501d040f010b200c441c140019025541c0d900540302000415402d000240145a254100a5000811a00102e142642a4042031900040d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 71085667 1250 71084417 71084441
    0x40506010501020f010b010c020f030c040e0105070909150308070c09060806010320091b04260114040b040602092b02190501050706020c0f060702010e07050904030509130e01 76
    0x105004100d02d60741003000c00c0001d07190200800c40880d281002a01ca43c1600c40000d004042c045000e00096a051010010180c0090800c0c010b1080e06420680204004c4440c5d0010a1412001158902c6070f0711a08600103070b26036880d8011070964943c40c03196080007108460002e4110000b282101c034a010312401005e940300103061079411880c0c625500914090600e140007142c0031568126641c01142903041803218955207600f240d440c030051414815030b0880d003420344071480440071380c404444c150820b1107036010003003001c007a0120702610b0707494040d113000c0c0c441c60080c0b002c240030400d9903000304401d0300b008110307090a03058a00c4500c0c610500c00303d08080c0c0c0118a117080c0545c00d0003007500000c1f404204845e4411070400001074001d0044800c0900815408120006000b80c00c11260f0b841101400031500289001d890090180c000180f21280902814400240e1814006c0495000d0703030b0306443d128203143e41341d02801111403070780190400c40303510307044900034002080c441e00c562000303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 71086917 1250 71085667 71085673
    0x90115030c230609010c1415090f06040302150702160b030406050c0f070b04050307060504081902030406050f1608040f0e0907080309010f0e0306070804120903020102330405 76
    0x49069000041080452480d00480040e0b00507090b1a030303101c03400c40300c00120908000351318070058142600000144080e85103203110744010070071101c1600d5031261284880b003045401c890444852140c84401c19a0010090380c05084160050341c415000305500866603c11202c030410440c56201c0c010980f9071084590b20400414001800310a000d81c41e80901002052403410030b281c8102200d510075104040d21141070000850f04018090045540d40d54000905204034105814520002e5214a501d40004840710700546c60180c000f04c140c40841c0c40544460741004003020380c01c0003c0e4400800100a95010103d10002174040300c0500041c00c2150b01480d54281071031802804000080c000000a510100080205280004c101c0b002e6450a203000d86219613414070940341043c0d19240e03076a0600500007006207031035100880038130483c050300b003413100c1e10201902a9804505400040d0043e00082c8214007c0300e811408051514080c207a60056455910040d00c0c1104042c2d8003154a90 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 71088167 1250 71086917 71086919
    0x2304090501090e0a02010e1507050a0501020307180f0b03040201020a05010606020c01030b0303030105060403030309080418050f0a0507140c0f07090207020405070504120b0c09030607030b12071d090115030c 90
    0x1050300c580d43d035400700d0000901e00d44e1100e800180c241d10304054018820400408801340107100402900c00d89540501213a83c1800245070050207034004071070f07004c0000d0325804c508000625904441d002c58000745010342d0910b01b41500f0b4480c40c0e01c010016415845000c0360b0000003242407041c54000e10165014100c000800d100050990340110300840c800ea0062005010307903601d00e002c0314112607041c180024117014500c0c000c05d0354000c2e640070040036030311088001142c8805821541c0708040810500440d1b9403003d241008454083c2d5440000510540c40b100c902c0486d04003c3ca94800c101c811905282003100d1500c0c42c2003000e4118136512034020031075400b141843d000395500100a410000d0801b401c00720f003401242500c0501500b000341810100b00b120564100f103070500007001c1e017a15842d151030030700603014084c180401400303941d2580010080350300201728001510040101000300185c4038404602c4280003410030300c855541c42d0f40000b80d500c5a050310b03800443c428001a9101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 71089417 1250 71088167 71088179
    0x20414150f0103020f03010915030c0f050a09050f040f031803051609020405091306180305090a08030c1213050d031d041109130f020c010b040e0a02030c012304090501 73
    0x1607002100141031600602022a5048417481924192a00842d000503441c2c890f402022804900c7d600c050314201c0c1c0a80c0110345082c2041c0420103540e4150f034104038480d5980207603002c4500c00c8800c2420311714003001080018004454a400035406498140d0400a2082110595883ca0f6204036040d900001464200c01d236074402e024014003a8040450810b0301d800d02261124500070301a80c0b501c0001e002d000c0411101d68080e0000012503201020011020f160203845680701e212428881d206242001482c1c0703400200321b034020b0801030040c04001901e12151aa65000a54240c0d6044400e03076000c41c2546a85e48a4402c950181d46c0d000c4a6601c40003c00740541c0309151140d005504001900d1441040703070381160324002064512602c5c521082e1054001091201d94415125000050380c00544005401004050008071010091002080c01d4a9500d40124400030f4040d00400c0c10046207600030040141003014455014003000e81750818105a58415001407801070b540d00b0042c860 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 71090667 1250 71089417 71089429
    0x4120b04030e0a080f0c090405060408031b0a030c18030804140d0203011113090603080415110a030905010212070c0302090c19031406060c060a0e0307170a0e09100303050702041415 79
    0x41900c01f91144a024201509c59075180d500060000e0003000002022442d901310701240d0b80c15107401c030707a01e054680c280728000030041c1440da103490313002803100c1c044886182c0307140303140200b1254004c0b4818586803920191000d01d40070b9685481d0f01500704280440075880c04e0284c1242e54001c50f000b0795503010810320107001c880c2c0c40c0d04061520f501d800820720004101d40304690948012032950030014000030000c848003000444606014042c2a1810040542007000701c07066034403d03002e071a81241a01a4065139000c1c00c0c034040c00000740c01000300b0260400c2800c40c0c2d085030f8403408261038607040e00c0440350700f034603007000440000e503980611003802103400c40000c0d00000e007181c00340e1074518001071090344d40401030188013080b40e031481c03119400f6070204111039001c1e91042620700b035219039100702d404039082602c504bc0031800c2c12150b10101d14003091118860852103244448007030642e10101c074142c00c41441203801c640d441e0303807040c2c419008458403840340c0c0d10f04542d824040c1c411004d01c82 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 71091917 1250 71090667 71090683
    0x1e0d0305010f06090909020402040504140f011505180301020c061302090a02160201030e0c0a030302031201050103110a0e041107060b01030b040209030d0305040c030f03110105060604120b04030e0a080f 88
    0x94402c0e0240280301e160303070000c00c3d03104a40306030801084036482c900000b8020304c80c3d9805550710034606030511284500d803100e07c522035078002c64035041d143c1e85ea80b4060b000280c0c1241d4140091420041002080d188002e103c0d00d8981c054001402d042c8403440651800405581c0e60000c0f90603049a0011807070485500c50b4420703900c08040d400c1c4402454405418070880318001d06040c2c85e4098980d0464040118003a00c0b1001403d00300744582c2c0f41030181d22588482402c00f4200481000424994068040c2b549071640008045150041d050b0781210403001d14070f08aa8000e803605c000705080340d003140c050032009000d040b000034040039080014048684040902d40140e0040c00002466a80403074101000452424042000d98a0749092038142c2c542e0f4000410b2204140c0f9020249544034441059020140d0001c01c02c4d601c56900b0000940150312524a08607600c0900b40009020482c1c0c09400c83e1190500321840360b80880050007a02040e0403440c8168407186045450003c2040340c58 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 71093167 1250 71091917 71091929
    0x30c060c020f06031f0b0c190c03030c06020904020f12070305040b0c0703090308220b120c0a1b030323060f012001141801140609091e0d030501 63
    0x10052208030340c0850480c5060076003507440342001000080c80303220068180d80640901e65641c200454694640e40080e030050303032005806118003c502c034216545528000523130341d000044814400c2c40c1d541c00b100c803e000f2080407601c17160240440b40c806d44890014241494035160503a03140e0112040740c2d0601e55004089004160501c030030f000200c0c400302001900103171415501a80d400d0300d4203060380c030f0600b00d03400145900400640003200405205c100c00e4085601e820150825580e000701010701c0c01b5000803010800c070020701040305014103000812500d8011300f04a51a00079640c010104c09281003c01e40119446080c079642c400070b03450328440114000411901075081440c08a414516100001e5050120300706201c0c000081d019098010801141e0003170018840c0804005e002c1c1000f47e603014003040c41d996020b03926000601800b2000e001d2100684269612041048084600549548458020450890601c605000341d14200000040090a04182c8a42c0050480390164040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 71094417 1250 71093167 71093177
    0x20f27010f09240302060906090a030b040b06010906021002032203020a03080603010c1409150d200703020a12120f02030105030c180408030a0b0d06050402040b0105040f05130e0d09030c06 82
    0xf420b400c40c08406a082900e4054031516299140c4a01246d031301e10880f00c1c1c01d9440224020f000007080340b065055441640300b08010f00789520752a00550340d52926001c0c0c040941c000e2500c0052807406580a1980429a4824404096645003003a00003550041003070300103802007000f010505030010740b81a0061001e0700200403080200c100100854100d0148401240000031043e0700740c0c0d01e40381d10b802c02c2d094042c100c5554500046c0250000c180040c4907940441880c0030507880c442030361064503841c0d074164024111801007a6603444a020761070882c4800d010412908200708131440c1f043d1004400940c038010380d2541800304051404603240c001070320802034190748105c40040415040c1d042030f44440e03815180c0e11009a00c0d8082c0550035000c1d500b003980100100c05100964020320b004900030f483c108082c1000c20011946440b40b400b4400c1c13941c48036241048103003001400090016190341000445c0c00919030950b0038060002c5030200007590304001841800341c1410440f004000c00c1c184 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 71095667 1250 71094417 71094461
    0xb09100b01020d050906030a0b03032a030901050d020d0f2301050607020607350702091003080306010c1a13030f03020324010203310909020f27010f09 66
    0x2002c0340719a811150080701b000c00131645d0903000b60031025288000405603078039040e10000c14810707205140b40380c0c00d03680f030348014421307008030301000301c0d88001410713500d2030715200c00403a004019501000305070b2402030340e070226004d00d0042c078802d08102004802c15100301c201c00ba40b4000200c50180c01480c4503042c104003100c0180c1c0c0e05070407182d103254010b400152011307600c4000d01405445900480040c15048504107107284000c00400a0f01d10845100115882d1a0240980d1000074000242541c00400204a0560042d41c503050007511034014020761100d1503081c98601041910751009a1903410500b40c10950071265100300302c0030628003181140350003900103c81c041d1018078484007900010790a0f191ba4828011151701780c0d0b0700c02100d1803550032240c049000c1c806440038035503505982080450710303010701d000d44005a4ac004041c0d924620207031041000c04240710000704200b600190303044005420f0f141c4118003c01000701141025450b00c100d6205880c00f0300700701003404041d610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 71096917 1250 71095667 71095693
    0xa0f1401020724020f060106030501031e0c1e030602180306060d030813080c0625050a0801030219030f0305070501050709031e080d02040801020702040e010c080703050a0204030b09100b0102 83
    0x61180140c040300411a2140c44070f0905074104190140584c5480c001c0390004980e894040d04030074100c0e4032440c2540d48600d401140741c4801c2c041030000500714441410304004043c075982c90b85030303410824403081181e0343d40c17a5600e000701d038411910349001d5071310f01150b050989400d11083d03034841001d5901b9841203e203503500804884008000e2900c510182c0c1c8000140074255064503881051101107800d01d05004502400940450450007078000351340d071440240500c40c1c001d07914400b8080c0c50f2000300d84d0869082120414101540f0720701140060700c0000450f0341d40e0400c01001e800b82c0c503806c1d69038149013407070317800d603000184800b0502450040810005e800d090841003c1092000b0800322106186801141842074008a0300c41600214010408880c194010070700c241c42100c003007002d0300704100381074281c455280400000c0b4100c1000070310711074029005141e0190092400501d011307104e03078a240308610103855103083c591200000c030a221507503106004a02c41c0074002407510540f50343d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 71098167 1250 71096917 71096939
    0x201020f070611090402031302030d050f0706110904060e042d08070515090f07080d200708030d09030e04060b090609060c15040b0a060501050d0209030c0a0f14010207 73
    0x10000034861a501c0750b01980d0725034000e05844d035804006006650b6400c000d520703c3e040100e038200030f038400e00030035020142090240e812146000c01d480c1c030031801c108868544100410001410030101c980030455080c030b65a4501c28200a42480b110744500c605003414594801079407517800e008006440401d1060100c203100500c9103103544013000c141d440f615031030454180fa030341d0072800c1038000141080c03000303948000c00d10303401c50031141080380c0b40186e4864031a90f4601d4119440c0707001c074002d13200c14001301d66405808181400c5a50865007e01c1e0380d6401c43e0726540c0019894642c145c0c0d00c2980004141c0d00128007079200707000b1a000e1080b5400c22140601c9440389880b241e100d0302c00018102801d8a489003503d41e0307190150f00b56000c00744104810b4287d80c00486040365004812400150300100600c211800d8440c180c0d00c2a040c4088484180000e41c410550301d6494420054541c0c115034403940100041c12400d100c003410b847c902074448003442030f594002819504010701c1400110156 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 71099417 1250 71098167 71098177
    0x30a08101403070905090a0219140f06160221010219051201050103020a0908031207030e030301080d0e010306080f0a020103180203030f03040f080a020f0607091d070509030304090b04050105010201020f 88
    0xb01200081e6525401e40301b918101c06950002d4000100b500c0d82160710207492400c208807a0480c006406105a240400481540706064203034401d6041c00041d142c01d800c9004008614405080607045c80e0345159141c44680d10744003814500ea400045004144c001c004151150a0791401e14505100600c1c00b03040c00783c00140146810940e0110340c9404203403240f0443e000915011040c3c0341c0c1c0744c00982d006403c240080700d00f00c001c2803c2c400d01d0025071400008480c101d030307c004060000110070702c10455000316031036401410961078240219403010f080c055a000c020f02000108440d40f018800901a10118003115000e008800323031010150302e021045442c40344046642136603a0351103180c1003210801001d07001c0d205180200e4245200c540010340c00c00b07075010b160203d503d60703a50090110f502c2e0f60341d40125419002c042040141d82c0f41c07842100c40c0c002c84036061480c1420100004249150403a9020031241522820700000c03500749881400c0c09404280700035032403c041d001700040c02d4815 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 71100667 1250 71099417 71099429
    0x4060b01140a0822060f230103060b0613060c0510050c040e06040207050307030210050c030705160f0203060c1b010614060c070305060703090b06011706041d030a0810140307 76
    0x2200380007540718051001c0020021550746003c000b240e049042200040419044900c6e01e149803403001603c1d280701c0b94100701060141291545540e003140d40700c5005d42880d410300e68008600b80003885030041140c00c1007024010f50340c0c8148090b40c1034201a498140d070601e040102510f02010720401c01418401c59040d114100182210f5499000c0410028404c1040251031404040740240070150b0206401c40d0141c048001801550ac9001315014144801d03202040030405c00c0010b41a516070b034411510201c4d000d00e20f0f19401c0182c41d000303e420132100715030300550030800003101e450301c0d1a45000e0f141c3e035094030b00082162500b0034500001c00d01c00e914102b44521000303c1c024010140030452440555403020a44550f0f003440180500502402d82c0c08440140013100025200d51140f02c0b1207501040803c00e4051544030b0344140001401c09003540e822a030700c0d003020f030003400000b04001d144c14823013965116450700e0800b0400302880200d07080018403100c0b8140948031554002529025211 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 71101917 1250 71100667 71100677
    0x30307030c051201030606230a0909020f03060709051002070f0501110f0f0601050a0b0c070b0913020c0a02010207120b01030605151e010f0302070b01140a03020904080304060b01140a 80
    0x10000142c40502480500c07050407180c0c0d02c0040100062a08190112480c1c80d05250040364405281880c00507000174490f044900e000040014801c04c4e00140c0c0c1850001e4603082c10081100c000c2814010200c1d4110007103809120100801c0c24a4001400b0101c224809000084c0c28560f0701c0e50100200c1c8596030401143d6030710708241000900064090101d03002c100da00d400556641e150f241d9400348142d07482031a01480000d0254081421200d84160080151030380034204412080660409461150814511582c0000b40e5495200910003d6903160003440c10811900c002482c006941d08500350121101c40414006103800709500d040d80c0c1d00c1440492036603070b40da140401d03c0c1d0035640c0c150b60006490301c011040d2a42d4080101001000785d07075070441e1500c0d07428140c043c1d1040120042c521814200100914100e0200c0305009020040c90901c00541e20380000310200303000d40b82544d001d1800424407042021034840c0c004110030a003844450f190058041c0300c040d00800c2120400d03c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 71103167 1250 71101917 71101931
    0x308030f19020a02010b010210181101030b090718060c120807090f03051006090603080307050c010f050f061905030a080c160b0c0f06070c020108040303270b0f060607081305090103111f0203030703 86
    0x3380c000c1d00043d01d426006481c041d541d00d04030700006c002c94145010f0365412250a5070119299100e44401d240c116000040d61040f424150310032145680010310b01c00c100320a5680104428a407289010020760181d00182030b00c400d0340b110030b405c54104ea800b9202040c40d049041001036251803d403070303000d40c2c11308002d612240d501400601500e140c20043d00c8081c80e0404202c644440b200c0c2c0c4034012031381503d165020b1a17141801c0329098941d030041c03561591000d00343c41d001640c520010703c005035a410551703900e885052030003034a024154002d564140c1e0041003100140108004e10b281038145070f002400503041c02e0b8005055040c40c40d9000c0e0401500a0000302458002d801c44200810280041400080344030006004d00003e0711045480100340700110741c0128900414074000c070070060200e40352541c265180782d0285d0020303000000da083d003601d00041c02da0300c090600b802103009060300c1343c1104000c010003d07035548100401070a80311180110012980c00000c0c0c1c1e91040b46800c0001b521 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 71104417 1250 71103167 71103169
    0x90b0403201507030b100212160804080106051005070f030806031f0e0f070b0307031508070815010902030708010b0a090509090304051503010308030f19020a02010b0102101811 77
    0x18a6074032803607484070310032000c0c4885000d18070155a8031030015580c04200300d4624000f08031583c44d01020a50050303000380805035481c80454001c3c10003048070b5080f141071071816601ea0320140c20135400080c3d641d649840400450030700c181041d09070112460850300d8907038940d895104e04010740d000a01044200000901151020040340c03c1c6143d0007400d00303c5c2000c80301c0f134280c090008000c00385407a00602001d00c0305400300103030f0381055810202c0014199600e0450840003881c14000c4400c8001e13040300c0000e00000d00384082c01c0642014070240c01d40c060415a0001c0460041c2d0191003a18810001c028625600141881c15500501c50480d541c22180c901210b246880750006a40082e0800034000035110010040084600c02d884500780441d194541003243d002c24400505000e10400004011020340c1003015481140d4281d40c006111034000301c1d0040340c025030246400760399035070800c40403036804000701068264910418000c191981d441310320600c2c03015400401d102141c501c0e100346 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 71105667 1250 71104417 71104457
    0x140d0f020708030412090503190b0405010b1009050405011a09010f020f120403020306150319030318030807020c0303160201030f021e030f0c0a0f0c0f080d0204060e0301090b0403 78
    0x5a030740103402e00c0e8407801c0034100140c580707540e0040b1601140003c900015542030110307024007420800c103040007000400ea120307075810702d10003031007282c440d5a1003041d6215039485040c5031003401071a41c0c0358804d4a00700f509004c01c4a0301a003000d4060880c1d05d40f0b890510410008465002e402882e0065240040560580c034041e032004541c2c0d400d00410311941e1401422801230001c50303000701d04580e526190061960855140000815010f401c4415101941e44025100e408070307911038940044d0310015246031811000f5003500440c0000c02810903c07008950400c40346d00d1540f0304602461415441c044071a00c0e010314031000034141a1614400080081e540e410b81d110040d00c070002d145c040d100c25400b01c04903807080b03842c01c59015003e0702092842c00300c0025140401002d0300c03110325241820b00103039501c0d03c0034541195021001c240020000b91210080e21074a070b21a01c0c0941c03900c2c00d241025040c64442109513009a00d021104800301d80c4102c1030720703081a0141002070f41443e401c008002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 71106917 1250 71105667 71105677
    0x150f0609160309121218020904081b030406050309010b03010e030d0c09050d080901020f03041d09011806060906060503090a03050f0c0313090f0207020d060506030f0f010603050d140d0f02 82
    0x10801660242a04280c00045c00d00020104500c20081d4501e008144440301d05000e0011350400302800c00280002d03410b000034175580c00d191800ca1120340d05600038501e158015045403000410101c00d200c056003090050410030001203009200a03071449a074940d4030302030345500f0b03100315455a4039682d0740c0d4002c00c07400000d0a0050700000254005081108250340b201102a0061040b60180300d0043c0e404001d5400b500c10b00b8407101032596801820182501c009082010a035684100001111035005981c0415500c81d140200f159850544c100040703d05690050301031020400800c2100d441c0800e1150042d981428040d80307420354200108458020701714068210f120000c2d80e00500103207558014202c4059082c24002d1a00c080f001d9030690080324802500500414000000140c4a81140750b001c10054120380c1e01d40c0700641c2d890300d010040304031100300381d6450009100784982446080750b40ca11a0500e600b000104040e406018070601349c40d50304803580c450025940100c180c046030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 71108167 1250 71106917 71106923
    0x315040312090606140321032d04060605040f1a0d050a021201050a060609061706011202120405071d0114030a17180f060a030908070c08150f0609160309 67
    0x1c211520391103c5802c0401042c4c0b05c0b4824030a010400000c4010a022990003690748080181152524010b9035a81d20900d4400b803400c07000041c074070100c0a414902548203a026000100c1c040380b414050000700c500c4090088c1d0f5490800049050342402048840c58028095942800b0110142403441c14003030041c000940c4085d0a01c0640840c2d90150807590060340160b0007004035595540c001d5034198828824100072034400d004148423503484550aa07070009042c1000910303101050240c4040b60300c0a00451040c0041038140b2040c84400c00c01725000e4041910f000003c0100404016901c40341441542620210824801003030744044c03140008140d0710210031442110700c070903180e4260300500c0c7c501d0002d00900716410050b00d0003c28901007100054072151130186411811405081c0000301521001c008010240014007185c400100900c080c01c0908a0000b00100060782240040c000c001107503032203001e10084c0e40e149000681c0110080c124502c4d0580c4201c030982c050405000c000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 71109417 1250 71108167 71108171
    0x60c14030703020a03030b0405010f06050705010f0606020a05011401060804081303020303071a160f110a02030d0e09070507051e0c04050709050102070e040b0105040921020c090603150403120906 85
    0x1a01c105034000490054040c480d0b10184102603c0c3c90520040b51800d00c180c0b850381e015400c0030440380d8080c9004100c0c00780960008145810a200d400d01940c000d035010b4801a404614200c05101c020300c51003550103c040314844040d49450401811118003500240c1388010001d0035000349088146000700965000c2d0a40e9100e100c01d00b404001c0750100c042d0501c0040b80390002801e41159110300b0904660142c60b0074040c0381c084a030450b540307030010b038142900e441404425800f50341c2c03c2142c0d44d01600b241d036a002c0c0c51a045820b00200d800007800f2942400310500c2608002503011400404c50341784440c00001001b2500c0f03281d46420511990150464a000c061101c059884441c000599500f038007281c070b8459030f034402e01041803411500902040c450030018056843c00380c1100051724041d005820b2080780100c10868610f4414a4000143c1d2100009802d82e0800d071140c140e20420440107065550b100c0c042106403200020f0000f0b0030442c01c0c034094007020303c480d80960f004681013041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 71110667 1250 71109417 71109427
    0x7080601180c0305040218090a02060d020c0d0912020904030507080706050603011a06040e0c071b0e0a0c0c060506010912060221010602190203030d050705070c06080709060c1403 78
    0x1007403419100700c4098640c1c4034200500c01d020b0303038001d02890f030260b03902501201e0004805100c01001110117030201c00c890240a41038800341c0d860001601004055440060b51005110748540c40c2c0b250044140b0240075440034100529a280b00c0c1e4512441d40644507051240d4441c6800c6690380b10301c03000103242c00408542c400602082c0d0f03110754070442c42a002000800c0c0d110148080d03088851004540c4100c04000078000c10381d50300c142c0c1d034118925100d014100581a03940c132028240e208d0140c07200708000d28040150303030202e60005400c88040c040410404e0640031009180d03000000e0007505a0740c0365408203140b030f40704189031001030580c440d0586540b2141d1410310041e501c031040210f610000ca01070581c10a89100129040300e80640080001070200c405061000d1740c048426a4540000d01c2100e011800501400d0b1050030f0681c1c81c60783d40d4406261002c18001540c000001b0082c00d101040100e50301f1143c4030307003525940d041034400c1140b075103048074800d44031801d100f0a07800041a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 71111917 1250 71110667 71110679
    0x1c020415110c1e210604030f09060f18050307080c030c040e150405011401090605090912030117030c010c0305010518160804030519020309030706080112030f0207080601 74
    0x208103910603500c08a422524006440d920200c1e00c0b02203901c89030100c0d000e10a5410441000380e4080c0240001034403888941e503140030000010320741501d80d0480d00c01c1008141e80030b507078418580820f08004180c0e60412000500080703c1c1c4e402e6070188800355803035900380d138200b41401c4020440107049482c40c0b510b428034541c4510aa41d1650b00a1060b6803c8406070b2611b0300039108000d503108000c21122540b649424101d11019105460955a45184138090614a050b8501038982d01c040403605625113014404c011400a09035243d42d00300009500244502c0341c110790458902c1c51015039100e800060381070941c417907817125820303640c81c00e0f050158164240d04114100c0e1011100d00c4000c0301001190307440c0781012201c043e40340380c0c0000c03041210b40c0100d0a10b9001f0f4080d10345541031181d04c003610784120100b6503203900544d202044403040ca140c08c1060070090035092809032a40e5242406080c80c1141c00040282880071490401f0b40c400d00c2003220360001c060000440b030603075075601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 71113167 1250 71111917 71111939
    0x4020d051c022413060908280e03150601030b280e0907080d050708041d0f0c0703020a080706110409060501020c042306130f0509010e0c03070603021c0204 68
    0x1612a02c0640002000806107607100440c00d10800fa021204c1250301c2c2d4070ba403000002d00b451141140e11260901c106118890340803007902220a01400c0e440e0012002480545401a4104180d100781c3c404c0c2c0030109840200d03529035030442c2080c08c0206403202110300007042444105054201000c0500d82510b01311540c43c540b03030850394081d1000900307450750880c0c07a803924058014414113900042040c40c03900d1040f4002c0c40780d503004032a607900346034541848100c0001d107d10540380c01d025400c00d11511180c403041c200c1d0041c09400c1100d10305240c5a034060340b1180700354405050b51002103500000d01116401a61020900044a070703691602d4103410702c0100f44500400c0e0040c494009650b1140c02c1511410402440021400c40c074080500440c03944d0950062245410000014500401c82040d002d124500ca260b440c2c00300711450b18110040c2140c03240305401702d56601c9000075010755100401c0141c1511440d10780541e98204c80c07020320500070440240c130007080703100040002e0000310302 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 71114417 1250 71113167 71113183
    0x3150e0106120804050a06110d0f1e032004080a0308060312030702060702160308030c07030e03010c050721140c01090c0f030201020d080f060d02010c080d3204020d051c02 75
    0x31902207601b5034a44c5030448204480c1d0040b84829444056240002e5004120b458205803c0d8544180c904001c0500011400c40300b8140c0350200780c444800000c03420240503812404050107003400d0805141051442d45c0c4c184980014040c4490840400e48a85003400310045c506d007100b030304c0c030b80c1e0f410f0040d8000c1d80e888040ba00c110050242c0d0188034040c040e0314410b901141c0c1c1262209085480c1d1814640c03607948100822001c1c030800c1ea018100540b42801f80103402d41e02034031100e840f8580c0d400c1100104903008808600700c4081c000b8151015000483c04140407003102040e03403a5100944414010840c04002801c1d140c1c03003000000d241750f500352100f4103980c03007a8260380b00c1b0440e092003030b141601c00752020034891000400140780340c180000280301c2180145404220840c1036103a0200580c007245002040345e4880341420301941d4601154a10225590580f43c11210399248030201140003030002840b0b40c2884000c0800c3c00010440c40c907071143c103210211542c0c404900f01035591001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 71115667 1250 71114417 71114419
    0x224070302060f0402010801050111030d06060206060f06090607030e0d060f0f0e1603020f0102031c060527010b0708120702010906150308070215190c0c0f03150e010612080405 77
    0x28500001d81c2c1d40c050440fa4a005030f40c1a15507a807640d003040700644c1c0241100f004070311036100c240150118141e0500500008040c0d640183c200c40c10210244a96134140c2c22240b401000200041d08140e21084100d5003103e401d8074180d84540c4490000a100c1459000050821800e043d8210310750181070780074400c0180040010030815005150554071030903a007106103e00095038400308094140040d8030308504205205072460400c1c4145400e202c0a00d211708206060350b640703002d101504225004004038240800308201361885410088044001400f4044036144041008000c0003a201e09483c480e11841008522a103801c040080c02448002c2c0c040c0c4003c0d007801d1070005968400848041a00c1d080070200e4a840c40b140c0070301001070212840300d01410340c2000705080301c03504816043c03103034020b0740d03039a0070f5480250420b0009250182c000c55140700409008100140400b000b44c05034254607400440c071140c0514109004044950056a08071404e811500c100410340c402407069442c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 71116917 1250 71115667 71115673
    0x70b09090601170403030c021606030504110301060f09110913020a08060604230a091107051212041b150c05150f0c03091609020403050105070c17070224070302 70
    0x15881c001182c0f60030305000303038908091900c004103000ca0b2003500071402180c2c041c0101d46071001a00340506074031000d0b0b8000e90003c0d90300c101344000c02111070000b00c0c0d150b07821030090140341d003002040e800102061040f03414540e55507421024040700300c0c090340d0750000001c0510300204500c2c04408003035403040c40d0745c100040821303001402501d01003050301c00303882c2d00840140c444070056100b00e4507111240d0000e50721000003800080c400d142d42c01408620040c07090000c0d240d001c240390007858407009810b510740204003480300f0030002c2c01241c0c55030b80c07042c1c229403001001c048031090300e0781a0b20150004a0304640518101c5960790300850740d454824401c41c121404200c01c0050107545010640740e12140e80700850225420b00b02000142d9005502e5070113541111000030611900e40110758080b8003640e0f00840e003042440400e01c0340d694000840e00341141030428659a50301106100b00300096031041c0450020190740310031516400c2945040c080c02c01c0902030b0303880190300d500001c03011030040c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 71118167 1250 71116917 71116921
    0x60308091002010c1e090302060c0a051606021504020103021306030c0f0c08030103030503100801050f060f01030b010923130e0d1404052209031805030a02210f070b0909 74
    0xb4070500c500b81c60510240c0da40280403084042c3c03481100c00e43c3c0d801d81c003080860344000c001759075214010244011510028081c6142515000c1d0821380850034220000d20301607802c00941d60045400490f8011410391240396646510050f002400b13003558040441e44ca00034082091901580110f804a0047c0c884841c1000e0b0380c002100e00d03030a1620001c09000e0280010800640900041c40d0004214060380c044141c40300d000c1421240c00b281c41040f19000c0100740801c2d406c0c00113032604441000c4c179007409560802e04c0080d0910300749220304122200c01140a440702d8182d2402880f5102c4000d00180c0c014440c0034050000d4460502160124007686025810300b500403060f190100341281041c501b0580341004200c0149032a01051500d891656407104944079a4803400c0160791181d1240822207020504400800b01241c04c0603003c1c0e80900f1728240035036070b0075054814100344181800b480c0341980070758505010207151680140e22a40001103846505a8064a4100416900c1c404d840d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 71119417 1250 71118167 71118199
    0x609061a010e04022b180c030303050c0403050d080702030d06031a090304051f020102040506041805010806012102031c05030106030506011d0d051501140901080d1e1206030809 77
    0x7489080305c14441c40000d440404010900803120000c1210682000602d00b0409410444100300f011002c40e00c02d820320409000b010741500c030781600410408405030406003036503116543c4001100110f000e00c5441000140700078402c06c00c66180c049814000e00c6001ea03030746440018a1680c0d601d07056072500c0807000074460300c4000180d50440300c0062070701c1704404843d9000f201da80c80761004503046540800000c1044c0d01c80b40f0003070005110101c03401c2c00f4100b82d01540b108a0310180c1040c0481d41066004000c2d50300030702c40810803072488894540c0c04e0b11880c03000a2500c81e0020740200079410401000c0348080d00321020354102d4455450520056480310011501c0290301d01c08580c82401441010806040992456000da0301c82c00c2140c82000c8020f10021a011090f4400145107082e000d1754001424020345050041003018001c0c0114641c240024000b00f021800c0303100c0c031507400070310030080620814440000001800c4e0820044c1d8036801c4c404020381c051100300f409240300807901001c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 71120667 1250 71119417 71119421
    0xa1b0509040f0b0d080309070918060f090b0c0906120a020a1d060403032609010606090603020403020604030b04031b0c15050909150102010207051506010e09040c0b070609061a010e04 80
    0x420f0b00001e01504603580c80355140b450580000c0c10642e0140709003613011545c00719a12900d01c22018480750f415000c8a03615100701610f0682c0101a002400c06c0311240c0042c0303811000c1c40c1c0180e507401440c1d89480c00d42d004138150340907101c50b5a900c424140140541380e0307401c3e401050a000d150303403030210310681003509150219003e1108c0750048802c02040000c40e20896850202141140c00782c58926a82c00c0f50355440c1d0700c10b9546260030303591036404012240d005001440100100d05041d4145450368002803414042d0340301c06845045840c0000c3c00f0580b0600851902c000c40501d08000c2981c0d90810391440040e90103403403108500a03602c9144d60b809030003070f0380e42c3d0a0002c02d000340594485640880c0d0301c056500403811f6640911040d000210b09002c1c19540030010041c8001c20700c0c0c6000010702c00350070300b54103034001c001190034800400c01c400c00c040292805807401d90b035075a050345801d00003844044006017510f850b068415001a4003450346200c0000241d82d40c008002091081100f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 71121917 1250 71120667 71120681
    0x105040b0c3c0d060302091e011a0c0d2c09060402070501061802030103050c060c0c0d060e0d050c0706050406050f030402010c080c0c03060609070e09041103011b02010e01021905030a1b0509040f 85
    0x1d80c00382e1001000600c14856071100c105685c0c3d041c48bc02c28060f811400c0c07514507841420404503055891b000303034544004840200780921140450380080310130020954008000d80360724055500000e8020900c902500601d00070074488550900820704048050025003007800115000c1c0a000c0480c40c2a29200095501581c20b04001d0314503901640200004848409012594141c4036110011070b000b051000c0d0300703220000e848041d80c41642c0c1c2c841c0b0382032240c60b420038401d00c1070a0000b44403040c2e00000384c40007041c001c1486076a98070741d4001a01d80f80c40e00c0d94002c04482c00041c00740e8031054007040703144000200340c048588645911040140342d610899070480014072900c104a1546040c405880c0c0041c000d211807070b502c80003070000c00d003992181400003500380c200d5200448182e070309100c1d401e040e01b0410004c60900890164142c4009820201c4004111b00400841d88800f00b56014001114019160240208103a00c0240a64105156142c803440c9080d40100108540d13009140c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 71123167 1250 71121917 71121961
    0x10902010e0d020d080a05091c0f03051806040303030e010c08041104110c030a0c0c08060f0703020306010e0a0305060907050901150804050a0c03050105040b0c3c0d06030209 76
    0x9260712469040c0608500210416a4807000c0c210610000c18104002443e8814607a40c40c6d9a851542d0340902040444546070304a41c05201440f80001c501164201e00600c2d516280c055560041840705445d00c8004580030390703001000040000415070154402e190b46411800240621b8000540590351100d0844000c0d044050f51041b1881514240c0d00500f10824074006090800941c04980c0e4519007081c490b850110b484501c44000303100d40c10308014024030490000b000c4a00d0103d600c0007072003c018100e0030a2680200c00700b480b50703000740260b100c80400a4444584565282007141e0b0b152000d69404100d40110300e408616410207034080c0b4161400803103940740c00e440c011b204441c03c0070000c00680d000d02402d10300d100003c0c28002550010750181002003000d003001d04201310300e890094261108002e081100c003041e02455800d00829079000c03105a61131001c01e4055103101c042ca00d0078100c155200040107031022840d540b1003016a4002c0d0380c1c1d84042d0385c910507208442000043c020b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 71124417 1250 71123167 71123177
    0x609020c071703040b040b07050c09070c0308060a05030f1c0906090b070201051c1a010c0506150a0801140901060602030405090c07020103140106020102090916090b090402040f150e0301090201 84
    0x5200035081c10b0b00a00c8070344441d404492510b5074400c0f80004641207034104100c400c900250070014844108549904010211404941800e2215011341140c600300001070621985000086a5035241e040c0c40c0010480542911000b00c078030000c280e2194002214040b103855844200c2e580c01b8454105881659400d0315002d43d12801e01841b011309800c070403c100d0410008000320b062064602554030b00381e00712801c004c298112907040440c0c0b40c0207640d10890400c0356000124001c200009001d94001d2480c40c0d203041c40028240100710007482a400c2148039600341550840584d0140c0710191003547d084c4000c20a030354941c5000c82c2c4038402c2d40b0800c2c0d4800c4804d00410401082e01c030051a80e1352050500240b4020704140354030b10040c09078404400340c6d602056105282c1000741c0e1081e44904c11400301c9440c0746100c64060014a80ca00610ba212500450080899202c1e541241c0203800d4804013101705c6d6903281002008032960041c0d54001429008000300c0b941414002c0c0180300303a0584507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 71125667 1250 71124417 71124419
    0x50d0f09030803191d1b0a05090702010e0303070207060207050901050108010e10030f03120c030629220501110703110603090a060507030f060506090603010e0606130b0307030609020c07 81
    0x1504010b4002408403000b064007544120404402403091640e902d8543c904a2480c1c07805d001894140aa1600e9110030300904014504d8a507441400d054281c82d07088070a5103c580f102c0100300d00410032800305903000d22000090010480c5c00041d1582100c9075030b42100c204070748072030a100f060f900a105003404034500e40d00601c016032103c6030569105500c4840040340950f00d4580b2014100700100035804540c4480341c88403051118040c050600c041c50605120803880d00d0f4000341c07a48407220f03640c0300070301014011280300714151040fa00320b441c40c901390583d40071031010500001c0500c3e02c11a03011031b0300b07506a95002c0c0f00c0820780c001100c1e0402c101740d0400e0102010701c0742c1540024102da041e40a101e0b05d04001a1503440740f24080c1c1c130039650020342c441a1000b00c50031103060350071092080b2024407400d0500e80d82c8104680c151582140d041076180c8484004c03400c14000c02800140101e001d100129100d801c04010303520500c0b6643d000c0c07004d159209d82c1c95080b40325646d005001030300803600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 71126917 1250 71125667 71125673
    0x3030a0c0c050303010f060807030506030a1e02090a0501050a080d051806090409030206090c030304030b0c0d0902030d050913230c0408150414070803030f0402030307020a080a050d0f0903 82
    0x4030150140d219810207001804142c1d803200c1c20b40d030007600011102c80504900384121544100f55aa0040d81807c0c20082d505114000a54603400d00d0402070550400301654451406100710004440da405030008000381008031181c00500000d014890003080d860030005501040011403561740d40385511503601e000000807401175000718110710035070030940c108075041c3d05481e82c3c41014078040c0290b0160026061400d0006e00303008050071308501c2588140001d00106000e144407a812040d400c11302e584d070300c5500e6011030203402a44006585030048a4586000c0d9400800426a800f411500301e00300c4515030b1405070890b03a492040d600f80c1c58643c0314000d0025a40300c0d5154010b0001c0d0807107402c00e990760948914100c0b200004c807000c100400e00b4042000403c01100c81862612005021030f00c1c203105d010703540c90000500c2e61421480d80380100e0300303544047c41210001e80e00505010001511040065034884100c0e00c04c5441d0b1090910118400c0c0c032480c3c26142c1110342d9a18a601d641c51030b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 71128167 1250 71126917 71126921
    0xd060b011403040506100608010602031b010f060810060b040b0a200106080c090f01270f02040b12060d02030c010c0204021213120206010b1902010902040f1d010e03030a 74
    0x16124180a16040c00e600801161400b07144114480d60050603140740030b964050031840390b0340c0083d041c0141900103000494000c130540748110040700d138207030303540c0351000710075003d0311502d03807045107403850110082230031100415401030070001180248951a51400160124071851103045001001404220b41c00d1f8802c40c0340314002e402d891008a040c080700410242101d00a90007039016911071402c201031801c0500449910103052001555150303d408842980c00c0c09503403852032901148a000d03241083c241d03001074035030300b0400406c54aaa49920700d00e0701c1c0d54000c1254044400c0003500080701e902c4e18803041c03000c0942c0a400340000045180c010b442024003000c00320780c003039001d01c040d08002c034080c01000c0c401c910047c1c1071284150581844000384048507040c4003150004001402030300c204204070760a0219201065880c40b04a8404a00502d03002000a500a0600010310102c00c0d0315042a003494041001280c10b00303840306841400c81d09442c100c51005c0c1c20600011321034186907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 71129417 1250 71128167 71128181
    0x70501050c0c150a1b020904060b0303070609120e04022803020c010e1b01090e0103030806120318040606050408061803040302060406030c091208070f0c150309200d06 73
    0x40411110300704107078000140d0903c585141c0c0c404400000c14020713012540200fa03040d0244000a950b500c541154011680145000f40042c0225899044e440c01580b4100120780d14107400079000c11000340c0e18074003034950201c3c00c0500c4000494400300b81c00783e46070600c215050020740b500086141d070050900c00912204034501c1000b415030034001c07160280020301944034086103490241200d04000200b8160700e00700308601a0400010100503c074804100b19840e06403a00f40c14540103e0b950f000c00140d13485d1103503c1d0021540004904603407620000c01c42c7d408031400844003480241e0312141e0481b024015442a183c1c990301580120340055140031420604901d568242ca280c00d80b03176008a00a075020b40c2c03181c00003d0b660002c58040c04d600140700c00c0a4141d15101801042440e251101d80c0d0155607005801401e044020303d042000e07403a0040024003a519218100640e1040040c0007465480c00a41d11070503054a0902d1b180c0e244118121002001800703078450741e1081c3c581c24000c00701 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 71130667 1250 71129417 71129437
    0x11704060509013c110708090f0d060912140f0306060904180c12020105070201030c090830030601080106050c0102120f0a0b0901030305030c0a030603170a170907050105 74
    0x10701c00e031142c040e41c1038414000c1080e002d40c250401c011301e242c0d841310f16059080b0700082044d2404280c0301e4003402c17400c1200d103901c1d00040e600d07484241786400690380c03041801005900408a0652a0400c40c450301710b5414540510982000520a44000d0b1001144004c404070a000100201d0381402044000345402103030150515050032001c4000c2000c6a241c4042c2d180441070240604080048002425014017041e801070716140d002640041d00c00e0286403002414143c0301e00c0301e100c4080c895486030f40140000000c480c01910700da030103458401042040e40c3d80846c0c9500800004c41c095008880c00f0b03143c1a99126480e0703180c80f40c1101d0980004000c0c0070f441d5000c002854000910001c4940a21003c08165440b424030321801c0e421100c400c1354083c00358521000402c04250031109580d0300c0703070308001c0780e40d82e4507800c100440050107a504000c0410701e800c00024681940340020b01442c42440e00c5920008029010502d1038540844150f0320940c0405070030f0116500c04c0019103000c581d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 71131917 1250 71130667 71130671
    0x5030610090f1e06050901080f060607120503160206040b060603040302030c03040b13060e0d030806040603060504060209010e1c060906140702010f050106140702041104150306050102060601170406050901 89
    0x14a03101041001649a889444040c0f181d03051008035888492820b001002d1508100340b0b404200700c0081c0000c20300030800d54405480700002141c0d61281812644540e50200300f40502264102d000b400c035800c103a41d4454550449001c19040358000642180500d8002d04181426621601048119400203000320114002403040301d030914001c0000d07001a00c0c12101d5542c40c0c1d104e0710002c4444041b01d41c881406c025035044a4003050b214440c40000c102e82515108059554940100b000360a00d58001444130746420f040000340071240c2d01030110708100f642c810038500030071410040c5915019025501c000650701203040060b8480d4030440c41248508004664001558600d0f06002c204a602800bd40d44412a0342c1c403034012032180e82c9c0504003505290605040c5840c9c810190301030014020700850f91215030200c41020001981c000700480c00300070030601182c02e002000781c0102d1085c40c2c09840f8072004034041d50b0041c0702100c0340d1008035010302c4155403140c030340c60302a00c0301812010b0f441d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 71133167 1250 71131917 71131919
    0x90301020f16020906010306030b0f040813060201020d0509010204030213020304020d0f11030d1803031803050a081b0613030f090f06020304080601050603040c03031d060d050106030c0f0503061009 86
    0xc0c030015250080e210782d40032600c9210750050150b005402841039040600e0940140001108140c3c01c40d08500742102401d11a551460041070354418100150007030080c40000044056054004280501511805000c181c680c00300702800c0c4d00650000030b5001c450072aa400f59011241e0140d03600c540000d05c11005114991940c034040c540740c00c01900c600d0905910710301103090400000c0003420461420440c55120008000c2ca54902070100030100500c18505842421080c01c200015581020550301700312000c4c134010141da4048880c1c4143c142c1041c0396004025008200750384201c1650f1081c002c000340c5a50704075500305540707007200e05011841030080f48501000755030a02400701074004542d03c42c03c0c040013078a0300384140e010f507200d802d0800800c03000a00b202011000c90f50716060400e4048460034180c00c40b14a0502c840e5007000001c02d4400348800e86400090480b0701c2c640b0100000740f1020b40072102d4000030380101e40842c0c004c001180440c10f24a0f901d000c41c000320302e0402809 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 71134417 1250 71133167 71133187
    0x7210f0f080325021b0f040f0e030910020115090b0303130806062b020907020f03070606030303060503030306010e090703060902070803090d170103081812010609180c050609030102 79
    0x19030816504100c24410701120411019207201c11248400c1080c0010320180412501495003050f03003120140c000c00811ba1043d03995100c80c2c00003946148120418072200e1441c07202207560fa0010010301d07105500310300b030b503210241c018030170300a20101d49a0b006680c0e50a0080e1030002e460140d6050b0342603c0f04110844135a15040100c2c1c01078900c44001d000f450902c0c1c02089600c0c20b545660391071500f14480d1141800320b6003920400326503419a0082d20a0f03650010503030512800b025481c0540c007002070b8003c00c0000315400602583c0c402d8808001458648040c9603803400111a400d021403080031944c0b80318a4400459a840020380c580410a1520b40d14007000741c1e0001c00c01110f02e96004428082c030002e00b40f110003503041d403a00c0d003150711141b1014003900002040c41f000d0020310001074490841081c400c42d00e030300650080d046001c2c08130381c0e42c2124001d05052091f01021440c00c000c20040914103003400c4d580e41d4000c01401c000745e0405040048650010900582c1036500300b055000f1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 71135667 1250 71134417 71134433
    0x8030d1107050d08100b090108040f140a03050a021c0e0d0c15090f0e0702150405010b120a0b090601050f0111011d0a15020702060d0b0d0503190207210f0f 68
    0x2c20fa04594400e80d20381040b0842c0604034146400c030085049080c0541245642c4c03141d08298090f40028852400c40040c0c02c01c0d5451440d814168000f42c0104c103062003e258020000f080c3e058500e60031a21040d0780e010042d0242c81110510000003030004203401241d14000455803080c0c0d0044d01f000b04119600e0a520000b458482c0c900c1d000300341d104100f048080110b09004000300403046d01d404d06481e0250000392211100100c503441c501d0540c02103810300c6000d501404034104041c140c2c51041410b0f1103407555070001c02c0d004880304042d0340c00080784404082002c031304072a00a46028241c2180d04015610034904042d20405c0350341e03079911070441b00910700d041c080343d010840c050001d9041c1401d181d01c400c540d0071080c01005004120b00d500503150392007101da14401d600030010f503030a103100c0011607040d10150007a24601c40455241442c005100c040c250f01222a000c6650843d915800486290311001c80368a072101c0301c0302020085904001040c0200b0301c2060340c401030780496920403030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 71136917 1250 71135667 71135683
    0x40f0212100b0307050301050403090b0f0c0d0e03010b0a0e2706010b0901110d051804140702010605032808090d14010207020901090b0a05040209030a0506010e060a05010908030d110705 81
    0x36280c0c2d100c1150076120300701441040054001031300207200da46001d0b1005415110188107680b1160800148201ca510070b04055540c40e00041c002d449481b01800720041000c3c59410080307200b54a04002c03141d4502d8000c840500b201c0f44040d00c404107640f02d02e04c6500c04903a010004102c030440c046419030703030f55040c0900c17400b80c00b10f42601f58603000c40d100010b18603806161100c079980c0c480001c00c20700940040a0341c00c1c48440202c040b520034400c40224010300541c110514203241d40d00f0070b00059540641080c02580c0c000e42c21a11540140048044440c02804504610403443c5080d4004035282c13500401c5071900c094401540c8a106654844050701d5003884000184d5011519004501e0400c040c1801407020000510010102030b0000341343d02c4051003143d104940c0040c00170000d441c140080c4040d5a04201076440d99070356081c3d110f482d01e0b400c0b26035a210b00c0700028041050b4ac056890740d0140c03081d08008505082c881c2030041d00801d1040702804001200f40b04000001d1001c0000360 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 71138167 1250 71136917 71136943
    0x40806090a050d0810090f06180501080c030c0f0904030c0c06090905010b19030504050c060d050901060503030307021504050a0204020f0a0e060f0a0e1201020403050703031103090108040f0212 84
    0x2001031038490420700e003880302c035a081204000f5600148140c5c007111440050503a05890f600080c0f051602c1c2500000704101d906c402860b000c1d8420102c101030165009604071604281036a41e2054414209078880c220689a0755102248012429407030034070303040080c0d10a20a0401150f1031006407201000d06000703038000f100184103038106100c0d04070f85d805843d0040203003603242e42c00d003600a03090b002c02402c040c0a90040598500000d01030017410004166074902c05480c140c0d80711016940900a81002c0300e006441f036007060400a0705040c0001200c6c85440c080c0e014040e1107c0383d8112420611003c0c10948040c0706040000c0c0159849100410061811504403a07988040c0c0b035002d0b10703c02a92152611401003480040c001c0c512190803161016100d2034a09904504140060301d46140781841c961158404940842013107070004111094034042d8848441048688404030743e244a601841c0d40040ea100d0003003000984070f454007941240c4014240201c200301068024a410a041001c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 71139417 1250 71138167 71138173
    0x519031b030807140c0103050c0706050a060905010f050901080606010504120f051c030c14030a0222060302090a0b070c05060f0c15060a080703120807020a080d020d060506070c06050f04080609 84
    0x610004c4d00030460741142e001c0a003418412898003540c81c0240c1c0c01001401b512180e202c0c00090000d88181d8800c80140922142c02c0005507181ca03440c01140c101400342c00c1c0201d111a00104041d10001034681c0300d0b082c145d440903e40f030708000110341c84071901c907000c80d20028601e070040d0020f8000c0c0f1810280c07100260485605604d034400040030384054142840a0100080050040d00c4205040725400310b85104056910b2501511701400c051400320301c00c030317040c15102001c108150f041e002449080c0c01110a400079988600090b8403611650720000e1201ca80613004010908108020308a01104109060700b0030280c110910708040340000501c4038040001c0404c42945020120301c80034044050040500707906560701c0c0258000c4001d01c95050220140008040354030800c0050f14540d8000c4072185c907020f0246014010b134020321400b40859003080c8001c40c0a0801e141900c0e807154200b46011111803a0441c01d44651f0b029101c01e4808840c104030102c2d00c45401c21071103000f254580c0003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 71140667 1250 71139417 71139443
    0x504151d060306090403031a030a050312090303070c0f03030f0f0b01020717060f0619081c0309020303090d02040b180a11070308010e07030f050f0601090519031b030807 74
    0x16800c54504001100344103a400344240b00d031646444143c0c1d07500c51381c58200002c0c3e00d40900045c00e80d5115012010780d04d8420040603504112002c00580741012031055502942d44440312029240d0004940200c0052042451003002c64412041c2c1c081c00d178040e04002509651480c0401c06450000f80034403002034540506041d5568104040c000405050020043c910950341480d601c0c0c440c050301c000b20680d508804507006d40d94211046441001b0021b284190342e5845a400341c8a022280daa0207100b01c140c160400c030303d4024000c200720030f03034020040c52408424900704030038810940c6040c0c1e0030940c2c07552980829110b003e403281d40c100e9213a40382c5500d031519241031816101458540b1030360401c1880300c4000a40c0000e81581599600d2803014400c0c3d0306c01ea000c0b001840f400e0100c900003400c00042c802040351081d000d80c001c800a0740d0b5405041d40360020f005a190401d001c410b50003540c13400400100e22071021071100300c040110b07629852552900c460036507401c0030009590039004415 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 71141917 1250 71140667 71140697
    0x19020a0906050312340b0702031c0b04060803031e010e040209071d1201150f08060105090a0b0405040c03020310050c16140304060207230915060d090b090106060306080c060901050415 80
    0x80c410740c0c0300c1e8040c40298940901d81e11103290030300c442c1c4513107012b858a5000b02100d40d951a00000042d1103154101e039240c0c90484442d42d24640c6070798414286099072000403e1480030b50410510883d0041d02281081d1a142800c443c01201d9819900d680c2222403028140359854080c0c035418810b0803c004500503070024003c04440050b5401200c0a41c16803030100105100415002c1c111101107401601554641344100c000d08a00325980350310900d804d00300700812010200000559009904030350174150384a900d070341150b81c16109000844010b1105500404c81186420005889440301c0640c1d004020b20043c0f464016801010268004c00d00500001d184da80e0340803400b0030031012204038a140b49021a01c0b895019041100142400700d026030aa12800200c1e4224910705808004288140c204550100700544240f0041e5081540c000380c0b1034449c4c09400c0a42d1802c0010b0f04ca8984c18004008540e07101c1d60095060040c14000001c98800c4d030406680949416282c0c60080e143d43c035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 71143167 1250 71141917 71141933
    0x506010303031d0106210201050d1401030b0606090108060907020a0c08030a0201050c040b03010510030605060a110c121c03150803030403120e21090319020a090605031234 75
    0x203c850b1840d030b1500358108100c404900310a103000000e00588614010180012650b91181d4010b042c0c442d4142074030360940c402e8000c0f0250481c0d020f00c0311220b80361100703801c02c440c921501c0c000c2e0740015042000300e46a845c000d000c031500200140100d9405803eaa558445035042c29030002c51550400300e50300340031035020b02800340e01610052a051400d030504117144010b02040c00351034060004446e800010602036400351010788802030100342c9a1701e801030024034415103840040258001c606070707800b03030342024055920b143d00f030840540308413032034100d4036070003480490321000805480720309440003500c00e140030074040c00c070f0f040182d503481c0740c0340c18040c050440c0c10902050312440c02c1c481416074080800c07110558505034039511001c0614000308100d5000c0c590300c07203506000d480141c81c80d0804810190312614429912200580e50310048070040342d080d849469010b4000844000d41c44c41c07604014604851000524801c1103d0400b4640c100d4441c4000290070103828103441042c840c02e5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 71144417 1250 71143167 71143211
    0x80105010e01060f030c0318060504050d18030206030402040902060304050a03081b0a0806010921060f0603050304120f0609080304050f06070e011b0f08070b0108010902030307080306030109050601030303 89
    0x4609510a41d494007000134400c60025018408065491602d00b0000340300350040803115000920310000c0841606100e001007205940440d22031107035a410314401070007a201420945844000c01d80042d103180c0a0103026400203104981c02642c130b08035140141d4801000e103000e42c0c098001082140451b2078007600700d01c0c02501c811034071043d00000284a50807603049075401019450488499190880143d60b120800c1e00700b160500000302501481481c0310b81c0d1104901e018404c2031110540c6c4202070f6040f69040d00003e41950800c11051100302007042030211500d01c41d000d1300c000340f001911007004aa01c40001152041390010601c030600100b00240c3e04041400000741c080c600303201001811184d103841c88175041c0146000103400c840006004100b90342d0b0090000407858071360f450030b454641c4c800c01c81120b5805546002041c1290144503551030b032a03001d0f0065240c132002d5116440590401030905900d50741300c20101000520a00c1554000d42c42034401144c600301e440154540c81d850 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 71145667 1250 71144417 71144429
    0x5010906091b0b030903030a09080903010603081801030608030d0b1f230306010c0b091515010f0504030507140f12010c021c08010905100503061303020105010506120406050903041e08010501 83
    0x11301c240440d031a40402200d40140c91b003100001c801c0d949141250040c013485044a44c136502e084000014409640f00034808868030010844518103d40015001c03990640118607039544184040000f1003821b83c80552039140043c81800c0c0c480d0465041840fa6060a000b540050311010100a032400c0000303031101e5031310404052504600d4100e000906015515901820004504000c148a01c04c18031040306e040240002514491404a50b207440600e4144100ca0005560b041e03c1034450780300700c0070703501500e502401074158540b0708281d52889002c000a0b0b07a41c440101e508400710744e9241204050118440000422280300884d0041d0402a007200c007849083d40c10308403a4106927010303ca16064814032540003070746845090502150000d190041c9400d84250014844000480640b903801a4481d60003804141e0300e5009100490107400e010b50221000d140224000880a4012a511119000450341895640d59800041d140d00006065401840303050502014100380106405810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 71146917 1250 71145667 71145689
    0x406050d050d200a0605060316080d0f0201020d0c02061f061704060209180f091218040e010c030b040b0d03021c0306050d060e0c09010503031605010906091b 69
    0x845501c0da9034036104046566402c01070300c1c0021254245040c201e10411418002c00c841195040f4034250000303010548800d8449d01c034202c0d07171000d001d4a04107800f042d1000700c8054108104e8001c0c06440001c1d4600150b01555000d0102606081c1c0600c500b191030001351340140114100351410070341d229181d01203001c520a2114091110b150041c00f01c09c00d0780112030030303042d19036900c0c1001d00c02802018000360b409800d09100c0300800100350301103400356a000c00074036000e03110600d005a440c4200080d411841000b48203010242c41307524041682da101c082c00100e11010107038981c50031036001d80c0000011030741d24420311590382814800d4190003842071f500a95001c4040e18045e640c0e0581c0b204588044051010f04001c05100745c00c40d8004040c041c099074030f00c081e6468142c0141410f04240c85061007803081c00c0c402841d050381c1850480d44040c0285252882c2c0800004441c26440750549196480e801840001040c40c802c8500d864000d03c0000d0b801180e0307206584000e9107a074003c0a00c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 71148167 1250 71146917 71146939
    0x1030c02030f09061303030806010807020102070201090e0c0c2d0307020901050f1801090c0305090606010f050c07080304140a0f0b0f07150504051b060c0a06050c130602010902040605 80
    0x250000220b0780d000e90060210703500c0700c2101001800e0b611904040010034518403400108241d04201c2460040700c0c01d80f104036a41e41d40880c220300301d018821010b03000407840384003001140024052150801c92000451340303014076103d2030301d140038041d000c894400d0705809010b00c1e43ea4800c000d00e08140c40c86070040c40c03a000054000445a15041c042c80d4402c00100d00b20f4102c55656408074000c4e07030900900e2820540e034030103454008000f9509090b000c01c1c100000600200f4001c11f480c1c0c0700d400c058641070100e003502c0c4400c03900c6130040d07080e04031039125100001c100c1e0740041000e0300040c01070341051060410140c003840300001c0182c3c4200981c1814a006100b0400c0d0700c015a00074074002001c681c4c82c0c3d0102e00f0b2044001d2072684602c044030345000d041c4414000c0c08107000d041d0720840301120440008000c2802180c0c85079105051a903001800c002c000100590007054000540c017841c94101401d10885100008450384800d002d030390764882109c110705113030203036000609088580070140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 71149417 1250 71148167 71148191
    0x9050301061d07030e060c0403020103060518040f0323041505030f040807030c080d020c0d02060105010f0e0406050907050309010e03040f150210020c07030b06090c1e09030d080a05060103 82
    0xc032542c00c41480703040072031a00084456101e540202c140205885c106d41050529049449072036001c0e000503400642454070100e080d05001c0a60800d21080c0300310060702d59100e0b100e00c02604046402182000140c80400641140c40c03421025221103004030141d84074601181420f141c0f69100101c020300000740f04008440c00708041682d4815040205195120b0b080e19049031170341d104d000001c110201c0800d0040141c80d256001d05490040f8100300c81d4082400e41d4140c0c0d884800344100ca002134050204104410300c5500f2020003501c025102182d081c1d00c850000d544604102c0d202c600084000c01042420902402074450b414144030103946850b003081c41030042c560f0203014a189001010031031501d158401c000410b911030004500b1515104025191511807150344001e80e41800001c000c142a0318090075010300034032a02c21000e1a03d800900d0440803800c100115007810141409a07841545050200403001d464070fa4a07201c0030710382106030702c08956000d40310700e04140c40d01d2689404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 71150667 1250 71149417 71149439
    0xb1903020d080f2107020d020a020618030a122d0507121b03031a010e1e060f0a0e040c0809070303050d06030609060903140c0c1507060515010905030106 67
    0x480c5070403098541c0c1e141d120383e448100c1480351400b0301110800c900624a0710000f1040c0e900d0050076542c0c01c1e01c0240c040190200d03550004954069131003c8204140310300c0c1165410309400141d40a0103507240d140a90311110350b609680e0200c0c401098014110000003080c0031410410030000c1011712006520340c001c000c0250045240041c01028450504c01780c1d54003480101c4401040c00318412212800351130000d0103031074181c1c15203461820381c1d18004159805428986002c840107800040824601814002c0c042031115801d9080300d810012006001c0f0701030028201c020346600c50700e540381c144c0012b0104440d140c60030340e0100b14078001400103403d000b050f254100e0350140b42090302c0d0f04141c011030000b024560301c020078007407600b0050300410000c2c2d0050900c9034007903101c6000000c1448444c404074820b040305401d10341c2004d130b480001c0e89801f0803a0702c103025082a4a50900e5801d6860508079102034402c41c00c08501591034000729a8050240c0c0c000d03000590007030200c01c0c600848500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 71151917 1250 71150667 71150689
    0x5010e0f15041425021b1314070302070c09020406050703030f060b0c070311010504030c12060b09040f060509030f04051c05070e010611030a0801260607030b190302 72
    0xc00c004a00010280780d600c03504000203d01c640281d444040c280b5480b100d02154280216500707803441030a42001c11400864561001d29124105e000d0320f24280040283c0301a13807040c1e480415681f81c070f070b0030300151000f03d50a11460300303501c005a8034603160405c0030a94280d6403045064600404c0203010381c0d9445000d54090720b078141404550f42c4d24920003040608610b4001e681030b1240031501e51194100002c1c54021680035001c1c2c1d007807400c05107004440300d00c16400081d0080c00d0f001030420a03107517002158101180034040028110400320000341401c5400d503000e6a41c4028034400c3d0062080d18426113800c6042c1d40300440c68842d807022020802e0041d40b081c24822560205858500c41301000e81891a9900009480c070765520b5180700910700600380070f101c000903001c5000300e849000c0042147c000304069203031403c4603843d000c10411610801c10280003c08441844070310f4800c0e003007180b076000f820309440c0460210850001c0c032400340c01c2c002c5851820003000c5030030400b503110040c800e2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 71153167 1250 71151917 71151931
    0x3041104020301140f0409060c0e130e03030c0304030201020c03190f03090b0604090f020409060c0906020a080f0c100e0601081005040804050f01020f03070b10050d0b01091505030a050304030605010e0f 88
    0xf1004c0203062000900600e1f036110081c025500703240f44c4a1606034842c0c11404040802c803041e11801070b0540c2c500c411601140e4001100c2d500c10408150070041c0308029641c454800e00c009031801511002c12400c54104810300c0810302108046280d003240c00880c48084005c2c140340403c80c0000c0c43e290200509000b80020f40550350346c2540c5802c1c807041c040b691181c00e03005482030040402c1d40c90048010040e000070354000030030541c0041031041c4040f42c004d03603864100c40200c3c2011095400507405500c4080c11600314400e0b07070300e82d80e24604135000d800c04445142d40a07016640c544500c043c01c1c186055561081b2a2420040100158480041d00c05841c001c0d6410301e03000c011540140d01c0e10552071840c0e1580d110115104080080720242c0d20b00c5404030041c40250155203900f0302c080c4a400d8000280012462801804001030b44e91100340b0744952103010703d49540da00d42c040390400c840203006503103a0b00006014001c2c410030b809001d00600400e0141c00d881e1420003d81d6660075000350804d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 71154417 1250 71153167 71153179
    0x702060c090a0317120606071a13150603050c100225030804090e0c120d0e0a050a0b04090c050c0d0806040902061c0c0e0109030308040f1202030304110402030114 71
    0x259440e8a51107040c0b00616030203034189910301d2200030305a0b540d400c0100003d503441312000006445041004c00d6410159211030b00c1031786007200300340f5070a440c50000d21846210351209480004540002c58202c480000d15000041c6142141042c40c00c10305003500d402d0081d5584802822095030004440502c5146000000244c1c403142c0028540984181d0024103111400304010030519090351089095075a10300456095030404001e00c008040002c10481c0c0390b40081c1001e9040500814100a14910007070010602c10b4452000903c0c2c50040e8000510001c030214041c0811740c90380c45070f00ea0550044c103105040550b00050540e5816480e41c1c24400c100c050780103e1810f4955070002114154002c1006848181805034401c05c0f01c000000c49290344e0402c003040502d5070140101c1039031403206030364402c5080c0c25a00c081d5007005001d00112040c0c3c00c908038040c0400c80884103e00650f101d6405103549081900703252100b618049040d900c114810001000045000c4680c520300201c10b03692 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 71155667 1250 71154417 71154427
    0x1f09060b04060312020705010905010504090c021f0c09050607080304081c0c05070b06013213060c03080705131205030903161d040c03110d05120912060702060c 70
    0x2010018051030008150400d003042c0000c820071501d4801d556031191907034202c860640e515001115a0784842c4a1340d404141c04101c01e101c5003d454001c451b0401c03040c0110b6200703150414031040c50649100c2a451182d903034238483c0c1442e6038009030000041000720f07842414103000382c030b03003809510024100900c2150009007071540346030130b075010098016121000b040080c0c101740000d0156400040104c07001100c0c540081c25035070050342021951059194451100302161002020840c512020030040740410311141c20030051100e0050041d245a40c0c513180d0718016440c0c09040c01c0005071030328060103c14001c01803000720820000d400c82c0c1d002e841c4000001180d090003811482254195078150198407003166035140310740d20b450201c4661180025400502c500441c039680c2094500420b8080301e40d1041020543c4540d1000c10a00010a81c1449600359072b02c151034104401510a25403901144030000c1b4074003004001402c2c2c10034006050b0925000308001e4403a0401060607549079800b2035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 71156917 1250 71155667 71155673
    0x9010f09200d050706050d050c0703141312120905151207050c2a03010908030a090201140403050706030b100e010f210204090c030b0307030f0501200d06081f09 70
    0x202070b0a24a4008003501c2101da120880104260711035480988124200360104008040c001c048075607440e01555500203140715404448440d9020100380b03260b00320b44441c0030a0562443e01b25a0034141f0400c0301404840362610041c20310401540190700c20030710001c21300c1c400c3c0d4611088914855900d180d0f010030b0765036250700340c2d640d006424108100740b15104203d50f41d1101404c0c054542103ca041c0017402d91081402c05d170a0b9044901c0007000c004083c4089400c04010382c101721040e40c41418100c1e0300703c2410361001240d40040d8029101a4411442008940d4252207503d0b1521019940561a81d40e9400c0c0030344001c50108001e8108002c100c000071140d03101c2d45240804220903805100040036200702c5801a4026000e00b072100761030007810148160081c840e4255105014002d05100b501e182c40310362541c1d289040603643c55484040b4444402c1c1554a458466800e58010548a010010154048a040d9044400c00d90301442466401a2141a00e1082c45000c40004542c20741c0360310b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 71158167 1250 71156917 71156929
    0x5060606030f0c0304050106150210110a050403111c050a061a061615020c0114061206070f09030602030a2906090d030e03060709051306050d0201050a020a050604030809010f0920 78
    0x16105200410401d0089c0c0d00c01940826921200480d010041c410419500002c0c01540308017200d900104030108801c000003100c0d21080d801c15140244814201c18107210913820110240300100c5c0c5070b802001c041b00c20080140308100342d054665030403010007002440420b86901c9400c82610500c040480303076030200010030b0044c000d003428201080d901d604985100301e010348040400003400080b031b40002001030070000c0205680210b85402804a9200d480c4140c8444840c1060041080075241011010400c1c4c1d0008601401c5054800581c4030b00b40d0003644580c980041c840c6140000f6994120016512503090720800142290851007100061070117640701c02c6030b4241d00741c01d40111001c102e01a90810b21100c1115001e9072003c0c0106020009401120b200b4011540d101c4008060f04000d0f5102d0000b9210703a0419004540225046481d107d2506a0481e0118000f800b054200b280c0d0400a0013114180324181c3d80601030040650f0b5250341000ca180f60b0005603014040e0f202c1002c0c1c0c0c0e11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 71159417 1250 71158167 71158169
    0x2070614072307030e0d080316030e030a020a06050a090203150f160816030e03030f0613150308030a021e090a0f0302031e1204060201060305060606030f0c0304050106 73
    0x86080009591a80d6141503104040761140c0106465400b285800b000d040b2002d044050381c02841841d10304180c1e019100100401c003500c0c0c100d5410984030b400506950300843c000c0c4150490b078003200d22070400040540b4180002ca00194106000d50050241c00242105069a003c0e2000c03955a480c17922a030028922010082d41c1403103000401d2003003105040900e0b00505e001d0740c0c1d2195940e50b0b100d95100303095007842700f00d00013042180050b18401054024280d9000c1503d40414100d01030607910f4a585c1040c1c035400e1541d00014140b00e041c0c540040003041c1041104014464201408015040c0102502c0060700201340000001d610050550445030720b540052289050302045502c80815504129800ca0103002c50b084081009010741842104407540140201550540001e5095003401d020b0703021500361040c54003410342c1040c200c019102410a40c0d00000f0600d10390b04046280c000d000c0c2c060340c00b625040060040f06004026400e510200c150030075a030f2600d443c0f03800c50052243d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 71160667 1250 71159417 71159423
    0x1061a2a011503030923060403080a021903210c05090d020a080703051e0102120703091103011b0201050a0506030c010c0503210103120905010f030b0a05150c10020403020d150207 78
    0x1180c000482010742140b03000042c0e0300302c51101c084c00c40601d220681440d00c4880613540c1f001041c0010000204504000e040304002c0d80b06589880449185461540d007406004502082c1c40d010f01c158141c840b000400d181a039800341c1030206003007941018140d44544400c81d4059540c1c001040e05540b540f8080400a00b8000f04442d091582c900f01540c0ba03e4041c003400c904407599209000f20203c050007600c40c0202c1a0b8211b858640f00d0301c4050f001051100c4003103030403101034651012165000c2c0700300b0644403d848a000141c1084800c0242100c034010804811140780901b80021510700044117950342c0402e003444611403102d804c205107035008103540a4034178001d0b000007005d41080c00040d64100ca20401007504413046100046d07501410710300509002603040229101c2440c4a50000d181100001e44040314054071030000c15a00380082d00c40c50090300c030000b8141c201520800065400b00500c4400b1130400381564002900004403400241240403840810004003002d581102d13501e0354 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 71161917 1250 71160667 71160701
    0xc020d03020c0111150a0b12010c080a0b030a0b040210021c02010209040b1804031d091608060d0503030402060a0909051609050307050616080c030a0201061a2a01 71
    0x180514000b9a1803070300710300060006100329119805410700290031020b51407500020000c95982c050207000400450b020194841c1c0e410081a080c52028405c402190109542e4042d140c40c2001003a801e5602c4644028001d81c807108a07000816005100c542c2c000388c0c110b56240c100300c80c0c9101240352003070072107039421301c3c4000307000440080f5015401080424420341d814018a41e005007088410100650251880b020080004001a214045005110100c4031b4205c7e001c055000200d43c5c00ba500b2031745110312840c2241c000c1d01c40b40e0440e180a0b8007035012100440c200c1e41c00c0d078950b5141c4c00080d00082c09908003144c400400d90240148102502c500707a0204442e18110758a4540184445506c40205205031000304a0b420007154900070365501030800b602d0401080c51060344410840c1082d2440032003032008108000f4144000c0410345862341c00803d0090500c4139095004c4504107880284810402450481440010803645044413a20210440c4016046c145000d000b1214511806807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 71163167 1250 71161917 71161939
    0xd0f0b0306090120040308090d0201050d022704180609060216050d03060b03061c0602070209070c060c0305060d11010915090f050303040b040b0f130306061d06130c0c02 74
    0x2103815400982090000352149401040004c0d0300003c0d4800c90101038005203081082d80d030141414007161040354410702d891440c000c50410718004a81101f84a605040400440500b05042e010404501c0740c1d0119810041e90783d502014000a0f8501100200742035111112a801d000b81d03541620000190040c92420b02029403810365103503400d41e9010004245011408500c4210340303015070307114280c05031903202c4810480382d0822109015030070444176a17808214820041e05d91303410030340c0140502d86552004035402d02e031043c00e0b6a02c0b88441410903242c00b04105203540c030968401003503608400904000c81840340100c0d1000c02070b801c452541c4541d424500343d0107600c032155104036421000e07801e0300b007501d5604054680c0b14074840d4115801083c40300748102100000100040c0304c05040032840d100060151100081c0c082d80180c50143e5a01c00800803213a4034010f0051191120500d03061516207a00001c0038128041c1c014650b450741d95a2440c0028014620040010b400a0402d0015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 71164417 1250 71163167 71163181
    0x9060f1e0305010801140402091f0815010f0e060904021c060501141905060301050922060603020a05010c032106080114160804030c0305030c0d1b0e010c0203030d0f0b0306 75
    0x1801080c03050652642c81e150046e802c40c91070100c2030b07014039030041c40240301d515044018580d040301d203a403100c481e4002002c0000c50107010480c80e042d2080e40488980c480d03241141c2c041c845031590340003400940e000d8003084480e42e1000d035555401581260414501c040c44022001007082e10303a0000c0030185814000f15000e00c2009220398642c400711340360600c041d0648900d4003440101e102d1950080c0c800d100500180c980b898240b5031100b031b9002000c0060801c4040c0d0082001000010740d038081e9502014025424080056405070400307003441c0c5541d5810b0381d4010144181c2c01c0006039441354000551217148250340001000b400508000d0084581c900304c50b540820064074000e2503041e0100300004018011500148180c3d0143c40711007114040c0d407001d8503103a0005103501113100d41000001c2d81c0c03c4452042215504420003031164505000c6030281101e01030040f49030511040017403035001a50000112000c844a9810200307100000400d2000a400ca080c080c0b40c1c103000f510b0411240d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 71165667 1250 71164417 71164421
    0x9030509090f0a1b08010e040302030c0a0c0911030606030a0c110d05030105030d0f021002071e08030a0c0206060310090f082205061201170a050615010810050109060f1e03 75
    0x20515508100314001d800340301900c900903684c00d800d020900c0e000c01004541c4102c09060f0303105020740180c07490030748005203c5003812100d040448068004203010700400f0898841c00880003102400e180c81c2d4102280000c0060000401403140b140d11250001b003403c0c4980081040703030200008480c00018299005041a00240151400ba22a40c5002e0a034240b01d02d22200042c00d45070044e007001d141c01c1c44c10348041c2d4031402050719030151501c2040d0300220055000c3d490706003e00c50305912070078100c0449003664820f0035494119440315051048955011542c034440d0a0200000160112289014204403c0b011805441c0315408140d0f040c1424031450f00e8001d215005440422780f0751200c0802c5801c1c05200560513140d150000144000e120002c000036100e06803604550440f0744607520a843e020b0308580c10310345251440007948103942c09c01e03101500450340d0082c0000b118101000280801100d2044102b0046040d83c442c9005014042c8400c0070000280052840800d410020300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 71166917 1250 71165667 71165671
    0xf0102040b0904150f0302012d0f0201050609040c120302070b0a05090901081f02030c0913020a11070b0a0525030e1309021f0509031c0e09041509030509090f 69
    0x3010300d051018452039131401c454100300ba9000004034103200c50968004407a220a488002100f1480e8512144400c40c4226070301e003080c2800c4d40d10a0206054442c00a003941c0c13000e450b1300d0041142105020000d0454400302040e610880540140c0e0101418200c0c078000c2d995205145149001078a02c0e0441c0d0b0110081c0b0062109030790301c0302c1d9a41e131002c40596034640742000154026040c0c0148030303000519001180c00a540036078040c102500140080c00035103210703e0f40e000482d0700145841100d9000003144c4607071411100a800050b14140751801e0342d110b540d408104021000403100382c0c110b004103c0b2909041c00704041c010481c03240c0703070240c00e01c0e00d0708510603c035207011400030582d429640a0210803d070f010b081401001c5010042c4011203119680c510280030f03043c0039222460300d0800688402c0710310b4060980c03441881610180c60a044100d0780c03400b07140d0a2040002041810107050780c0354429840001d085a52402c2c102c0d40c5005550030b03d544420f10400340042e010700c03030340c01178 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 71168167 1250 71166917 71166919
    0x17030405240405060f041d0603070b0f031302030f030c0102030a050a0209010f080403020c12030702180705070f02010504030c030303150503010c020c0402030406110c07060e01050901081501020f0102040b09 90
    0x142072500c910369000030886a014052400c40c10801403005050510250a0000540711158145911031807078028510440c4009400d1880403020030010b450304201c030200504110428919010100d02c12a000d840001c3c204a10162603800000c2151001c00c24400b10203071074000d683d15a030b0030340700940c00303584103071444501141004041501c001e107a108441104030140c503662110441d800c802d45500800800680135401000000c44064586c2c9113200c0390230320888080c40c1d4132401c83c41040628040307643c0c0c1d000745100b100e04100800c6e420204580c025500f10f41ca841d40000a07100407206881a504014503005881000004241c1c242d0041198400940700e0042030316240c2c000c1c14222341040240300b0040c1d000320b4550001d420254003c641050007607002190981803000201980d602c004070701c1c42d0551050400b048800d0780302c00d051222410900e401440c00c0760800009042101c00f40c05114440c0c0c0301d012810061703008003c81c45010301d41800039500c941c1d440d000286540c001d12006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 71169417 1250 71168167 71168179
    0xc0f020106050907090512010605090c04050114160f060e0a08030406140c0d0e0106120302250e01140d0f03030518070803030708060a09020705070f090e070311040617030405 76
    0x4102c80c50004401c500ca2100765032250346451a00c001c005028404101826503551ba4030408146511f40e000601e100e030100c00ca01550304c51500b000181905940d00302507000c0402405460915141034100d010302c0c60304015011f440b0316150030010010f10303a0b400010000c2c814410f209003045075082c0918450740c01200200884802c11041080070482180c1084000404000030000140258403040300040040000500303280c1784c00d084101d0100c6101c003030300035038020101000d03084440c500a140c007d00480140040310325042c10012140c030103000300c0072040c48009041315103464440c840b01c40b030354101c06014100b07030560038090001c041c10750320008914880011784840e050001284421901c200d4006e40c915911078108803052200900100d500c402c4680b000107911841740007070803640303005102070302e8654a0309101024079020f50b0321000d44141041d500303400968000c201501104d0700f1029207114961103800203002130104da0840382580b41c03010b8100544800010152080e10016110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 71170667 1250 71169417 71169419
    0x100819020c16030f15020306100f11030f0d0b0102070b07060902012a060b0102030a05040509060307180e060114030a0201030b0406051207090f15060e210a03140a050909040f02040c0f020106 83
    0x5da4060748070803501c6903084003000050408035031147c071a07141f00d00300d245004440c041c01c01800300d0441c1d01c8203100044860000c10240e0a8900390310481840001c24002400f14a01e0000c11420901440760302801d51542c0d240114250390090b0551240b606480b0075880501c0003524040c1c802511645e401e445045c9090b1300340240b540000304541d04007141e502c880d820545030400300444054000c00c41c581601800c40b000036000c0f048031547d075032144403910120f032214460701c9440c0340c490b05034007588440280d21404100d5403004605450050b4086c13070045030074807061000c50302401d0250720094101200084400d101d1501040a00035613007040748c207206030381c1c02c0046c40e01594820020003441d0022800c0400901e4010490400301c850050100143d804803280c02d001c50a89160041d0326a0b0050007201041651000b42504a4a00198801d0038984409001031050050440060003a00900c2c00f140074045162900411564003c00500c41031401c03034401008540800811b034090341c00d00034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 71171917 1250 71170667 71170703
    0x220602011b09050d02060306060706020304050d08070906080703020a020a0510020705060606030c0406110c1915030509060718030605010801020a080109020405010203090f1914100819020c16030f 85
    0x4142d03003c90f80024000483c1090640070401c0c1075102912140e80102c0400c0144002015030000e140324501450280840e500b01400140035010000c105a0070001454018030049030008042c40d00944207240040e00c980400400b81d07d011460240a0810b102e02442c04100d2000383e0001e01c0034070711582c2942c00c9506e90030203028441c003060341c16400c5210140010b02049104000700c0c0114081e903070803955045040d0000c603031448808a441000c02002032818000600241706008281e080f40c1340030410707490104a06034850030090070000420212000414007814141d4041c0c01450704546c081009581d07c07103a550003503010b83d0042c80401e41160002980195610036901151410f801035468003000c0c13401c001c010020780794407680c02840181c6ca0408001045800000340c9221812290410980c01c20007240c000f5800c4034004015032079007003000d00140f000c09400204440d0b040561900b408001c1281013a12204800401c80490000003007030050202c035041000c0c0c05040d2664080c10402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 71173167 1250 71171917 71171927
    0x3040602211f1a04030209060307030b010f0312020c03070905071103220501021b01030f1103131401090c171e0303060a0e010b03180c0409050109061b0801030305220602011b 76
    0x2910a0b40803c8040c402000542090840141d00110040685007505d881e90303913110ba040c0e001e030003040600c41d40c0b800610800c0b089207400d6420207607900040c0544101341c1c00180d83c0b03103000e00404007000c0c1c035107000c604858007540c0074041981c400401c0d26200c2000d65080f440107444a403400040d02d618000000d030650001c500a00048040b00c0d28581100304403005401421140d41041d000075550b5000803009003a0300061760042c000041c46040a0420307052580595101600c1305401d645480e04d440000384060580d44125905d0309c3c0408403074540005218181308454070b4035031064001c13218418a441c2c000c4000c6115050445400403c42d46403549086120030034040e0640ca03460400200e0145210421090403000e42901100d419004080114007910b061003400c84890b9103581c00101002094004d1480c0381240348820741080c460390740001d0603c14188000340a100d000105c00084c02c00d02044800c1c000d260590700b1001540d80e0031700a00814036541d8a0791040e42c031180c282004c0780703d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 71174417 1250 71173167 71173199
    0x1212030f24170312090a080a05030601090b03011202091f08241605160c09090b090f031605030705120c0f0f0601170307060f02070c0f0b03040602211f 66
    0xc1c0003e41c1003000c100c2e12044c0f407480280416045105120848001603081e03c0105075810755569555100d041460015164000f46d40000000190900040c454216400340c4501c0640d01250000c146440d00070211480c0040c500f9016507107000c0100209030702a00144054944002a80c11b80408039503203c90f20070110242ea040185585840702c0341070b904c0c42040038050018003104070b03180c42d003d103039140319441c440c40d0300455200d03407101c24403800c6c4481d081c0e40a80c02440b08000c1c04541c2e941801c0251284111024080c02d4401420600f003401010010303543c84070b0f80101191180d0b52001c2c800502500016803d1000d8407030148400309a15002c07070808038620800000700a26401c20f1400c0c503401880d021150300c03e01c000c1c07003544007190b0580039055915641020050341c403152818948044911600080544141ca04080120800e0902140d0380560480b4005803a01d20800d00c6440c0344000030411281010f0550600000400000c3c00244c8418404004030405584a125400500321 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 71175667 1250 71174417 71174459
    0x6130207080a0e130c02010b010f0318020405220b06090603011a0603311e05072102040e010507030507090302090105060a020705210706091212030f24 66
    0x140982040c03680140c150103d0100014031403c88000f01d519101c1c12541c40b1000100143e441d551510717525604101168058012850103000161402c600310312903078103508000380101e6032100010542c031070000e03d200c6604c15003406001c880f2081c2c20010b94801c0e0030f8842d50300c42e41301440420860702c0c052080005001c25400c0900a074801c060820885410062000407a001e85a002c11400302c03c2d92010b440c2205040042c03006940c903418119a80c2040c45203100c0702c141c9d80301703211b00854000610101140d9610300010300404481121031520300a40000a411504010303c0c000910019080075100f20300955040000380d0b02e020b0225103120036480b001e500000520700500082c1030540080c11890050300480350308580e80c034082448007403c001035080007190b00d000000d046500303002c41c00061807039140070143c0c1c0e41402603001c900350441c50007d000c54003508017480410b009070403640002c01d40b05020000100a903501c0c60924510a00807611820072540c040703002004c5110001d2021b82d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 71176917 1250 71175667 71175683
    0x80c0105160609030e211002031b03060103020d020d0f0b040209011409030f0d080405070f0e0c090f0a090905070b03040807080a110d031e0e0d050f04050406080606130207 75
    0x114540b10702000300782200c070507010000c070520044040d894860f0700c4103210860601c4c181d0f400301e0010500e400c1100c042c80b2482d0309030041041c0001c009214040005080d011802e8503542e407203080040c1d00912450840c03403180c83c00130410403000c40a0360300c107071511200f210050081402c2c4004000032480703a00c041a021509892880000303041d60000b0b072854903805421100b614000031401d501d04090032484000203052901000100038040c051f80700245910a00c1c0d4100a092400c0d007034a1071340007015103403015800301c0c01d41c2640c0d4800c4900d041d4020082c2580c03018613210220304015129040c019174882c070814000188802d84007084030701c20380d000354005050000c00d9a440740941d01407030100c2c0401800740c800c01008070003071141030504440ca80300010075003071226501c2c505e804440d003006410340c03901e617040d80c03a1400811886540c0302c10346080c0303548101c66043c0c5030081c0659041140c02c02c1c07030200c0104014400142d0580036240880b0440c81820301046100c080e03124420005003044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 71178167 1250 71176917 71176957
    0x30d1d180f0901200a05040906030602040812030601021e1c0801080d0c02030a06052a07060606020a0309060f030608010509010e070f0b0909060a03061e0507050c03070b0705071209080c0105 83
    0x404d59003e4103e50b00e841c03800c146420307a60079401d019580780d90000d665640c0d0024007042000010002c02c49800040d410f00c078110700d49800042d46400004000301c9440c02c104051200f0b200040c49a4841400071500e0510b50104405000b0940c00c000d0251007000c1c4100322030f1480c035500400180d91407030340c020002e004a240c1c41e0345000c050b007005000c15502c00a00d4070f503c9591410003402448071207c54840036280e8080f414a07070159038103035006c40155081034000c240801d600c076041784156602c9040c042c00003030f02204120000e01c003d81c86000654a8182072114481042d04203000e025071401c02c1b188950740f9480c00f81c0481c61540704401c1c0e41242000644a81c0c103002481d540d002400402d0304074806d40e41d48903101030300c1282c0d04844183d1241050759240607140c1c0714060300300300c05180440c140100c08480b030340d5030b100b168800383c001d2401100140c201840b82040300c44956100318119841c80d19220003400a510034040c0c01518042c0761900405548603c003030354811010a245801d01c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 71179417 1250 71178167 71178221
    0x702011e0b060c0d031e1e0509070906080309030105100f03060e031201030b2502030d1d150109061e17160f05041802030d1d180f0901 59
    0x91801d1540d25400c01c0003800a204286400e01c41503080800c6602c4c00300380035041c6910f0003000d000c4003510308029850100d00e80b0600c5805600c001480e0203031000098681c0f240042e2500d01034195100f1049141070080209022070044003802c0034000c150002d01070f0340c49141a030700c45802140034884801c40f000008201203581d98020100c003600f0703401928a441030b01c1c00340000500c0c00b41c005039000441002844000302a000c0c2c036004054442160800865030311a000b5104e121b011440c15002e501da103039424544003440c10480e800380031981100e401c4005500c628111070030034403864855914000c0001001d0f82000c8a46046052b00e2500c4128a41440100003d200e404200c001003072140c00e0201e12901c2e810360f92640074100d41e0308040c44035454039003000142c80c550029841c0011032990f0300001610006020410400c203810840c01d48681801004030090341b00b0300c801d03800313000700c203d121500c41d41e071002c5030098034a01c003080000d0786c0e0440c0380b40c06d0b10305c043e084c030b092003840046042403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 71180667 1250 71179417 71179421
    0x3010f0203040f020904060e101a03062418010305010c020f0a0c03061a03010c031b0e0a27020703030209210a03050d1d030c0c150307030507260402090702011e 70
    0xb026210707150009003012300c08602450a6908c08195515590b101c4030440036140c8103a016147c1d8500328010074681c5030082510442400c3c400b14180c0860101e1424011a0381e96407181040241140e9070310515a928200786019084070100342016008000c141d80c0400390120310a20780f1034000240c4448185507544c2c401c020041d043d103900c402c1011801905255400b801803221002059a010070010380b2000c2c481d81c90000344501d6030038000042c00c868120340324503e01604035060085501c000440b1030416080c07030042004c480981910005601c001c0641650182c04891019240000c002c00301e0f10008110640c000f90405080e80100031010019105400510030203001c0100403c00d014040001d52600c0d003000b02c591030315000454a01c81f1084200981e41401c18100c85102c0210032000000d20107101c0545060201501d481c000741c4001e0190100c41c40c0d403000e0010031405c0e03004981a40000300010b6404900c10740244010401c118414010010040c40780f002c00f03403000549090000c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 71181917 1250 71180667 71180671
    0x30209070c0203151b0a0207090b0402090a03030c110a14090907080d02030d0b03030306060d0c030b060304051b040b0a0923090d080106030612020d020a0b130503010f0203040f0209 79
    0x41040141c20382800140c40900030301001c1c2012400c150818244a0003407034079010700042c0a48080000c0c0010050306070700059002c100d41090b00c00003080101440810082d204410001d6040982d1041c0041016030000340420f80134011846030300d0850058040180b5a00340748190030000c045007100888902e0300c01c040f240c110400c0d038110f8400c1e99951050354104090201ca20380941c0012402448240d00d60155495003403084020b14950326008000400701d01031290885100d0342d841e280314040d54000d40c03211242c0c07200200301c25101d140c145400795482d40307085024240384640c3c034506000c6040c00d00550400c3d4400038554403040b070511510710020540501d00107030705401d901d40041030710403561106000310b0247c405080b600d41a100003070107202c01a0b000ea401c052030300004101d03c07080f030044011004d90480f1003c135512800d0001411004a0f034000b0208482c00280f60013606039501411000c0f20020f400030f00a00c60003044241c22404203c034080c01c0c0c8200c0d03029030001482c241401e15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 71183167 1250 71181917 71181931
    0x14070e030d0806093c01080d200c0901090603140606090109150e0405010e0f031204061d1005060a060804110409030c060203070e0a12051b0f040e03130f0b04030209 72
    0x4040021120707200b038a0040301a900d4145c000c0260804009a00d612000750150042000901b020b840701341004142402c0c040601c5031018410f800034101c0181840301040002d401040280d036961100a4031008041c14441100c07400e43d00f0400540414012621038480c04005100c860560703e00240c090280c803d03c0d01c00c0c28038182c55100440c103600c0c2e1741c040b2070049008100004031640980c22607440c0c801c3c8070b0b501000c6030340148440509403040842d09548aa42710380c002c5043d6603c1040345a45402c243c04000e9940108444031034040181c1c1e0049110f00003c8038000c03a43d0740e481d1000d0398120015540500b00c031002028050041c10720340c101d40e200521030707d0404040c403034a8540070100d8009a8400000500d0300500400a1400c0c200700c03006000300d00c800d03030031a50440d40d500c0d941e802c195511070b118081102c0c405086a844900c02d4001b070002a01c1808400c0800d07103656100d42c0208400c0300d03d02c448800c041407400d001401c1100340e07410780001a19080c2190200441c0404c001d26171 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 71184417 1250 71183167 71183191
    0x90607180302130b090609150f0a0506030702100501090209031c0c02090108070306060b09030d0c0305040807030b0f01080a02030709020d060909030309030e031c12020d14070e030d080609 82
    0x1a1110300c000f0640d4002e000c0000f032509000b03402c2003541c62000e05000d1095030320300c0038000c3c5050381e10001d0302044802c5507a50906194030010804012265100310360102011042001c225000309081e4190502200d0400c081e03a21103400a0884c0640b445035601517100840d6140001d0040842800000742e60500044810003540090102c0c2c0003600302030b03500d820522080081280c0c60150768050801d00041b1410441c3c1e0501003030303441c203c0000040803c0382441c005003d150240707040303c010304400001d81d40c020b89c0ba810045c4e03059209540c1c22046c001c0103400040c0c020004a6807124003035000f4040c0203190301e0201c2e188040c1d080014000c03061a030701c8200003120142c0780305901c0f0092080e00d010800101600b400341c1004160355045000c0d400c075400030054210610005071700341506080440340050101c2d903250003806864406d81451745849110100c0e400011002807150585582380503015400c2800c0c56210b02e2144d814802044e02e46002c65030320b250000342d481c0d1000066001d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 71185667 1250 71184417 71184419
    0x5090f01020304140f030406210e011107030e03060903040308031008030a0c03020c0a030510020f0f04030f0b090a050309060706090c0b04090609090b040201050f0c071503060e09060718 81
    0x4960899000b039804464848551a054000f03140910046074103800c2c0001443c24140307003007405002c140d48002220f20422420300c0400a04010380d2002d4a8006080002c0100007070001c0c1c458080d0780404025004140702c100011224600007520a1042d805c21019506261440e50703a03919640018082043c60402800b0100f032045082010301000c1e5680d540302c0a108401e418041e05180000d440035000e5840e96100b0301c040f42c800209030460644040005030b890440d0f8190340721902840b14880c418000c009800801e000001c20304042c001e0040030b10001d01d41342c200d000c0c1d580e11785068004210350030900c4459403d01e49000542902d500403a40415049425a60700c1003008107030708059100d080214052200c1000f5100c1c10700a00840c5804209200058440d00030221008000034104080050f2242d40340210009444034151042d04071400c01d0703204c0074070b00204c0c40b01800c01800207141110001d80070106613103a5001e000c644000d0020b580b5509800c8411201d0f5040c149071029411034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 71186917 1250 71185667 71185693
    0xc0904020d0b09010609060503010902010906050c01021b0105100b0c0607260709080c04061419030210050403060f02070b060f01030e101d010b0105300f0405100c0509040509 76
    0x6021880ba843d150000550700b42070948240407150b0640000e4000c0e03142c0050080143d070040d06e0301e410b9650900b0110b0b20380303142c4848640688580342e80c514150454210b0500744a005401c03031405180c81512440030305d900c1e04032006481c0544540000c0c0c0d50700540115000a0003800c0104d0f404103082003c0070a03010301d51034000c0000c0c050343c2d1000010b59a520401c9170170010300094020110455082c004185056452400e0300b204109440c800e541d504186007040c0114202e16004541c0039140d21040c40c8902c8000e400789d0000d03c42507400a05040c0d01440760141d42c400c60302826440040619551580c0c0144a400c1c02000c0b41541815034400c0300c003018103001c1000704c001190071a004218440083c061400c034010382900d00105030705085110200380c2c0c10200341c8254a40d02a03068444c0c00d000c00601c60f40c105517051a00c23189222a003131211a00b5142c04d89407040d0b000306c08842410184110710404c40311341a46001c00103d0a20a8001e21f02e444d400042c1c002c4020405c1710b440c040c0b006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 71188167 1250 71186917 71186933
    0x50603191a040524011404090f0603021009030507060e060f09010c080d0606020c0a060206070f0207050901261c0e1311070b010b0301050a03140f060703060503010b0d02030c0904020d 80
    0x30300c80c520006451030459010190010a613005450280f910808a2008615400c000d0040c1d004e01029162143c035117541e0b00607141c0c05100296001842199905180140034007014002d0001307aa090103039000c042a0300d406084100b428110103440d003450002c142101c1e2000f42c200000f0981000b07051070030003002c20101c1c4060b186004000c540010f519180403c06841c0c01740440300c00380269100c0f0402c02c0340b2500070031126070180072400d20160701d81c01202d00b20f040c1841504165444940302d030000c540900e0305001c844a0308441d1910021f900d0f000410305540700d15807032902c06840724507501407950620400b402c0750300351800b410b181401c401d0712030020161454034014400c6200b012554000f0f010101d0f20450051006100c400d01d15414400825004101b5002c040d0104600c03204441a0301020482c044030002040d066803e9030421030001005028184100c911960905006412a18003003d4280c20b072a8000e00424990f01c1020500041682c0180260f074480820259040410010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 71189417 1250 71188167 71188171
    0x30902090108010b130e0a0b0402030f03070302010b0109090209151c05151c0507030f0c0b0a110d090e0a090606030c030b060420072406090b040501050603191a0405 72
    0x8100115110b290316061103400748068801d08a021b003070000040440c44003003032180c00389401044049107036580d400468035003807102582c22500d04c00011b4100034968190300800c0c02034800d0340d070010890354500d4120141c0c0038000500e940450408880030b039484120000b021003180c0e030383d285000d0400410410040b039108980c003640d4003681c1d840540c9245030542c44040503800100d45041300440944400b96141d841e400001c120210140046d41440340c24480940100750580c0f071150782d4182c8800c01006817000112401252180c041e12041241c01a0ba1203020b0700c0c540c1c5034440aa940e0481191b028007145101503030490b0f501c001c040f0100e04982c04520145008886c2c4401904108003030008940700c030044640728103105402d01101c003901034100c2d0034250b0442711a0f911602856820128004020044410140752050004002055030001842000b04440810440c1c5e66101402420302c0100d421006e95079020403900c0081450f9806601c000c042814038280044004e00401d04485007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 71190667 1250 71189417 71189429
    0x503030103050705010c05120306031e010b090a1109040b04020d022a01200a020c03010c090320010906110a020a1805070f0203090609011b060203090714030a020607030309020901 78
    0x8014010b100c01044001c000306400e00c0c00b84918550381d103425032514a210301501070751200202049142e03034100081c10b03551000c0c00c0c0544d210504000598003c10815441d1130152522100240c58600c0301c0c441ea074030620207070000a1910f80480c0820000b081c2c100c60265202d40d0078010404608800e2015000e0b03203030004080a8005548943d8074410320845000c0c00c0c1a07030500000760802d00d100e54404108000a0549a895205018069003003200d699500780d010341c070309404d0310360065005110b21300302c0e4015501c40419501d0204c0c4c2820b402d1107052000c0c04920f0741502001518414440d400000d003c034010340d5825295079002440c04081a03001e01c002003040420104045c005100382c1c4d400040c3c1c0c2c10041c0e405840008040d44038081d07808c0e0b1500c203100100749180d0690183d050641603042c0c502d181e00328105a0f103040c0d8000d40003516030b921a40f01e04540481d0070200040d2200c13400400400800208205500300715599014046c11010952221104401030315903c09450103803007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 71191917 1250 71190667 71190673
    0xf0d1b06080907030c03030f05120f0a0b0a08070509060d061a040f150b0d0209030f010218100c0602030c0f07050706020d0c030801090e030f030408031006080403121a0303040305 78
    0x89030010007481d2490103460540300b504803943c2000040d203d101c0e901c00300c079414200380c421340400b904240d0313090242c0502140c44140000402c00c5410494078494465890b1035001c014804c00c22003806405640c2e03024215150740081401c1c8440d03e491600b6550040c0018031100c1c0e030032015980d41d02500d4031003d0b80305030944001c4e04c50003286081e016001542075890350030424003d4038690923080c984184558140403100107401070403052241c046802984003c1c04541c0d2118180c2d940600035440502086001c500c0d1000c1c6604511b404a0000031020a964900707407a0911a1500c81c025400500b40c0a03c401c1e041000c00c4041c0d2280c0302604290380964050a2071514003500a0708201000c1d40e94003c03c03003107160a00c0003c0e00520101d0642e01c00380c400041d182c240c10516850343c81424101c0c070001c0c1c00442048200865030f030056114400301c205207442641d9900e0240d903140310a44004000c1850010716480406260340400e4451310290540580c4070f110901103821a0300075002a81d450b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 71193167 1250 71191917 71191919
    0x11030a1406160c03020d030f020415080402041503020102100b010c060c0807020105070203030603250906031506060305061813020909030a090e01030c0501050c01060506040b0901030c1d0f0d1b 84
    0x44602c03070002400d580c00c004040da0100e94000351201d000c10441c4081c140e44111124000d0000c0d416600507100c80d0389004c10f400c0743c0c008050030142c0c0072a000c920071820400400c00c8100020906001c0303039812b03001040b003015001400d0b005003510640190400501511440100f6142e0003901801900354072103e010b0700340703914000c0c00d4a2008021300159401082400f03900e85000981004802c16045040c3c2c540704c045100f07880d034212541c401080e8904056000c0107200107590100d40b0b1118000d03040007115514030044d400e4440459032254406180000b2007000d0b540c030907042d64000400c030740c1030040e020540d0024030101010348042006510125480300010340000c405800f8005241085080b50300d540c0d200b00400006010340f03810000301043d078071402c0e44250402ca000d040014107503500c1d1901c556108149400c24415180000c0c100f800c0b010b038281c0645c0305005050b0065070069540321079003040c0b1a00c103010304407803900800c0144008011071030000b9000030600c0218404e510f10703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 71194417 1250 71193167 71193181
    0x6030a0b0f0d1e02010201061706090d020d0f0c05240603010605030106030c05220e0109020405060904030c08090a120b0103140708151003150b0406090e03030411030a1406 75
    0x42412059070a00401c911080341c030101e0030410310001c2c103c070080e150044903070a03480104d02410850f805201c40d02103030243d803280c40c48041040792040000e04101d13040c0d101e000a0481c2c1e039150300035000f0003280131166194061840340140300b1100d80120111881c400a503c820710308da200003003100000b00b448409001041ca0280591001008100c000740009401d64a6070301d0f90200600c1801e10805208100440001001007810305007944108100f00c1000d600361441d0203090901803c0f882145440005100c42c5803509116002e00e1309940c448507502440c0c0e441080b5039211070340290f031040e840c80001401c803411340901c0400600c6075613420225403541c23030074003030144058600c003040390440503040c8038040d0b001807e60051440b4902c2c6105980303c0400c507102030400c43d04040c020181d60304040c0b5502151340c00464510005840c1000896a070724a200d0440d14200300620352500100301160108840d02c400003807107030004050310100c094071754914551905055055075990400d0040102c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 71195667 1250 71194417 71194429
    0x130305150403081b0d0b010903050601081c09060e21030406050408072c100b030a02120f1504050405010b060309160801021c0e07030206040f0509130803010303080a090206030a0b 78
    0x106003102a00e032800d030000344084c0458080c401c404100c40c0d90302c002800d2a13030f21840c3d82c2c40c010b64211045d9012540c54140031502ca1204800a8018420842102e21407500c12103100c01254100d946a010254078001003160100070b0070181c1094403c15040c010540d01c06200902c02480585c980580d243c3c80c0950203030816a1651010b0326418440296181d07c400c010b07940d5030310800f820f032095050b90303800d203010302ca5500035045001006c102000b0042c11080ca50700410900080c904079807030f0f503522032140f00d0700680111401c015050700311184402908081e0841500540304138000b0611007042d001188254000700c0e0002d2460348112140e86211921139001000740c14510029403400c0c0b911315840c02910706904918618940c0c03444407000c1c1001c20710000000c3e5600610284d5926a00c6810101c4100305004680c0f08110b05408141202052221440e20f140d004003002d05584c61903d05540f20940203044e0308d00079071a03551910042e0795038001144181c1e00300c10005446001103080c043c0f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 71196917 1250 71195667 71195671
    0x3020f0d020d081c0608010c08060603090a06110307020606030a0507230d0f290103230a0501020a0201140105090103030e120f0d03050711120f090310060611060f0c13030515040308 79
    0x1500c2e905d00340c01060840d03808030327441d40e100c44c0560700d2603039079101c0143c0c1c245071604110740038000916250010030003181c550f005500071030103039084a00340c0d10b0780320801d6140e010300e410080441e8840c5d80100411303900044100c4861a0b10209000c40206490214010080102007140d1040314000000c080005060b0203030010700701c41e01d07810b00512000e035295002c1f0406020140550000d42010250000c602c02400704c5044080e044d11455400e529246000c1e410404001016509040b0302460b400c50703c482c010304071a00101604c0c02030746142c600383d940301800020550042610007072903400010810020700f050484000034455000881d00c000e0880e00080d08480030003180158140d45150002801744100e650070817807513982c40c0b200c155020f041c840c640c5025050b0068050850607600340e40d202408a45464880e80031100c0400c400076101c440442c0e05400450704070001c520311a40210103441c0b8541448440c3e040c6d96101d07221a80361980118083c0c0038141c11038104000c16900084c125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 71198167 1250 71196917 71196929
    0x40f020102010c02030c0304030201140408010207150e0a0f0206031e0f0108010b06090112050a15030b010e061008010608040302120f030601021006060207030602130504050408040602061003020f0d020d081c06 91
    0x142c01d00386c110192a07128411888040c2c1001081000003604440c9403040310010480f40c4000c541c0c4030168034003410010400380e004100360f440c01c03500313032200c03540420850000ba610010901d1a5440c07a03003042019000a080c2041c03078458032640100389024005900d00030b030082c480203503c561520440c1c500756501c40351142d004003000e124022081c0d80000e000b02d4006070b14200841d590303580b503540d8001410202ea0b80d42820700c51540020610103d1070398030b8140d07802191600b816070381d00828800c0c4032041d4100300001900c51360040261034403c4d021240c02078401d1041d0303a41300d0900ca200c06a13035041001d24000c500c0c0000240030496804000013400000c490302d051051a1400c54041e413165082d20016201503000210008405a081d15010107424000c008200508150804a210350413901030745025114001c045480030b0205420712007101c2d80100010080010345003400948030700a08201e810089416500000a8a8001601a032000c9600c2300f02522421aa80c00c16110306a00c03503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 71199417 1250 71198167 71198173
    0x7090b06041814160908010c05030402130b132c071701021b060f01060302030105211c02060601171504051e01060f1205070c06180b040f020102010c02 66
    0x484869250001524221880c55903003a185140c28800d075005803448608003c00401c40c54108282e4002a05042032a1406565a01c1220b51070303450043c200ca81c684200008110107000182c010700d00111400104040e20501090403440f2401082d10175000089005506480304800d6461100c01c0003880f01e009003013a08102540c01854005444c1c42050003040c40328850a51000c0320b02209404a80b20442009420000505086200c5440b40070580d508401d05041e000000383d694030074000d0b241610380c010f040741103601201800d04900340d4400703822511382c003c5000c074030500301014035458a01c0d0602d40103044646000c1000400403c04481400042c2d40c41b2000d1040070001d201200c1940c000030349002850b81c8400351030151442181618031080d0700480d001040c001d510640e8840c6d0f10000352580c07805138842d01004400d44e03a04542400c00614a044008045641900303c140050880c840c403203c85411502e0309544000b00715016120002540e02400455a0921881075081c0d09031000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 71200667 1250 71199417 71199431
    0x109050c07030e060904061206050a06060c03090603150e090c130e07030210020312070302121e040204050403051303030207170114150117010e100b210a0207060c08090709 75
    0x1404000d003030540a4029000403170041601e40703503580105d014054503a0000943c070041d00c0c0020241c0001c031105001e4604080f1b0000c0c0300742c0500c24005400f94076480d062440b5080190860040c21003010171080b00c0c07049940010710700030720381e0301d030b80070344408406805590401c1003800010100e10701c1c0441068500040418101c0002c03800c0e030281da6044807103500c0b1480a00c0100d00d580a81422410195414414454101e415030b0080c001a8002150403800d40d4890404241c034075044a181304030003000d60b000130010315065018662040c0700e410400c1c2460441c400c40c0107420341d640c0080700980e100711000e20a1f640e6090b0620260002c602c02840484801006d5440225020300901403101c840c940003483c2d68000c001c401e84648c154400c0f500a90785d1052400c00c0c0040070345d404020300c1842200460a030400e001120201c1003008000b22146003040180344112000400703050310340342c0c01c0c0079840c00285540961103441420b99141c400c0c0303090280002c0e0034242c0a81c000e528841c64440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 71201917 1250 71200667 71200673
    0xc06080105060403170903030a1d0f01120518010216030201110301050f0d060f050f1503061005060903011409030a0801090207030c020d060e0a050304080d0302030c0706090f060f02030109050c07 85
    0x100f1030b42541e13848401c60700544264140c00f50540111a034003941f501010900e20101548080b00000c8912001142d403c1c608025091200181480011600081c1080600c102500d100d1304440d4104001210b000500007030b0305507032800ca8211125134068800b8211f551000d0590900070070032100c5000c01b000780345525020016000b02d1402d07810b140540710811408040c0212503200304001e03911040140581c0c074015243d0740c070812045030304d4114102c903000406075a00300017840ca4031551121101414450422081191079000404495415900d4900c40301413031a02411140c02009450700a60f15404001006490507030141c001c01e81161060002201280d80000104001c503016160540740005c0c3c1c0c20000081c01219058203110b109501500c2c0c20040000010700c00c884038103042d1090f403210104110182c0c0f00903680d1108401045c820400450500e07071021140304e2049000b0391407500d480e82e45006450580ca603600d180d55021004011948c038500800744e01036110003d0601c0c1c454559 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 71203167 1250 71201917 71201929
    0x150c0a020f121e130b0406030c0819110d2f12070305070c0b040f020906010516110105070b0106030204031109040b15060f070b09010c0c0804031407050406060203070c06080105 77
    0x5100d440081240c180c00044079103c8a044a94001038180f4100361607440e0603014207194418130500b070000c1e207000c900c43c2c040d0703214188548c0541c1850302d120540703039500b0340d8402c00b4101007a00012662000c00400181c07280d00d11039018118141c0c00e41d640d001681e00b40c00714054006107181c0c05095003c1210704d07240003003049610f90080080c10009000d80b61480100e40511113600c0041c9074036001d400788400e001543c15140301440c821101c00342035030754100044030540200c0032202031b0000c040110b8400601c81e100c07920401001850003504003040c0b078441c032450702000e034003002c0400d80c005828410700504c21310045041c1002d541c1c1021f503040541d51021280b2000b0440141100c10181d44822aa104003c98004800c414203d941725540c03400c109582c40d40903240080709601c0d007204801c010f8020300c0400111900041da050820740303561a8541032841d0b840c20031032140213000c4003048694417032080e40090403a41d80110349400071032522864a004036040780303003031082d004010403041d90f81c0c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 71204417 1250 71203167 71203177
    0x302070603150f030501200c0a080d0b09010f03050606041506050a0903080a030b09090a030206040206070503070b040c05032a0d030c15140c07080f0304020102150c0a020f12 76
    0xc0c9800110b10400300e81062010b001c6420100c9090701460000040c01070540200148440000941c0302d03602c10341c0303002d172400e10500e80760001580014a6010121f080c120242070307000e41b04080411083d048200003528690260840300110002c008180281f100410607141d0180c4144d40c2089410080503035412881498071806040042c0000d003208000d124048046c02154043c11003030311a03241e84000b6014081910078940111200000110b0800c40092511813070381d01900940241e45403502807100ea0341c0001d10648142c07004000c0c44000030024050988150700514031000c5c03413401c00040600781a603025040780214820081c0d1480c02d01c507440c0350f0814100071280c1801290403450f09440c03408c0030a0b40581000c1100300c2c01000c07a503003a08031b100e113641c542499455030340e1a0104500d443c01030210280055034140318074019051540000d43e0010300500481c2d030300e01141c01c042464541c00321108421030790040785180f2584d404210800300003d42501400781881088880d81050181d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 71205667 1250 71204417 71204429
    0x307020d08121006230f2b0615020d0905060309010905030d020702150a0e06091305070c0204050907050306060d030311071b2c070203160303090b060102030403030207 73
    0x181504880420800798100c0398080101c40b0051458580394040400030b030001d10540000c21284034140404000001039002c5100c280d5a85a003040807000c200c640e1908210300f800d40398000303050b9640114107a6480520900668100841d06a007800c4090288160312040803082d507000500d6030b10450b0b040035040042e100b0075903c06417696a1407502c1800b4240c00d44001e0064080000c080d02406141d400034402c0a009448004151240c641988441e10881c241c4c03500080307100300c0e00e02003403130160000c12407224014160100e03c00c07412090780c12108241c0f24800888c60070074001e000c5040500031203600c80250360180022a180c100400d1321400020003403171060242c01100300815002e41e12850b2190702114460b42c642003189024240007501a142c00d010744040c590028203140030917103651078440b15100d401c168800409200220b04c9001d030a4405600080c003012008030200c44405a0950103580c009c65108510306011241440143c15203046400402003400031980001c1e400c411108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 71206917 1250 71205667 71205679
    0x91109010c0203120d053c13020603010e07030b0604050a06030f0e1e010f270302070e0c04090e030703020c060a0c080a03022101030201091404090b0907030506070e03030702 76
    0x551001900b080d9000a01810081001c541500700384810b600c400c0c41284800240401c0c80746140f04001f402c1071445c14186542c003600b07005820178a40039903e030b400180d415002050307003c2a0740003800e6504240c2000c041c01e2141d90170081000e40c10b00504842040540d40c9510702420310012440c0200c090240b10103254a83d280c4441c1804540e005140c1010140142c2301d903030740a040c00c00d9819480f0303004100103600b08401e9203c015414807803504038040c640700700c0035020342c0991500d0622070b10400581c154000c1803000a2030b052115211449902e1607034106954a0a1907040c1c0300315a000c039035114940d88140a0040080e8000403e0000240102c441030303110098590200c915003103130500100500000314910f208603816401500750258904805945212402458082080d0902c002390010f004800200a0121000222410703003001810104224400742c07546222224180c0c1c50840c241e214100400900c0070a103c001c0d0008040c2c588003031240c80a20010b6980d014801d0080d1242c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 71208167 1250 71206917 71206937
    0x1d0f01031a03240a0203090601051c0b0f0a0e01060503120f07080c010b12010c02060a051909110906010206101a1b01090203070f050102030304080c0708030c010c020709110901 77
    0x280d0750035100714040d000141194607003000003915520b004120450211620981000308003060218003d0300e1081e40c0344001032200b80e180c90100019201c40401150100c0c03c0e0701900030102d90103006032032180c44020009001c0d410030040000c05c8030300d4441d5044d95039240c614103000d241d601250315000ea1005040e0700b5118003280c50204102d100d8498000d11540002442400844042d04400c5900d03008860200000743c403041c01e1420799028020341c1006130404400030364075080c15030015811014210b20450813a0301601800215020050291a8031104501503025445d12442a030742c011002e1000c2c02107130619035403520b00401d035401011810320f01d211132100300f02065401e46000c6241078405049044240700664000e01a0103001d034003034040c00c040480e204e803542c24103504981041e4011442c1d43d6035900d86031000d4000d0369051081d40580c640024000c20100042c5c0141c008800000441c1041140b010b49024896448125103d04040300030036505190380a42e0500c56081c00e02d103241d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 71209417 1250 71208167 71208191
    0xf29100819020f0909010b01090e01050904060504030912080702040615020a0f020301090c0e150102032a01150e070801050f0a030609020a1a0a02061305060403141204121d0f0103 78
    0xf80004098079040714140d020080b481205410a031010b0300d00380c0703c0030b044e6a203a112000e03007000e00340644c0e900f02d9581c1002c280090076551003250b00c40e010f858100342280e10380c0040c112040242405a600e070001065800030362401e0721910004240d00030160340c0d400c10540010f905c650722050041c0c12000541400000c0d92029000320b4140ea60003200d80c580c55840b00d15244800ca02510102410400b40d001c8e200796500004c1203c00740d4445040890401c0074031000180b544008120b40c4c0000e5481d4842d0340910f8002142c248042d10a0100d6000e8030f03d00030700000c200c2c1304160301c8240302d001002040c40c1aa12200d403510242c0360000c0c008284e4002d1800824500d500c960301442121140b50b05600000c00582c3c05014040b4041c1c2c255005500c48242d01520311150a2004c1d16903001000420300080c02100419154803440c2846400d04100d400b41030204041124150f8030200c007a0004e034500346d0b000c915140b4824002080356550101000400e014140a000c1c80e03051594038405c02c128 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 71210667 1250 71209417 71209429
    0x4080102120a180f0807051006181505060705010b060a0302030403121e0504060b0a08010608010b0406210c03050303040804150c051005070207080304081b2b0f2910081902 75
    0x4550040c044508903148c00c0c82031001084648038203991030341c2100b00c0300b03818001030081c1e10001d1001d03007150040a04190810141c0d50106604681c03541d07279449544100d0312180b0150800c120552801603c0b8501401c01078a00c51400341803c0c40e252030700c941c03982c00055441c030800c2e83c04400305000403c0c5c0e6403898044001e0030030840341070784041c0301c0800145400d8150407217015140510024002d03401d5041c03d00c02512014004c180c80f92030380b1202001030706e007074003440f0184500810307009240c0b43d900e40311a801c0d035009030380c2a03170303041c2c000502880f2150306410f54520b16607181c40c09000705d0440d52501a12a2841c10203950300e80c0e00c6402080361644208818400b82100d00d007a42e40d1240e44030881e658441125502041d24981e810a0a8841c43c00d1a03402d00141c01000d41c264052800c03040400000c0c1c11040221400c68164400802166412028181400d100c840281030084c80e02e041020821000301600903260b03841c01c01744041c000c0829204903161508961001e000312078400104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 71211917 1250 71210667 71210677
    0xd12020d020d1d07080c010801050f01050906040b0306091e0a0b0f1002030d0b040b010c0602030606040e04050a0309080c010207030b060a0b0a09150309030903030f0c020604080102120a180f08 84
    0x1515090400307020b103403e07034440040c49040c00c2404a5002c1a07903401c541303858018140049000c5204d101c0100241d040110400700c00e007905161207440e15030480002400303600035402c01d81c0403050100800500b8107042a0310798000580515002c82103001c90480368030204020044d40e01161501e8140ca5907880d112403464184038000e0401c40700c0040820025500d400124076003028031300f410030781511400e00f8441c40340511010303598030b01800c019031124800395201034169500007404000c000380d03403505200002d000d070744030748064a916840d40c200241540c2c901e80200c00c450b085401e005915a0b000183c46084a503c040b82c0c000b95990b02c00041d1605280f46e100071801000040c00541035a40030081d141600d0305528152100202d01404404032015120001e0201d42060f40c18800300b80074554114101c1e8003850008400000ca501160454000c1c0d4807031507150f0740114100c0d541421040000d540401459000c100222040e058112001035181000d44000007048025042c003101c0000c9078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 71213167 1250 71211917 71211937
    0x201051b010c0201020d0f06080712031413080f011401050d051e03040510080106080f061c06060812030420190e040201140c1b0303090a030c0501030501080d12020d02 73
    0x107442e041d0000e4080d5011030180460140703444210900d040c0e00f44211010740e0209402481018208145404440c004a40c154180811003036504880c85142c40100101c24010450301901480c0400851800e8580c42000450b40d051030384426810001810440c1100c200b2102d000e944041420b181d8181688a90f50031700605a083c00c004070700400100801c1218800e0301d0a2425030340c00c220482d1006400e002c1ca5000640e8200811803032404044043c2d089540100807044041e080c12201440903640f02c004c4400503207808041095075803d11061140c0d01040c11800d2031850240c0d80d5a0310b840305050528502c001554420449850340203420410b0000c4200882005031900304020b4101c104880403800200040602c4500301e1001c01a10003262560b070042440d040844148400d179200a01482d40620090010310f143e40d4401c5070a0f0001d40c0501a001d00712402c00000501740e0b041600003038119808a20240072041d80f14419001071100c1c0c110058130350011180d030501070710601d0844 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 71214417 1250 71213167 71213171
    0x90a200a03060902040b0705070e0f060402032203110d020102210702010b09010305010b1c02131a031f0c0309020102060115030f050c0315090714130308030108030a0314010b03040201051b01 83
    0x4c500c0c200350301c0040007c0f9000e801254040340d40e07641030030328810003220700082c0a01c1d414045101801c09402840d003120103400142d4450703084116481001c0004030302500090842da4141c4550710082c008425981c510384003d6140240b4581c0f1245045618074102403201c2c0a13000041c15113200394840026620700401900d240d5a59080c264060807607071040174810001d41401c400040b104000f0600c4507640944045188644501224003e06042c20030380a4046001403615103a51f0030301c200184241c0c0c4603004c1d55220790082c0c04134100c8400814000506143c00040c0c00540e800081450448030759400030300510f04810342c11005015400f030003102e55070030103041c4910101948003951082864181911785440c10b40304002c0c0244060b42d40713401045590318400340c00c81d5200010300303c2c0302e411181c41300116a40d940d034401540c82644420801e810109800d444994107000c5e00320b03440160f002d40307041035040011600c0c0300d11010307000906102c0c0006000210441c001e81140f040312050f402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 71215667 1250 71214417 71214419
    0x1051803070305030a02060709031104050a1b02030d061203090e0709030f0308070f0c0c2d080f150108030d05090c04060b0405120a05030a18030f11090a200a0306090204 74
    0x40f00c1e6694016505210150041100045600d0700c140400401c880e002000a904e440d4800e082c8001480060700c00303d1802d440d2107180f8042003052425180368175880c1c0c02550b49808501145044540a0f00000c441101800808010a0b40415004161808800701c81d4030354849031010303a48000b159100500c48800281c481c014540c10050145c0b142c09103841c0e040c202c021440f01111100e180070001400440d07003480c14402e400280c0303c0707102605011480414000410b10000700b950650b50312840059011844018800c00d051007140c0105a03207812240c4194102840300d0b4a900503e4440610358ad40c4200203078030342c00d00300301c03000c1c910002a00030000b01d6103581303583d4201e81c01400b645005101211032404580e2000070340c0a5043e402102645c01d200d61004102d400a8114154581c440c040120200124810355003038100d1522441c00844548080801d105070100000d05d880c0d5518982070741075801e40e01003841c0c413140c207021480c03080d5980c02c50318040c1c004180035040110203d01c0410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 71216917 1250 71215667 71215673
    0xa030b04080301140103020304020d1202010f0f0c031b020a030815100807020c060909010e07050c03040602010603050105061c1101090b1204020a0b0c031e04091a01080106020c0609010518030703 85
    0x1c41c103030741104213441c03e20615000150268441500d0094100000e12032a9011403900010004038042030720000c15003060032400d280c2034070b0700c030b602811403195200544503031240c0521400e100780004190105000361051000b94542c0c01c54840a030a0210a40004d081403004110001c0d0403000103000380380741842d0b14002051400300301c0710f0002610600800307030090700d0008142c4100281c014400302403170b0b003004885a903201000c1c1104003404030500c0b2121888900340040d002500c15a400001c0d000d185080150a68801808003401100300301c121814603001d00191400550700000008401000b40c80121140340301507100ba036210302c0109102543c3c080c0e9101c3c6501403402214003000141d103a4160a510380700e036100e050065801005940100c00d882803841b03884280030340d0480c3c10301d07565840e00c0c400d55820740343e204495080f055000d900c640c0c00403aa5809480700348002c0c80c0b240700d8840441c0d0755100d80c0e085a03040c0030020400d90f6a0001d00344c1111242b0f5009001c2c0c510b04c9580789 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 71218167 1250 71216917 71216933
    0x507030902030607081b0906070c03050a060506061920030a0207051906021c02010f020d051f0501050f13150908100209010509010f030b040504150606080c03150a030b04 74
    0xc40c040b4400d0064402103203500384200612030203150041000700d003807480112240126407040300b07084d030014018000440803030607800134100250700500141c00400e90794a4008111840141114400c01090118815003e0815147d40e0001d400c0c0c20b00c0e070303400783d9115664018008220a50440d82c030001030240d400650204217003040703440544a50890001410682c00641141d01030040142e0040c0c134420380c02445160421403640f024000041e10705602070b400001c1c0e81c0010602646152070311f00780032149910700164442040010603000301e09042600003400c0d40308021a0344540f00020460700d000c00d65070310594008010228045140c854403040240c9a4840751141490034002c00030340c5424a051402180c01c140c4050f5030300c61030020444010f40d042565002202c0402da074a609503422500c441c841c2a024a009840310642102c0240d0024103507201e58002804100501c005d02c0401504801a00d8000d4681181025a0080040440c10000b95580040d26144030310041c003050101d50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 71219417 1250 71218167 71218181
    0x1b101b0306060507021018090501060306050a05120705040b150c0a05060f0f0735010f0609030c05040e031e0d0b1c060e03090627040b01050f0903010906050703 70
    0x40e10244052595200d0955050045010281d00000c02c0700c17800305590b105100303150403200c24034a0300c0081901da001c9503084501c241c01071008255107510600107480c101c4601002004101c50603068041c402007081c4c1c69072220300c2010300a03074860790103032019a1002e031002d0070688004186a00c824416501640d100062181a140c90040c40b01090712504903140183c07140d40c11804100654485140c212800ca000111900004200b02c1d04d840c01003002c1036000e032600307100b010024180c1d4105a105441110700764001420300c90089420000944e900950004030364003114000703921510000321a0441c480c902d82d1500440c1031201c03d07142130284801401e4041d002c2d030010007000024400307011000c401042c20351100c04444503050002407098110701d07034283d005400d41b42408226004102140c00400041107800406549014460080e50b51000c401700308580c00d00507224104c0005e00188134190800c941c603100000d50f6900c41d02d003500092940c0f41c0c803aa003049a032070010300041c014180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 71220667 1250 71219417 71219471
    0x3021f02040b070b0f0a02090d030c050109020405040b04020f010305220503091914030304050d0615050301051303020f030f03040201121404031101050703050601050316020c060316020712081b10 85
    0x241710f011443d295003e1095450710680900110100303075a9031000c4c3d540c4000c1d08811a050342d202d1070300300c006840380e005150040d84114204d243c142082d10420001c03001c002c08050425141004002c52000c440070034034410395440100c84c07201551400d00c0c906501c1342802441d00f010300c1c80481d1485a0407810040100d8481c0140c3c0040100180201342d1a80b0803882102c0c2d000340044201c03c01700c3c0c525401000b000c280914200103940e0b80b14041390a403041140c030700702d4480030800c0706c03802e040e0144074501848034201c028520b071400054010641d4000608083c2c10403c889402403031200305a80410601c2c0030202105000b4505494020284000104d189940c0d50800000c181c07164080d0058178061081615901e045a80f03000c0e00321456410210018114071031aa40101c0355100d041c0250b018440080903d80300601d0184043c0c90916903a01111042c58240d186501140c1440e09842c00e000a10400d0300c50981841441841c015000301e016440b645042e49809544c4003040c034200711f40e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 71221917 1250 71220667 71220691
    0x21b0310111209190303020a1803030806030d020601050a030f0c03080d06030606061704110a0b03010801150609150528020a030305100e0a020d09080316020c0d03021f02040b070b 78
    0x600d80f0b05042c1c4401034404002600078101c4030b080c0020307019030041c043e421a10700e410710707107000e54114519503101e803540240c1c00f25280350180400b40c1401d01447d0702e0700c002400142159450a0080303403122100d440050700d03203030003e54000308204004a9090003580c00034009900c8403500504074000b420740e440102d0700c0718542600083d2650003406214082c034407000c1d071454203507a40d0300c5805a0350302c10180694006000c105c0880c218030b0f00c0d4051030113060107400011312000c0c40e14200301030f00d816070072150500001032020420410a51030401002580d0710300030352943c0d8074241b200d0f503a025840d1000c107100d4014003503000040c3c1c0090b201c0c55041c0a554103000e240c460219081318440c1d107014620381d840c24140005c2450740c0c1a0004c0641071a4010300107002e00c1246c07a2025182c000707075048910302610140000c01d0136030400c2001e4141c1421076045020901079500a55100d051214401c900fa0112110030301c5030030035a040d0b03001041110001a56170790326142000361448201c1c2d403495044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 71223023 1106 71221917 71221921
    0x8040902070c090605030304030c15051201080307030807051c020c0307020919050603070b07020108060d050d0c03020610140d081303060e010b0102060403021b03101112 74
    0x19001c0c030303110102c4a060481010076a820b907405980709030301c02e00c030520119104240f55011284002e4082c407001c14104401c0e2454015490040c1c502c2d5101c3c400012018004001802914803030386e01c56605568008042d0340a004590000780c030fa41c01c80c00804000191540240000c140782000c071b03404e20700307258005080034000f25004400e07481034542e042c1e803203007050283c2c40c0c22040c00c90103440346a040c14030381e16060040940c003a04214546000c02d02a0b00c07080d024007111034024080da01080102080904480c5030442c04400501c18140000d622041000c540010398007007140c126074200001c400c00001c4080d04009640584041200a0152580698002c020340c0b00d25400310b0800c03550b04840d42100c082c150f940341903400480c10030002a038046241e118260b02880c404080f06c1c00000800c1c9400014001030310b8851409144002001e140d20261000e01d40e0303011106815 = true := by decide +kernel

theorem cover : BRFrame.Cov 71043167 71223023 := by
  have h0 := BRFrame.cov_init 71043167
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71043167 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 71043167 ≤ n) (h2 : n < 71223023) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
