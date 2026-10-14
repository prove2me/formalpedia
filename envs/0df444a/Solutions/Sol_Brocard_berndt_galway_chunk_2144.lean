-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:47:03.010474+00:00
-- url     : https://prove2.me/submissions/69229f38-8de2-4bdf-b279-13103024b6ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 385431654 ≤ n < 385611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 385432904 1250 385431654 385431689
    0x51306030201201b12070303020607092112030f09050f0705091009180f050105060a150906050a170c0306031212010b070c05040c12060b180f030120070b01 68
    0x441d03c4507200720f148849015071803a003041d145c6032401050742d0881c3c0c0f01d0440b4805516030801940da070a00f154180000b03804172001007012170001c000c6c18021500b08591207851078190341c80b00a1441d050600300300701076542105c401004140e020780b80c415802800a0244a012103280300c0c00e220080d0081e90144455406000c10560740f019007008594070064000b6102000c650000c440b18800c4401403d61900480d0314414020b041d40080e01030007084400b00b003600d40d60751440720010000009040403d10b503080400c4078034040c0300100a841da09203440c252980c1c60402040c04c08005642101e1a0036020003000a10f0600300440301c1001c1e01d004509080c0320b0340c0fa180b2158010140180a288031000c80c4141c01c11010707410031406890010814007600701c10700001000381c0031901e407015081f030402d070f40046c0354041070085a00c1c1c882d13980495580070001d0018441c082c0c95404100340c00d03650303510b21041c2524031800700000600d814801c040c0c2e0f40c401810800717811401a0041540b031000411030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 385434154 1250 385432904 385432967
    0x809150a050402010203040e040b01060305011203050703121b0809010c0306051e0307030b090c0102010c050c10240b0c0f011416020f0706030c020f060717040507051306030201 77
    0x1254054403484020409640301d1004030b0840c0141e6000241500d280c0061000304840580420f05a4072195001c004682e030b41d120500d200500c07030318080c0201d00b0401c510702c0864030503c8500700100d81000c010803007040d101c4d10a03d10b0705a201015000445c11410312410b40402c6c002c5907000801b40c501030254904010000305c0048000c0485041a80e100c081100d4a803801c0c40120000e641248540005107480c800642c1c03030f022000034142c019403a000440c40264056015a540d002400009000340170b00a08118014070f00100600848104800c0344400b03649040c4103072001c2c1401e00b103020b441e550b4050303206160484d034040406413a41480125051041c0400503941d100314407200c03090355004580400d2f0b0405583c40048540b41c090841d0200d50a40c142c0c2110040450300c2d070032100c4e0001c44022641d200c2205603069000254104005503000d40d2a0324001d03081070046081c0e4203a180e4075400607441400301141e0002c49070700d41000300195038100440d001401096000c1c0001490b2075900c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 385435404 1250 385434154 385434193
    0x1090518010e13050604120e01080907050d05070b0a0203091809190f02031501171b0d0218151302070b06062b020414031b151210060809 60
    0x90210b100121000190982d4844216454025080740c00d0f6211801c1506001142d04440305544011500801903220706500c180303e05481181369402a01040b0304003030401c0800c1c00112404d071054402c0c0200810f200849100515001c01c458005554811005c014890142503410080344c00704440402c000d1b00310008584009032140d0306046203039140365031078184070b0300c41c86510107505442118070442105800752151416202a0100002007035003400003e540c5091610301c0d0107600890000c00032040c2005180b22007010b01c014101c0c1e412003881c0c0c0307880c200484111002d14003c1d0304280603a08500301102e104d6500081503205515040e0151100c0d62407020103000b03280584000070740200601000c0140b9000030a01c0c00090005000c540e120301c0c003941180c000c1840e100313902c030a40b070040c0c0340004a030000318404042c882d2031140000100510303080c0000c410240c40208100c1894104c1420307140c00d102e000f0141c1d078000300c1790600e48020580e04004010b02c1107030744034141002c031201d42c018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 385436654 1250 385435404 385435409
    0x30408031215030f030414151642020f0a051e040501170a0e0106270c080f100513090302060a060605040b16050111041d0402090a05090703200109051801 67
    0x2030381c00419044040100b502d24884510179044d0840102c1e0b0744000701c040c122340c11402806000d02d08400f50040c1d00e00c030040709800000e540242202d12500c501c0d0161a4480e401d0072b80c84107001410140341d024100075603400300300c0e608005040000c00005941300e00508409c070002c503062040c10181401c0c000383c0444d00f4000a003c0c21b01006001940c500b07040e800c1200745046c000000d00810344e48410480c2e0740d0600c92403818855019080c80040c007680781c420101c06540540d00c01102d0740791a60214200b80c00a0403451504070180b00109564850700589105410700000004081100e420000d0610401500e505035050070044100603181c1c2c08025034041e0744404401c0f5540d000300034500c2c0c0c403241881c88010a19404c0003000f0340c04081186c083c00884030102080324050180003407002503900c049600960040c480d0340400c8490300a507001030342c481d11040031a6a001d85940300c080003110081c00720030721100014905490741d40d000d00050000e0100341e500001602c09616080b81025050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 385437904 1250 385436654 385436669
    0x20f070e01061b0f060204080a0201091421010605030604121d0f040b0a03061518090203060a0c0c14061b070c060c0305250201030b030c031c02030408031215030f0304 73
    0x901c9080f080c0308481001c0708030307183d001c082103540300e41c0c4900d041e468241e800b900341d000c6000300100040c07040003420000784050b00141a4001c05d100e8a0200c0310b081500d0f02c40254540d0707101008101600c1c104005e50140340180c95001001c802c59000828140d40324040c03034000070500c00d03140280d03194025401c03000c890403207000c50f48254880c0454030004440d4406091a401c08070502c2604601c855130700c06607400480720087c142e03405096902607a200b5200290140e0103a00000c02561040d0300c4070710a00d0151600854091890b00c500401c90181c545003026038100e042802024004180a8119089445640f606080c403a03103a400c07400d0300b2032040806000c5e903445e10404040c40b5004644258910701c0e40c00f01d1161102c4400c1c89a1030130403404901127450103481c8011850002007441d007640c00100100500d5842c2c0710400806004414040306511044c0000b0135440300500141100c0740c1c8274054a0780741d15001d1300d400510050b00c08254006d4024202c01c18a03044040308680595014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 385439154 1250 385437904 385437947
    0xd0504061d030901140f070804140a08030c07090b0a090c0e100c0312020a031b090509060105032502010b03031803070b041212021609090209060429060f0a020f070e0106 74
    0x5d103c00d42041e4847c1400c020850040020007003104072002c0a540400c80d4103031035001d061074544100650364420300c4407280b1a40e102c1c100c100b003030390496003005c980d00001030900307042035580e2039a51082d40c2c1044120800f1580c1004051098100748030300c41e40b5500a45801c00e010101a100030700058a8221590581500080c8a8215a001c0d40004c00001c1c0015041000c140c00300704010041d080c03a02400384511034400120301198400c4007500d00072003003c10b14942c020500c102c00300c8603d1524003050255500c6a03042c60b0326039020b101500380c507410758900c0803141c040c003010541850304503040581c100038140014041d0710300002011a01c2a4030115106024044a205a06d40700624180594030741c04000007091800540e0002c100b440e2094480e40d45035100d89080009a0f0b001c074021054484d8005401060f6064480102c6071a41024001034030b40340e240c2090809170352103180320001580c008844440380800806c1098028080702d034400e545035051074070003080003c0000c02c6001c031044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 385440404 1250 385439154 385439167
    0x1504090b0604171f02090f011107030204021803121e0706060509011d090703031d0f060d0209090919020906060d0603050115090e030d110d0504061d03090114 69
    0x7140e50403100a050703c0c004540780402c0001c04980d44d40c0603002c2946031400540f1500081e10f08074000e49028190041132100312010034001140c09071080c050801d110310441c00f001001d40c503580b004101c0c0802d910340c0b21b548110400145131501c500b240c03508160f03560800030001701504034009988516a041c880035510001c0b41000740c0544031035000f46600135800c90000a040942c544a4400ca10842ca01c45107280d0760403510701e0710388406110107408511102c801ea0b040c02d10072020101c81d0f0a0040006843d4810500414201d030000713426420b8140d400207030640245854000d25500c4080500100081c650100202d4480c0c00754000c028000d0500c0004240c0329035500059844240140804004869490415902070014009051480c3c41081c40c04118445203001e4180d40101e8000214900480503d060005060014542c540e9980c103001c00503402c921801514052402039802103400a14000074000703a03403102d001c508a40d8404c05c105c2d03010343d03000860b49903c0a1815150303921100c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 385441654 1250 385440404 385440409
    0x3070324030b040c03080309030712030b010e10050c0708100e030f0909040c080136052503020307060302070b0105090103150506060c03161407080601090b03030909090d0e1504090b 79
    0x4aa90001086d60354048200030703001d900040a404801c1c059a6007058540d00c1840942c22601d80d03041e01d46c0066511465400a810140c650241d00d02c0c00340390091500800c0c020b0301d800d040e45900502c5c0203402422660b10240340398080e10703120302008000b540c503000054540c10704a2095000311070192680400080600012403016002492035100074071400e00f8450340e4056551070040c00c00c00f149103240301d2480e2200b107080001ca24039481030081c43c100d40640e4208840340620241ca01e40c82141100100c01031b2800d0203031100400b95614091780f03070005d5190905454a05800c040d006070903100040011401440c84884002e40d060700008181c3c6440300442c40030b10981c1d10002d41803100081c440341c1e9108000d40702103018010482076807500858a052a120403082c800e01c603150b0301c0030005001106559000340b0a02c040103088030325001910001c030b00c2030041114459001e81211400c02c10182d004084030f100050110769000505e0b03080c000c041c11900450290805166a450103c00d464 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 385442904 1250 385441654 385441673
    0x40611040509070309050607020c01170a1b0c0b07021209010503071701140a0503011b1404050a031a18060a0903050702030102030103120f0e1c1a010b03070324030b04 73
    0x2014064250081c601e4800e1002e0081d017100d500450301440741030300040140d031000c2034520340e90384165a01d0920170403064032203141c1200a44103400d103c1e07841c03c041f011182c1c24040004410742030384608203490480e007031684d1005001003c82e400d40d00540122000c0106038403c9400c2280300f420120785a0300c4802017100c40d84810301c1c05c40d0035840b40341b0001c0b5030035040c5110780900c0c81003128580801600c80c0149406e865401c2100b6444041016403841c03d18001c051b981c2c24a440300c0745890516584400142111100780e00c165030316104020301200c140109440c82d81d00c000c069410340c3c0556103950b4126521240240341d03007803065035600c20304101803103582140c10094009000395104d5031a0305000821182c050710700300c04504c003481c21104460203117a01c01c04050000344401c0e0342c00c4a140d4201c03100d2840081c119845225246413909000c08a682180685449191340e6101d10f4200400380440d0a84030005418555110f4482072144c40c000c02d5a080d03130b6114030342e001c03e51101e10703001d10308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 385444154 1250 385442904 385442909
    0x120311060108030d06050301020f030a09050f2a0607121206080a0b090d08040c050f13020a0c020f121e011e0c090504020405011b081902031c060e04061104 68
    0x40d01840d03000284070030000000d8180711540410402c10384c2d680e24200b500702e11036440400610785051000078600c2c60158070200716180100c0c00d450340e41c0100c020050070140d10b4900341440041c0585041d01508120001e100c80c0802521a680f800701035489002e004030041d02c2c42070400121001c8000400c40700d4200400078035024044031040c503220b203024282c400c01114185514407031407000c1010340d40f00b20b905600072500080d444050320309000c284140d40d20f50012440e0400709404900c54100418401844218138aa9a6000c10b520724070401205007070b00030101d407050703070842e50300003400d0030100340502ca014605040d86440741103040384501412808103000b03089900c480c0544044c15a0360410000150140e940c1c1e05000d8460317007004100e0040e40111400078030400b10003488540e264034801841d6015061481c2410740e40c8421a41e0806490000710041e040070810b00e4028a040150700d08150103541c0174803046013030041d40c1304200ca004101030300081c1c03504116540b00700100201c401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 385445404 1250 385444154 385444187
    0x40810090206120a18080304050f0109020a030b0604060518240310090c08060c130b1603032c010f0509010204061422060302040311192303030d0b10020111041203 71
    0x5e0880090900c0100354100b01c800303541e01d000d061098554120107200d84442c4660041c051200d160a5440d01c4002c4240145059001380d61902c02040380c1d51001508201400d0340c813100741c1c5918041c0c0544c6861601c1031040005c442c61002004030343d503004141110138100c0c5000002c2c075200941068529075030940c2c40007005010705004c0c400300081c141d004141944c403c0441056030740d40c1e000a0030041c4120b44511003c141000c01920009110750003c000080000c80c68940b008402c00740c0350144183c6032445001030390740d0b5406410204540c050541d000107010000c5040a18048028210700f9603a03035203440307101c0c00050880c03203095075400b030f90482201128041c00701601c98001034020343c40340c00261840325040204005c140f900703000d41c00c0c55002158034254802c1c581110301c0d00106000c00c44280405440c00e80d102c00313480401c080e0803640e130810b80125203410708006000360060280c46031021641802c00350380e0140442c8003102c080301e030f8018bc1203158144500381218030007441018500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 385446654 1250 385445404 385445441
    0x1c09170702010509180609012405090303070507061d091e1f0e040b06040c020709020a03021c0c11071a0904090f0309030c09020c0a060207020406050607030302040810090206120a 78
    0x804240302c1581c02c0c400d21b002d607000720140c0d03260050304000c03144000181d4102c1c410031000241091044000c1d1000c0d100c050300f00e90a00d01940d551500704413540e00002d001030f0120b0764607000544031007400c84640c04103030b034143c075503007004a0168030640e4454803100030050a003020030a0005940c00100010f00b1380785c0910380e595111102901c1c05001074605407000480d101c0410700c146000d00c22640048603070707001440d140e4030f403030800c5020350004607040090640c00d0013409c98840b42c45a00e503107100e4040700c000454607000d4801800a508201d400751295100e51014001c1500c2c2544e020304112201540302e44418548002601038850060024190201400c2060030541c022450b0800d8901c601315541085441c0d0781d000049006004022015912054201000c00c05a40c0205101c5002520202d481038690002c0f0300c080e0b100500441c0001e50010301006124020320040a9040717510806001c40c641540008543c1c1c0203000034842c5182840010071068816684003424480c08000c150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 385447904 1250 385446654 385446679
    0x106110c0f0a030f0602030601081509040b0403110106030501020c06070306050102030a08040204060f030302100f0e0c13020c010203010b04061701061202181c060b0909070e04170f1c09170702010509 87
    0x81003e50010342c1c232940825070050104580445c4401e821000b4035014109910540e510348074043e600c0f90242081d42403109003c80b91004032030a000340c0c4060f50090002603035446640e80d4981c40e015000f003810b0f04240c541642881b46070f901100b129401c9005103094103041d1940d0002030001c01403036119150321030145900004164000c074100c04046960f031001c103c0302502402e0442990340f0b031900005150000c001e884100c2c6005060f07105039034803d41e00141020b0a2829850883e4000c0c2c0050403004000700301041155804407465846030a81c1850203c2549040400382c41c0040603422040642d802046060b00521032180349030890100414004005201041060940c03842900544c1d009041c900b1750030540c20880c0906028401c40707030041803401c2c6001501500f80c1d2018200b155200c0940480c1d004405042000d088001594960280d0b601c2c410008220080c082c60b05a200035414420030340045203080800c2500d422016001d1596400035200484440c403d0b000c0b025800400b10704007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 385449154 1250 385447904 385447913
    0x120201022101150c0209060d060e0307030c0b0106030c02210904060b0406180810150f0b0d14090a02060f0c060a09020405090f0c040207020d02031e060106110c0f0a030f 74
    0x1603038101c43c03030f000c14180145030580c0100d80e500805200690070035071010102d5901d09000790200d000500884002a6a0110440081c2541d00c5000d0039800501e10b141054148100c09840c01d00400d13a5080400038071001c1c10000c0d446124044004950617101000d05d0f0a04000d1801c881d002c40c0d00520800419480306100c2c5016000740c0100000200010044142000220206400d43d85904000c0118103000c0c90403c002d400e401e0342490100031b0240780010100c070241c00c0c2da0064114039401c1a00c806d41d010b40e8104407203044450f0f09100882e01c081c0406401c000c503140c0041601515896580c070880c2c10b0044031445200303900120346c420081080203034113055002e8580d2500c200c5e418015500e6051300b55a4030911441482001d80244242c248140340940c0205002480540305c0241040e164000030f0400b03d4039456280c510a40c062400f82d090014087c0b1405480c80742031050f0700790340c4680c0160303984071851101402015540a50b0311560780d80c40c85080110340c044405406090146070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 385450404 1250 385449154 385449217
    0xd0c030e12010c030e010f1a06090406170109060b1804020108061f09170604030207090e150f0702070f080706030518030f1c06120b06180903040509010b09030a12020102 74
    0x2094160346d46003070a40c000c041d0721401008080c0a03404508244101004200101640091380007544984d0b581307800241c0800402d00025a01041c100000391500a41004c0e015208009802449246a540002c241820381e80c0d03825080303034087c03800e20460380d50310300460403070042e17001c24440e00d142d00c800e103440060f0312040010595004180340815030805601c00d5550b058190340c000c025801100c4144140b440d80d500c245c0c003004140e0110389040030041c00701941900305881200c0180c0801c010060101d4041080c04000c0c00241c030b0002910b8070305407a1580b40c21090255408040d11500891003485640032480c1c1450140d0081d1b83d51000c8100300050b090f40607158102c40c401004c50f6860554141e442400700320f40b41c3d0101c0007981d04041e03550f4030407500c0040c801da40c0110300c035106d60000010645180d10440d4000d0065540314180070030001c829505a000080152040203509102d40300465215009503018ae408005d607060345d10141e0190080000104c4a44924495420b01908000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 385451654 1250 385450404 385450421
    0x30a062405040c02060627150108250f030e073b0c07060e070303080a0b04052e03150203010e06030615010e01090506161101020d0c030e12010c03 64
    0x5040003251540c0c1e03410701065440049034400580c010340002046d178181702c41c9141e807002981c16284038030303403501c801d21101403815100346242448000080c03041d960484541c07608024280c086c0b0b100400074078074600c2c00780d080028110800a5040c02c00c98aa4026007001c1c140c02202002e907500d49031105480c8010048410443c01ca030500072140c1d9092600f0042416a101501c0041d00c4441d50f590a90700c01c01e600044080303920725514080541c000905100e00000f0f103101c4d60340e10100703080c903000e00e0080d1407a01e003555220741e1803d4203005900440c0b15a81210403640c1101995180c00010182e907100235a40c00a407810b816488541821642913006506a03000300401c04226203a09043c10342d2420200e420307a07ea038201c074400070540d44c02440c48440d0070038149085002c1603226408a001030308105460a90340c1000342e036000400000310010110840b00f0301c024080c200159130000c03d0a81c24030400750522071404e00c41d6500d03488dd0080c2c0000c242c1e40c000248941c3c03090394002030043c00c816 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 385452904 1250 385451654 385451711
    0x15070f1208011d060a030503030f190c1d12030a0807031404050c04050a0e0a1511030f011502150f070305060f0618030703020406080307030905150a0e030a06 69
    0x1201214a50340200d5256058801e00d036454041c810f0004503100d211003000e04065407016140d1000400244200011480f44003400c000e1040d5080c0760702d00003d10240140c08100c05400c104000840c41e6008120b80b46003000d009962486410060100342d0400d608905020789000010b806544583c02c06406802401c0c00d903010080300041c1070601949400070768001b01a50080380c2c200c81503144c07036048a070b04105011400a03040c401120300323903d081c40c0c5100898010002c0c0704c0758190b4030301d2031082c220802100c001d01031851801520145004070705001b0b40982950b10681151910b00c20404500c103001250b8410ba802c2c145644d410007502402c07605800001c0c1404001802400c100f4211300182e03134080c00306800c1661800480e000031000c7c4680396010301c24807100201603035440c014800184406e402540e0340f4189828020301840351070f00b01600440c1c02103002c80c6082c940000303c865101a914120654070a018006070410401c0b24002d40b002e420402c4064050380c42d03000070912403c59 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 385454154 1250 385452904 385452923
    0x608191407061718061003030809070b07080c01020c0a060204172109010e15041a09061204020613080313090b0306041e051002120703090213020915070f 67
    0x4400141d5940381c180140e01c0020500c1440e0314034440350680c50b90b08a400d10044090141c1e10704890340c5403540c11900241e405008003000c00901d80c10401450f00070080c81d0203404001c2c00d04514a9440c442c203440203060f94800601c0c505041429810341c0c64007805030301070320003800b86401c000700030350868040d02203030480a8410348054100028a041ca200e907920304122400507100307892100e0b40016660b10306011642c0781d034080d960f907803000c6c018491085401854546041007001c0750440810700480390006010000c005076607607240280c40300d1700c2d602d0031191155515480482c56502a4018640c1c40e1840f4180200c0c00c000048090103102c481d02010f0360486a4564940042d030300504111609a0004004103002c90ac0d018013030030b10003084a0142c00141200d6444500e0001a4040710001a60101f04042014500d1050940000091174144420038580d00081e0b1400c80c00c480000341c80c1e50024400300340303440720100b40003c403980c100c1250320358003542000c8010038180c0c2411580c0215 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 385455404 1250 385454154 385454183
    0x4030b09161205070302010332160207081504060e0d090509060a030b040803070201090215070201030c1e08220606090501090905060c0901030b0603040f0506010b0c120d060819 77
    0x11401444004160081d00405100d481c5d500103500900d02c0710310411a168038203d0308442c69003182c41c0c029854842c864015614a41100d0402c04d81c032000e00b08104540104204201c0a030b0001031107005403e4042449055403291324144008004203014a0410b0140403800b9007004c1d04045ca0004a0f80c3c03d03a4012055500d002c2000a004040d000c014960f0400c50007003008a0140ea0145521980e82c4c0000500d858942c0c0005146040002c401005400e00082c1c500071540d06016140480140c0c0c2000511031090302814000c8076a8800910104100700c40010401c2007000d94006200302600e40e003241042040c1880c0014000078092410303050f0900000041c0d0354124410a140a601304002e0f00319030325030071414200b61340415201d904050b200c040300300c00d503034541009502807407041600c20f2403292689001410710105a00004c06084248001e001042c00031441c2c0c1c00c40014421041c2d62180b81401c100001e0a0603080710540b807044000610040308070442c174100c49801200e44055416 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 385456654 1250 385455404 385455419
    0x5011d01170d0c14060c0c0c09160f0e19090e030a0f050703211e0b030601140a030f0305090a080304060918020702030105040803071107080a0f0804030b0916 69
    0x4000d0408030702030340000310480080c0d100b04100c0e40ca6900c01c80c3c0c064071018200c5201803034034031309031000100c0b021700086018481d241080a2010804244d400d10b03400e20740600c1c0c407042c10002030300360020300c15030a50000343c091080074400d035128001032040c0d0342c1084405040c0c892000501556800341e15180003214509400420383e1140b498035501e80440b0b41d010001200c903500800d600b00d0900003520540024905105851040070301440000100d180c000f400c4c074240321081e0070006d55000d01c3d1210ba00b05503200444d10a054030f0450b1404002c2059400200c2c0b008800c80d4409000c815142040008140d400300040441c418102c49640d8901e8a83c07440307a07240d1180d4424a8085400000100704514050a4416010000c004010300703200303071900400d003903800c11541210000f100108100780c00390003010103040d0003c0c0c03e000302045420020035654488030341102070304164110380b40301c041003107100840b000303140c0c046022206400d054507010340d00c12015007060141707003140c0b00c00715051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385457904 1250 385456654 385456679
    0x60504030f0f0912060c020709060305010906110327100e03090114030c040e0705210402101b0b041b030606261b0406150504092a08061305011d01 64
    0x440c4c03101040e8071640c001d42d8604000302501c000d1076040d4081d00e48002520803040c4240b00040d0b0003a40042480300b02880c0220881d40717241c969211050050051069140d402c90b0181c1d029a0713401440303072410640c1c6415901d0003030001c4000c103405080008a020004004c4083d0000d070000380c0b07504010a1205a2200580c003040340e00c002e040d071081c0410000d01d02869031641c0c00030024144249055420700c0540c905041000c3d10400c404e514005210440c03c041c604c0c00340601d80c602d080c40c1c1c1501d810380c0c00c0d03203808040c100c090700c1c109141010805124080c002c40201402110b211412a545c81c81c0c000c0c0a070050348210b04540300e03455031030485c420588c203070070b0108014080034000c28041c86545512041c001c3d400c464120f0340d100c401080d44a22500c00136090161520781715210f17490566010f042c0c4002400046c000110720a41041c05100e039462f02c211046a814940c0303490b40e540c0081440c0c5212101c0140b80103081c68000129603540e08080e40507041054800216682c8402461016 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 385459154 1250 385457904 385457909
    0x1412071b0b0f031b04030609170f16060609020c060405010c020c060904092301060801110c060106050a12020403081809071e02010e070e070f08070206190207060504030f0f09 76
    0x24808002c210600401000295440080e4100003001010034420050700b5070020b410031100155901d90b10030902c40824621203c00d28900e1129250405032010f40c081c034041c1c07030b08034030350780c0607814080741001004d4103c54043c1ca9142d0701151101c105090f03641d611135042d141640d26501e002003403078101c1d10100f00c4600506019050074030300b880e50030910008250349442501c41c101301140d04008000e060301500181d4a1200020612070b060000751402c4502807640d001200780108001a2804000700fa21030468030385003407440c0c031800c50350010703201c00403000b0300680d42600c006404010411050058000074003003448040304c00a400c02400302c01d041c1038903c13401044048503c00e003202809c241100e803403203c1d0710012420000b040c94140c588410781e00102c01c400090001c100f41181d010116000d524140e1401380b44505100d003010b0740b1010042d041540d000c4000d040088244003c0c0c0465003695031000301001549000c0c24004c144420f4031040c400007440c036007404c0402038804d9508106 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 385460404 1250 385459154 385459169
    0x4020c010c090902090f06480c0307060809070306060e011404020c060a020c0a3005190f03060302131406030c15090406080609030c010f11090d1412071b 67
    0x9240441b80104200c5402428420400601107003903480243c801811111056100c42d001803c100c082a2800e80c0038006030b800c0768002d42c8001c9000329035540010700307031007101c50034241400551501355149007440e156420280516003807401c00140c406010702618100c8054050004182080c0400c000030707031007454404d50296021a0114100350b41d80c0e801818507042c0d03a011500b4a520a946079480754008100c0e0000d06c4c4100c01d098620144416202c1103202e01d545405480d080e5181050b10102c0030138240c0d80d00f003000d42d00002d481c040c040d610510180d50002e000c0005034040003007120141c116420f5100c5691000c202161190800240d03407500c1110040000100920002545800b50001c178200c0d44d0160f2101c0b80001e1884003408414081c6411001640d81c5482903425642502e4108508124061600f10b008501143c958181c0300c544004640c100803042240c02d101da4494291400000140510641c000301c01805800405041e80b00d00491600c01009102180241a113031040f0719 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 385461654 1250 385460404 385460419
    0x30c03020c0402091809071a09090604051303140d021b0708070f05280e0f0c031005010509040908040f0303120e120c0a0b0408030a0e010c05040b0c0c04020c010c09090209 75
    0x2008a91202c0c803035644411506c0c120b80402c2e6072019400c200b02c45184040d1407420000039524500e0a1607942140c0c0611b0a8809000390300f803010000e440401020000b40802540c01840f07601180d100084880d0020180340664075800d40700741c0300116140c1d2641000c65445800710000715128003107030071400c640c403060701103c2080c58802440f5284d00b50041c0141280c402841c12800c0444440b03c0308007508803101c05600503e021f083c0c0e800766a0016044030000c1406000704896440302d100d01500ba51401e2801c40c0d1601c01c200e0110f4003a25a505009080d94004a400705900c100c695060040b24020740e514400700c202c10310138004031200c0c01d80000f6a034100c0c1e130799003103640c620380004c02e11001c1420403940074011035140c1c0700032098162002c8444c030300c0000602034800c407030740102b6112050980080184200d005000760131131085e8422810f640030045415001e403007081c004400c45800c0038005554030403041d90801d00800d1064410808100800c0010501001600c20b0360074a080151111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 385462904 1250 385461654 385461679
    0xa0c0501030e070f2904060f170411040e03070f060b1c05030301051903080f040f0b031003060507020a0b0405072c0402040b0609130f0507020d020a060522030c03020c040209 76
    0x400708994814514120170200a240c807205410000140f0080480c1d55903002000c0b20540001d00c5100c1703030051100c1008880b018840410040840c811407120200d07000101d8600645d0018214013810074013400b6420306004c0f983c01d0000720380085000c2d00d42100c40d01030318441604080e040b062100c4007d000703a4400d00060015080c88210a40c00030030b500b1090314065681e68032105140d11801d01c0c8050303002e004c0b034100041000c0f400d41070094901c4110131401d42c40c120081022001d074511019100c0c5450380080f0300043d00038050b00321040e8000780341c0121890b04d400c0140d80d8500030312a844034404251710fa41d8850800d0351256010f104121003d80c200d88640d003c0002828000e02e01c07545c0720303c0410030800c0300d6442c000303011b000d81141c501c04a041751904405c00200d80004241a040d9005101c02c554a079501003500d844055100310000303840d413a007030020a0103450703c899540c134503018583d0040074141c001c18800b440502ca64211816510503d0034001680110240990000d1040154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 385464154 1250 385462904 385462919
    0x50115052706041a09010e0406030321150803030412021612020307090507030e070509130602070c030c0b0d051e16031413140a0f0b040c05030a0c0501030e070f 70
    0x526401c00000e04040c10161140c00751107000039281511440c01c100019040d40d2543c005000e80e0380325100b201c042010500c0d540b0b024081c00c010402200b4011199a500c2e41c46180a07403180b2521a000c1040c1c0710b02702e444905460340d903402600c041d242d2020400c1c0c01100180f0000310403c1841101c03048000c4c051500ea0707060303010404400200c1c3e150140481c042441e400c50301c1114425001d6507000704070354015020060408503e5008540581900300412107207078401c804444817960300c084016a80c8141d800c2c45a250900c580008001028800300042c3d4141035501900d041005030348100101d840d525907601041c405006152410720084000450814801941440211f4141804a512000820059221079040340d2030039901d070300c007a48601403140002c00708c01d441905000410604041d9200c40b088501284801007900c011807000800b0086518442c1c001001c0141c11980c5200e4586046005d4030f0490007440e0001e450800340040016001400d0700803607480c040e181e18410708040c00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 385465404 1250 385464154 385464217
    0xc020a060f0e210f03152d06130b070c06080a0603050c01110c19061d15090111011404060513020f06090a05180a05010e160c0213050a05011505 63
    0x1921907800052000e40e85029100006510030613140d01c1c0d0302501100c2c41e00308038404483c1f000340899841c0c40e080752001e5103e907001000890310202d500d55110b403411101c80314034680d9900501250000428401d040020f28035415050307600741c1d1501c0304c09548688802007210081e100c054250b52040d040512954000ea002d0110350440d8415610b91007201c1d00402c44031003101e0007103402e404a0b14004c200d19a4041e00719205107403808035108409044a0000310161840202202000c50010707601d1016030041c4407020320810080c00070301505003591200442080301312826600541031600040e14480000080c0c2c14181e8000c10b034403040c045250038407130386402610005401410b03d1002152503951484c82c01901e003922001d80c0c48903d8401d05407401e079001030340b00d12560103a690a00180c1350800711032504011051034130060100b058000694101280800313841140e10342000e0160408040d04004c0c180c0b4001c41000445008504089826115440f4098054801c2480d0300c5086181c404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 385466654 1250 385465404 385465453
    0xb121e06041e0e0c0310062607081203160c2a0f12120908060415020f0a0507030305010501020318040e070506130320060a05030601030608010c020a060f0e 68
    0x90a07a4042e1111503400d003103c3e40c0d030700a80300b1a40000c0000d90305280400030700c001184000c1090084500c0c1c01800b90086003c0d1006540070007049002468140080007800c0041164200311103400701c201200c1a6136500a84032102181d0f00001404034042c041e40d2805059640104400741541d00c031012009030382c4c20140d44480000110a0000f101c204c0e05034244040c2111166940300c0328054a000d440c01c0540d01409010700494440c10030100c1c0d40440e4180c0d0140e000300c4120b008bd4003101181f0024841d2150003098020017280e60000700b41d00c0000f9142c5035219840c2081786907224001a42d40f4000d84566000000c0202805a024100764004202c00c206103404c07102543d480c0c000041c469041a4005041415042d40400c140041c0c401c04054218801c441e10821040e040c011490354407070400c4000a00800001107400c592190344002c0c001c10030b80b0020001c1040c80b21000303440e00b41c3ea501c19150700303044c420400c50a400314481c12501c69080c000801e10190b05003869520a00d110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 385467904 1250 385466654 385466681
    0x150f150302210411130b1e060403030c0809090106050a110c030618030d0f090507060c020108040303090201020a020a0e160509030c10050f0301150f0305060307061107050a0b121e0604 80
    0x14456607003d40c44017158041e031070036180000304810841c54240a03443c1c3c1141d4030000c1003183d1a0803580305403200012034007525090702c0c0410410050b400c200d0707680d10410800d2504801d070100000b40e2142c0c401c01600000240b03554941c6007141c187c1c041640c030040148101e90540054011880d00b1101018030080c507011601a80c0c14110f003032031210100c4091001e03000001c2c2d201c518003410000f041c000c0e24050441414801114441d540000f803d0460040008051642d40d03141c5400350384c000c0104042d00d9034020311001304541c4540c4080d400d40b000b51058600e00300e0401807580064060800c0c1c840549020b0001c04802000070308000e010109010b060b01401004c00c062039401c0c1d840401540a0030000503050038403a041c1d00d00078031081a00154a081500c1d0034203124841d9070200f5040c1c11a84c2626195000e480340000c00e60030a02c20354045584052a454005030862410004c0c0404e10307605000810f1991f201d0f0506000800c24903c3c09900c071941c0340002e00c5a250942c000c55105102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 385469154 1250 385467904 385467923
    0xb15180703150b040504150609090b220906061406030406020f0f0d1e0c0e0f06040b0c0f07080a0209010918020d050f120f04060c06150f1503022104 65
    0x141942c1c1540c2c48035002a00c543e0700000301800982040e0003000b002c00d003409080744804d803900b940140940c429001d050405612114210115a1040c5103942c21031401008a491944494407100050100f20340440303015003011400600e5a042505c1608203074030240640e131840da41e03035a880c0004d520076203011029010500c40c3e010b5004802025003c005940e410000c1c03101c042c4230020711070741005441d1324078803410701c00a050100ea1200c0d40c00e000c18010b0307036001600400400010980d0145400c42d82195101154001c100140091500c2242010400382d42519440e000c45580b5003404d4035002e0341169012004003d0150594000d402489000b07210440302c07201039002038040704203e14165000d90106c24001030412040c80020b8141c61441c000520344009541031220a000311300c03d007001e1003440d078269801e0200680018003084400c000c9102c076117071120240074088419004080c4200c04081144030381030300a2085462800004110180810075070503a502c050800500c111070100d031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 385470404 1250 385469154 385469171
    0x110f070f060504081b010c0903021009090c030b0418050c0105031b070c061701051e03010603060e0a1202120706091412030910020405130b06120903070b15180703 71
    0x103480c40b8041c0100d200d221002c0c1d50300340041c21100d55041814000c1170310f034900710040c4121a04010a00c0032660b050350f0780000300daa040010354200e0f030250b2201c1c00c1d1a00300301c80800100d6040d84000e040740f404450410681c030a49031400304030340800130000e010b680980240d03490381d8041c2c800340d41e11130300c0f0444210700450014440000c40c2c002100440f00c98800c0030040c003116810000c6124980002e4980d0b807032641c90301000030342d50114510000340000e807071a0f025080381c6080d04000d0285030444001c1c0000b4a03003a2000c0ea0394030354698141c1e0750a425016480000d4400f1692041c084000b40145007013400a0311248018800c2c504101e503503902d62a031454000d8810b20220105150204015807645001040182003254142044500c3e6204200034041541c8030300c0e5040e040c1103028400074070200c000d004134600f8410008520b4000845104212072948004011304005214141250a948429819000d080c01900c80d01d6070020040b0014200c000d903400c5c07241e910200615000c42c0015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 385471654 1250 385470404 385470413
    0x110613020909120409050f1e04021219080414060703050724090c0512030702060409020d021b0d0e09090604060b130606020f060609011514070602180a09110f070f 71
    0x5200354807900c01d0301e0300c0c0c1d400c1190008040d16044e60080c0e80490301007180c8c40c000744000c01144014402442808030256418040c8004c1154040304040c12101c04010406400c000e42c81d03400038800d00c08082c414a1452400d410b01801b80e0b01c2056064480c1810102c5d00e40d56001c913484204400d10400c045000629900c030180e002d45001c2030b0161210801103410041800040440880d0202c41544104414001070b20780e03000300c80840700c0a0380b0040e100d42070303488000042e208039407a1050300c9645c1001c5154401c404510748090200303035204c0c4821100100300307004042004031100b00306900000f000401013111600407a50a83d4020304080e07401445c00c1c010801c80e00c2a0b04940b0050384a00900380031100100001078102000f15003110466241c51407000c0c3c1c0c0c6901000340d80030000141081084940d80c00180c3c0c00403a84100300355201c01100700782155148000c81800c0c8242d0200b180000c41c52181e00c6040c1e080303c880840d03d80b0301507096480c4142c03540042000c542d4250211041d0021a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 385472904 1250 385471654 385471657
    0x5130603021c110702090408070c0905011d0402190618050f060f07020307051e130b101b05060f27100207081b0a03021b090601080702150702010b0111061302090912 72
    0x242c4c81000c95546841807814845619081502f000011615110042c0280418401c508480040703488087d4600d60b40d0384080307040b100d00903a4404a1401500001c92034541000400c03d015460410107400b41e80d569081183c0c655000124a40142082181e02e1060030504c00400d42940064112600281e588000c0303050312401c1c00740c05030100041000408540740c40141000e2620864105100b00f8081e81c00055241c1d1601098000b03120007a9011034090f80120319055041d078208040d07601c60314100340c411110610864041c08140388404110324a108480b1401c241120840000c141540c44020010300135440003a060f40d05107400d200c45036414201c5001c0c004c840c001c400260002c03060902d0040c4c80d08650380301c2082d030401030501001035a12048030301640b1800074030b44020203407542c56003a0b0901c0c1201e880e0484190213a820007071041e40540050208040a80c0e8213040c6803c00401582c40d41003c0c0d034140c0403407080242c06400b51411118040e0800900010b0788c840002da030944072410b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 385474154 1250 385472904 385472911
    0x5061e1b010605011b0209010509040c0902030403031d0f10020f0c010219021218061b0105040327030803060405100b070c0f0f03020102192105130603021c11070209 72
    0x81e03459030400d21255901c80110b8060310102c2d02c00f148800300550000b4400a0140034580c00303000b0140000b02446000b4a000e0010020383c04215078908007410014040c0500304030700d070403d50800501c88071025001a030100649050350242403841413540c10350300a50b101d202d1490051005103c6042e00b100d080c4014481b0f0020780064540f1056540720103400e00c494551600300e003031414001d05240942504850082c03170303012a51169aa010740700302421083c00211005801d40c641010001010f401083c40009100109111035107920b01030b0350314440c0c00b1280401052140700340081041814203420079074209507070660807030081b034031146007001c00e03001490b0555209610130030820003103000714003103006444181e00c0f080402d800c50700040d64a00c111100c0040b440c9840c00b0a0b4244100100c2081800d80210521110001203030390040503900304080c020004500c1f4140010500e01900c200c0318000301804168003c44249001a4020600450f0aa0f40b094040083c140140d03100404c140c407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 385475404 1250 385474154 385474207
    0xf0304060315090c0c170d020c0a020a09021804090c080d2a0210050306040906020a02010b040e19030f02010609021201080c100503190e01050a02210105061e 69
    0x1624500390b010b030500c1d01c0c400c1d440005440d10b03000340c604c0c600d5407041000d801c05030008000000340c0d03840949840c55114004503280340070710102c1c0c4500e0b158070110700d0300702c00f40c001c0b00c4882c0032680710364074170080f841000440c0c03600242004c9007000900300794010080131030040400c04c43c4180d07504411030402541011400c0000c2c21404007096103138811010340d14184c80e50100c10681c1d4160340c080741d8a43c008403080c0c024080044001159542c458002c10055a8090000e544500ca070800c0a4003074038200c03416034461410704802c1c144015000502c021001090480c00e4414580c6480c1a240b008000c1800d00440d501c40c60042080c002d20b000800f000d05503119248400d601d880c0301e45007804c0c0e021500030303c5500c004e00d162075425404000c1d41e40040d04500381680d0030040300700ca00024060742920702c049500745001c1100c080c1155000d00705040d04010410711324030500f404802c0c40d070424015150300c21802c0c41050341d0605441c0070304134004c00d1500c003d0719100c6501840c901e01e8000c24500300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 385476654 1250 385475404 385475411
    0x9090304031a04020102030a110f12040f17060105060a05070b01060c121110020f0903060103050d08091204091d1c0f03020a0e040c020312010b04081b0d11030f03040603 74
    0xc10a442e0400184000e0300e507200b0002e82010f0f40000e4403803241d080000d040114580c2900c0c000768080c883c001c10b03480c0c071030112074610b02001080d02458210340f08040c3d003200700003400500305030300d580400315112001004d800303160300707110410105030010341010081000170b00a4000081d0b2070714449002e000c03191154840c0c5085407a00e0310b219580662001c003089000001c907100104001411070822008210260300c592031810610309a004001103290326124000000060041c00b040b516442e0707500d41d58100300740d51030205172a61003902c6c0308103150250301040100f2079002240d00108852094040d000245030304000103a00c0c00c50035110620241c8903144510107196009408565844103504096040c8080580040e02850040b6842402640c5030708800b48014400d10885458684229401845503102c1c100c200b12504503000d042154400d01c0d0200704003ca101d03085001a203001000d5859030701440d92007410001900c04819014810280340150405040c400b40000d40403564000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 385477904 1250 385476654 385476659
    0x1503050102030f1b090d11061b07060207060f2a0b0f150d080306270106020f06010b030c0d0603050f10050114010807210501090605040b0f011b0f0209090304 69
    0x2c4000d0280542130307490320340c0c0c41400c000c6000610b8064585a880132034540d0101c0c0203a0402070411a000c40b4810390101001881c4001003201c00081ca000034040307000c9a14107512041e01f03036510100d074012440410041c018100d04103110351800d41803500031003507401030348d03550000b40505850507038001c80380d0300745140411569501d0b4501e1654013015054070104428a8040850b01281c0e100d000030345154800000540303941c64029000103038805a1101c04075142d4074102c41d011030003003801050700500940d903000011800001395241610410b40e941131440e141c500d401c010300d52100c41d02041c202e0700c407903002005c10800d100d40b403440a4020042d0180031a84114482150700c144c20900c1c000c00030981c40d0b29640d074450340303496001c401810851150b0f000c1150340c422040d4075005210b5040d08100001c1003030040d54101c0030407580f09880c180604001e800421503180d0841064600180d051000041002580058078403240d000724140150020190041148400101c0c2c800c2075991000a08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 385479154 1250 385477904 385477921
    0x212010302011b240b09040506010602060c0f030a0203090a170d29060901180303020304051002010e0a0236010f050303040605070204020a14070b040323040504090501150305010203 79
    0x41183c03410a607000400b4000c090380e0740228100820700d6804c00f0713400028100700c0c450901d90141e6045a0000c0513009540351610703026a0782e10f024061800140104030104030008262025102850300c2400110b08584d250068040207400040410300c00c2e219410720100414541c03924600d0786980c40c160780d6642c1d003042803003006480d207c050325100b07860b24076800903800030040d6200c0000102240c035940c2d25120300340101c40c410300e040d140f03103244a800e4900000b01500080240119142611070020449808200f41d08a40702802c8100312904803100304001071925003060b60b518000c0100c842c1c0c80b0400203000c240444000c85141510700120b40050008003404c4c020003005100c21401140b92a080140052090103800402030050790082108400c044c00b030903110b088412a001244c1d103403455414124403d12056409a012903a90080348210025829030320042c015503921680c5440c0ca8902404010a80010161420b56032135038020b008040c80c4a5110045000d800096141e0034203015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 385480404 1250 385479154 385479167
    0x706060f0614030105060901030e0d27030b06010804170d0509010b030307082b090809010801050108060a031b080a290f0a0e0c03030a110c0a030c1a0d021201030201 72
    0x1044003403285100b070841015841030b08030fa0550b0313020f69005032581e03e40001600a098000c0c59400307140140c0c24002d0909620070b541600c0c010518a580c05c00807900088141d4580c0c080c00082c00400c00c0030000740c015406583c100d900184201d001143c40c04590840c0041604000d810303206c0345450301d080c08400002401f81c5012400308034080d610b005107941c1c03182e04520401070416005078044034010b0342402104544182403040c880180459080c52400c6003a991002c4030392030210b8a01e00c004503195100d081c0c078500c202009084a40e196042d40c95904081d2000c3d0b1a4001000302468007007502c400c14031101c41c91034824140c59841c141005030302d030b501620250703a03881440d4a520812114807451014285c10094858000030880c200c5001182800624100c03c1d8052000040000c000b56200081c40e049008200946181d040140c0410912030b51510000c3e01c81c1d001d02c2e206004032425062001100130b208210325107400400100d54003a40c0040001903c071000032001081036582141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 385481654 1250 385480404 385480409
    0x9090201110f03040509070e0409062703020601050402070203101109010f050c0a0807060902030d120c0801030f06020a11060f0a060611070603020a0207031b0305010b060304050a020d03050904020706060f 89
    0x4020b001c122204090703455680c0924803c2d80d00c9520b010000c200d5a03401017111109070b080c05441031164640078100600a0150284d0036070303801698540b62202c2d0351252001035825075040e409024940d2030502044065000348030240e0b814004c00002005241181c8a800549446841516107860441c400502400c00440c280e1082c410200300f08042c0007008100140c03040d520440d059100c1c003c6046c140010102007800a405201b0f090041d801036401080c0f03207035980c08002d800e00c031090400304100d545803400c2c0300042000e074002102c41d00040710342d00a84210b184515200b0703420f24003220618500a8150f0b08540962507080612000c0301c1e050048502400f00d505100701c12179889848103941d01694421041019800f10f00741601c14401c0c0300700c10003540c01801c11000c4100280002c1d220502c90710040f02c00d5880e00550f07000754184481568425a0000c000c1c100b42e0b8200e0b001d01c0605094040304508220341000300800c00d54452015084450117034200040c0a4204000d1141201e400d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 385482904 1250 385481654 385481687
    0x5090a230103050c010503100b18030115030f0807020f0a0e0708060405010b070212070510020705090906270307140109060b0307081b031c0804030f090e010312110709090201 76
    0x300c0144003080000510803140b1a0a2804954036650380c060100000c0c030640140002100c00125140ca11840900307800500100b20001c02c89010300310408107942a09104c000d260760079180740303200421070607000b07401d61500141048c0c2c2c903540560001041c0400c82c2c0c01030048406048280660160303c000d40315070100060b5410071055050680c0d180d154028408001d110354061942840c1071501400b5210081c48080d190b0020a044101c019480305442d006079070084044c40c0000d08189000541c0030b010b4084043c9511901102d810703000c054281c85250800207100c00c120201c001102007850380020306d141e000001d06c1500506d4100c2c20750304c04602e06442540840001d1241d03541c003140c0541e0f00c0c1e040c814803031031102c25000403d0411900364810440600034020340104660006143c601c41c03842036813451a081c00f81501950094807a01a11407103801e11001030000070034008025070311180c5402e000d01101d0076141d1461510416400c5040c81544880c8a01c0071035070440c2c004941c40702d64 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 385484154 1250 385482904 385482971
    0x1009051e0411040608120a2715050408120d0f0908090d05010e03030906100b0f040e040501020d05010f0f0b0c0d0c02120a05010c1407030801060f03020405090a 70
    0xd4201218600a400540085510300c1c400000c0d554952000e00240400d100351401a000701011030256040941110081403000c2038103503040f074400da5031313804881c200c03a086075040b82003120301a4944e40201c1003400f071210400010601610401071420b240c010101215036801509032120151800d08031682c0d0304500b01050040090282010b5511100d0240d881c00021042c508010303003d0000350000c000755000010a0100e89880030801600c505202009644002d5030358103541e941c1c3c8146642d00c00c2c90300050100b40030f40c203c02d942d2282c000e8040d90004d030901e44490302c5542111001c0c0d1080400050309141040390f43d0815000000820b00b004002c0d041c840052195070b00d80b20905020b504110080c3c3c1c145003155a10194400c250010000720b0342101500e15200f4020b20002c0914004910f03d01c0900001d00d44010499070010341c50b07a5203e48070f900c1c000d800c0c0c849469582c801c1003895001c1c00040b589896120500780300720648030300400c1c189011818071800180b002c483c0d0402c42403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 385485404 1250 385484154 385484191
    0xa0c0e010f090e0603150112050c0117010e040303020409020d0b0a060e0904020d03110619050c09011d01090b07060b041103090723130c121a0d06090605100905 70
    0x20812507100440d000501c0c3c40c0b44039070702c1c200001c1c200150060390a01e0000300c800045461550040300360005441031003150101202c5000540d100c080a222000071043c4800040c485920f2648805400510078107000d0308181e190b100d01c5040ea00142119200c10b83d4850481d02c00b0710340301040d94001c03c2a414007825450206000c241e01680041010b40980d06c04a41c0204041c412040c46100c242d80341c003694900d080034104d405d201c00010030f0303540d03103d404d010106440e100071038100c541981c0b058448490783c85160107031400842d02144502c0c1489003c01000404840200081c10000d100d100006007148880c0d08010448404071603a1548400c04c4c403c10a01050021359070007615950400b011403000700c1184001c112141c0c120003070b04421001c0c10030302e0900081c5c205030002003240e2a1260080c1091121404071441031007174902c225000d0400704200e003000c04070a044a4080d07080070490b1802911000c003a44c00c00d442d2006903101e01d50b400c220f041d1292240325004528055072040201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 385486654 1250 385485404 385485407
    0x106060e060d2a0c0c06020111090d14060c0409060806010302030d1d0d144303140d081003050c0f060c0d0f390c0902030a0c0e010f 58
    0x501d0307030304022880e50344540c42060f2001c1c403050751210065440d02080c0054200008200f500c280c18202c40501c070418010400030300600030040035001041040342006805010441d0310b0000c0002550b100c80380f11350f41c0500b44014010351f0310858100014070382c0c0f40d251001e42021640340b5444603249400101c010b10050707602288903c414049031608039942035454009400d008840701405a01019000c281000c000c94980800b410f0f0201702e05030340000320005123200c0840e00004002d8400c1ca03150841d209034400328024401e030001110b40e444041e54403070340e40d04000000201c580340746912021010300c0d103690184510758410703100c0415001292030340d51025136860307807085a548208c00707034507107458580c60302c40949170704142c108100c58401c040100041c040c45044084000000c040911617031481e4245520955850740514410944106180f040b0702c160300445821106071481000000f000300b40303030015602440d0320150008210b044000041c000d40f04642044d8140000405d0001d13149 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 385487904 1250 385486654 385486657
    0x5010201091e0c080a051011120c0a020705030f0105010e0c0406020703231609051815090c0303031005010e010801030b0f07050c0f16051c0305070c0e15030106060e06 73
    0x2205201d290300c800a9840c2c1030f031140000341c012245a210740301e5900240140003c0d4420f02005c02c480800c00c4d464001e000c4111889403651800581600f4004108090041b0000789191040d9206850b901521540041d003402c03101600380c40544e442e82c0040c407c40c9030b4100d840da001601c13080740501c1c1078500700003e5140c59040c440680310147e03101740d9002c80300100f00e4181c0003420310b00c19114070701c0c0200c040a1040c2c0d8070340200300740d10b85480d000507421841c1d07620725410031241e02d000389040c2003c2608402c1c000700c02050345080b4022480241544e890400240d0300607191041c10000c0b003400c5c240010203842c5008506070400216800410119500308502d581052855a08045541d0351000c20780e000e2081c3c94800c480d0348924520524101c202050003480c41c1214005a0b003903e66032010049550b2a14408010b52501904d10f480000c2c041c0e001080618854544c01c003105656441059880b03030122a07404032860024070940540c5803e200b507030041c1002e03080c011014048a400b09495 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 385489154 1250 385487904 385487933
    0x6060306130906090c180501080c13050a021201031a0a05190e12040f0906090902030c01050d1107060e06090105071b02012a0c0902040506120a0b0301090b0601090501020109 76
    0xd40e80742044824494150842070340e132500505810791541e612442000740309201d610325025a4540000420522804074002d041808010611440355104401e10030080c030000e041c501d81310350308110144050319490300860086000702e240720034601128152008842c030003440c41184600c0d010810a490350605014070700c10818100010b80c0130760031526117240c01c00700c2d01c00d40703e0100045000507001a103864035206940700e04d4028032500e40e0f40c20881c0159601d40c6c6000354540c0040e09040600d500c281d02519810040c0307031000c01c503903c89540d200030359445442e054403d20b454000381da084650030072620f5040004080200060b240105004180b002403a850510840c1505501025a0312034440e95880c07076404041190056100511450511800801101c8040c0c41c0000010070031681d01c2a03a00f00e910141c211803804a81d48443c40d94208000c0001c41741c645d840003410001d403024030030700380241d10610301c05409090030000981000003580c030590442e8101002040010f28080c0384c2c140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 385490404 1250 385489154 385489189
    0x1a13060f170c270f1914060708070b0402090705090307060f0512091b01020a0506010e04020d15290609040b0406080a050303011d071b030203040f0314010506060306 72
    0x3003a456800c842079607071250008070030803415000c100c03d840c1c48041000c01d411000868081001511900030f208042d203402c421600f140c88203007000c000d06010340b8002d5078040b03c0100346614007c020b0350707031106d5a0011102614200c0122040104500b094500a90040c50504050b410704000c030f800655118100d000381800c10071344841c2845164041c0302a40c1d207803074140d0303070380d82042c500000903ea65079190064040c800c095003140e003246500218107800e00981110180420307a00f400c1d002298074802810403a08020030f1034500010900c0010346891000da20000481c255522414890394030304c502026000080b28542c000c00950344103001c0b50355040040d2400b1440040d0100001e0050641d984499001c3c0942d103248000c2240c04001541a182049000e03119200001e01200c4001344c1203d03110089541ca0030018411070300b003000410300510034030450f850251586600e101c001800c1e0300c103d030030841007405600100300a0094a901620a03105542140752400004015460701e850165 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 385491654 1250 385490404 385490447
    0x103020d12050417011a01030504080a08151e0a060908190f05030f040608090a02150c210c070801020f12042111010f05010b0a14041a13060f 62
    0x29600c0e4011000d0b2401400025140c0840c2c80c6100301d8130340079000340c80340240e40d0038601d010b24890398024450140519040b4034001d0800000603c1175499035005003850040500b24075400d00159148c0d40310301c2900c8250451202000103c0e018004450440c2d0003540034056030328810b000510340003c4483c5141191507103070a021210b030901ea9003000c80a031015206000014128031413800c502c0082049980700d0b0f03292074075903444509950b11109070410095101c03c0c80c0202e02c111140c0180900010320011056030400102c002e52507155200c551485111580c0115501d43c40c450140113800080800718002d6207060008220310600d845200c0c0e01c440da1a884c1d40c08103040c0169914000f9850a2005c078070b83d1042d41140300509400c100c200110f0a40d800d212011300340f06403900a89e41244c80940d1001e0400e4240503094822881039403451418800501c00004c20801a80c900b000b94800c082e00f00741e40315120010040344641e2a0088401c1c04120613200402c42d610040d003860a26401c502403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 385492904 1250 385491654 385491683
    0x6090d03020a1112030103170301050604120503090d061a0315060613090903020c130c080a1a0301050f09070e010e01090c030207230615010806060903150c0705150103020d 75
    0x540d08444038109002051140004e80c040480458005506a0340100c900c540c241045076000285480240603040c5c1100d018041040300039010491880b400b032084003505c3c01c1c42d0118000c6444002a14070a82d481c2c0c1c0c851a0070b00c04842918030820008101342c014100c0c83d080007030407021170351014101d103024000c0000c000c0800d991241400e405040b09500501c288215820002e40e41d0700074200007032007880d0214010030060f880744285125022103403582c150540d100003150703000b8800c4000021044800e2070000c41a55001e110305031246007a65003680041c140581d6903407034103c4680089944c07020801c01401301d44108902c40b411501e4282c0082003000b04a80c085010780506100200091400d481442c0e0140140945c0c0e11f064a601e401c0b07840f56580d00e65500e0b0344100740340546022500c0e085c003040b5030703060100040800c400090200c40300040103100302c07145505d045548860441e808110b08007000024050b01081000211042a4a50454001451003051000010031403007000689 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 385494154 1250 385492904 385492907
    0x14010e070e15030307060c0e040209011e03060b040e18060601021c031103010b0a020d020601060f350f101404050a0f0c0207080c090103030519020f031b06060306090d03020a 76
    0x10072050b00d0160a4945800461510f0005090b0307440d03042d0302007080194100c1c26401d25100751004040165160885126408140b80b84e10ac4d900c41100105620388401085449031040180020420650380c0704043c0742600007290401c07903102e5014500d81000b0240800c503a030002d810b50000855402c0320580f01d200c0403064000740b03201003030380e81040400300000035140e03c141d028040820f8070381c0a0750b91101c9000022a100c1909001d45400f04035150107411900348035014041d40d4140e40c081440d0350000001c65540c00c4c0362843c1052031190010020083c1c40041c0701c0702650130401d801c40d0004600d0030807050207501c9031006c04250143d0341e240002030700101c15400410009d40c3c01c0404002c02982558001d4861040e401441602e100b54900100d007400d01d03c1712603049075010759815080403154902124003c0d21012404114455410039408104007480103040801c910398541c1309220070b48500714103141c80284514441c5c0c10100800c403041c64042442403001d002840c0c0142e4030b01d91640b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 385495404 1250 385494154 385494181
    0x60f060a020d020745090f02182503020c010f02072015030a0b090403020f0706051206040e0a0602130e0a0506030c06130b030a140903030c1204080403080c060414010e070e 75
    0x80c85c0036481c144002030003480f514405580c282d900a4402580300c503885040403070120340c10b403000012800541402e180c070703440944907115800c18528000d840c0c40d2601c4c1c080c40c02c0d0b90806802c107c7c00d640c001501000c00c400b20500540142040402400d2a203419001812030b8004080c1001102d0700000054480e14559002c0c1106800c000c00b00221030800c5e0400035580c030949180e8443d01d204450012a0050080d001e48082403480c4207840c2e529500c050602c400b40040301c441c501244994204000095a580081c000300e03903000c0d0104038107d08d07000ca0a4a00c1c2c0c806405201440e1414042c0065510f020910700c0c00c5910a41d00c10380e56007030250414503041c03151780c8103a0b0300ca5404814044500010342040fa0704500d0340c0b2005025846091044d912840151008000403c0800c0000801c0d06458401d070307400340c0108082814196a900d44000c1684140749884444e00724204100c104441f0b0942480d01c0407480000700000c10380c54450036503508440c0201816401d0200010f0008804a40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 385496654 1250 385495404 385495529
    0x11e09290d0b0402270a0209040c03020c030a08040213060909021e01050a080702070b040b0901080a11090d060e0d0c17190503060f060a020d0207 64
    0x50003041408004540d5a1400c000080c080d04a44011012503415280c0301074180340158124148525940b102d83c01c0020002c0c1306000c03042091011708010506201c0450001c5c4a80c20804d40507a544440200b0401142d9001d4403080500d40305102080c4241000001d9561040e840d00703240e00345868500026854080440d4440c0302181071070700c00700e503403d0b00e0b4109969140c400d445101d200303411100154507810040d40c0250000300184504240c06102c5c41126030030401e203005982d002c645502c030445840c1e10540001d0052600028820015644600610341c0180981e408001c070010001400741a481403a41503441003901101910500c031080c1d001c0b80c40480e009049402d24243c0c07100181103154501415100420700340340d40150788007400225148040c0b240c01c50304144940c0c22042d900c0e9007004d014035401c90124030034090035031241e80081c00803d900da0003c082007005220000d15004d11341d04440c50350b0031613030084518001c560086044084090000c9808089440300e03004c405e80c0000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 385497904 1250 385496654 385496669
    0x71517160309050c1c06060503030f09060a0302130f180605030601060f0306150905030d08041101121803231c0915021207090b07030c030e030f0102030a0c081e011e 72
    0x582900035080311749111801c4541c450101400300365030b03030700c100754480c080c1034602d00c0c124004200f00d50440c0782c404010221500309080041c00d1144038100300d9801207031a0400c04900e0403407401488507143c040d9a400803000c0036a403e001c1c0a0a0202082d141e0006228100501c21a0500b400a450007070300005e000c0c0440c01c5059000c8106054010000d8985210f0980a4082c1c013070b2620002c1e1062491901c03071a0031503826040030141750700441c1c410f000660121031480c1d40300d540d203c00c201254000c0503680e009640b555000290b8003000c0302c0304071612106e18100e90040044070008003a84c49100311a01010400050300e054034281101d103122109020340300e10740300081c03200c913001c030300130b10a03000311443d0f607560a90321348540d20000d0030b1150f0700c03003e0f01040c1d1911414000030300c11361003080c031082c028081d00c441045445e100e42c00d80e0400d550b440071003603e8548509040c0e61000348254014030541110321007500700340da11032a5005c18041e800c1100512601200141c002c60101d03001040e04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 385499154 1250 385497904 385497919
    0x9040309050f24090a0807120b04062c0705010c0f060203040303020903190606050108012402030904140103020f011407080f04170307020a090b060a12090203071517160309050c 77
    0x2903c218200300e900c00c20701188503e01803180421080c0c0002400c000303a882c1044070500d803003059158503840d10002441101c1c41c40c0c6a41c2042000c2c0c500744a14050380c1c4080344c5c40306284000080a03801c00500f500802d0400c100c0c05017550201c0d4400700c0040b6001e401000050f40d98581c1c1c10110082d203d6150329507003504c10381c840d036601450000700710142d190183c1010084c041e280d1004403080c1c9000c1c811083c80f00a1194a00c203032200000914020460344e0048030300d0084030402003000d4483c1c40030402c003c0c440020041003036003410700078480395074800d06e4041c02c1420b452100a855006038a8003400700c4c0c2010600c0720303003248c281084601604a035120680200101d01520b50340b0b070712021040380030350000e07207001824080e14000d45030751040081585017030001c11102280c9100300700102c0300101d51214600b80150f02c0601c460030280c00c072925001d81d2414034600103030260b002c0b0214518400144401c0010901c0b00c502500580f540c14a004a01c00a140c10054038140c686448143e00555 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 385500404 1250 385499154 385499209
    0xc011b0519080a1103030708071b17090a0b03040b04080c0a0b040b0405010c090303020309011101140a29060405012d030213090b03060103030c02150a05041409040309050f 75
    0x840b6005840c14000c2c03a0744241011070ba0203925912400103542000109181801041c000c6005588034400c01e41c40a40c030081da00850b0f160f6441403000d1044100c0119400038000000b4202012060043e154004100703107142070664400d00110341c001c002a10340c0030041030144641c9014042e0aa41c1a00040ca1200c1c40c141401c005504440c25542112998a00b40080054501410048003203030f815801550509440c0001540c968001c0344148a05558500644190707141c0045128000c640302000000cac0c029000000c10004420300a4003031984600c2c9042c080300daa00c807400c0310152042803070100c40202200304a6596080750700c031140307201c40c40b0300d0070151029410760103000313000084107403610381c0c0399030b01081012036032122050398154001000520100340140c1540aa89201800c58083c0103109030440c00c464120754108000180b000074108290300410856081044084880da03c0c182407035075015145904501c559406002040d40110555942c01d0303182c0980380c00707004850003550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 385501654 1250 385500404 385500413
    0xd0c0f0b07020610061d13140408072904060902010c0609050d030b0a0e0a021e0c07090f021204170d09030818010e030d0e0304150e040605030c011b0519 67
    0x10011140c95000300403c0000041e0300c1d2081e200351a80440300020090002451807d001da11424041d034a020651130b00c407980305414103c61418800c1d401041600d407076040034505840e0748044400184407900c6a000030341c0c01c640c481140c80ba0481e034086000035402845200607102d20180400203002e13240381407611000c1c00008113410100249582e001c0001e010000100185440c0600500341c0060328000010a201c1059000380403c0c0403901d40181410404201c00d511795101d02c19003061900000700400070900e45004100400c80216001e60510340030109034905070380c000708040c1580200051100707c01c2c501000715010400c580d0400d0000340c001d030601812940c403c2c0c034081041181056400c810380410b128820581070410065450306810f0b0b44e100e40a0050352415070011b000800c4002180d4504030000047c1c000a6286e80011501c0e0204100854000703a10090003a0050001c1c28040d1ba442160100400c100250031035480b11107050040c600115140b100c010710081400500522 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 385502904 1250 385501654 385501663
    0x3060504021305090c04020918010611060f070c020907141b0c060f1603090e01030b090d02120405010f031407020a1e031e03140a0516080402030d0c0f0b0702 69
    0x254000c1e035064540c41981500c4204640c01104c4201c0180c1004d0801764882c681900102041c0d1001004140d040028103294042180c0070b9000e40b0120f02d1010042c0001401440541d80c040e11a04102405241c1000302410600c11050001d00c038400281c0010b080a01030311141041200700c03036449446903061182c1c1910724001414841c0705119415030003140e4900101100d1000c00310448440c00c1c9225101c010b040100310b070784202d045c0044603401154070a81440418000c600070291a502405c01c00b216a0804010141786821500070f5401000c205401408440843d54286080c02142030030640480052030400d400000b032100c500d00384501a540040d00458040c0984444503d0b401a0183d01c104031552242c024007041c00580f003e103098807011100c03541c0090504001c14003201000f007281d140d079000c60310150f440740d56406204403881c4541c881c403411469030408170307000d090035000643e0b42c00201004d0800c020221100c1001c103d80446103d00aa40c0302c41ca00c002800d25040c06503c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 385504154 1250 385502904 385502911
    0x70c060504150c110129040902010507060509060103020a051f050a0c060608060a060e0f06100c0f0606030312110906030901110c0304050f0a061d1f0216060e010207170c0a030605 78
    0x540c2000d00886c100b0048100a542844e4200c161030400510b140c00d01001e000050816414403000740f1a0001181c000c0c024548200d100310090b01c055070440c810046a091a43c00440c010703e880d002103000100301707190340c10254000d814803603200d80307814000710750104600800809940c100f20300007410240000310340d8010703000c000040c00340701d03107482000a0160301154102c2640f81507001003466424284041d030050b034064508407941c1462a1685402c07445c001404640640e40c3e0b00f02002850780c01081003000d0400264140111818044084103038001e11100e0b0740f1460000000c212070b034100350700424101c2215142c0e1600c0d000100901c6031a50040e10401d800341c5d600000385080ca2070481742c848141d41e00754440c40d100050035a00e1155103298a07290a42007604084847c1c00c17041c83c40209240c0d408541e00801e54400c0300400c68494010780d034464030030710181c4501c9a440781e80105001d801d841303624524180f400e402c5000d0502c3e045501c480241c00064008002c824020141c020718032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 385505404 1250 385504154 385504187
    0x1110d02181002030d020a020a0605280e0a060506120d09080705060405090a2301140f090601140310150c110906030c0607110301060e09070e070c060504150c 69
    0x20000401c01408041d9050800c100016002048a143c61107142d42c0509030b000302c0c910448544480c01c1c3d03100d900b1184290340400815118142c000c46030340c0324010143d00f6116000c001c1c01030100300e003a8250759240218009080720b45440014149848950b042a51160f007401124041d440005014088014a000d8800309010741c80010540c1d00b8608110740480b44050416002e0340d4036640030400400007a0300f003980560031900d65043d820f0500940501a250064840d20410ac55400b00480c018100c02294011258241003011582e0004056010700012020169403561220303100303a44007180740c218240e03081c0c0c0141e0746170354142e01030442c2c00085d00c2400048040c030355100400600d88d008135600c0e54940c0c81b6404840d480c2c01c2c14400f501ca1544501030841011000e0000203007981c10750742002e80020744070010003488680811034400100202041140300d414401b00042c0383e4456446d010380040c0e10344010404001c0c40714100041180d40390004c115048400f80c004142a844822116 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 385506654 1250 385505404 385505437
    0x1a060a060f020d120b15090a090e0a020f03030d0606030522110f030f030301030f1b0308030c07020f030613060614060d0c0309022e031b0309020301110d02 68
    0xd0240d00074062010760340c00540040c0320025910100f11040300514001e60401d6031110b480c075056032143c1a400c01c0351410951890385886584080c0640440d5680c0030300681c509100ca680303841c14010540a40c0c20ba01034402c1c0004d5180200424903600c10301ea040b086039460600d0010b0641d0781580002e006c1c203010034503418034455181c00c1c5549540e803440045c041040c071300741145040c0741003c8000700704200a0300f0f4801a0100942c10760942d00240d1003612810000c2660804100424070842c0080c402546c92410035800c540300d00c0907c1c040180304c002546030005469055550781102c4409101000703044074281e00c1d00c81e12000781050314210441d203180c10000080755000b88a14828134107400580490705100030011450f014040c0204010705065071800140b02584400ca007404099181d202c3d520203004948a40c00d0401e120802804100740c600b2079400c0e00c91200c3d0342c1c140d00b952124900811034001d1400000e004101c9e20340300100074200050240100f5415401a006c02800e540801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 385507904 1250 385506654 385506659
    0xe16030c050906120405100603080927010b0913020307032a0c020f1912050c0a0e010501080603100615030b0a030305030612210712020a02060d11071a060a 68
    0x1914240901c080c9281c0c042c3d81801402c481d1540f28a0311030380030340035004440310070074540c0b40d280c1164040c1d00207482c008000100070640b400e000c0300849584050030307540108200ca42401d40c2000006001d240d00308000092203003c10b2340c0700364000d91454110074003159607041098002d001803030480d02d00812410912600c000e80c0c00c10903038110000600381c560640954407682040642c0b0400801d940d800500045000f07403004e01203000b00c3c060710f426407011001d038541782025441d00621107003161280f10089824009042075a1800b41103078402e0070b0501523620340707000103401d00300342c420320010082c80c1c10000070b5880305240458101c0c0d40d09131010403550309880e00788103101d1100d000c060003107842080841c07514241800c44207c0c1808180903102115048504070310381d8443c00f1452031a032a030106091081c8441c2103040d00c0104518002442000c480707901041560096101c282042c954442107103200d5030f04c01e03049858583d400000003c840b0909117074240981c4090300d8040c052800c59502 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 385509154 1250 385507904 385507907
    0x20f0c1b1f110f060601080a05090d0c02030a05010c031e0501030209010e041401090c0504140f01030311010e010908120726040201031e14130206071b0e16030c 70
    0x40854904001c1d200c1c0c8800318000400c4248210701000d44420490a800450b80000c02400b000c80c0c05000ca01c06481203003024800140190340141c01148810b02d44000e1000800c80010342040c090034a06007001000c410b400040d041007000d12014190b5402c110340b98481e0f42d45035000c0e22580080001d80d9007505141e0725000200c1d0000d0000a40209001005010b810141450141c1c814800e4000c1d80c11945d81905c500d080d0740c2103480c1207840034150f40b4240a00d2501d40070b050a01c0348443c0040c003a924160000200c400418400607040c00100008071074824029084440344200800003400030b010702c4e140902c0b2551100500c041510b104030302143c2c0700d0703200302503c41403000031614840c800d52400c43c2d0002410f602400403410b140e81c1d1180d600003810040c030201c2d13465202010010752000b842d0785d0846195001802c5042d1a00440010401030b5160404d83e0f510b641c0041a005041480c1803e5010300241034006044a1710740c5410003158030207140306981490f003540e80c24040f0390441c050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 385510404 1250 385509154 385509193
    0x304030e010216231f0203030f0a1b0f05041706061906080f0a060f060807020f06070c080c010b0604032f2b060e01020414090105030706050c01060306020f0c 69
    0x10004c500d5100d082da0301e64010b4421200481820080054102c4107848212035090764065240001580010040001d015968060b00380e010f11005018401d502e02407414080004155501c03c1c24004e1900b800070f1480e1140c010703030f400342410030100aa00704586200c01da850030101c44041c81121a412a492400c883c9144001101c0d51525003101548810745d4000d00810000d00c01024155a00c80c0020803c2166005400400b12500c80300c003141032500b070081c105560388207100c01551010f410f00c110207a01441c503022564104050307588501010b0700c160701400c101c01d0103a0f4010404034000c401e000d29191440c420404a02d0100507015004100d520081c942c42c40c00b41d40070313201540b144c02c0c4c1c91003d00f4080600b035440c00d15030320f04401692920201c0b6401410401c00e40c1d80450140319503010141505007143e41220314a400d0740c504000a503072100d05006420070001c002c21204070105094103c240a5075021500f55110074600850040b60340110840700c04034400e6030b0000003099040807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 385511654 1250 385510404 385510409
    0x14010e07081c050a110604030e01270b0f0c0601080c0a150e010c1b09022d030601230406020d03111306050c0c1e0306061005070609020a0b0304030e010216 68
    0x100315201c2d803100b00400e5805400400412090128aa59680d00040c0a1114a04c240e1203074440042c400b00c0400014401d12100310466499144152030401d0761081006210803a42621002640d40b482804109254051401d1072030302442860b0021030111000f2403510003022003a02c002c1710840d91502504c151004545642e0b0224810002c150410351040e10850304890080440c128103c0c009041a480d00040754070907004036078081805c0322103011001e40c1201d50020083c9040e581c404004076481148001361020b0305020780c1c0c480302c448070f242e1010960084040102210744555441c0c3d4080c1d11040030741c0590000910385480d4100000b10002500c0328000c000b50740c0d1012609140301980c9542c0301040040881c41070848005055070384203e41d440c0c0810500d01548602c136508285807418401070102d500c43d440c0d0300c0d4580c05d20382d84a41941d0701c440d08401c001c2824541c3e80080344600003036401089480100000308028143c104203202c10a51003a4204e6045d0010700180d618080500d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 385512904 1250 385511654 385511683
    0x10e0d08010b0d1b09080708120d0e1501150e0409050d1404050a09140c0f0d090c03020d2111031b070b1902010c030605090a1814010e0708 61
    0x100010700c820b021210180c03074000542030f000100000c413900b150440030a44501d9000051030380c8418041000301307100500c001d003800d90080901080000d08072016020b25240c0e001d501d03554a44400b51070404001345544510060f0300b91503156120514034920f0100c0154a03804a240c036045802103042c036105290303229400c00d01601c0008980c0e50f00b22441000740e0440f40e0800e60501000c100350340e840300d102004050203800014580c4c440718140046070700c001d01c00c148a4034103101e03550340b580c0b909040300d00e508507881c0f00155640700d602d8242111201034101940000044400c0000c01000112051288800403002d0300040ba090b40120781c20313400c90811141d160001d00151031441040c401007151195004140c03041c141e01e03a584030b102604880302c10200c40312442e043c226010380a104a507001c00d29441c041c440c190501020840000c0b002c0c1151030b0746541d07554038901984c5c031011041d1070705611400b101035810f000100a40a00b240e0a981011030081280c0052100c0b000074510b0710000710b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 385514154 1250 385512904 385512917
    0x2401090905060a030210020a150b0105031801061e03050c0d030f0e01030905100213060e030309060a020a02090408190e0d11181906120b0c03070509130203010602010e0d 74
    0x1040c202401a0401500ea50b400c00ca03c030101100583e107110107a41e600b9110f500400b1b0a46560402c16031134090300005400903468480041180c1c0d80c0310b401c60740d000c4d8a02c5034000c04032000390710642c0180100d40c040c150081c0c4141116280e00003500e91002124007500c1154900c0844208000450307980300d0f802030126800c0c02c4d080d11101d0050080302c0d49480d05040010740f00f9001e8403280e05181d42c80e010038200340e03800118000a071030201e1900e00944080e00c0d0610340780d0315440c04243c0d04e1040804070341c4500804582d0183c8584204a40c401c07255014003652007906040c0380203605a0401240211845504020300001c14442c1082c2058250000c3c070001c200e038003640f40e801c00c002d801040e01d070f000b501c8080344c03a160008245070310307002d50790784000000600c1c1e0740c001b01030450300940c21510080048141b1400812074004900760401c005006555403034460f41015542d51203490703032494000c1803000000d494282990301450490308660020f01601c2060403841e615580001d0911020884 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 385515404 1250 385514154 385514159
    0x209010c060b0604120609230a0204110c03070309030201082412120a0809010b010e1f02010e010609050603060f19050a110403140d020708030f0f0909010806240109 72
    0x240c0da0030182c078204000d0502c514064864017942c4034004181010f56456486502c007004008003205042d25000a060076410031100c9071314400e0b124080c2480c082d2203940c40301064080192803808981006031858202e07a514605490b0241c00450390344002ea004c6000a0005005040010844040c0c25420b03020307200d881d40d501080268264203010b119400b0302c9045007945280d01840000c08000c030860312a000c00b860074108440c203503400d040c2c1c10b60421142209245540d11402e050650200d05080100c0d40b1040b485022401048031358841e010941c284280001c1190789980200e024203003e400307407139040c0e0b1408001e1940240a40f030700b00f40552400c4540383d94982da40d200b190000748600020403116005048100703a0f0304130360401d0b145c440c00061102100041000810100085400a016824500050301c0d07181d0180c0242e00e6402c4074000345181e801c203d42e00c03c50350035540040107008256120f4015a580d804100c80b05a6034004100282c4140da501c0c4503400304800303059544560250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 385516654 1250 385515404 385515413
    0xf020906160c0e1f0504060e0a0c020f03031017060c070206180d060c0f0f0806010f020c03030c06180703020906100507200102190b0c070c0305010e0a14010209010c 72
    0x201e01540680b0028144000401c6050640b00d01c07a000300080712803904144220042a080c9400e03a50203503125501d0b000040081d40403d015a50b80500d544c03100090722035a50400340d040071000c0e0801c0e403180c0400410010454010390594003500d41404525400c0100a864599a1101642d441c0c500c0c981c280210401403910320000d00c41400401280301e603600c00240402c3e030b2008000c0c022901c3d291a00340424940740e018040c840101003500c4c00710492504035202034120540035009604204820015507880c9008010050800c1000b600320b0313556840c0d84625645400050310030501102c0850032149001c540000c0100980340c0090529140d51114001c2102c809120300c010400d02c50284a001d0208900002c008600310700c1604d0030344088a143c0c002814090240b90702031180310280702e651f011407403042c1c0180d800b540c04007a0b650b03a00c2803420040c60f200c0b49540010219824040d441303940788000700303009190034030410701a00201c03000702c0c007507080c0d02400341407038005010704481c2000304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 385517904 1250 385516654 385516687
    0x9271e0b090118090503040909060c031802090f0a0b1503040501060803040b03270a0317010906080601051003020f030702070f3809060c0102040e090309031b0307050409150f020906 79
    0x1300c2c403800480e4030301a40c40c469881502c1080c1c03402d03241245d0707600c54a55456018018401c3c1c80c010004805424545540041d030080809400c02208041181c0003812040300740e031041210100060010000040f48130901c8c3e0507510480b0704075051350130040c0024a0403000802d55040c0ca00f4204c0050540d50350341480102440041b98001a1a6050384010540b2109110010000c0e00982e50111001001401040c1c00710b01a80300c40c2049240102c10010b02002080031415540c0c21500c10242c00580b07102240079005000d8608403002c00001440300203600000c14108079215100001c841c20382d14825030034460101041d0700c850700c0d0122058071082002e09800f18540038503000940c148420a00403401a40001545071242d03940002c0a00c000c41408901540c8940072400462500b20724a01203922000a0b0304076490303950424142c900300c0c1e501441103202070040684200802944c0f400d080211006130b0403e4064145094842d6407224280c1c000c40d01e40d00c10241405150001c0d4070701c80c9510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 385519154 1250 385517904 385517921
    0xf0402030a02060703020a03032a2723090f13021201050106030c0e0f03210409050c09010e0a0f0605090d0515010512030a09271e0b090118 61
    0x2600801d00c030790006a6640f0b0103001c4080c040d80c003c0212841918014003112841e071808010060600888030415000110326143c1a4003071518041000c03032a040a40d02d100000c1204094102595022481540321185500a4085112640c45802c3c02c502800494041035910412840c44000010750324104c0d07866203414148060300e4000181208200380b401c540080e048600020340760070401d052075901036985418a00708451860b000c2ca814000281e07a00059014082301c0014107600c210300350020030030b4030000c0ca0542c01c207100300d207840008056154006a000c90214000e0f020303e23038540c00d0003035050701a02c2400001c2030700e00c1d0030900c065031035401c00b0032a40d0f800141004034a001800510589030081081d00c50002d1a50502c41002201c414220700d1040c02c1c0c0c41440559505940b00d4002c01c01c40da400c04d03200305403103002801c0484103021030009200186c00c0c40c402254004590002d070040022460301006641800760401403101028801c460183e01c2811000516900a600c010311 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 385520404 1250 385519154 385519159
    0x50f0702120109060203090c01080c070605100f0306061d09060703050c0f1308070501020a0803060904080c0a050c0f030d091802040f0f06021e0d0c05070b270111060f0402 75
    0x207024801c40942425035806000c00c664058020062241444041084280003582420003840510b403112281126000340000a0107407525540030500d00030007070390b510000e030514020142c442d686030b05100c0c0250442d4801c401c113101d86461000543c0c01c801c500c40b40119800c501400c015147d086084000d031038060144040d1000805c0f40f0000607060308000c0c10f00c02c1c000804850018a000b0f03d45080c0f0400380c2c01281990030030450030000450503001c0b694071880440c1c11140075112414102001d004548207203407039104025150040c0800020100418041190700c3d0540d504880103050715000e000c4154404101c0001e414005041c803204240340c040c40e06200103040030b5944010706201142075000810000300c0d441c083c40195414486400c8008a0100b0014505444507540b40c5e2440f000c1d0480301000a5207844d40308214040c130081009007a0102025150a41da40041c004424001c03a44c007002e035644010140c40e54051844015034841a40c00343c0380740c2e503600c0021401e000f00144101d9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 385521654 1250 385520404 385520419
    0x31b02070e010b0304020f04320405120a0f0309150903050d0506120703030c0f0606030c1715010e07090801020a0302091305070c0b1e040609020405062209030e060417060c0703050f0702 81
    0x9110304144030700c2000c124276003c0b01a180b801c240c00e115007005070b204840320520200f00000090550006500034000c05503280000300c1d07a2041c1050303d2420500795100d0503540c01d1030441d030b09040c1d1010150442100504003004251615130400c03200385030481c139400320f0b50440e502c2040840c0c010b08803030304124081e004500003011150351311404c0300e1407034004880100203480c051218070703000c4d81c811f0920608400142554044600e4651000d0f10510401d554118158005030050380318072203000040103d40b00035529000c1142025010b500103107046400b910060042122810701400703180d0107802691504a0041940d4842030040f0780010420070401d0f00300c402c1201000b200d443c405108030f005480001da113242a10401058400c06002c1c0c0307100d40c08030f0306101404002d00b00e0720120070403491800500c20800d482d086e00c0e03640c81090115030140c1d0210300040c203500543c0010150380d0302e4000307848041e0b5840b000d40415000e03040c000340c0000e40030310a481d2406241c0c401024024001840f40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 385522904 1250 385521654 385521701
    0x309060f09120606150c0c0506031906061d0a0b19020a0b0f060405090a0314090a080a291b1c052e0e060907031b02070e010b0304020f04 60
    0x15002ca000b0420032541c1542c1c5040c200300b0040c103200c4c012941007240c602584601a1b0307884615210405000e140c0c4520000000300304240244900303608100e8a400042c050180e031402c3c040c02040510b4800e100c0701540c6007094070340d86420903028003598180029242042c0c0320210a0003100c1e1700500c0c0c05e0035031040400d1000072038001000c2600c0b036180c4544455483c50207500740425a400900a20b5030750307100c03c6072030b0300082d0004610300c90300314144076840c0c6400c070690018040322404d6200a1590080c0400b406c00d204ca4014a808501d40c00000c40a81c03190b4680c030320780040e404644032500101d6100d900c0000c802d4207801801100d400e20702d00f044500d940c641a00481d4801d46404192001c3c11802c0c021240c42040015410071034811420741040c0742050051741d21070020b049910621180b4002825035020340d001524441c8050b408900c03640f0101000703903407000c59010301c1e22030f095410000265000050b00700c0744242d60160a04150015800500015207103225841819000e200c119 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 385524154 1250 385522904 385522919
    0xb060a0803070c050a06170f0403140c0f1c300606030207020f060a1713060e0f0c030118060509010f020d0902010909020a0503040f060209060a0c030f020a0309060f09 73
    0x160070014003c05044007000c0c9001c00f001410308280d40803100348100110b45031100004503c40c00e900c10700201243c4450b60b51031804030756850702c40c0b48042d14040045814501d02200290306d41c000c030f040100700e881c2c42041e00240d90039003270003000c4034000421001c04181c0407074840c0740c8015100c03000f50300e20380d0355400c0c01c040d50261007980c1c20407000680d000c1007180541c42e02101031110803109070790703103441c0030202c801c0100381c03004811501e0a00641c0d207000c144045e2503840207414154010302c0c1001003c000c980140e444500f961084a041d110b01250103c0da8034040c8260171040050b4010300700c0d03006865513464003810b030040049010b55640c958920848070b071070009100d03070104514000b44101c1c481c8005814011140c1000140520500000990303540010440c1e4106403c41500030401c0e40e17901c0d010b000703841011701c0b1542000003c10000310f01d54106c030481e10240e100e6100d1f60f0310b88800031022a6500c403800d9019001810faa0400c201550103200c96006c405518a400340c00c0e81d85074400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 385525404 1250 385524154 385524157
    0x607030210020a11061e28060305061b03010806010302040506030a0c17121801110a08040b12060d02030a0b07110f03120f0c0706020f0d0f09020405130b040b060a0803 73
    0x4100e010a00449620700e01103020f000340c0364084603200c0d01302d00c0711ba59400341c0c101401008060084035000c4418800d60301d0000100040c40b14007540c000d200f000d803030b071524546030301702a80ca0340d1200c002d0381c40105858040009030b0b8160f540d24802004243c0c42c40d001c11000c0c4c00064030341609070198242c07682c003107185115620f0107400b00d020407008a40d104444c840c6060b1440220711039500040c42510040f00b2601c10000503d6001d20309a03400d0103041c18084e060280748800104000c5e80010f0020740c0714012800780c03030022000390080c0c02c83c1c1e85040501c1140b2101c000001d51540100e4124400103844010654224145103000d80e005e401c0307003021078589640048400b60950020600c524085880155940c0c40032a4150081c01400c0006160001e0700646800800d8990040307600c0c0501032200e41600c03000d0203403403018028045442c641c4002040403020681c0500c3c01d0200180039106031003030030b25544e5031208001c02542c1d07881c1c031052401c05005d007400340d00c01200c07040092003180400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 385526654 1250 385525404 385525417
    0x1050714030a020615030703050c2412040302010f090b0403120209060c1006090b030703031409060711010806010e060d020d0216031218031202180307150905120a02060703021002 78
    0x3001404d45042c02e103480c100e040303040302442c1d101e6840840140001400070030068850345054900c4d820240440800c02101140c014021904410116840740740c000050301d66405280690000c004d41d8980a00e594252500b05501521078603c41001c14000703071080e240300e107000421038801420210301100044140c0d1280040e42181c0d401892504109401803141c40c00502502d2070405c4080703541ca022a85800c46844060f00384a0001c1d200c100c1458203000300c411590b001019541d4030002844c255054000100006000460500010f0599400340c000b000004200400590403c2c88003501040079610461150036034030340074840782c17150b0100440b030344840c02e01ca6100c2490440306507030000100c80f400c1f035445e00792015210888010031341003064580c1c0c1842d80d4102594030703061184514190844002881d82512880e6000610005482c20340320a007046913443c496420b40d030308204115403110a88000650308000d05100040c40e200009001c13281c402d005890414a900c24504102d0f080320 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 385527904 1250 385526654 385526657
    0x91418070506040b07172514060106051c0c08180708070605120c0901080a050a0b09090d090e090d08192406050a17071413090b0a08060601050714030a 66
    0xc0303020400c018062002e084100d0341030100c5410030008a21400b803011f442d00d1000c4807500511001814852902c43c1c40400c0b1484d5030444030f90756940d91000301a6440703116000c0845450042240e0700d03e0301400380b003001c44041d07a0b034504a40c55000d10f58819400d0a4411042842405800901503000f4015a801407140380c031034a455241d1005910710341c20004002c064040300400000981d0380e04076210f02e40203005540700003007540c1d417013049900a01d88045260391010860f010040c0f218000100141340303c40b00d03a509c02140b5560f03049244852426104c40d40c07103400040955100c24405c0d051942d000181d4020390200031440e0f00d050f412501a0903000780501861200911104040f17600000100054a03003030740f401001340c0003786010300400000135014010f01c042030946220790102d1400802c0245074139650030759810040d5010b140c1740709074007446e410708031040b2780c520f40790301000c0456010801800069031484011100c95000380d40458121159844003a5846030402c090031110341d65 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 385529154 1250 385527904 385527907
    0x120d270302010c08040b04150209040e010f0e24100b070804061707120504031e020709180201050703050c010221091b1e040207080a1701091418070506040b 68
    0x2203080090a555038403501d10203105a2400b8000054480308a099100d60002c031562042076409a1020291043c820078640c01400c00b008540200d4043d8040512259042c0702000007141c040401910b0300000d0901c40100700240340d07062102c11000480300d40c08001c46061418280c1c84010b00c100d00d400c01241507802840105040c07041030b400c505d0503891081c0b204044056031520391f10091149200c141c0c021652030f01c403808107003094012451040301601000c040310441703440c00c40080d03030f4900e244900e800c8107040c182c0481d041c6120f00709141c18150180e45c0c2501c0c044260700c0940c4e541e400200365008a6608224a11221011113442c921400c0031401890031400e100800780e14005600c400b540d00308100180160305c030343e02c00d07080810200c0340081c150f100300907040010b8001d0045034006413002e1400102c41400c1c070f03070001030041001c000b001c0002c8582d88505141c0100c2d800032031901c0c4035503102404101084983c9041045d6460340f00304590480c2d441e42d0101d0301e5030f00681d0150080380c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 385530404 1250 385529154 385529231
    0x9040f030314131214030a24060c03230a080118050c04091817071202030c101802030d11010605031203040b2e030b07050309120d 57
    0x2403602601034900032410703906100d420520780c90302040c3e01501006044800c41030640244a00800b140050007000d0704619440c1d2820350384160142680744000480c0380801040c09070781c1b40703022160400b40e51041e620010540d07070395501695101d1700c0f582d10004004151074029091455007008080001c0c85588074001d651414210401114121540108150901c410004010f00400680c0e003101e0b420000420000b005999041a9081c3c5440c05488016031040c000c82d031000010062210307510484290300b115000d20310807600c034000c462010010360485881c1c8004e0300c0850308080704a04001104858100c000e500107860413010003410000300e03001190503100d0308828803851006080030340c0074154140c00203e4582003840010001400503d104002c202101c0f01c3d40c07000c0d0700c583c01114101d034949070710a1020102c040940300841c0d41503180d20001d1051403090041c1d0380501442401403070521400311401f04107412003020382c804540d070341078548150061150200d206004c0802c00c1d060310700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 385531654 1250 385530404 385530407
    0x4080d0c030e04140703020d0e010501030503070c0e0103081606020405040c0207081b0120010908040b071205070f060c1107030b0619081018020a0b031504050105011413030209040f03 80
    0x1080d102602c1e208500c0c04515440703c3c040072200c0c1d0390000c0340d0b00c0c0040e5120b9511102ca0010803a000d880325596107028004010040300000510180d0b004012009003640d40e04004141c04509000c01412814240440440e020200510f62400d0f803003080b01600f4151140c001c0b5045800d1404041d0042c5d12040c01008522418402191482c82c2ca031024000520381d080042c00318104201c1d04049001c13190000780840c1c00039030009201907442410595907903500c064000543c1c101c84c90507601625103840400403503002d101200c14480e40a14103007140344070340d201d507001080e40c40c0d52076050101c00e48032500161014004000a14499020301c502410071606002500043d41c410a14406403400d0030b000e03503400080d100c6d01040d2200030110321202002c408174008102d10300003e40022219001084000c00032015511034843d04e8030710003000100d2001c00080e50028030584d40030501a0f02c5481c24101e101c001003480780c200c401d46d408802d54950115200947c100da003035441100c43c007500b00816 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 385532904 1250 385531654 385531667
    0x70510111306020f0d0e030106080a0b01031109070c0809180a09060b031504260d06060e0d0c0b09060714030301030b0c03010f050904022d01030b120c01110304080d0c03 74
    0x10900b0307200070900c92241c5900c055030342c0604910102030241002c00010960b03004d4001201a046040554450345071071300d481711030558280000c40d0089483e09000c1604c0c100040864403503100d554503c590300f100c5d0340340d0000c04d603c5072110f035810540c1000008480c440d6200e00f64010342c400d1000150710502814a02c080f00c000340c2078075110b81c1040d0a00c0195880120301260016040f600211815018081c3c6015100000f01c01c0707070f004078000c151840700004581c02101191055110006000040d9003041054511210010032005e1614030500454003604003400010001406075840c10109440340300c8551030600106455a01c0000140308110b03c0e0f2404980201030a07132240d003554140340c0c44c0804000203000707050042d20440005015503440116880304001000355400100640d0030100000a84482080b40420305040c1c0100940c284440000000e0000c20082c006902141004680324483d001c14181c0c2c62205000c0807560900c14002941c004040b901c07200303081c40c0a0720340138088 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 385534154 1250 385532904 385532909
    0x11070918140322051206091f09080c011b050301080c090604090f030c02240904090c03021e1801080a3e090108010b150705101113 57
    0x41424144200c0610380d008088100d40e560000080406500c0341c0e400034614080ca55101d4000d60350a415014202c800281c808165031064800d242d007801803404442ea6244161003010941e40854022030401c0781c443d0254155035200503000c0784402040d00c030f503181a08581c43d9001d01d6559049420f072180c000c001002d0701600c0313074102582550301d01505251a0b550310b2a01c580548c136804001181aa11607001003800356000611aa0901860a0003401401d144030200d000b91030b114220000340700d2a11282c055842e1403800700c1d282220701d5040c00050401031030110350b290000340020005903524200f80b070700e101d07040c0400480110290100004c000d0f581305184680c00e008801840144004580703014450f40005000c16900c0031503039243d1507200a810307203031409040b00c20218a0302c42c403030042c5140b100d0115500c01d403c0c4d0720341004500721014101425480116945115082d030492000f50a03414014016190441c4003d0421401c1c1c1d121403c082c4103c001c0001c40145004145404501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 385535404 1250 385534154 385534169
    0x7051002010501170a020102100b060f0c0a120e0f0d050a0c24031521050706032003060325081507110f06060d020402040306021b100507020c10020309101107 69
    0x10b6502d9400103902c03140140c0c0110f03849d07074458065009035107600b401c541e0380f840700c00d4102c0e03a01c0d1030f00103035251940c0c04150115103400070303103244002c01c45c4904a00415500002c0800441c0240c40c8200000c00b2507601003200c0c01d01409210784c01060020080d84010444000c820000c070f03407403510b2500241c001c8aa0341c0141441c010a400c0d00049452100059405280581d0021417554070450386c107041360000101319115022020441c1c90b0325400000c4241c008448610b400a075400514165000880f0241d8065000320400c015165501221070400034a00e14a82969a203900c402c83c14441305166029480c0200300a225840742c2c0b00240d819058540000b0f08041801050055112200909010320034000010003600355901c540c102c5000319480034045507141180380c60702141f500010b60400b0f0a0042c404048140001c82c05810302c1400550f0140002400d0302007001100140e8a81d42011440280481c07803050320380040c20603031a00d65850b0010b81d10700400809181c1249a0406403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 385536654 1250 385535404 385535413
    0x3020306010e070c060b240405011b080d230109060e0c0304030807200307121e08070c031b0b06090c0c03030105120309030604061b05070f140705100201050117 70
    0x11201d5000130103030350950348a84e0105a175017480e00021320541502c2c3c0c03070b06000306103d0540740710310440300c0040c01150b500fa25090000c030024500c446540500c1140a441d01da0b040000741c1400318198081e0140c0e003481c000300364044500d504520000c0000340c10803002569921402e000c1c6031882c0110716401030403010305e81c0c91482c0a0f5402407803401e020f80980c0900403003918505481609264007168034a0000882c8d0325510713581415070f90021a85c044102181d04500030000c0004030b002607011800031500d8401c442e4031010710448a814840d101502002440d5110b164146420142035052500800e03121115080206c1080321101001c1e00082c021101007240a103070301c1000c0150b0781161000c441c1c0300714100c18031032179604510522003941d90600882e4100070070880141c0c0412009400e40c0c9180080c0c44000200b56003c3c4124600a40440420300c000320000350100c01b501e410304160000c0d02e0004e075440c40800c500200c180c905201607512013005220031090080120b000e00c100c1c0d002030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 385537904 1250 385536654 385536661
    0x905040201021209211011041406040602120708090a0e07030b011b111203130f061701050f150c0a060f060e0f0c0405060703050901020c0307260109050d080103020306010e 75
    0x2c1c1e4410074001c1c1041c0311400d81540c039031150717001d00c0b484158121107174040c00b4a80100000c4540c0c0e6006001e000e9005400c40170690b00e03400c2000903a000c0ea0f02e2900105180c06468060448982004408aa6003c001c11041d101612021003100040000008803003107410110005403e45442131581c170f04002d00c10031034440f40000c81800740402034019025000c96140c042c042208c01c4404001c003000d600c4005260380050b140c4d40d1720700b8100c031400d07069498265280c2104546181c6001445541c8000300c40c0140454a000c0f1a0079000c44402000e4500f48255505858910740011440c41072300d4012100c14020b00c1220300622000912039081007283d9410481640b040c140c02038546880e0070881c00c00181400c0c1c41c04210b074054a0004d02c51500c95105107001002544802ca01c14014003560381030b43c0f0503050003d0900140d43c094101e04034031b50170a0196000c02c80400f1300c201419034882a0040200d00b0a00500364040c40664490b01c040d03065005161801c8810f3f423203c0c80c100104000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 385539154 1250 385537904 385537909
    0x6040506090a0b04020d090f0c08070803040905070201090b0a021b010e030406080408580b040213030b100b040303050a081314010509070602030f040506220905040201021209 76
    0x55503001c0b254181c00101c4055000c082402401150686100c0381c1c6080c0c4c5580500070302c0f0080105072072007103174013401081c0c94914884c0c4803138040c0316440c00c0e6441840705000d200a16040a0b0703020b0b40500c000600f4102c60384400702402c005542154480d40e0015441d0682ea105982c0440b01281650081c005d0079a5944803d54900c03507840780d10208131003803000c40d08010700342046403004079801c0b500c42484840c0000781c80203130003606c05282030404080d01d03194a00d50005261003800c100300c40100790f180b04200c900780180141501265020358200001c80108070030b403082601850045103c80150306d0f00344403280d20b4a0180e0081b0048034428403003000066480422120001e1310342c80d1212035500d40d00018041c920100b88011301c01d902449106054010550005104005d4002203500c09542c402c0e06030f860307201d0000c2c80c040c1b21500304810321603820418001c03c10000040d5040844401046074540e030302c0100d40054406648030303810302040d580c1c100540035200561071881454118007000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 385540404 1250 385539154 385539169
    0x901020304120809060301060f172505040906090f0f0b0307060c0c0902040b09010f090f06210504230106050609041d102a2003070c090b040506040506 66
    0x184002c05000344654410001c28400303807131410b00058407454480d44c4446003e08a00b0000303c0000c0045c0c41d4031054164200c0b81a08a80165a20140c1000c2c0e0303100c14440340c3d29010086501c00034031030100b1000490440d030f84605c00082404481c0054049548400340c025241c13030041c07183c01710342000c0500c0207035600428070b00d040350031504015031007240c43d160000612090364441c0301c0312440401c0001e2508080401002035003800d0769542e210700300000c401d45050300b06004031803070f00300340c40300074840d9600585074590f5100160b01001060881a07003c101580e00c12541158548000440d80c1c010308402444281d010721807900034070119040402040d40b030700036504401c0c031541d103689041d510645d8482003c001114404281ca0380c220030180c850000d00354861178804c04803a0710f400030390341c2d100e075565082040101d0341e951141486485a405500b69103601405410b000070030064000400144c4028010541003034007048a054038002c000032205c2c0280315501483c1401300300b0074959201c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 385541654 1250 385540404 385540409
    0xc120303130c050603010e060420090427050a050706050306010c06020d0e072408040f020d0c0816060914030d030c1407140f0a0b07081302040527030901020304 70
    0x2540e115440c15040c4050420080d600c1070344c1080001002040d00707049011403610484094605000e1000d013261000070f44121602d540050000500c8281004d203001d4004041c20144100c1040300c2200c0d04c201160300c2d5007141c108450641c410a101820030106104100040c0094208981140f130000e0010348420181c10b4010f00c010782c00190580f04006a41c004024601c482c0300315402c494a440c400e070082520482c050780390706e0300f09010711703481c0344100c040301e00c91a03100c88000412691340e07083c041c080d410000c08030703030300200c00c0c00125143c2d8040207002071041c1500c03440001c203450100090a144c0d410b821014000102040e400c64640780014a55000055850009506243c1540071a00c108101e00c00034461280090340d20184041130900b101d0600b6a42c040d54041c03118181142d03582e0700380c1a00245040c01c81d0000545d0340c5c0c001c0d03083c180e10500940480c48031441c60360026080780c2040780c44e031924a5408111128000c20145582e01a070002001545000303090000070f5642d02961 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 385542904 1250 385541654 385541671
    0x60e1002062212090810200702150c0d180b0a0807021c090305070504091a0406060b0a080901140907030b100803070c080114010f060c020f06030112050c120303 70
    0x642c003031020300081120a94440da00040140d2002c0700e11031004040501504c1050500e1013403282d2040b42c0340440c0304c3c08050403692442e00d02520310020355588107800030801a40d0101000107050110015030300200b406c1c018040140009040d10310014024844080e5655052583d00c0b60501c03902c180304040b500420128109414181d0310320404034540214659008082d0340c40c2c860f144007868101d06001e05aa1159050341d10203034540c1c06100440b0010074007e09040d215115000c03081854002054001c0d010b92800f10f0340a0b2100e0011100d54000c201031000960300008100314001e00303203c0e404001c0e50319600102c0c0c0c0e041440c0601da60703645500000d8900b21001c8040b5103241c1c40b140821004040000c203994076010701e414504480c1d000c0d84103941a5508103500c12004031010b086190590340b0306402e80e00201e0402c0011035082d41c010360b0482c2c0184a1b02003500d0150765400145008261040d40100320340d01c2481d01d40d003010803248a09001c0c9a030034181e020700b00d1011082d2a40030380d48 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 385544154 1250 385542904 385542931
    0x90510120f02100509040509010b011b080403051504020306092e140408071502031b09030c090a021e21190c05180303120411040906020c0304060e100206 67
    0x1420141c0700d20040e050025030210340b0a451014594000d070203030000c070200703c508001998540b0300140c280d91a0a044500042002c0c0100103c070140d10401e21800340078400c1c050616450380c0c1c60364a0050703489801300c1d0611f0624200301c110328042001d9a840408100508010b072213400c010445500582520121440105281242c0c04520340c070076522684051703e1401141810705100401e0b5000b400182d48034003400d4107030029140e0b24003c6078084c0409403a00d05042d00c0c403502d4440550130640a40754123000d40b030b000c001160f80e2240c2440c00343c10704202c01a6640130888060b44402e4085140b40e88509081c8058119004411884100541d048a084055036540300c0c020340c045806200f010403152802013440c0308643d128002c1c2420556003445c54012180754002c25949001d48410480510040000540000d424280106142030080c06c042040b0500395241c1c8160381010b404800640e102203010000e507a480310440b000c400c02510001400d0b15160402912010001c0100c0001e211 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 385545404 1250 385544154 385544189
    0xc040e03090901210b0f0a061a0405130e030a11010b0312030c070c03050d0908010b0a23010e18040605070309050d030c05091008041727031507020610090510 69
    0xd10190aa0380c50750145c1c1040c41844e104120b040f01c28011741d4040c80c000d140c46004100307000c0c0120030404000b01d000090f42410700d02402c0181111a0441c2051820b03110105000c2a9a0410141c84206025200e00c2402489040441e00b165180102c9612940c401010103011810240840f81c100500f80c82039903481d00c82d8145080d4140f200d0380010810302c07a68a0504030140e100000da42034071100070080c04803d03481820020814814003800404200029404820040200d03000c103032401d040c103000314008481400a054032041d46d484ca00300c0c41030b80041004121151080d10341c050700d0781c01c082094444581702c159407111809440c1c000d041d5503250740140d90b4028010354030f0b071520051100c0e402c205101c070002c0002c4019542110361602410a0019040c4800c051b2150103050044c07900748100540040b40701d02c900703204502d81500400c540e0246d01c04405200d24461022500208400d003000c0301411000401603110414036841c00b4140000081107090b1a821100c010751649030011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 385546654 1250 385545404 385545449
    0x10b210c16020a1508040c06030501030b130c050a060f020606030616050d020403150209040506040e0d0f180e01060f0c0201050901050a0512010801290a0605070305040f080c040e03090901 82
    0x56003001104c0d42e100c0015890580d03101d40b4141c40b42c0d1080c2c01e81c41c001c5607100c90680544000303020060041c5190707800a0f48540c10074000c8a080c1b40100c48071091907680381c0c04142401c1040d045034000a1441041802950b0104501a0040c80682c01000b4a1901c02d40401132210a4040d203410071800041c45925007a164041e6401f81d1381002203802c58490740e5050400a610244030796004605140c0050b04526203441290589041a0042e014464400c403007100c074607032100c0008091141404003013044801802c0b120020b4a810719125290b5418801c014040c3c24440c03006508201c4410300010050364427800755154600d003800d085445c1c00c2d4852045c0d50038015921401803007081c0800005441005400000100d00c000c1507002c1c600070950b9030030b1540401c0d040d6041d0420740101c010481c0724810b100401c089406440c10a041984409084d20743d00080c0c0d01801541d0711a4403100d845140c0351103a04480404a0021443c10045201241100b80140304000d10302d41c101c0312100211 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 385547904 1250 385546654 385546669
    0x10e06150120010f1a0d11060306060705060915010b2701030b1c2a0e040809031c0206061e0108070e030102070c090638070209010b210c1602 62
    0x1d8450300a00046070104042c00013401c1c81c81861301c0480c1710081141c103a05214420355607403030b000781c2c4510750b14202005010240d0300c041c001c140c005e0380800405000c220123001b0340d8007618041c000b5044403d40ca0714008841c00040c0c004a11b454000c2200392040314140b0902c110700c025050390280300c4c0744040e0040c3d00a00ea04182c0c550071804803c1d44001d4a5200d8070401d10413403140c0c1294094603404140d01d10445047c0d082e1070000541ca01d814000781c844601c00d80c0d40144502452464200b10300040303824070000c08200f181c088824242e001442d50180056a80410103441c0307801d0280c0d804500c0f0354050405107c03d070510044501003203500c0c0c0304200f00c00803e4030240081d9615100b52a00b100d141c07085124200f4003900c0c1c6900403807804403203c0e003241080750f4080690101f20b10403901100010b122050f11401010800c03800e001a12464160781c002c2250313804545c0c461041c1c1941c22100940b032005a03450b15804020000d28249000c1591aa10400040100401030380d00c08034460 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 385549154 1250 385547904 385547957
    0xf3c030d0318080705060906010602070807050d1104060e1005060a080f040c03050303100504150605032e0609080c030106030314070510180c08010b0306010504020715050702060702010e061501 84
    0x2c2d4000070b0024107005d0000360060140ca003d004560107a03984441c200e856080500a01803281c025050070030492030540982c940b21400b404c413405c01c184100c000502194400d50083e44561001002c1004030800302d01108001c05080e1030b01d6250104142000b0040c80300104041030421705803007c54140100d940f07904001c0d50340803085a0381c80c2440a03515242007510310820344114100303500e4507074400c40d5a140302d045800c50340700c090558440d401000b090b915401000d000041044914200f441c1040c818540140325a4403050750301402c00d5151030604802c0300d02d0702d00aa0416070100b0000350b000146c0b0521007a82504652603003894613005081c80a2840300c66026810070302c000243d10041050342c0002889010090303151a40e5034040f5090b628001003040e45500824010419410640c004013081d40c494400240511410301403030b012500103640c240c00507440740c010000c0907038092050b240c41c462420001c00302440c080c02d40d801a144222015810000b10f505e60a610f099402140c640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 385550404 1250 385549154 385549163
    0x6030b120d200c090f01090624080603120a03020403020a051e150d05010f05121f0b0a0e04050604111206010302060a020316081908070507020f0f3c030d0318 69
    0x79174140f0400d000400f01003030251107503252a01800082d12504d01515100c014845421607064001c16071058400c180c008021540600542d2101581c410f4071f80c004108041e00368a0040e1507900b10300600c00351203031981049008510701966143c91640355040c0008591045640072580c0e1005d01001e496406111110162142403900106202c0128520300054601c10b69001c00c00b140c030718401903900c50401c95030203402c4003400519032158400b43c00010409002500510495540d00d40b43c162000c4101c80c15281c0e60032580901080100244210701680c04c1103810130076002d00e40d101e4989911040c44001e00c80e030700000d40c61503124002c0c0251556407001c81121900582607040030040d07580044100b8a8060240f42200300550103410400e028158598034542000003075400d00c2a40492104801d501940c11010440e07035946109402c520843c000807486d0010703100403d4845100c5a000c4101402e13010844024160b88001035080c030030203214038010400180f03c4214202903611568003a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 385551654 1250 385550404 385550419
    0x30504090f020d05070c0b0f0403020703080a0e011d030705060306130504080a02060a14040b04060e1c030f0e0a1506030b070302070519172206030b120d200c 69
    0x44500c07100340c0c007500480c20b01010500080d5078116089410034410300c0000c1c41c00d900350001c0381180b0410302680d03504c20300c240100c8809945a49610707004e07810540c412000071380703c4000312030170b540d01031075240802006003207a8910364030000020b5243d03d1103024083c051040413000a8959562103410484418822700c02c0009062905044145a05c0f040428001d40310f4071021445980040c41003001c0401c1e660482d00043e04c40b031751807401a80300500103031083c0d501c45a120000071000d00400c450421240703001002c3d0006a02c002c2c003a1800c201210031050316000740610104001309110040d02c3c1c3c0024180c005e207082503041c900421650b00060310b0a24400c1c05c02c5805901907000300782d0310707000b0707412130304180c103040c08401d503654045c9402401c9040001c0554003000030813010b04036608030b9a6219501c8050207000c4480102d003980b0103c0042e807a981081e50905007400225101c000c0c410280104c90f01300c210240c0340c00e1412111442a090381546502581824840340903824030046c907c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 385552904 1250 385551654 385551671
    0x90c03020f0d02210108070b0904020d050708070f03050108030f071b080c0f1c080901030b0d0b0417130510050c0d0c02030105090102090f100201090c0803031504022503050409 77
    0x90b000750010000021001031410f802102c421031030004904030340844000700a9241400d01d8116281c0007124100d4200c0c1e028405030b000b1315810300520f403007070030741d075441601c0c41c0342c06031004224911481201040c1860300300103000d10200401114440307800b000c1216580e08092600c10a02e044000038840192526030020a82c032402044010181c01c04940e460235088001c010441c12407290001003400d074003c040e1450002d04c4140c09003010407814100003a0760380071100451004c1013464022a1444c12440400c0704002e40400c0710390080c01c05036902c6080a0404c1d2640e09100b44030b01482c0d1294404280c09140b0310b203c3c4003100c400d40c1008c401d1328000c254407600946840c9010358100d10075401c10000a01004051080c1d4240304002010f2042100036401403011355004404c9140455484002c08400b048802c0d030308400130003d9000271950b81c9040d101200302800d05800c414031490042201d6140e803443c41034412641c148140e002e50540395a4901607499200d20381c8005845c50808070704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 385554154 1250 385552904 385552927
    0x31718070605030a1b0c121119060e071a0906070816030e010203030c09040b0d02120d0f0207060c02270a02070b06190b0d09050313140f0a090c03020f 66
    0x146000c0c5425070000e011000e042c0110300c14004201c05e02c500050640f101900120700c00c41842903c0d032085007001550715000a101034100340d10707044100742800601c0100d00c01c015283c0700769000c0f1149e98018004040c00c0000303001c03070040c565a0b8080e8011000c181c2103001d5541508403881e85034002c0707a030b565500c500c1c4180501403c42030405d6022070300004404c151540040100d80c03282c10058211450142c0440800c002000d084800c1034010703034a0340c0b5000c0180c6641e850740c0300030000d110090010a0079043d004001d080014040021504101407c02c400c64201a000710280c0c1d04450650200d50f89644010540b807803011039020454070741c02402001800b55005080030f41c0540b1003048940e4502043c000072001162a100d42c180303110f1420403140c0c000c200502038449480d6404110650300f911380b1451904070039208100380d1206282040321021010b8104450704050f506425841c080d4070003d00906551310400b6440c988400021184034882e5045a098840c130503015915034404622 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 385555404 1250 385554154 385554157
    0x906060509060d150905010615020a23061504020720010f1d0409080f04030809090f1e090c0a0e0103060627020703030f020d0b1309031718070605 64
    0x2414000c1c1c4011012900354100b0040c5160010740041804c8030364541080c40c003004000044040d05e5075542c0742030109185c0031610620040c00c400d58001c004007441c50a01401c110703010310010381c1c1034403052928602c0c00742c0451800d03070080103203a01040c961200d2022601911071090003d0018a1400742038882c03822910400007140800e0f640c1c3c0c00f460764007100544546808201c51400102040d07110302d41c61903c2d400551600b481181028240100366007296400d130403517042140c0804022032120094248622043d40c000c011400d0040d147c108440040f01d5100031003191114581190001081d44000304034841440300050142ca007c242c2d02c02e08120b01d0082804101d0312281008400907100c140d4041454611000440038008a5044a400030080d40020412818552107100c0405110894400b50120180642001c5203000040040006020030755108190891030409807202081d404501c2e642c44214210f4009440d888a101400100400310410780451150100c0461a55170000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 385556654 1250 385555404 385555409
    0x91505070b24010c0224211e01050f012a03020f01060e070816171501090e01140f0406050918010b18070513240e060f0328090606 57
    0x10741c041c0b0b00030101001111410404d140c042d44c00085481e05001900c03042c2e0355000030100b0307000c00f140b501485880c00d401080c04611070715140b00c400802c1016000069003d03014a004400a47d001503042000154480815415007410800120540da02100701520703421901c8807004c90302996841d036460001d65480043c4040042e80d42055800281004040030b05030080d622500ca0a17415039038070b003501c10b944c41200010020401684500c8400b0052501054090044070107100d80301c10050001500300c5969501c40c00030500500010440d0190b49840100f200100301ca503054003044410000b006030802e40c204962010800c400e03c640721940d28180f003a100c88020007848000128400c010303500c041c4820300214160728000060315a440790300184022042422442496a19012a07115291040c1e124440c42c0d1403a0090600381600400e800007511030440718640341200a40b4441034a00016066412410080d06c4004001c001c050090700039100d07901c42040b81040300e0412030040c14113072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 385557904 1250 385556654 385556701
    0x6091b0e060403050a030c0812100e0711060109020c030903011802130b0108130302011d06071205090a0303020304082104030f020105040c0e0907050d0605010501020616091505070b 79
    0x1814001450500a00b80c1e011682c018000c0c1c136a03049030707480541e40c1c02000310b402c450041c8200240c12400121498050082901ca040f5400d95400d105191410240c090a60001d1007a60022403480000018406040d81c0011a02581719210106940d14500505404c2541035080c2003d51100b0754101070310107130030390007140d0b1117003641044442c0b4000c641280440a0020313010b6000111907103d2511704606052107440005030b01d030962401d144803081c410000400d690461000c1c010501d62101d2034004121601e40e0420a030b0034012103039543c03407064400c0242415004400102405103080a81e41040d40d00481e000c0071031928145008243c4040700c0c2100410381e0f081c154000c262051150900c45d51b0300652216409042c8100354803000d070000c042c24042c5c80b8480d03010a6644a1480c0c4504480c0b18410100303032541450000790070400c005181e68032203612001d8009225a01000841c1120309190040101e450f4690046403d44284c0401902200801e824000c4901c03414030800da010205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 385559154 1250 385557904 385557917
    0x306020f0a0318080703031805061504050603011401053d0315030f11060c0118020307080a080a0509010207030c0810060b2a0c0306041b0902130902090406091b 70
    0x1208001d40c2c406020f8000350442c201440b0400c0003a020781d125001c1c2c1c03040c006c01e01000d540c0b5640ea251410303a00711141c0321034680507860f000c560300b0b1174065250000d03003c4009001d0041944448031400c001441014801c21012007440100f40220040c0320203980e120903c0401c081e44a902e401d004411500440c1c002031508003084400d01c5d03030300090f00c1030304c0c0d000c6401850003481d0b4480003241d41070003038500e80c41801000540b490341c50903c10044040d40130029803640a00c00d00405080200584c030004a07600a00d04040003d1200411a034804070703a428581c3d210381150004034601a442c0e00b0080c140240301134049901000010484603040c3d580a0a0205a84035142ea00300380c0609202c030b00c0740b12003504502450b440071002108480050300d0403035100591000029150040070768081e01c000c1d045450181400a046c00700c1400752005210552400e0f00c030101ea20126100d51041f100803960224141c40c1d56a29a040768000b040103200512200185c3c0220907400d109021104011a04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 385560404 1250 385559154 385559171
    0x10c1215030f1b0b3901050703270302030306013e010f090512090d06050c121e060d030c050703060b0f0102010b0a0b090a030606030c060e010e15130306020f0a03 71
    0xc21200312200317028902e00083d01140542408801c0e540c03100e4141400f440e0f02e0301d200c010780d58240714940c41201180e50104100c1d035211841c990300026a8010105200403500200c0425000401c4a070804020b04c0c0c4080300140009170450128600e44e0301c100c82003c054514162141000c032600c080c8162880200702d8a031120000004403a15180d000305950000c4000c00f900602e080050016070300050306020081060307034cc4140c1200c1c0d048034610041400450f030a0013140c00b01000682c4654020302c00f0700c5d004d07082100e446010200805252090700801c40c4081014426480740b13a0450348942122011512882d000300641000324a940c0101000e5400c4078640d841405448550640501485540e6082044500131a070200410581041d854000080040c0300e9128500046004080c3c3d03c4000d818000010910301a9141160400031440540781c210303603c01e002d21441100b03800356507075228102c0b03118134458281540003600040c404120141c4107105140100303200c002580d420005d411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 385561654 1250 385560404 385560419
    0x809190516051804140c130c03141902030714030a0605010f0e2b0c06020312010504111c0e15090f0102070308070e01120c0c0b09010c1215030f1b 64
    0x51465500e80d0300f4003c0804a80411840c0000003140f000c0300041d5960442e818021400c0d8031a214a0308841075074038004c441c02c0581c540f043c124000c00030486107009003802520106d0003040340d03460089a0758000045480c19004030100be0306000b00c0008240c40e45440340d80580103281f544940360100b08d480d041e0841c400d229402c44e62803031200500d24001e03403412050401c21040d0006130b09208104224007503000c2035603c8101c1c0001c12503035005660300d4a00000c03041d840c40d0103901c414091404d000b500c2c503960100c4000d542c40c04c00d1a15050b0104103208440e0000381445001031180c0703005151400c1540005070901e24460a416002c5031f02460301050690708070b1040c9a009800160700c040401c14081c41280c4400030701c00140b43c00c0030407000308021041203403685091140400c4804200c1c00801503105240d943c400360f1807008200b09030220b90054842e451a003000101c0c560358480c104944107400c04581c0c05580c11110200421541d0300e8015003079682000b50b1612460300c00800954503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 385562904 1250 385561654 385561669
    0x60503010501210c0503030304050d0e06031302011b06020408070608011d220c0b191d1306080f241b030c0c0f071e080706080919051605 60
    0x21455101e800004420106410192000c002800c13641600202d4000966540410196002c2c0740110050681d41141e00005407096402e000c14501894080c000c10040d10910203030000002d4081c00d0114402009a091031041c001500f4010406440801c01284d8030500040600a0b1100c40e21041e6407030343ca03441c072582070b030002145060642c407101c00041d0505491582d1400c0d6030681c19020410700302551340b104d242c8c101d1500051790518021135498208101a1061101d4501c0d45c00d0074000c8420b16000a1718171998400018010040300300c0c082c0044000c3d50202d0001d240380001e032200c4d0b000c43c036000c6444401d0700c0464444c090780203400700d0f82d901088441034050b44c1148221000c0c44c884580710382458100401210403142c0a01800056880c28400354406245520140c0502420524410040400d48200d1440480501b500b03100210001070f100702950440d0416502075503480010700d103060414080d418070500b8007030047c000c0000029580103200500d000300d00d075481d01e407014007044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 385564154 1250 385562904 385562909
    0x30c06040b090a09020304030206070801060c03200a06140103050606120d0e0f040c0309120504030b0f04051212010e0a050702060f090705030a0f050114130618020d0f06060503010501 80
    0x4140104410040450000e00070082c01c40040d10340c44040c0d03640c40310401203801c200c0d0298090780085003004102688108071601400c800d040282c0302c074055880080007035151704080984d0340c1281d00030b01d6040808000031011668890300c00e100c0340f04410000c8100b000207100c1110070384500d901107465403401c4250050030342000300040407002c29802c42181c141501a080c00d400200802d40301404d9240c5000c0c0b501c0083c100c0d20003044019643c90a03210807030184403120200030003030105200203104d9041c00703034001c646000303d00300b1903c0c3da0078902e0074050075100301c8098100004801d6645074403984454102c07401000c440c6c401d503440b0382c160070039038404444910041e00b2000024a601d003a503034280d5000b0b01104102c071105502c88000c01d142c2500c1e00e4007526502c0d00469a04104102405407103203074940040c90300c1a40c14509092062440300480c02401d43c0e44424142c40a081062080e82545800920320b4450141d1402c2400505c201501c06584560500c640400d00b4241405803904 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 385565404 1250 385564154 385564159
    0xc1a0408012f1602060c1f0c0c0b06062101080c0312091e12070503010b030304062012030a0606180308030c07020307051513080a0f02010507050c04060807080c030c 72
    0x341082c00101e40300055020f0540c90181e00500b0100801584814001d450382040310001001008100c0302c3e810030001001c01144225424412088110b940c0405a500283d40c002781200054440c800000d5950007447c0f000108000102e413000c803d04044d00c0928101d03000041603404c030320035080c185510764050821a00080703d08201c17100040c20b144222443c204070300300c48a64081c5601000035024030f019a902034480d4819042030203107240070b00c540d08403e001100103510381403500704040c094414029050200200039040d140d0403880c28000d0f128407107445042d5030398918001d0070307200c024903889c092280011114004505032915903801d250541c0e070048001802d560300c0c0d504650456100c80000c84e01406080b0000031203481d66041c1c4003c1200801119899503101c0700c0494601005502412a5074004054500031581c0c00f076081c0300c0c4640a01e0426a9511141400c5c0c4c50941c040e000d40380c01528110700069040008142d03907054400f424241d0f200c0b100380b0340030156074035083c680f03040c0e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 385566654 1250 385565404 385565471
    0x8130b030405060c0a0e0a090203070f0c110d031b030f1403040b060f03010b0603090a06150f0303050d06171f060b0d0e0a020603041407050a080604030c0c1a040801 72
    0x35840e6060b02c4c094030070510302d13207800014000c0200208409804075480340c40f00c1500881072001513030b085010807500d94904d04c1c10364000601502c600c400c142452620034081c490b84c001c410181486580b0610842d02c4000c90b40c00c0e9071000e40f500030002088042d884002401c10342c90300d030f003c8000c02c044030300498004007000c50540b030b0a010041001200c810040c1d1543d03940d01841c0141c1c4800e0080c500c1402998090500040c190418000740c5011301e214a050355449902484000b07020040d01c820b6030381510346544c81c1c0307194a001200a029a81041400721400301c98030f41000780001c2d1003400d454001c141512541d01c0d078168081a61351a004844c0d1050382402000340310316013584070840c20000c150403113108400a03004503036140d0051310305035030f00400280200b0000b80d0070020b40c4000c1c80e0540d00e0101a0346000d0704151500b4001c3e100a04100b421429034040c402500d520b80090f140c4039440319000b0f100e0064045403a802882404802d5003004400b002c8200c5014108100554001c00c42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 385567904 1250 385566654 385566661
    0x30703031a040f021b0a020303032d090319020d0c0b060d0b0c031f050603010603050a0f0203011d100b070f2402040e0f0403050412031b08130b03040506 67
    0x40d40500070241540904140c685051601d55076180508406140510700040c0e0301c1019a600d40d05446440088040701d81c0311044201c01a140042101c2c1e0140710181ca107040c06245540c41400c1020f44a109120303001d04406000c050300010004001892020b12481841001c3c2d202c281d0300c032000910103002207000c2c0400c0802050914100d190b00a070002d00c600c0d40704406030354040e0140710695469803c05070100c100700b050804011044071400c081500300030b40c10315001c0000c240d44814002e580406450781d010802850154001700a1015400029500c4c1c1d038441002000901006180c480c0064051002c980b80707802c002d50326000e4400b140e0b141d80c13a11f40103840350b291100c103503107048400f204429000d50030110b03001e944401210003c2c101603600d51070020304201c81c0b40040c00781103002103108180170000e83c200c0110340454420f0140e141b4822503d06090300e0744050f0040340700d5000b0b94148a03c1c20001550018100c02c1c484e02203104d004c64440c2d625204901044900400e986d1040011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 385569154 1250 385567904 385567907
    0x50f0c0a03021e03130218010b041202030f0a0506240a1a0d05040c05010908060709090c02030408070b090a0b03070c0f02371202010c0b1b070803070f0302070302030703 74
    0x40078641c910392000c620181040280f021641d00c2107803203885c459042c408420031440c01e201f0102034800d0b075258843c10365041100c00211440385103d848100c032092644c0748215101880200c7e200c01c0d03a0f0081c0c0d80303400c0340d508005840e94411602c40308502c1135010840070702242d40000441440b00a072104600e141030005403048072400d56041001030100303101c01650509540601486244124501540c05103460300240a9560343d402103000c5400150401c0015907000400f4003c443c021807022403030318241d1034141c0c1188115000b1001138013070f0f100c0120382c94080b00010103103d4410350f1a003404581d581c11001490206550440c002411017415001181d140801c880a843c002488490010200071212840000c81c0ca03c04003c40f0003001c00c46050513040b8400070043c00c40c0f92a030500c55103d540000d00c2e1502c2a1340c018000f050b440c0c00300c0c008101d000c0d645a10048403102c540e030340d02c8140c10b03d408550011103070000011511009860b442d84a03000742d4170460f605070000c50802856550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 385570404 1250 385569154 385569157
    0xf0f1528170a080304030c140d030f02040e040b0a0f02040e060a05030304050a0b030c1201060206060306090706140f0d060323150c09031513031e0f1b05011a04050f0c0a0302 76
    0x86e4104140c0701c10302c10101e5215000c01c00042c0c0808001c15144200650140030703a40c1082e01384c2a5244107000030403002011240940c0d0290384211910510b9032075403014401080300c80310580c0130510204020130032341d004c081d62900507a4229846059a0b0307489c03003050369070f104038069142c1142581d80200800c40c4074401950b0000b41003c600c2d42030038561507803400c40d582c0036840400140d0000c0c2c14004c0c43c0c10140141c50f04140010050841c06040c12405400348045032000a00040002003c020100420302541d8110700c3c40c0301c0a21210f5501e00306200c0c2101c0501c1035145204c000145041d40c0c9500050810b001403070020181700320b036158a807421143e0010455190540505159605502c12403c03889205503910b510100c010025402e0042903019040340114000001034441e9030500e421147c0440303228028a405410201160840503503054040b40080c155800c1c50529540000503020b04500403c0a5500300090b41e00c55842d04e030351680945140344090030401480303034041d11031340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 385571654 1250 385570404 385570411
    0x1209030e0909032104021906140721050705121306030905030702040f020409110909162616020606010c0803150904050604060605090f0f1528170a0803 66
    0x19a0308184c0c0c010321802e80ea0303d44a40c0254041d50007010041145024100140d082c1d5681c3ca070b01c00040d06103400a0700c0a8207002001030258404140f1108100781301c0d10385071480b496007100c0302078000451009415134000c400112824025140351260018500042d2000c14040020010080c2e00d041001c0d002401000d0f0280c039079000400603100541c840740a201d1084021020041c0e542d0700d032069900441307504007403089104104114a00295940c40c00082c2c100e8440a11030001040410044d603106030035079030003c00043d541000011500c01d128125129816141203d03103000c4030701d80e04030b8071400e085035100c0c00f244580041c3c001144260029660005141c480c4200b22140c050004000c1041150304803065840340341040f040050b207001c4c1500504c4207584006250406240321650804002d0104e80c0550132080090a614500d00902820040113403012203e061451500c000794140700c0ea007a100c8441c118000501800c001013110103007048000502003620070340ea908116580003071f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 385572904 1250 385571654 385571671
    0x21303210c020d0303022101050f0102010e1e030712170f0702061303141303020f060703090b0a020106180b0a080d0c23070e010608010b1905031806161209030e09 71
    0x30300c0b1250290f060140d01d041d000001d40341181c119271400c401c10056901143c43c850469041002003085401c0000ba050050b403111a10410004075140c0f08070f280d4094040b01520110f9000d0f681803d01c0e03006120701c1041c1180d10b400c13400036500c401d00040554400d0f81c1c51801030740804005049216045603000a4912a240c41501d201c040c0044030096049450300713607000030070507100301304502e40f41c07d02104400d410b0305c505050000036180078007002e03014070900a100d2400a110113101d40700f98400c0b006854081c103c50329904540d2220b10007480c2203403400c1c0c0115038808000c10303c0e90380098007130307050300c0c0a940e0224031507160341e01e07880c880039038500d02c03094080403c42d1036001341c0c4107200810181c80041c1044100e0761621800811014060744029400340c000c01c0040c55000c0c0c0c40101890a501c9821310740e0781c035251050000134084804010b41058011030040c400b0b0b20040411006000e001c0f40c0d202400c1c000c00d00000c00c206c48000320018041100c3c100b214246003803561205a010484 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 385574154 1250 385572904 385572907
    0x10b040e1f06050a1701140301050a0b03030a121401170105060108010305121b07080313060e01020c100e0405010314010c0201020f0901030e0a06020712140717160501021303210c020d030302 83
    0x12645d85258003102a0040b803007030038031040d4241c0e01e81424410540c6c4403a4050091244502040109032240f02c1c040715070080004c00101c00104500780c2d04040e80d100442070503d084c07917079110340b0070300c4014120031240100c0d4244000f01da40ba41c4a8110a4140e941101c0544015840392004500300d0344510300c41440a803511500300919401030048100418888014603998008014994030365034254000c00d0500a40f001d40704030070307680003400c0c501c5614280c1707019120605416055070010b40050340c0300e41c0542410300101c10841c05020f60f22503221554028040c030030100c00c06900303038010f010740b55280d140248690410307503103c0d4000d03000f8500101c00b628607074040c9849400503640220401c3c0c1d01d00e901e10039000c290551080c1c520000c43c002c4508141090415034a9455000e060700201c02c03a90000320b001800c007840c0181024126a00c80021035450421105000900e40e082c40161040303140c803a500000420b021150f0400c013084c5540d003405500389035003000317004480d0290070b408140d030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 385575404 1250 385574154 385574177
    0xa021e03090a02010e0a03030e010c0c051c0201020708010c17180a030206010302010807080106021e03090a030c08010c1e0f05120916050429030312010b040e1f06050a 73
    0x80400641c010300c0385902a0104000d0342c000544000505e000b00750050340d801d030040010035808081e4000040b42460a4010020503090465890005d500216400703203403021011540310382403c0c0400340380d200b0380070394000c0c0b642e800c6510300301d508131809000031407249114031071045010310400368040480e0751500c0030701c90710800c07040c541404c495040380540c0c0018018030540da04650084c0e803194071850000c1c00c56041c008002e44030400c030b9000103070310420707101c81c05507080c800d0003070b0303281190090134881c05241e8a003445442104140305100c215480c0c2000c07001d40310310036100c080380d0003001480d403441c01019010885008107506a014100401403260090101c43d84200038011440700000f841092860415008550380c00c0d07100c28441c5291042034100040003540120990070340440d40000b40d00c903440841d055200390b05914403010f12140021030940040310180054070408071a030030550b41d44112070440c80300040030103182032020321020042d55100d0001407218000514020791030130f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 385576654 1250 385575404 385575457
    0xf060c0521040911160605040c05130903080f0105030d120f18031d01021908040308040e0106090602010e0307020906060c060a020c010f0207021e01170112021002150a02 74
    0x1880700301001120400014100110149401059004078240c09440c1c0b801030b145d600030010703410140d401008079482e00300040500404c4050700c00184006008400c01025180810380280100003003100840c07072060201303c03844441a5102e05031207014004180c0c03440006400daa5041d00004881c602940b192440003000041d401601c5c030303009404401440100b098a4040c6c61a16289c840b54600d06c4207900e0840382c0e030303030001d0541403c00e04200180010000c40c100090584110380000d81041000070303001658000500140e4100e03201540c8240107691a05822426107200c1500e411280c6d02c140b1220001d03240070060260046001000c1d81d1415403446d40103410114104e0705401e059070702003541020740300280600380072000031610841c54003140e64009107000c9010800b01222948108413000941d0080110351000008182d86030030b19a50341e551389041c03200c2140c00301c2c0103038000c0c080600070500004644001e038109400400046d9514002c44d8002d4008441c24060340c030b000c1c500001c0b00e5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 385577904 1250 385576654 385576693
    0x906030218271b100e04050901020714030a090e09120a0e1c26030a0218030a050f100207230319020a0c05030303040b1504091a060111070f060c05 64
    0x6402c5a400b0702051101240a0094028145902e500a0452800740030030154000194400303008221340004080c1c13a00304400c2d0090041800007403100022800c07075244ca100000140c22017611030340d600c07980b0300c0e10342c10b203a440f541042d1185900d6500010024100303800c00809880030840303e241138034240c5d000d203001803240040e0b00030103101c0401c400c140b9800d0003080e540b50007110440c001000c800c0e10108921841c03610000b0310410980b035010074030080703183c0a09000c500c4201e00604940c1641041c0c1055074866003005401d41d41c1d0310034a903a51066220900a0341c2d955504030043c103020f545085d9404101b400181d0b0054aa4082044118004403440b090041050096401000b014440f854031540000094200394031a80c403d01c00c10000900c0010100d40c0241941c01b080301030411400403802074000240024984000c1c81800703003901718013a44003485420240e0720202049228655a52981414000e60010b4020355134103220742c90184206c1c5260a104404807680381c4101e00440c80c2c02c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 385579154 1250 385577904 385577971
    0x32715020105090c0307030b060411040803120a0c05070b040c0b39060c070309031e030e010921020a0f06020c0307061e080603151f0906030218 63
    0x184221118050480c0e8248141584040310320020109503014100080d50b410003484000c1100c88034600081c02d071740343c1e038004450802e02440e9440d1039039140c0348611717125044140d003190541c0901d00040c003003505a0103481002c54041d00c4003850240720b0707190f580380c64000800aa503440000c540024a41403641c00800006107a000880030003003d0503902400c80b07403100c00595481142180d008101c0c440820110b8021120000041d5100341625081e9003001560380040c0c08240c5030500c500ca000ca803400c3e00c0311914441e07514101c081c01002d0064844159a005038241a01284140c0c1d101c0900f0305504a11a0b000401041106c0e5070749180041d03400e0b0a4000c800160040781d003540441c101008150090049401d082e80c1c602c200c50229004416244124410030014401081040d10306018900040c551240280301502d00030f01818040350703014610480141c4480b03000209500b0503c9008103a0f40d00a01e89024031980030071400d180b1001030210410075850050300108120a403101041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 385580404 1250 385579154 385579169
    0x203070b040503091804050715120219090608100311130e0a030f02060115080c1204060605010905030d02120306010306050306070e010f140316110a06060e070306050d0327 75
    0x144e9100710b0080c005015074a10282007944000014440007400128100083c1c032400c11143e54100741e032110840701840f10342e1b200c02c806840010107000d90317000d00e206c040c0000490740300e5807112076581d030040710141c00451b440c0110783c01d440030600004a007000c5481c4051030080081803488410101e15040750880452003140d6440081c0c0003040640040c0600f001142d1383c000b80c52158500002c682d02403038924208401c001d41341b000a041400d061059a0030911408034504032481c080c50400c00400c003500426010890f080e900107401d10700041d803c29408001c0d80501707410a10b800d1840b501c3e4202810b16030600d9100d2501103900c1d2003c03c4090f00c681a00d0340c481e0440c41c000c00024060b8010400780b4020020139a400311889042441166000140400850540011000d0841e210022000c0001e014080d84800f48144511904207500f40e901030180034088e61600c101c03c1e0119900c9201310b07034200340e02090103c0440d008503074580303a000491041c862034a8200c50311003010035403a04000d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 385581654 1250 385580404 385580407
    0xe070806010503151302030709020408060603210405010305041e2d02090606030a0e190c080102031e0c0403050d030e010e010e1002070507080106260613120203070b040503 75
    0x8542000c1014a0040400303402502009410140d64105100c00808100070240c1042c403420442d10200f0801e8000c1003080d0b01191520707100c1050f9500d54206680e2540700b4800e0068565040a00c0040f070500500c8904425181c14a400019009014001c00903500c940105038003060b034410710480d00d56030343c6c4500d0780450112400c0024030b1294151800411200b41d681c142a00140c6400e02c1f00ca400881c12681c1d0354581e0703184a02e640c09001345070841c0392035000c0d02040c62410513140c0c070080030b428801c404901807580c6828089080340400c0b80e8078044822910b10f00e040c40c0c09045500e075000900c0d051420b1602e44c480c0c442e0741c83c0c088400740b07050020360f560002d08980345003845401d070100b54060003400303000030040002d691420a80c100509455001038001d080010400001d001841207000900a07550794000090810344010f0300c800403541c0142118081c414007040c080c1c480c0000b0460059070101d1500c40d440c4c0800480040300030340c03000b00b041c00701003640001014070480c030500085 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 385582904 1250 385581654 385581659
    0xe19030b04021c0c0635010f05010518010311070512040303030e060f060108090109020a080a020411130303050a0e040f0e160303050d05060a03020a0e160f05180307090e07 75
    0x10031110b03d42c10030208545000490342c40090510050513048411610b003101815100011643c11364180c40141d46281907030781340076031190107000c514034103c80c5803484401042d43c0d900f0041d2080e1180d41b4580e1510008040380c00364a6010354002c40401300516074203420014103940c1c0910701516807540240003d80460100304040d418003440782040880009040b050401140c00c0380c0202c030141919040c0040300300003c074041803d502640c030380c90700240030350003040c0d580d694940c40e8003113100168002c030b0402e18203c0c001c0c0442404c88280c120810b80564113140380d0348044650750010801001000b84d0b40358942d001d551580103240b686013000a0004428540c0000e40d464004440c008a0521000036010000300390018250740c012441c045d004582680e50400181c40d1401c6900000d6102407045004240840d80300504e034450b020001c082e020440e4036480548018903c083c01c900010420895204400c042812814841c1005012100c10ad51555164022307140c2e041600d246651111004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 385584154 1250 385582904 385582909
    0x15010b0309060c0705030304060f0b030313150203130308070303061a0d1d070501080a0207020d0f0c0806060d0318080304141302120f0903040e0a09020103140f01060e19030b0402 78
    0xd894100d40c12080d01c0d071500300d541c5d9a80341c480c04020406090343e03a4544440d0104001078000c4600d80038000c00b5a96665a030386a00c607020a01d0b07020b08000c1e5009901c109940d00c4c000003c40308070800000000084610b90740c1c3c3c15106510030681102095110040051a01010303020800001501c1d002140c80d0812003d640d01207402d601e01100400306040801102e028001c5002e005a40d02031902030382c15030b00c9240550191089480094200e85040c0d400702c144048102a03080d0648154860b07405d240e59a00b01a60b00ca00594503640d2001080f007091000a00408031020072500103200c04074030303da4071030866003190002d0380700401244044202203814079001ea20000d250040000c01c50a1a05102e01003000c1180145442d0082640c00045001d0201c01c106540003400d48862200c1207142007503001000e032120343c40c100d010900b4078000c41440c801099200b441074000f500c12a0040e841e00f0011a0081000340e00144c0148005a01d41c400040c40304079280910b014080310307191420903205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 385585404 1250 385584154 385584163
    0xd090c03030f140306011b05100b0a12030509010f121a031002030f04020d02060705070f090501090b0f10170c0c0c0d030c0f0213020304050a0203070b070b01090c0215010b0309 77
    0x40d00b400304511820242030071070102c2c0580350080d001b032910140042c024070b6076002d070b41c41102e0003422034800c0442e20718001916400c00b0400500940314140c4480d07640d442403691240040c0002d021030b5083c821042254450103500e1060802071070082c0b90145103039202c0c1c003221032881d0402d26401c40011600e1700350030100220340c414000324604519600d0300c1e080401d510a40a440244510801000c0d14107640d60031040c0e0341915004001c0c2c615103696910052103c1d021840744291030340c2030000000c3c0c400043d1284a40d1070700e0183c02414540c5d030707170001c1103a582d0450b070011303080c8150b42d4110030160b41d01d00c0300140705038407803a01165a03038807084445242521b614801d40c455000c01414800080c0e0003020250200da02988103030090503c1d10014a039841407407a01d401403031002c02000306000001507503010482c02941921070321034030f91105c082d141c400c3c80300260070210030740010483c4500ca94006018081d99106541110b0303940c50100d4000f61080e804030230325410100c28050490002e20 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 385586654 1250 385585404 385585427
    0xf0b01030302061e060d02030f031b0d0c0203210d06060215250f050904020307200606010e1306080f0d030c0f170601020a02040c031a180105150d090c0303 68
    0x466040c1222480c844c000b4030014024075203030094072514070139400c64030100580b50389000400d0640e03403176510078618007546540140904003107100303a811410506004245d4140c0c00c540290103080c1c444060703411840600e01005501000c680100000b0b03c5640451003020090703ca254094162000c0d0300e0044600010040d20ba1020b00441c414a0a00290540101082803481c1c0c2840f55000035802d1042d0b490f030043c0c581c0300741c01034000020032030310320751207004c0d543c0744091051300a42418142070084e68035001265042d0226148140910080c9051402500c010518140120703084d61540030442c1481514602190160b110501d10000c91390140a0102a030081345480310030b0809909000708000c01c240c040034000ba0000b404181140d100b8896019001d4001d0401c0c45000d607a500010010003d412400014042007040030990789460201800f49140b08059645140d0a04e400c01811040d540802c0010303110400c0542c0d1209114026142414024000040c1c8685581005804a00605c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 385587904 1250 385586654 385586671
    0xc27050721020a02030417030c1204090518191103070902030f0a02030403050703110c0a0b0a090608040203071e0e040606050a08160303031808030a06050f01170c160f0b0103030206 79
    0x1800942ea80681c004251000c03604600c160b047e01c08001da4107542148a40d040d09642400b5541d851b82c0704c402074900810440315074000800c0309a40d2a47c4c011868900d502102000fa0005040d07401840f040211040d0428019506001c440d00e4403070000e0b00e007148130b90025003440d4011042001c07000580d903101c1d0b48080c04200035440e516041c1ea00400521940c0001420300c41070b00740c0c2c2d40510a08015a4803202d10140c40002245d403905000400c0d0741200518030006109600c001c20100d119140c928003a646c06001804210300b000c0c4a481c10200e00502c8003240c50764080006175607161881d90f00d0240c1c0c01003178002100c600f0081480705400441d0800c0419501291a4051240140700160f040320b4051030001813501c0440e0510405480304140a0540007012091241030542984084100e4804907040d040401010b80192440c18000003112051080c01001030040c0d44080d000700750700c9052158410b81ca81103650b0780001008040000d4400b10358000040c0300b096010000e094104194 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 385589154 1250 385587904 385587907
    0x90e01060510051801030207170a0806120f06040224071217010e0f0703060506070b0105090f0402030d1d04090501020d050c04150c14030304141005040c2705072102 72
    0x241d44e4030040c001d44d08840c50416a0018280b02485658003441c0d058000d030742c4d070843da200001c520041c80c41c0010745625100720540d10b56481580e000242e800301503480000500525070b51502000440314032075160017904101103250103c50700180d0000d081041c0301c0d005030307090a808c3c14001010035000b5172000001480310070050000500f043c444950240300c0074a403468135624150110040e0119601c903980001e0003041c940c0400c101c18a500b0306891040d540c2980a079141d80011007e0841580c0194050300503d00d4826814400c43c10911504001102452b005081c2400304046a03c508401c0d11180d40c0891031201c4210140101030f004460308504134102270901e44441d07130825884c10107009010301032280340104a102d02c20601244841d074141c0e6100d1a142c18041b50407000100d40360060b000b40e240002e00103131030b4800c0500030307a0082d50f8501c1003070510030800500174400038000f000d894001950b58201025004092040034560344001a240c02d200302d40c01d50108030008031120600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 385590404 1250 385589154 385589167
    0x80601080d0c080c01150609051c11060c0c0d150c03050405030f0c01060509010f06110604030207150e03070312030e070317030c13080304050f03060f0f10090e0106051005 75
    0x24440030007502290840c80643ea50a12062403900401103d102c846c104000b0703040c00650241c200350000201c4000340c41d140d81103945801ea000c0081c8013584001c00c0c1e10105407000c8010305140002e1b005c42401c0c042102d0783c1761708003000150003026040d0211501d01070201c6031b0030454a64002c3d000680c04c039003418042ca01349569030301d44a0050b9102c420701400c02081e005101d001c01d40000000300409881501196120000c01d018485030307000b01008140995140b042451300090114072640d055406804440c0c100b0f040012a5903950038030404012900121046c0f6907000d200001c001e521510f003860018001000c06003d44200030201d10741178000b44010008079040144418065500c04e041c1e65884c0c0e10320b80107030b219000e400031008200e00b20003400300c2c60750340000082080d604221880649401c0c1a02010341da40350890700b5000a1489001062001484a41c204d070451000c00700c84151580f118510400c44070b07241810304460b9150b00c800c02c52424505200f0b008110b0a2a040b86450b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 385591654 1250 385590404 385590407
    0x6030903080a0f0f0501080c0123031902040e0f041707171b030c01020d0b04090807170d0e0a0c08010504081210030f0302010c030621060e0703060510080601080d 71
    0x10010705800c0d405454400750360f8500d205902ca8084000d45801c100082c1d41c42d403009940e1484450f11490100e0000c540b0050a1031420f8007103603080b19100368181c075550b20341c3d014120340e051400b0603d5025400348404030b040d000c0c80061920416814924141074036160070825088050070501044891003003000202062011040003c50070505040e02e55440c00c3e01c0e40341e0a4440484500402d5000120b20078100107019001015051500b4030240700c0707000400304006c00c40c1c18840000300700340c10030008100090b103c5142d80594105507807a241c200352543e641003081c1d4403218804c0d5041d4005901030410004101d4014003d044d040e4020000c0703142c107503100101841030704882c03c0c9a051102c0041c4144916002030405140d104808000c10892450040c0c00f9014400d50000400d05180002c50f9a194a2800880310b6400c0b420081c54107400e5125200205011990414680140720700400802c00b5806141c2c00350340010401c004241c50001075904040301078100d14110f8020f1402846100e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 385592904 1250 385591654 385591667
    0x1b060f07020c04020c0f150a14101e0b0409060302130902090f130f030f0e040e03090609060c01020c0a0b0f0f011401050c0706051b030304080307080414070b03060a06030903 76
    0x10206880042c4c0c0d403c58030f0344044c40c000d1075600180451007803c0b0300911761400001c01c21300900006006010b44270b48045031a1161604030b9000840c2c03801e415080005c1100c005020b40400d0f41d100c10000c0c11600d41603507541a5000390004000151242c0081003142800305180c260420340c403208001413a00c903400101c5910014012840489080003c1012031114a11406400341e000083c04ca0400a52a020384221040300508010500c800d200d540c4600b047d00404211240e50005507180c5054a0100503c40d041058a10b8004109020240c0ca94100340300404c036034904d01c802000e1503106407410b082580f0f4014040b00290740c0c1d050511084250b0804080d054401611041c03064203d000012070b40d500882d06c001d641c9103d12324001031416000001040c004001e00c2c4c40d0f000c01e07034040c100315560b84410345004041900400024920354031524070140c0061141b403107540b00d03505504882e450604540c2082c600c541001090001034600081c002c1c009080c903040910511146d6240038000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 385594154 1250 385592904 385592923
    0x1050f0102030d090303090b0108160b130b0c0f0c120d120b18041103030406020309060304061e0b0414090c10030b03150604050a020f07261b060f0702 66
    0x125901588040240e0080c03081e00c440c64140001080130140340c0c10010081e100e540c1040d2503406103007001203400100405c030070f80388810000300c507130000d0f140c00d00e031903440da0040040d46414030a034040443d4040d1450000c00e00034900c0e900405c20548905012820030700d1003800c59100c0c18114440010710507010a95501e00c1c1e04500740300040940200f1800d0261002c8042c0681c006a84002d26030b01c00707850600d10740a1401601c0e0f01500310054810b140d43da100703500543c00036034010f0190210740e280c500b00850303205100d0840866001100300c280341c40d900344400030204003a103078607200c6c905041c10b100f851038103c00d407011b5070a5404c102c490152120041c1d41054010002202c0038802c0320b000c0d8100080800300501118101d1030020b800f0454020f0030b039900d40c4900c2c105408103c0000c05070081d926110413049101b4075150032550b0f1242e0f03408000842041030311901074000c1c42218401d000c0d102e10440c1940c1805100032002e00359003803d4008241c1c40f035505231036080c003d215031b00203500d455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 385595404 1250 385594154 385594159
    0x60f15050a0308070c091404111009050d020a0b070c140102030403110d0314030c09090a050f07262401090e0a0e030910200106081504080d05090f070504090b0105 71
    0x10760f81002e0030549684070143c0c1044000c281071003130083c104000807007c0b51195000300404404d1103414070401240175402c101100c00650034403410300c542d2801001d100c010781d2008103801d06666a0701d2405d40544c101c2c48041d2815441c43c0c5080060314106245598014024400340d8501070440c1d440340c103040d0103040c10034010b40d0040d0b40c01042501503510102801802e10300300c0d03246c0c501081d003880c2e40c0d0320428405020380131a1010403002061809414080c0010080304446591514012904559440b407040b0034103c4070256030a515003151207080c040c0c5501a00c03841050780b2066603070868408000341c94104510000200b04c40b0242d00c001a400086054000c584600015422803842c081c080401c1d40c86080640200701c03ca80044100c0100110380321540d100017001501d0b40e0803a961846030b2040344d0441c0d00010348214910003e654000c0c4180a81c50134881c245900c40c080b200101c90b80034180d40654050385004004200c004010312086505000078005503842c6102c00c07c0c180304450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 385596654 1250 385595404 385595407
    0x8010b04030320010e071413060806040303051f09050f0c0a0207140609090a020a090519140109030f0f02130c0210022b05060a0506091e1903060f15050a0308 69
    0x6400d003c0a4010100c4910000c0860b400251030342102e0840c3e06485005a105034020500c0080c103102502401d003c48040030b02500d140c0da190307103040c3c4c090a0014165a610f00e42284140b402c40301e03a1031000050845035100140c50f1a20001000350766002820700ca0011109000c1880000c2c3d00044034415200a00b07148902c041c0980f01240850041b0b01183c0d0b0f10100b90010000c03617081940c040c03d02101150f4400301195520800c0c428900e8020110304400c1129440a004140d0b2070403441c0340c01c40061421444190741c81d190880308080d00f100c1144c0110304003502206519000456012401c003900041210344043c140103075480c20b05c1c00151002e640c0103c0c1d400e0044200079a07040c0b078150814030b010b0b1000240d1500710000c010807622036109000d42e031808035260400e14180c0c3c0303a8000c00f410080c048000420101c070100210f4005640c450403610364002c1300701021500340010740c800d000c0800e6a060407084441a00c3c908201d015882e40b402400304000d43c1d0f0307601d10300d04891700300c0080c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 385597904 1250 385596654 385596707
    0xf0d03110c03100b09060a1d0408040f121b050d03080a0905060f071205070e040b040f181a040210080901020c030703090503010c1818090215090108010b040303 70
    0x11410700d1120549030740c0c140a09203001c0300b40055a003241c19804d07401c80e600c1080d641c80d00200a281d8000d4040d25840c103010315407a46078052282040b5800602502d0780e41d00341340c0da40d40c008540c60500e400145040714010b05113000c000d03802d9000c4504240900e404688242004080750b1150002d0001800304200c0e040811000c010344e5000441964004060b644240340c01c0c0031038418480c00b5200d2070300081030300c0c0540e080043c0328821517016404030381e030710a00e01003100100000b1f0001c3c0110550f0040d5100c2d45100b01c0020740c8103468043c10105480f20860255003400600b0000100504d4103d50080302040300503550002990313283c00650410750318a45070f08540a00901034010705400d07a20001808501341a08a0320308421100c044009014045003c0e00440340c3c414132001c02542a21207070010f0220b9180811301589200d500c00b0002003c00c0036400151210b24040c0d0518515000020b80c200c541d40c0c854840ca0140280f1020302e0f19082c5941d40c000c180802c0c07900040d4400690b907a11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 385599154 1250 385597904 385597937
    0x3150e0627031902070603050c040509150a0e0a0b030f1c0908060106020a0606060201140601030e460f0201050a090302060706051005010207081c031e020c07050f0d03 73
    0x72032080e54241040782d071201180c41d40051548000003008015100e40000025010320034054644104002121107007440d10b040e00384503450f800581448034580390b41114001a4480300c14020040600c0c40c0f040d035143c2009030310001105e071503c080a000343c01c411104501024006000400240c1124200d07802000d001d03021210500c2d2038001c800940229000000c0060740016002c00c401d024007000c0155a0307071400280d08840c00c4032900001e4410140004a143d0701a0380220001d17024401980c5020104903000b15161128009500c41c4031107440400720780200440410760081542c0c616843c5803141516003030305003940b0f01802410030100040d0540714134840d8020310300840e8040c00c03454543c012440d081c1c020300f500300c4146000320203d0304001000e620000700c81d01264880ca01400c0b074684040314008660401207241320a161710364801412240d0711000d41344030a0103013440181ca901d851009181481095070103144511038011003001a5a150156010026450305100a044031344058 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 385600404 1250 385599154 385599211
    0x3211602150408010b0f10140d02040e15040203190506061306050c061b070605041b0305100c0c02130e010603060e010c09050a12030f030e031303150e06 67
    0x4001d4108544a5440241a072024041d0050720a41e500901818811400f445400800145c18941c0302041c0d4a2158026000d410044c44800d1365580071842d00c616000d00c2c1e010381c0d203e80d0041225804000800ca5030842005650810078006c07a410352450418008801c42a091054908080c40ea10004a002075981004540450049407014511039030740751405025034120f05000c807854007845c0001403501c02d460319001e95402003d4490b505001086d107a4130000d0200800898a55120035400030b03030100c07415032010080d07109000a1000c1c00d8803803401070a68500c1421b07141030005000c08800141d5441120841905101c0400100c4042c806030060142c22070380c2c405002039292018656800c10190412081d884103525174080f8665114103105101d880361180c17028408070420348600003841105804108c00c07151501042d5580031020507400c0d0392004004105454408000300304000801109140c0d00503da48d04024014400926686a0b00000d124550881181200a003031220845 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 385601654 1250 385600404 385600447
    0x3040e01210b0c03010e060d2004060905040506040c080316030c030e19050f06032205070e100603240306021e0711011709071511030304200321 63
    0x203902d01d9441c201460305600551007030085100300382100c00040e0f000d040061203030030566842a565540c140b4408401c41090240c81d8060b98070a4807842d00049031919401268012802000940070b10300741850300b180741584650008280e60414030080242c0c00b030b0300c8625141aa0103017465041e14040d890100c503204021380a940d84404040d0720f603005030300c9481035070701610015034150300309451171030130014a8081151042c050302a821120b124a5184064a80e82c2a00c25011110b0950322030f5101a010302c021205a8120310344150100211503240c0180d001000c2d60080c40302f40c0340c6001c1d401d040d2296080c00041e051316000642543d4918003010b10f0240100c40c407003a035407114a245007040001c07200040507070009401015200110b070403d440d01d806224114007c10f4040d2800e4101042110403104060900c0b1000c5e0800303030750180600081d84a240b05503c14a6600130341c061541c060b44c40030040600a030310074116001c207079001100490341650100511620342e9400c582e81901e415090 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 385602904 1250 385601654 385601663
    0xd02010c0b150f12030409020c011401030b06090a0504560601081905040303020706020d0e150108030a08150a0806151512190501080a03080903040e0121 67
    0x21020820700c00340308000b0102802003200c240381c203041c0a00801c250019840070045045e00108010000c3c02800c0c0d000300f0601c1da01e0030000c120b4501100c4000900d130801d0f842a41c074000f038903040002c0b91801340b64083e803000362401c04012500346915041d10f1104035012020305411202c945414642b5004103090940040000445074240d050929035240090700400c0003503c1d140c04082005503000300503042c4950361009000e05100c40b44d03622039001e80000390080c0c0616900300701c2e600106c0c5140c0008c0011091805c0e01107542140020750314036100380e102c240c405440300d00b0010b01c9035100200840302003a00380d1400607415214140504449140510328940c00b170640c030030000c1c1c0301c100403840610604107852400f58074a2a0014014066404144001d0529081007101e1104640000284c2c014001d909104250320040c6a18412a2000c0e00581a260310103240c0307000301540070080c05d40c000d110802540c20189410b494020201060040c1d04220006c450044010b81c6c141c00540c0407290407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 385604154 1250 385602904 385602923
    0x60909020a17181b0d170c03040605070b0906040206031501031812080c04030c06030c120f1b020c060901030e10150608010603090c0509100f031a060a0303020a020d02010c 75
    0x10703d9038404980c1500c8116455406000110f50070100040e00c0c201c610300780504440028100c540d43e8860510b000100d14805643c10701540c68182070801c0600007400325a11074590b00c0c0320301e040071074406034010410f60301c59000c1c50800c00140c41d400140d0350400134400856601b60403440058011384070241c01307000070088145c0c0c0f03541480300c005031700360006105c0d4603014204d8880c000070040510841c0405801e040101c401000a44e210f0307400b448076400280381c500300c1501d042c1c8015050f1008881d825507141d44991803c030041607030001d0010594882c2c0018400000814041812801004101c505240c2c0d145400030008106024109402c403002100300950544400103284041940c020400095000000071655600074404d250700c41e90002d80c0e0a0000b80342c0b84c10444001d0005200c100409100c410001d6110543c0c12944080c5104071200c004003180b040d03500044100050180d4450318000d001000801d130080345a60801e1b40549141942c5030f01c600041c0c40d00c04d0f018000403c2c1810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 385605404 1250 385604154 385604161
    0x70b0309030d0b1903150e010e1005070f08060415080307080c06070c0b1b09040c030605040b040b0a0b0708070f1b0504150b0711030d05070b060604060909020a17 71
    0xd01000802c2280c2049000b00f0101c4030481c10b014030382c1e8504110101121345840140042040071121480100007400d0204402d0700d10032032507081d40c503440c9108109510820781000b420040307000e1140c0c0110746240c865020031164000078500701300030303041e06c0c0a40e5480360341c000c1c060040002d10011b4000c40003100d540e4001482c210407940d000c0d07511003005028940101c0e000da4400c50003614000c0e0008540e1201c2c0d2a0b00e040410b441c10040108880ca103010065220300b6200c80c004d074901001251800501c5500c0c14045c841564228980144902e14241c03d40c2105e50303a007030030071054603030a1804586805651038910301e940b01ea0b480142804400220b504104601c41804414440b040300002e102240e41d041401300382c40031149500721402c411700302441208048005403200600071081c2a01424100c4003180c01c240c00b203416440003c400192102c1880600358940d904404241e030468a0305151080051101d0381c603005000a840c0c00040e891905031085e0482d1b4121200700c9222951810f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 385606654 1250 385605404 385605421
    0x1e04030807031806020703020f0f210115090506030a0b07090f03080306030d030e1b030a06020301081501060f0c1e05062508060315091e37080c070b03 66
    0x54031000d01215041007802081c4e00344086581d41c2145d80c040d245110a0b440c800800c044c9080103008180c004a000f200100070113101440d500c0c0008070000002035620006903580f034000407036000440c0325810300085c031001e80c40018043c05582e0b000042c2c061140c03a061011260710b01303298170400c050341c0f05050110912514000950080f6012000c8900840d01485d099050342c0c50080030350181d4105190000441a15501c02d0700c0a190003401d90780c684440b80daa401c22a002a0000c2c00306034000c1e400144a2000c00c00e41c1409040c040c00c120540f01c100543c01014848103001c0200003a14801d80e1040d0710380741040340d4030056482010740f5458070303100100030500c10440540040d026100390f422086a409513000c14055800a8040c004011240440d0b1401030009444042c032845500400000c0f001c4820000c0c241c801c80074042d00307040611514401840400c1c581203010312124402030b58208da4a1240000310541c0800c41c0c9441d0190340320f5103810070300b41d40c0c00402040d0000080040a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 385607904 1250 385606654 385606667
    0xf0a0b161206090605040f0b0123090405100e060303041a091c0308040213020f030103170702031506030709020a0203030f040519080904050a020903030a210603081c020f1e0403080703 80
    0x945054a04110710a0502541410740c0c08c0d0504942c003241e000e420b000305280030362640100c05a4803003121807805004001140448104840c03182d9111201c0c01c050009001c01110700760002400c0b001503042908080101003a00307039680340c078406200d0000e1500443c4d103c2110394a501c4d803031a0307100150b2800d2418058400101182d00700d1180c0c1940381402d001060a2003034601503a52640100e040d6801c0d07541c0c0309610032040c202c54034412018800c203001660204241640e00000250020b42820700009252601c1c201d81c001041c02c0340180032100043d51f000003075a0b485400040b85803041e440711f003001d906107500d09450282100400b841300e0305000c8040c004016059040d10308201d50395944c03c01c0707000c90243c9403e440e0f00d90010016000c0052094841d0902c0d0500c00504030100c1044610740c1048852175030040300d0020011941043d21203048000d0003c0046645065140102c20344010340c0600c40c1d0140d0700c0c00403490907550b51144c40c0c410300b0740300a1540030040503600d1419042c0544070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 385609154 1250 385607904 385607909
    0x608251205031e18010503040f0c03080409060e04020f2e050c1204060816170a0902010e01030501080607050a050f03011e090605091503160e090f0a0b1612060906 71
    0xa003c003c000880781e21080c5011241501140c1d600c07400c1d28051040110342590003c0c0040d12541320048000000c100c941e180c420045200314281952207140410000607070b50325500440003404035104100150300c1c2c145448020072400c45a40d007050003918059444c26026000c4200020004204413910b150040c0007400b04805060803100108040c00400d00c0b14442c40c05110000350b1141d001c0746040d940407a507070700d08019900302254100c0c0406400c40c102e03881100c0310041183c540070704400351758001c1c2246c03201140070701c0c0a015941c10035800d05c2c1e59880c06030058041090000310a04200d00c11002c1d03820b41c008070f007000c03030356542d44488a8015030901c001f000a5014140b00c0090240319622880088a41c00b170200e240d6944c50740002c0d0510307008508010b806014210758550040c50201ca25009442e440b40280600e05041c0769042c500250800a04040e034080303141c0c0000b08205850907540010314003120302d0880d0002004941040e1050380c40c03442507091150110b404a11604540c00707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 385610404 1250 385609154 385609177
    0x70b0a0c1d060d050603100c02060f070c20131d0705090403020c150415022a01080c091804121812060c050f0d0e010b0301060825120503 60
    0x303110164400044440491070142540b105007048001801903090b0402030b403000700107040c0c2d038032841c1b070502e80c2003034130800d04000006030800c808115111508105181d040041c0346040c03000405d80b542d517455503914207140c800381c1c1803c803440344025560b580711112a0303501c80b003000e1203028840d000182e011400c4000c00b040c10300501c10b0100e83c83c1840d504091060f40c240d401080b18092000c1070004450030690000b14038041000003064116111000c40303090f8903940c0c018209800004e420140741c1500049540d0018040d903544450b507030740225503a03000909804c403580d0b6441510f00242c500c20a0f05064103c8128860070001806184003c5c041e2a6440f0f4603044014404407083c402d04059030f0141c080240501c00408021608640c1312146010842c141117152410840032842580c0000381d0424038980c0351404984462002e006200d0701400c190b0080c4601c50500b4030503900e5100d02640500700c11351404020060014444104000f801c00c1111029502100e09113580c499025280460 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 385611510 1106 385610404 385610417
    0x20d020d030b0d02220f0204050609090c0405030609061608040c06050c010e0304090204030521070f06110706050f0906040c0902072303120a0b0603010905060303070b0a0c 75
    0x1000c20b00c4040c42c220032405c8400031a410f5543c8010383d0b042c0741e0b00500041104e0380302c2009607412001c0886218200f030340c61480404090180d41d21442c1d00d80301e0203003030028200300400c0c00340c040c403000c80c1c07200c500d843c1e030100503210858141c07001000030044910810209200f040a08440c400210010036410100b00041d482c0d03402c02e0700308545440c0e0004003082041010440c0702c0110052600d0100049031000c0300070307124003411002401440540c038a050800100c0d600190900318080741040d120b04150900c0c8001706012142c81d60001940790100e06100e40000705039101c0c1ea40300c200340c00d205080035240c0010790041c000403114105845048242c1030f849521214161160a000315103444094042c0140d13510050100c07032000e494900404415240c0c941124103580d1031403400310b40c0703880d01008a45984100d0340c001d0030429003103080c0820100b00c8d41000500b003442d6a12070 = true := by decide +kernel

theorem cover : BRFrame.Cov 385431654 385611510 := by
  have h0 := BRFrame.cov_init 385431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 385431654 ≤ n) (h2 : n < 385611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
