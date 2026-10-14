-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3570
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:02:59.385273+00:00
-- url     : https://prove2.me/submissions/82763392-5525-4fc3-84c5-17ffc1f05c61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 641906474 ≤ n < 642086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 641907724 1250 641906474 641906501
    0xc10140f040e0406051503010515012601030b162d0c0213061a030105030303070f09180f0b040c090302040c0c0204020f040501090b030c0301060c14010c0f0306050a0810 74
    0x8040d02d0790409440340350111801e4034030a44500078130803070302852007030b051414009074000e205520304415400c1000011505d0710f070401601d07040c0104030b44040048080d00c01a031030300300c2c48956582c0c101100b4249041d80e80081c1d01d2182404012411301500071f00e46180207076480085405000d1001d2080168064480d03403c5c07000c09492000166101c681c10800820000da0006400f82009404080000203c1203040044010001840643d42c0041540d1703002c19546403c1d07004002c0708404a07084030003a40404c4081c10381418503e00401960805038030250a220b080144a440100304420340761900d13440800b0582c804d00c2403001d41080d801a040e030f21580c1c200884004001d90101d0200d922a0170740e000c444c0e4003c10140800e6900c40300d860001d0004509550030f5050401741c80180348010300c182028021101c40303107400c029001c81030041d02ca403104000c1100304024031018000781014004040024a440404035081c54219800829550514000e0916414945041b4020101d40f0103010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 641908974 1250 641907724 641907727
    0x50402102c0d0501050a0501150302071a0a0b030303070e010201050f0f060d050c130b0411040303080115030b061206030c152505011e0c03060b072009011202030c10140f 74
    0x2404501d00340219405411a00000140c56141c0800071350106001c227062020075004010b9000440c0c2e40070603600d00ca0000d41c02800e407030b4545405504c0100340308010903825000100c00c03c850a50000c00b400c41a0000f83c0090100d50350b5a41c2d039403040402240c1d0441c8059001001c42c21600b0810050300180b4840c10448009141d0000082d840c11221802c040b03109403910202e00c079504040c018000c8a180c80b4844070704003404c598002d408040140140e44070240c200585100d014801d0f04a010b00d0480540b5541eaa070700c640c01c0d520691103003190001d011303100d803100c0d840702410714011b80c41000840141e1541041c07604c80f5a49031a154255410309103005480390440400d00c01c0c4540d003542891480304100c000000e0000106843c80811444145032520ba0304004920f0000c040b5000654004046007000354848100c004245111000c40c4e00b1001c044004140988003040c21812039000310b049480e101d0b0b2400030402840f42614040c0001480390f60100410220580500b4a0303410440045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 641910224 1250 641908974 641908999
    0x4150f0306030501060b04080f0c1c150501030b0609130b0c0c01110408060115030c020703030f03090b0a0c17040507151103070c060f0f080c0d02070f0501050402102c 73
    0x1c0d0944900d40c01208074511b00150030001034504111405032550304201601482c86e84400048405400a0a42e00340000d04403c40c0c2c1000040d8072408040041080c040080396180d08007803003140c00488400e40140e2441c004200b4604a25130030b460752a13488640035210750b4a2200c2002c2c0c58100502500840d034907a29004200c80d40200030713101a0000c20002c182c290300d412244c02645039500b0305502850304c1d0001807101c955007c54150300f540c0c1c01d41084031000c0200441100101a41c030009403c0e8940e040030b220f00b01e211074000c3e02010007141d0390304d05100d40b1000c841c44000b0040c5e43c0200b03298000d00c4200b06039102c6d5994002390036400d00b0306401c03032200004000e08503840068110745600c0c0c091020300c0040d030400d070204501c071428075000d81130a40800d000307070000d000a80705003020200800e0305064035170181c044962540d481110300344d0b9001c551411502034a030a0310100d00c0790460300300a030310286c4140700303d030440c01105a01c0e500001d41c0048114001e0b00300507501c0d410800c4603046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 641911474 1250 641910224 641910233
    0x1031103030910180302041e15060806010818010c020106061d0618010e0303030f0a110a0512221109011d040807030210140f0109060f0b0306210d09090204150f030603 73
    0x1181807201005510030076080303071003004000b280e100c10108901700703d403c640ae00c061948101140d074084002c2c2000820381c0c85480c502c1000c0e5540c100018600d40c2000100104c03d64103400010172900301e030700c40b00c0d8140000304040042c000640c1800f030f00541c0900032864107010702030169035880c4040c10009900050030010a046a0003100c180031246143c42c1404140281480760400842103111500d0400c520300e60020880d119404481c2408180a00841d9401f91013040f500100c405240104080741c03480d2a1844a150840224078400e295620000038811262507401d140e20240c2000b0900c2e50b82c450707444044076042404284c0444c4190060360381c0c1ca405600c1020304100902001c50460725104501043c080c105811001446081840800811880e55104c00c00c0c0c801446150742c8903501d64005c503d00f0360700700009008441881090206a04012800a1808800356030b9000c07415160340c09101030380f190b071045404200b4014861a80d80d80714001808031b5880f5440c0c04640e4913502d8a9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 641912724 1250 641911474 641911481
    0x7110904030c0c0614090111010b063c1b01110d050603010506011706150f1b1b0d02090403030b041506030b0405040f030507080417060103110303091018030204 70
    0x2012008120780702c0045041c4003c114003200201041d10f000b1110f100c0013081c103451800364030040c80c1030040761041001013403020b4000c00d03400344014141d9903c0e6059807c07204903e50b5000c40325640c1403440000500d00c400034004035446d144410404614216425800c4902002c02080340c0c522550303a40b01250000308088024190f5078103801005c40c07541428000c250840d10060a487d05011520442d0b00918011021695224004a55081ca628480310340c00c040340c402c501100120f241d001030000b890504807450300c040ca400180c1256024842d030071020507e00135190f5160351110745100c808005190942005500c070f44240780201d85900710300081070544589800c002180c00759110b0500074070358980b1401c940703040200c1e824802414152551a1001c80e281c1000d010044001101800e016548003110000d11003d4180180c0300424140c242d1620028041191800040c0c503402c0c1c3d05140000903102041401488542840540742050b2164610f203801c42075040f03400310000016941d03901c0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 641913974 1250 641912724 641912731
    0x9170307120203010f030c08032a03040b0c030406030507050c061504020705150105012c0607050a021903150e030a0f02010f09030c02090606070b010311031c111e030f071109 76
    0x4410300c170340341075141200c0200500e8018501d16402803001c0710002e20f001d0003180e00d840700d003000400e100c202da1000c00e0461103070b134201c0f11001c0c0c800030300342c0d20f100302c000000d10889002d641e0411603521381d4103003180d103480744071103108150388030001060440e48000106064503100070310040c60308a290381d40b1030802d00c007074071442c0c042c81008004002d65600242d90f9003a220010b07542040c1c0700d40300401c1c0400803a02000c410f0060f0008584101000b008005404d11141c00801085010070101c011103160745590104607140400d0080a5444c640f06000e6510801500c0c8007541c285105140c1c01c95a1141c1e03174000c0c904541d00d075031340700151070800d201d0355841034041c0d511000144040d0040c012406000340040d40240303010071203803012403940c0d0740c00e40c1920b0f8016261005003144400091405e404400e9000d2403040700f200018800307801c120b40c81040c08100003543d407034290581d2040020203400c006200c854000b013003c484c034510140c004011541c0b0548058030100b6021011501d9040202e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 641915224 1250 641913974 641913989
    0x22110f0a1206050601081b07050a0b130c060e010e0907120203070e031b0105030402060f0c07300b270d02030a1706010c0f050a0204090605100503010917030712020301 73
    0x44000080c4203460040f03540c40f0400307003000c50090800d5140c60901d20135003800740300141e902150340f8080050070b005c01307211b00741c22400d0a5103604081c0c88262000c4240c0b50200ca5201c074240001035610f0081d002840b40e000d05868642c001c021385000e0000c1841c0042c036a5080102c80c98003003120400c0c034409540210400d47d141c000d0741c01000245031905a180001031400164401807a4180c1c1e4032404803544241d055815680700c0d504400301c001c40340a001c40610032802851b2021400313100029964880d543d505400d580c80d00d1050421542084d1201d1014000710660000038040b40c0d1405200c1e4490b090000f080c4804100e5040510b003048103460720407006800000301c80101640c0f050200b8120703910f0180104441c2440b40010340a503c4000004011689400c0404203000c0e003840989041c58014100341708845040c80d2410041200700d07aa0745400c41055408981c0e410148140d14409a2001c06141b154180c810b1090403608002e00d050b0070032203604000b0340d000030b960002e140200382d82d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 641916474 1250 641915224 641915249
    0x6050703090212160f0503060a15231503040b010303050a0e18181b040c03020409020d0f270b0402030c310b0f010e03100c0903060522110f0a 62
    0x105164013121555650220b039451102a1040c400d554001c03c401c0c2e0170041d00040020a08400c1c01c146900c0704450307000c07420700301a07020318040200205c54800501e02048034120300b550b4180d02c032200c0901041c4d8001c0c1082000e4401400003d000340300070401a911414061040c0036403c00007181700280c084101d1203031030148140101c5c40100c441001c2c0c400e90312809003000754a001c001e503910741d0421404600c25074656110300000c43c026030440e4081d042024040d5503411045074100050903130901e00c0d0b0102442c16040c1000411a80090620041e0300794083c190484103803a035002c4000c004d841070fa0f040c0200c1880750320b5035480c4c4000203448009110018103044107100d020304500403030840303049014104001d0180c0303130744c416207a10161402400c2c082164452040401e1800c80b0501c82d80c2907143c604850038003440d8100590200b100e100382001e0100f45c4e20702e0f06101c2c40c2c00369500002401d103125845040010068190f9042250000c1c24905510f160318001403d0090213030701030b0700c02d40a07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 641917724 1250 641916474 641916493
    0x40609060314190305070f15020307053c0f12040f060e03042409080601081b03010c080714390106030519051f0b0111150406050703090212 61
    0xd000f40c444820004007003a4403880c0e55200504280304044c0f0003440030380d5414003d400c11900c103640d217080804000046403240b84c8440007810070f40c402a03852612560884484c814061032400c0110202600d0541c2c86000304580030103802e83e00300303940c00640300300305001240300d04281021980c03090780210f410400103c400e0501c0c1017120034102c19050a40c208020500c00070b98566211700303c040982d2046c00322004682c44c1121004681e400a0380e0034040c9000000c0d1a55000440d40c8043d581ca06026201c030800c641014200d400e503248110110b021507000404441c019130961807030f521492017440ca001d2101030300303464918000b00380c0d41c3c5c0c07484e04100302e000c1c8901c030214420103102e01b02d00801080d4295125917035199100410900714180c1c03d800c3c00200701040c0085e1820810020081c1c1440d201d450460f03020b051501c0c152400507180ca0045607084d280041d040941e844005c0c8200c3d1640c40b29100c41d030281000401010034145c4910500340103032201000d941c1c51320700d00300140c101d495 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 641918974 1250 641917724 641917763
    0x30304150c150213060e030c100201061509030b060f030307141506030d021b03030c010e0f240703020702040e06040309090507030c050d050709030c030c2603180406090603 75
    0x6010b0040030034030500c14415004030100740081500d50a00b070181494111800103481d00c400131090baa000f07502c080400285d59015081a13042e45c0d2030314680100c152921340101c0d81c0328520701c4050003041c1400d010034098141800c0e60844c203c40507094a181c030903151640340c0c2c8040c3d8440090f5243e03100802c04542c80d041d070303100f407500541c00300c000e061904030711078000350755640c22282140d1004c0c01c03140304500c9580400440b13004004450007808007113448400c90307894801000d504440382c000d04031130804e40288148660503103d0000305880d4541c0b101c42c0120b0007500000c004076001561505020f002160820a0901c114465500d61218605050601007502d4015007070a0625081c103020842c01900281680d070312403500080042c00e60348240d0112104c64840c0c1c4040d0090103555000f0060241c2c030000d2100384e480c0351428460344001c0320101407002840114804046c0c1050020002c40c03821441300f10b081d5140180b003c100079440303118000c12500c6507403049404054140c17002d5001c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 641920224 1250 641918974 641918993
    0x7020309090702061b043507091a090105100c0c0b04080109110103181e060204170609060c0901030c17090a03140a17040501020d050a1d0607050414030304150c 70
    0x1c50302181e07282014545180d1f020341e52200092440e2041c400c1c04499036101d030440c042c03d0301111034021101700c10351b0f805400c00102021989114100080c450304c1a140c03c00b10341d050304030354000d045e0444210000c10100c5005080311021140706140030000210b4607040400750028001c064000a400031140c980b840c00500a4003206041c1810284000407803d40030851440f11500040025006080350307480e80b40c003400040e40181110b2012070041500c4001c3d9140b00c50a481d442c0c1115840c1d201c501003180c0d6041c040300d0070f241c0305004000341680740d48203800500a1001c42d042c500c8110f020510400c5888800b1118015a94005108403041c545e00c006080c0c2c80400640303260345442c2c5104001842ca04400180b043c00c90010008501003100c258100c402e90400c100c0c00304140d0806544190142170381c0320f640105502e40c0d08420422000110703c0d18040e050139242c0c5446c0c50726191210135011300c0b034040175074503000610001440c607841107035071070482030665900c101c412201e00d00900788 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 641921474 1250 641920224 641920261
    0x1a0f0601020607030e070b090d0b1512010608030f0702120718060e1605070305070c060903110102010b0d1103210703030507080103111c021f030605010f02060402090702030909070206 80
    0x2018100100b10181c3e505c00301c0c1804c26119240201c40e035540081003c114041291900140001c020804108034002003868181207500212070760200385c3c2c0483c0886d800d8450038095090950801c000324143d0060103001441e40c00d1000e44841100d0303202900c1d0b103052071141d81c003002030102c0401d41da00d1140e54502c100d0000c0c1c80400d00f0448a42000c8100c003440142d051040c00501a00080190038540540c054400440e8017450303d209007910780da802401d030351582c8800c880c08443c80900e45220341c018080c0d9040c010f0064190b80403184252a02c00d6000c08011540b50180a030054011401500e40c03000e01030000342c840815a940c1041c42d0007811141c00038000010888264014000140040c81e0850048812603403498a240034070b21a01a01c14070703640c001d40c0403032024060280810b114680b8280c00210340c5003044080c0d961001950203901c030680d540c0041e08544001001413034100c8907a90080701d03501c1202d003800102008141021010344420001d64080801c0084034208101c42c00107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 641922724 1250 641921474 641921477
    0x1b050105090f06060d030c0803060109081207020f0607030e0904110d060e0c040608060f04080f031608010b04050117100b1204300e0102010e01020d02120c090a0e041a0f0601020607 79
    0x1017070512a00c0050186107140700080001c140003021070860f078860320f05000548841070954040018240b4146030503400950224000c5070140311032061403030315001340ca07540c68041e114524089018420007038003000080c0100d907a00f007004807900c185e4840c40721011034288101800211200c010300e0052a16090080d040d1250781040410700c01070201285440e0400d50340a134100554840b894a080280201e4448124503400401001090900c0c640f99200348a05a11010801d03601e0742c04c10340240c0b01d180207403404201e1400d000c20032181404040d40e4480303942c061010005441c1c0903034005940c801005004201802d10074001407014bc4101401c512982864401c119128100c159091910444e540c070240100080050340990003904405400c01d9604021559924030040e020025003111070b0050003100b408000a41140305202124500c2c100140102103051030034061100310000103100f02e6018928440c08003400620043d983c2c080c10541a85070143d10702503000a181401c0204040c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 641923974 1250 641922724 641922739
    0x303031d0a12090302040504080318070b2502030102040902120108010507020d110c030f011a0103020304080405040b01020a1b0e07020c0f01111f020a0e0316061b050105090f0606 78
    0x6084100020895a050b610140a107000290110140c4026046a002035003043c140300c10001000b6102c00214410308000564003143e8403da031403251b64021078010384c060b052081281c81050121141d0380c111410f141c0724140b544000ca640406d0036a0080d03400011030300d80224562050701c0c2d000702d0f054050310b0110300801c0300d442c0c6100c00035596007408002c2424040c01511054130450b051004507042e07040034040700c0c40d194410780410300801d41d10142000720344a01c1301c03000c1151700ca4003c6a00898020014504141c00c0c44100001001110312840c19072280c00c403484006140c0c1e100c0550500c06061440c002c861501060410b0034500034817450854002c50100c1c2c485690340c00040d201d07001e0a103864510603100080d4540b80101d42801c038218141c081007504202c09050b0002d00c0c103744ac07980c175043c2814070102071503911240c175014505010814032003030009134481c104220f20142c440d003686800001585555084800030750342c0480c0c94000c241030007406002004250f0f00400c3c16500c5c907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 641925224 1250 641923974 641924021
    0x22404060e0609040e0f10090b010e1e01090207020f09010513050414191103060c0a14071416060e03030a120e19030905010203182116030303 62
    0x1440288a5030052406104180404480e59140c00c420b5980740744002c1c004100201410404070395940c202e030500c0301e07980300b4000c1107010500a8050380c0c105542c00318401e4107507402c0410051400c0d000800b1550b6050507081c51203915038103180b1176402006a039000507550740d500c2c014007003800f5411040c2070180e450003004000948075407614600614107031800145680f141c0c5403162415161500740d400e20710a1182d0152200c41a1180034200c1703101d100e1510b07072001383c0c4c3c0906803140b00c03c56804000032010b06c4007a101c41e016816002d24400000d401a01d050b06035590300607200102400078650b075022084010b1032200034211300002e02000e040414000742800e000079035a11030b50b8404010804140b00c40c070060306880c0c0120350081103000070384020036004c4103130640c092002c0380b065001a4282c80001050350010045900000075042c0d0610000f03520014001c0b20665031440304820600d011b600d000c450320501190841d00b4240c0d420100721840c5040c0207042c0c581040030b0070170785024090381 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 641926474 1250 641925224 641925289
    0x6080105060a12020a17010e06090402060d0b0a030606060e01030915020a21020306011e05090d1a15030705011d1c0507090209010f031a15041706010302 67
    0x504403002290369a0361108150412a0300da015003122804490011854026458006400450200c070b6400d84103026aa105083c40410000f940d8217600903603620040342c0942007141c02885a1310324510041074030f600344000710300c440c1055481a0303031150b51141d00303001850f130100041208041c00d280500612115460300035080540c91865000c885d8001401260503001d003207460113074002000c0c403510f12514001c0e0b10000c0d6008a44080c001a1039681000d0a621020220355000c90541d49a03130900131407034148140310701075410580380110f40718103031901032082ca40107512515103000d9410b4514a21818145040c0c07440c0c20050600811142100b07540744c02d0510f03103d00030b00440d41c1608182c031900c9200001c80329014058494020740d00007041c9200c40d07800825400f030f4282e0720300d10444000d140032002c80d0408002503684080c1562404407a1601d5940355220752a0101d00c903240c2a84c072403a02c50030345024039020410b0340140b070041081d0700d8081e5800070341c0c28400400311a220302e41c408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 641927724 1250 641926474 641926487
    0x1620010807030509120c07050a0815060109060903060b010c140c09070e060d200703020304030b180303070e01051306091d19020a03110a0e0a230609040f0c080417030106 74
    0x105c48102c0c0380c000c1500d54a011042100390002d0801405400503d1348401c1000d403111401040c88400d2405000410b0095105200400464929030f42d20a083c5045aa802c00901021a5940d041041e4140003502241d20300050708451380d9240010296001000306015101100400040070700402c01130054050701c601c011194010043e07100010040c0e0001402c10b0448100c1001510040300440e45804041c0c00000900503280107941c01d0449982d80000d800101002d648140c405410a00c04185114022001c40c01075071014180642402d0340c42c10403420303002150f0b2140b03001444800041224083c00c01c0e14016004081c651001c030b516084e40c2c50140380003d00790302c8241907800580d00003d00e11030360024411209980005640d10035910004100c040c4c0601d1b460711561140d880081c0112100d02080369880c184800c03400c050485608001494015040040d01700d80c840c840d0b80c000745814490028500c8417921003a0715420107043c600051401e98441c601d070704000300014403001e0381208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 641928974 1250 641927724 641927743
    0x109050f04090c0e0112050c1009050103020315060d0b150901022a09040803190e10020f0705030d05070f0507020a411002011a061620010807030509 65
    0x84001c0303400c149600c0c10f09480002e42d480800c0a032000b10000c1403940c43c8688011246000d4002c031010505c50a00b0403043d864035a881a000c038552b03900800055000b5000f0303513400440d00304410001c441c404081500c99001101c0020b095039030380b0030700c3c25074a0f04c8a40c2d9010010000f400c61309100480303001030340c2e80c2030031240320100311210720454440c1464030f200d40ca00441c0286c09020a814646003003030349034000b65030781c10b00220318644a070180346c4148035101c996041c680c010003111030418501d10003940030701c007503c0c140001007101074042103081000344826441c0d030000060324a1721003002010f502e850440075041050030800c030005a0f840310410b03003e4406007080d0030f141c140ca009a08250035070300c9440352088820308003e40380004498000e41c400000a940c40ca01c4480c42e0b8104078200c0305500e4000c2044590101d466010307041c044041c245200031f12a003003019018945a02407409115007110701d400c4e001000410721540c1c4020581c1c2c0110403410180558101450b1150300c03402e054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 641930224 1250 641928974 641928979
    0x706030b0a05150d1a040e0c09240406030b01030c05060f0a030b01030e0f010614030d0203160804050d081c0204060206070c05030904150302091608010b090604030c06031a0109050f 79
    0x300343e48140c2c0d0400030880388030001d0220100158a007032a00410a00080c2c202e141c4124544841e8219180c130216100c034200100603d0604107130764209a400001044014003069442180a40c41c401c0d04d41e44500c2010314024003c60100e9891403411104c000d00c1600520700818052202d207404019000685681744018140800c1001d10840124001c041480e00c0c000c0303600ca038185d85880000107600c6042900c6882c0c0490ba012100e12007030507910800c031400c0354016401040a400b241c0e01429803a0505485000980c3c074059a81c000103e100d1500082038510f2440041c803142e05152007007d02d21494241c0c1001c2d41002c0c5818000394490800900400600c145911600108076091088505518001780100041c140b046982d40102c8a580022806441003a01280204200034807600110385e0543d50400d15a00780400a40c03a600540c42c1c081e08800d0a10002c00021040c0c1407503005020290740010782208640d110000084903485124144401d4940c10310164450a4104442003420b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 641931474 1250 641930224 641930239
    0xf0305060411030a140903090f04090804031a010f15052d0f0703180f060c03021c0e0f010f050a030e121605070e0903030a0f020d060303110706030b0a05 67
    0x6600124014040000702000707a8031000041015403082540008205c00e081d05061038103642d0000c0d201e6070b911400d50490390208400c005200c00b8541a001650014402e0700d0140c1040d5881e51541513107100302004910410490b4010b000450103c0311050061010b6580b04400324a00400508103103d810f0303032108907050444803070094110340768900c40301c0c01555a103150359589240e10803102c0d0b00018012400204091100c0a450b06d010018400b40c49180740240900c52808005480043e207180049040d40144004505c03102c02c4079080d480002042d460301d410b161909400c004d0030102d41080300d818800001e9200042036804001c0d5045100d09007400149848110111850030414040024000000040d40700c031041412006c034014070310800c12a01d003e40c58845241c1490301c1260300c0d1140381d0085c00026075034202a000312480c102c041c0001483c00144c002c400f0261401c540040c0c0208000c20031052405808200290041125243c100480103480000a640062500c680ca120f18403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 641932724 1250 641931474 641931481
    0x19030c03032a030207061b1e1505072f0705061b1c090b030c12060d061b021e03030412180609050a0608010605160624080d020c010f0305 60
    0x80c0c11000080b4500310580500d00c1c0c070780d10b140083d690b4403507005400008002d90180786c103a61005001804040e4460140c200c40c50340c400800031488903825050f2594007254a408411400c140300e103d001b5541c1d945c0c0c410200c5001540c060410000400c420b1007901610b0940c08a0b00d070100d0040d0513594210b540c55590704a010311690141c2d6038140c4908070740604421945019811040d0711813081c091b4840c5940341d543c2d0040c143c1079010480700244401010001c1300c5401001c8903500741c1c010802859560340c004c158441204441803024181c0720281000c20505105804118081e8280c032100009008900c9115181e504c9010140000b0984041036034104501c9019007080e00c2c546460013081d10110f655480d00402c80f480e140300c1c542c003590440300085070b402d03c10320100f0b050b030301c0c10f850302894076221540700c2840442c210701c1500c80303654034824412640c6500308049c14450084050b02507290400c490941020302900000040d5030003d03980a06e40d981124011030008007500f4001466503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 641933974 1250 641932724 641932757
    0xb032505030708070e0a05180105031c0f05070201140a05030708062b0206070b09070f080309091816090c0809160605070c05090403171e0a0f090605041119030c0303 72
    0x1041b90b00001c0c0d12050061650708880c2c511940b5034104d410840846060311101035240301c0a48903e4000c500140c8044000b442590103003000300302c0e5920602d0b1a640880080c16000c40e503400c41200c50780000c0d0004140f0820300d900180041d00100f0460b90000b040403a40c090304096459507040301000822130700200b080d940c0b0786041c2e82000d504280340810764504401d01944842e041e004811200320b04010104d0703001c0c0e001060f03800d81e000c00b625095550b160100707a0f1032070082c1c22030002140c0c81111524080c403210842c8040c0202003904000c10044842c000140c0f400500508899030359001c4240030003842c8036600b8100445c0d2711400c1541c2e5981072800d1103545042142c00094100c0c4031203003440b04040d0f20003c1a08000304500c00790303400e07441714032501c102d6501143c60f00c440c5880f041c1c00300d16100e245030300003c04040c0d80200010481721658915056a90031507003035494485100c007550701d905004916190340c500f6001d00d4001103003103507980340c0981e229010141c10000103070762035807944 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 641935224 1250 641933974 641933989
    0x15060e01030e03030112030c14060106020f0a080a14070609061521020607260d0c0e0d1104020c0a0b0609010815041b050d060c0906020106120b060a0b032505030708070e 74
    0x2c0d50027002c008081d44507007280703503910282886072000511942c4000c0904103008150b0000c6075038042e1032a450085803200c01c41c0c800e00607148040301c1071410411103000810510030295650302c9004086400110b4071031010900940381e20000c3c040000d00c40d80c01200004085a09040b98100c070072903111a65400d0940300e00d603506489000902d40440a502881c0c61a4050b14040d10400030500051010f0081181e401d10700b145000d410070461030f80d8000007010712103840d4000401400041c10701c4070b0350414910f0000700030313026070308040d0381e9007170003418104401c07140d01402511000f8494240d601c0c540940310040288007800ea600c0c400490312060b40e48c00707940b000409005181c404521610b051460042030f0100340400400c61448001400c28018003915084441d182c0091001490a0700c800301804e030010a5a98010040c1d640451440c400c00c01039801526000748401e150b5554012040c1106803c80086043c480c0074000c0000b1191b20050b413951050b110714207a500440c029002c603000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 641936474 1250 641935224 641935247
    0x10020f030d05220c0e0a060305065509080406030b040b09090c133305120709110304080412020102010608030d0905070b21150415060e01030e0303011203 67
    0x1c401c02e0fa00da07418001c404800c030701600c01d811802c48050b00e40010301d00488050703120081594020000007220055a00040c040c0d040c818000302882c11aa034a1071082541843c1c2c40008502c481d0f0f843d00700106921105a001c07903040c00c020018509503440d070308264040c610032981055151a83c00100303403507036004400c51000190580b6441c1c103100d210142c5588603110041d00803903000380c91006040440c0100031083c100040c405441c155501030001c0741000030a0f4107200707504030800000d03164841d90b52100c615011079018107802414151800c0c241c4554141ca900c03000803e100b40000300300400308440803103010443c5050074542900c0140e0240000b80d10000341e0380004242035400010940050b1000c5200d4001e44503066103400d0503841502440302c110250654040c2e4103440040c2c07900761150003107880c140c8100414076880014043d20b6082c04160380030614083c0c200419500501d10034040d15007400c05002407038505651580c2c901051188240c2c10b19201e012405050103082e00a44 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 641937724 1250 641936474 641936521
    0xb010f0e191e0f180305040909020103020909150102160503030904091103151501020a051e15041b0509160e1908060f090a0c0302092503060510020f030d05 68
    0x50320620342080c50014808104800041410400343c1c54074105013102001c882541501c50505050070319981030002c0c540b80d0b0040307060550070441e14215544d034070343c4a44107a9031900403581d003885070b0740024204174840c40d40400d43d85504106010903603001c000d54036405819180040d1284440c2400340e6051146080c8a8160003000103040007942d0360007100d071182c034031082c4444400c911034004aa40d02000710004d040c81d0080c402041c81d40c521400907280a4440508565100440c1c1c5100d0391980700c166412030b40c0e003460400010120301d038040001c0007407400301da18120916128030b26805404202000404024190700b01b0081c640d2440000c0244001c00c6040343c880644455005960b480141c3c0c80b0080c01300d501c000100c0c0d070b080000310004182d0340844101c014518550900820b10006400d03407681e04c1e604107010050f8a2036600d00248403410b9900403602d1442d020600074200b0a401d0494115004078013254050701000003210880c0c003840a000401e6542e5480400344564141036026 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 641938974 1250 641937724 641937761
    0x80a031b08040206070f390e0a020c01140f04060f06080316050708070b12100b1902210a080114010f0809030904150608060402120f0601140d090b010f0e19 68
    0xa02c10003060f00309040c1f0194030034036244001e01d110040b8520441901c030340c0c0c8012101c20300203041c1900a8001d41800075030b8000100f0300c014501401c1080410444205101c4a064800c00045c0403030390250180501d03c0060800080b41440340d0107440e4807806180514688048400c1020440304000c0f2000904810041e2800c0302d0b100c0000140641c48004043c81d40c40701e00c00412444186003107007100700c48800844510703019600c00d00402c080c02c0c040c04c110550154058225048244c1c03034024001c0d001c001c841c1a65a04030300000350080c0c0043e004000c0940b40c0d2214a9410f0b41c0003004541c1015840c10440100e0361104400b41c5184600d40e105c07608541402c080e00080c82e000c11250741030350007a44444070305595480c248030880c040c4200d04031003400340c1c002165804c0903602005d90000340624103075204410a110300700d0b00e588600061a0b050340d0718510803051042c20303048076002d4404030310410011460010347c49485100540540c044000300c1c4844a840c8156500c880c1d03e400042d0303980c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 641940224 1250 641938974 641939003
    0xc0905071e02070303031d0d110102041a04051201060602031b0a08210a15060e030a0b010b032703090906181501110309150a030f020304080a031b08040206070f 70
    0xf9150080e44c441100403070b00b000005000d4411128007030004c480000014803200044142c120380044a0141c00c0605550070000441c00c4130f0b070800d159603041b04102c0e0b059503980c580400e01ca00303408914503105031a45010010305c406030313021080302c1014a1126a060208000d0801c0038140781e030008000b05071100c00980f8410042ca000c0d4500f02c0481c44050041c080d96444000009940300c50101c00560240642c060081c54000e80c0302c000524400781c12500d20b858a41d0b51105221820303004000100d001000300292410703145903904110a0001400807826040700c1c55590f01d01800c4a62403040c10380400280240d22002c0072040d207406813500440480c1084147d003a58a80110003d40c0000d40e00d4100c11007a05001040791810000a00038169a04a080940c441ca0b08030401c0d11041540b0f41c41c00c10b660300100c1c0099400355009607041c03940c2c1c0c0a80300014017220450070200c0020810780b200c18040c42e8001c01e03110361154044e40d80341da5580c100d2410070501f445151b0020281221311010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 641941474 1250 641940224 641940227
    0x1207080c090a03061b11150408120411030c0609090604090f0203060708060411070f060b040230070e090c0f0d0501080109050f0313090b060d090f1b030c0905071e 71
    0x5209149205070b5007460300000d2030215141000070f01c62103a87c0d4410400080f45130401c0c030900e0381c42405a0f40c490304080c01002000c001500644040d0f8030761200c0c5a10407094641405200442c8904a980d10715084001002c620f4400e00184070500c41e80c1e86c0c0041c2001d10501c00a00d00100340d008090312410310740180003030035011042c3d4480e402a45401017440482c0b0000044503803003500065090900e244c0b0396034000141440c001129041740d028424190031040b2005003001d00070160076041242c2c10b040582c5c144043d401810340c01080411a00901280c0312140140d0b00907450841150b81c6620704100d440a520640d0b070003007240391500000041009040d844880b0301449182941c103145009403505540b4015402072800042c07014808001c0d04074140d1008014140c054070042c144803551000f00100d07000c42500ba19030b000b40440c81d0080082d0b004103408a0380c4100ca148941e00d0454590030a00002405215401d90b9030303c2c04101a5401517500d0003100403134800d0141000722104c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 641942724 1250 641941474 641941481
    0x2e0801180b0c04030b0406090215030115020f010c05091302130b0901031a030613020109080601090209151216200d020f3f0a0801060906051207080c090a0306 69
    0x80c1c5581e020a4003080600000404031000c598101150003003d45a44e121480245100d010490744222030b003680800028070203000e54000c0128910604104860030300107030518251554461859241040c800c1d1056000b00075120041815205903540030107002c4424001d224248894102c040c0324003001501c141305100134517900c0f00a0360240690200d481c502c00c11004006403055140c1c000c2d10004842c448619055101c0600507d001c2d02c4e215980c03555942800f200782c004447e1681c0009140f0b8890034041320000d10b50604d44070b400d02e08060440c000c050b180010f05041d1024842040c03100825101f2041e001d80c03541000052004051800ca03000d580e0034403150036001501512840440e6401c02261400001e103c6003101d03e442107550380b95402c003048150070700240903c003c00a195078134842c070161004500319124406154100301024140c4001980031100304081084a2804118441c041640000349402d009000b44c4401c088002d0301c0c000c2a41705504500c1561000061080c0e540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 641943974 1250 641942724 641942771
    0x6330303110a0b060405070224040501050c07170f0f0a030b0a05010306050a09110c0f0c13051e07030618050a050c0702060703080403030b040c08090111032e0801 71
    0x21075034109480e0a01c00e0300d8807030803441c402800c8506060002051400c10340c128551000c1240305480c860071188403045a17405489244120003050b200c1000100003091080035048401018424200416569070350f06051083c06c9281c00300001041d0010300512040c180c80030200f1003504152101c254680080080c580016428820003d600780082c03294080e01c0740c10706691014051102d2207040110800280164240c00d03680030008010740a0082c0d400c3c025191107001550150400c2c5d600b04c0c040140368040351280d040f03181e01d0701c403c0c00742c00c11141050340a054125200d9090940d15580c080d0001c1106522148011603050f440d150803185981c4050321610740140f04014640725030b90601d00d80c4c02004030007500700d48204200303008a40902680d5034040d100707290201c3c803400714001041c02c0e2403201040b1004910420140080400c1c00e0054000155010861324103600d0100c00105030311a02845000c0f0701c1c801039040303031191021444c0020107010000000d111800300684620340a51016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 641945224 1250 641943974 641943977
    0x1d12030c0606011d040b0a03020a080d08060603070c0b090a1407061d0d0807080d09060603060b01021b010e190b07140a05102a02100f09020d06330303 66
    0x180050301540c059454003122080ca041c494600104d1a0f0901c4010014450361035844640600004016a100c07443d01d00608043c0d030140402e540004009491100040c15240c443e070310901c100705078140d001d40300c2000304c0c2d0002c06a00071908e40048040c00c084485202600403520144405180794000442c5021030304030fa135030102004039083c040c191000fa24555035034046a0400c04402144001000c0c00e40980541d42203807401070690700210464402460441e2042e440303e1082042c083c582c812600e40d90030030b00103084078003254516003e00909010b2414140700c0c45030202c844948540543c42c0002020101d21862203807a00e0340a9841d4004050403150140709258040745d40e000480e0354280e40d64054001d02805400025000180c0524017045030104020b0710010b1140c0c0801c03242c0700f20000540c002d0003943c07500b8900c4406640302c40d00b01d1100141006407250043e181d0303010028040760800c038002548031014178401c16500351081026040045481d5640300104805401c0003228480e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 641946474 1250 641945224 641945233
    0x15052b050423030408120a11150a140f0f18010501170f03040f120f1e14010903080610200c13050c27060a050403060e03030f071d12030c 60
    0x159441e42d5078034400e40c050b01d0304a8000040c2e42c9010210240500112692402c01e032206541d952411840c0c0081e01c000040d01c03010900501c0810849031081e00c040d000040d0b40c8481d42d18040b00c02050070f11003d0941130400200c1d600050400700030480304000c1d806a40020300281d42d455418801c13001038050881003d010394203c2400300ba20010071242250000c0d603040c0f07019072a00300d028847d5114940b041c3c850103508035030700340001d44105c015180108281d01e000c25040c0181000e1010401101c20600507a00d40b00116000c241c02048565024500b04c451000d114440102205c04680c84c0e81800f0004c1481d1401030740c15000414401c10b40d6800351307011449a404400585c013918010384001c0007101003040500322051361806030b049205800780c4a0f5814180314000314031a540001c4030700b400904040303000c1c41007025034011000c2610a4800460a6003810400e9607a031800191090060001e480c3c0c198145045242d0714040f403410003007042009242e0040b8945e105e9205c02c2510300741c0d016 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 641947724 1250 641946474 641946533
    0x10e1f0327061112010e04030216030b0a050601030c17060d06050f0405010c0c0c0303081e0106021b0307080601260601060503070f020d08074515052b0504 68
    0x103030f0003d030b403000c944804130181c0070b9280c030021000c2508042c00640031030165030000015900300115800040d0701c00c401080c0340d0300e44104071008441014100360f04050900c3c5d65030241030741c460610349144800c00307251215929140c0000758007891802004003aa070030402080001011001c3c01c91140d0b001d6802403013a024210030484460031a2440100700e80e82c80502400428481d01c0d40c0b41d40300c11440300180a10032030f03000701035905a003648548010380c0104226044800001c1c080442c5e17080a0f801058614249201c8a840f40814054145211088424081e00a805035280c17054100e001041d40c805584a1030b0040c49980200c4015002c60282140121a144005501c02c541502c0360f69034039013620f410340212030000a24414a8660642c00f10415806600d50984134203083c08400c245d15508903868172091b1a200c03079200182039004010700d4448290085c00310b4848800000c40191040728a0301c84074800807038007450210f07092402c001c11040201d0801200b24a1380307141e002c800c1491 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 641948974 1250 641947724 641947751
    0x15031b08190504030201021c2304050705040e120c0309090603300903070806040c0b0a050d20180f0d080d09020301200315010e1f032706 60
    0x4107a40c400c014a0529061041c0700c141035002c0c0780c000e84288009454000c11048a500c5044100f5031841c00a81d61400c8201c0408103503005860007002040046240c50280c5640c0d03203403101032254a00031030b19a00d5070429104140034001500951804045c0c80f130440c04030040d0f072078003c1148240290705080115081c3c0c9000102c0c4441c80700300c0c0c0310050200860b4141809110640c03014800100d0050000311040e650602c22040985800d400402c0c4c03030b1500342043c15515203550310034052540200503412079a0740c400704036030740480b6021002c95520b42d035100d090541d5211244007030710554040b41718181c9555440b02d6a02042c4203d401e180744003440c004010194000d142c00821a0a042003421080d000c540c01c2207a000c0d000030000200c8540a00e484821920b01d51404981d0070000001c0090103018500c101d17507001420310b40128504140000300d240c0e1642d02d86042d00904100c5449080c1710b03c2501b18034409500080c04000d18400c01842e0402e80c0450f04003180d810b4100942d550540703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 641950224 1250 641948974 641948987
    0x4180b090c090d03200703060509060f0628170d02010e0615130f020304050d0f03050c0301060c06060801020a020a0507080604020d020915030a08250302030307030b030715031b 77
    0x8004109014101aa60b01a0340c220b1902d01707002048a504046145034550a1109078000c502541020840f0310702440000c1c140b035001094040103e0b200001d00900b910390b0100107080c62500f60b050000000c0b00800031001c0041944810103d8100c1000c5000c02040481d113003540c1005900240508021111010f442d03c0b001c0320a40d003030303418011562010349410980030201e40c2111500203500c940000301402030303a0040f6025249544510014807100b0b034040364040d0b00c24118a400c105505115080c0d84040c0300c180b040300e00f0000d034100c0e0342041c40410743c41480100014002199079544600001c0d442d0f00345240240c8180c01b80b03002c006000780700412420b11817940100038039850481030b420010710000c042e012040101460301360740d001d0b84080101d544a5802070200c65103a940300501e0414280288140400882c0109200c10000c0e80000951303070400450b060214110796003e000c649044900da02c0008000340700f060300c2c1e10710303901130307129916402d02c00e41d010100c20309048095411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 641951474 1250 641950224 641950237
    0x509041b0f03350a03020d0c0206181f0b0103021b3d0e070e04110f040e1f3801050703020d030c05070602070b010e150603040f030504180b090c 63
    0x29005540340d039440000203c01014586a01e0900605200441d0b94800482c0e0102501d4800750b8083c0c1c0078460301c01160111420798895581c0100020300c0350643c402c800310b20350031003955003989403000170304d8680c003a4058a180a40c524422882d10542400c05a82c442544d49807400001c10113074031300c01c8049485030f21121100185800085a50b402210300001d140d2900c4490f40c0340907180002c01c41c15800d500780c0380558020108507110104102c2000844620706030010302c940e20b4104000801c01c804070b030852051598181010322910013608000181c5035102404d03c14940741d441c00c600c0c0511002104600445109851425402c114010b40e0548107031200680036900021201101a01c250040107010f83c06240c02401d004c09591000c1c16600080300456450310300e00014010100032007040b650060081807401590011703500070514a100c083d10190410350b0f400ca08200745401801202c005000b11521803983c4200e020941006100c0303413001a203c1ea0010020440f1212680203490340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 641952724 1250 641951474 641951543
    0x901091203021204020607170a030f06050f0306040f020310020c0115060216171c0e030d03021c0209040605090718080c091602010b100302040303090905010f0509041b0f03 75
    0x540c0e403a5502080256001590b045411600721100c50f0110840d81001d407034134600b182c41c0030030400388bc00c11135000e4860981001c0d001d01f4241000100176900000c100340c110390400c0d03420704c40c054540003081c208010400950001400004d4148450b04150301c800c0c1c00a000031380c200c01c4551680d00403600c404600520400812052500b800686081c00f41c507240c0210160444015003485000b030207503588012515400b188079540b60031303d1420305101e000e41c00211403404602e13000300341071800030680100d003002c3c40569001c9400003458486078403002c09000010255075051406880082c01c1b4218a41c6200b41031030b05040c000b544810005440060700b400a218a815130b41d1300c8040d4004040d15a0744c40b08540d01c0710980d02d0349448100990125908555000da079076811404c010303000e0f0754507a100149007441c1c01c00410502c2107030880030081c0e034412143e0400e1074035103013090480c010540003500e503001902c4400040c0d203034038405c1c080d00b00c0380f2130304a01400c3d1891642014080c4802c00c8441ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 641953974 1250 641952724 641952757
    0x3010c080115050405100e18010e0c0a0512180f03030405030304110f0904060f0e0a02062d03010b0301210201020c04180b090d03110f0d05060f09090109120302 70
    0x48854004401510307010b2070f00d070850030309135100002014001c04030703440d03000f1440c203200070f2440c2d050500201315825038400303d4035600c0d40f418174a00c50414004040c00c0d051038020a0b055042d0b442901161081940700c00f00307680a0134019003a03988414514240c508034452441d01601140c004010b07a403142d90804040c40c03d550f50f548034030340f50850300d405007680006114005c05040d03641c1d86809010314050040042c10307001411245040b16407a818007031840d4031400303000f80180c0d01c88040718548041000d41321070b000c10900181d0030580c144c441c0b18113806008400401d10551070300186048549408592541c0c00c50340540940d81d0008080c00303070040e04010b0361090f032414150000c408600794403601c1f049200c281c1d1a20340c039081064408003480d401100500700e4955050044250076036005224030b25007850010a04050701ca8000799548940d1180006601d0faa03550921141c96034003d00000441d01c0d00c6030456008010610f811074400024440b50b4030030a200b80f094580d8440d00070343c0c10b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 641955224 1250 641953974 641953979
    0x50c0106031a01080c1f0c02040605210d090807031514070e040609060e0a0b0f031213050a0b04090b03101404060c03020c03040e06060d14090601120b07030b030106030b010b1803010c0801 82
    0x447d16402118000c0e80c000f0303190302c3c00050b180c50b02c42d8240800d0000b0280d021446a91543c0103081035080c0c0f01d80310401100300c0052000c0100400d551044a034072401204002001140f41c0300544500100c0c400f601490808110402e6003001e5410380c0c440b0101c40c1003020300d440d402000d0071030b00d95020319403680803e0000100405059800100d01c0f41008081c086080000000240b801104040c224450140407404170401ca017100070460103000b045030300d214150700b0884505403034010303842421052502e8801100840e14140583c4040d1104840103211115481c80c0f140d0a42d0400d803822540304e441c051000c1d10407842882034548010842d0051480d107880e101076264103000c003502c101e90008040003c0001804030b031081d001915501031501c0345030b140000d122030030000168040c00540800304000300000f0003050303c695007c40a070400007460000c03200407034010708803074100610301d0014070004508000b042c1c0c0542800100c04d0040d07010040044180340c01e8418050040c0d01142d001c0c00103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 641956474 1250 641955224 641955227
    0xc030c0a0e12102301061e0c1205040e06030601050a05010e0105040b0c1e0a020f041e06060509030d020111070b070c1a0105100f0f050c0106031a01080c1f 68
    0x1500002401091000d55801c0b8040450a11a0319804003004a83c1c070300703109200c0982072441c240c201640311900e006030740c500781780138005080c18100314018075035044505a5080c02140c0d00c80e030803500300080b1012020000000f800d298000e0081c0c400b28484400007070040e240001710b2506940c00a441480102d15007001940c540e0f89610360a81400300900c00400c4410043c40a800e011084400400c4880914a004a62100c00f0207100c00c031504603113983ca000d62500d400766032410b50306503800205035588103074403020011400b100000d9039081070400103005a001029202540c021400c1d5039110075941016422101c0c1d403040072104c10070600c101ca01080028403815071214450810407801a159517480300341100340341a00e9849d4801c0c1c4014429420400d40340e0080d401329007420b146c00b100700003000d8815410302019000b04880001c1d10480321400790804802103901ca901083d00d0781c19100701d40b480d20b4003401054031074440d020f030a130010301d0f041c084078948049030303c3c4015100360000c20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 641957724 1250 641956474 641956487
    0xc030305150a06030f06080609150106080705030c0711060a0e030d21020c070803040b1c06050f0907120c0c020f090c160305120406051504020a092601050405150c030c0a 74
    0x1c0070705d0b6580e9800059859018080c2e00d20402019010381154079014812500d1242e06070011400c009502041240d200e030013030103c1c0d4001c030002c10f01136200d00b20785c074010750311881d040f8a4940028000c00c000860315040f94210700c44200850a86141e1600c140048400203280320901210806148500c5520620380d8020503400c0c5004040d01e14a945134881245076920551210700d0000c1c0c0042c00c0890104014105440c40c0d9440340d092200c00e24000024400d64445440f9500c120214804540a039000b440d0803d00d0510010b405e002da4150004040c084500c9003100b40c2c018205191803070628900442114464040c01075031300c0c10f01010180b0240e90040100b01141484401c0000405e00503110006a200c1da21803240481c0d140b0f0203858081c402d2914100e014056801440340d030342c0701138103c800c00082d07490500c00000e0007032000d5201c082c1c2c100c403c12000d829503e44002c0c08207021700801d046000c540e410318686440c0d01c604c2c070000c24900c0221003080300c0d05402d009440343d0350b100780d9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 641958974 1250 641957724 641957741
    0xf030908190c0606080f0a14192901050117101a07020f06070c030f14030f04050102011b08060f0103060b07030e0108070503010f05010c020d0c092c0304030b04080412030c030305150a0603 82
    0x404543d9061280342209d0000c4c10f0b90081603e45856000016900304494404d40c01d840855110550f2654503160010300b40e40b814101445e9900c082c1d8002900e1080350011000003010410498980d04481c40320405590780b1400701a03005103040d20a081850030940304032104680c1c8643e182c3c8191346162110425800e9405088480d45508006528401c608001a095240400591035551031401001a00713350708020044041d070101c0450080c00d41d00180c400c2e5200d54241c1d103203c802e042510040b0020000341d00300c0030700510007040c120f06045c0d000070715038120513003a240c610712030729000d90a6585004c01d10030240c0000080e2030504c0326500c40d11510070150310140910303c40351001d548032404054290440341d8029075801454113242c1448509100421121800340001c110050845440f031140d8040a0044c900e6840401d0410815108650040038074000f881c44085561900a05407841040c054000074207010109440464207403180c0c03000307007000303101c10449482d1001c240d02505d65103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 641960224 1250 641958974 641959013
    0x1902070c031205121e0c1605030d05011401170a090809040e0f070f08060f040302120d051b040524130609030b0702060105010f030908190c0606080f0a 66
    0x10b01e581c2200d4642c944a03898050300e5107008041140c5611000340003100c8020380040e0380510480b400542d076040114848255602c045d940d00c038056008150300c0003080c510002883d0075803800658000342c1a034500c0211945c1c07409402c0c004440e1170240c041941480b00c40d002c041160010540d001010b02807103081094205030418000804548120400b1003594115415100d4140b00a10009018080030400d804a00d030070071a00c03d585007002080116042040c101044c01d00d402082429054544c00c82c01550b249003410f0420040d01c8103544081000c04050380e0707030a104140e4000da40c2030f04d802401441c000103c1d040b50000820070b515413007222000030050000f912240310702d004050101c0d601c60f4411140303180b42400035440010700181c21900b2500040c03045a901204000041c1d86502c2d01080086032414110100e00c210194100d415a06101070410305402c0384c01e0314040c41c0603203810850340d80d8401441c0e0711014a1030b800c0750f0710381088460000180c03c83c80c0070464506503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 641961474 1250 641960224 641960243
    0x203100906090903022118030703080c070e01050103090b0c0a0c0203120c1501030c0510030e0706030b01180305030a2105090115090c022a0d06020d14190207 69
    0x5540c20803088960640000765183e0321085890240354042103281424500d643c1088100800d29400075818000e90140d02182c48100b824950240d0b01002658040e40d00b2029207503031002640366080d52120a4810050209191300001a40d03600a1151028840d048400d80c510350703442a11640341a4868084003042c0800340c1121400b58500301324008070f034150910b500b43d80702884001603180803907105120180310b26003001400003400042074401243d02c182c40c044600081d05200b98050300b1810000001403003610800603906605030010380901c0750a80725407055048620b00600c862207030340000b034071650040001044441c4205500c4051030409001072420b06210036240301503c0c030960701052160f4403010046102c0400e00a0000100502c8400300280c101c011006500d40f60206c2c00348500a808041c4040700092490020074a40c40091074032002810300d10b4520001c0d0800748016001034500041c0c0350b44100103104c024054065401400d42151480c0e000ca40a9445110700f1941c0c0c0340c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 641962724 1250 641961474 641961479
    0x10215071b03020706030f05090c10050c15160c0327120b1803030f010902390105010f0b070615050a0308041e0e0610020c100512061012020310 63
    0x1001c0706080000e00c2507010707160051070400001c094680c10310105c01c0841c81c10701800000680062240882038096940888011b01444184d40fa4003895001040c58060340d03072011400c0340600d40c07241c0724564502c0e03240f0480320f000508540c0c012803001d005001c68620001404101e0300303440b0a100030001c007040d14030025100c0c1c90380c2d84600380c01e4030100d9030303491214180102c2e2036030312028002c1c085686004600358070341020040c1c040760040c400c0d4004141e001949039040032000002d2400c2c0001544024444c04c110101600c1c1e0708042c4e20800382c1946060700110304014050f46a100b101e140364000e40c00c001726522910000d1100100f09008429551400202521502c0783c3d40010750060801d80d031a50f15000924100e1328448062003d0106081410b0108078908000c440d004602511034031012102400f060789010822420280d011a1205500142c41d07800320041c000f007202400c42035032607240d607002c0c000301c8807422030b65201040c001c10000f480010b1a501850344107141c804603003245907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 641963974 1250 641962724 641962757
    0x904241523151902030d061413051b03010608040b07031a061b060118060602030a0504293126030f030c04030308060915040c0c050609030a090b040501021507 69
    0x143d001000f801607000804c048038141c00c94492840104a050000449010035500117031420301d8407260030204951f00d001048030174002014134000c5403c20041d541d601c3d42c441030003504441c0115812030302d420082c000101164030030701a4900c0603c041c60000d505c0c0110008028460300304510f4003044401500800700c100c58200405402041100f2114030300f10a070181d030170700356000da82100301035600400c4881d00c8182d10208a5003210058a0a4510302c0c1d90420851004240c00c654501c90b480e01045d02c10700200402540901d454251289040200d02880c40c101e00301e849214821045003c0c503c62400144076982030401c90400d181034030701d8040c0d400307214100c60b0020b03601c40201301c502140500030150003107e070b550010380031074440e04075280c54407410340f13101424240360313010302e1b1545240d160040c06503405100e025402015070b803035480c0441d0165502c2e0403208441c000502600c0c40081d826030080b04503000c3d0350060b405440e0340507403022403150040340600f50204000c4908660481d44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 641965224 1250 641963974 641964007
    0x2208160516030f030807020325020f130b0a050d0f060b18040f020a08010e0a081b0304090b04110a050930010f110a0e090424152315 58
    0x46100d0f40f1465140140c6060040006900514580641d071042050311407004400c8140c1400c03201c96440082e1459561021500d411150300d00c02d50003505074041403000340b1168001d1580504160b0301451000c0e5a14200150020702e00405030500c5564504800403500302c0d000300e01d5105001e000c00c1107400c10700540840c0044219415941180f43e903103447d0851505084200c0148913a50007030100481d0800c0c2907450704c0114034024802e00d000a120704006800c01884130540082a0075071f51141c1d81c031901c480142203013120300e034891403a05080c0400300b5070000c2034a4036000d051341d90a007085e202c1e5044c0400707120303158520b06120b0f4401070300d0380120305e019044208802882c0d0001c50303000d20100c01f050548400350840080c041040c85180c16880e0300c50610315904904548a1405840c1c034200800b480d61080e80d0341090040b2038102c1e01003a11107410441d40c510401c4d1201c100290743d00c9030700080c100c528a180c1c0c0343d090000540c00e810301e402292000300d107112030039452502e0f40c60030010301c45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 641966474 1250 641965224 641965229
    0x70303020705041a180403110d030f060608160c0206160807020a0806010b0d1a040504032003092d04021b0705031203010b0d06031205032208160516 65
    0x1644400018403090803d8002c4103c640540d40102042e41c00340000516072513032000c000c41c2625440400a014944104486031340c1c0074080342600c00401d101c0d40c00a0107400c4030071041010701c1c1003200000d41d152103240d0840c072401540b00da02d40304420010045440504442040e40d000c0702c00c0c81009000303a170410035024400e1007001180c1e42c0b0a83d52050090408169004c50348030b4010900402c060001c08040310425a00d03600001029a020190880c1c465158644142c00c50320300810402015040103003819072030b00d2401e999680d6040d4100b50b503503a10414038480d4103d5114502843d01c150021000944204400071002618012502203402c0780c0002c2019402c0741541c0955441d105028010b80c00609004d03806401c0000c003086004580d848107200e02c041d4800009804110000c5a038000c4003c0c0d94403840090510701c0800c0014103580007940c80d50328010441da8864142c2d04444045181d0a0344217480c0c5040400140c035444409000540903200e0380544289401d074003554400c0b4030b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 641967724 1250 641966474 641966477
    0x1c111c120f110a0c050607060e060403020f070e060a0b1810081605180910030b0109020327100e010b06031f0816031b08010e0607020607030603171b070303 68
    0x5081c0301d18180140307071100841030850345411060086000c600500303000420f031441510865580c0d0043d00d8080d00a12500800d819a8081e84003840200b69001c503500a00031042d60840300203079101c00c144103000b0015200c06034401c6400804004e9007040038050044080903410310b00c40c24a007a004500312100681110001071014010804809004d4203c0c200d18120303440e0136403c0003100b00d03002d46141120003041d4400c903010390003d83d42c0d0761500d44000240d64400040801c07560349042400180d0810388030b00140310b0b46003c00007102200c0340400d6601641c50001010301f00002c5080c440102004d1a081d100d0307540343e441c480b00c140c40301c1c401180681c20380c11042e00c5101540103500c503049216000601140c200901c42120104211492800c0d20b0b00b26a40740c80800c540c040322408044142d101c82125400d0501c1500218404500d4620452480d0241e03001662095401c4040355032500006001f00e203d084506800c04c1c0300300242102c6e50b550445401500e003061415840e28035607510440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 641968974 1250 641967724 641967737
    0xc04080d02010c022802062802280b06040e070b04030c0e07050f0d1136010801050a210203120c15040f0b0a0b120c1c111c12 55
    0x2c0d940d941001346140a05d080283c4240c00f07603030404605603c01150002904c20000803410050506d03105c2101e4410352080300a0720b2a2070406a03000e0744a0010320709a00f487d142403640594030103000c180e5100419846240a4910384e00c1800300001044403543d0040135201e140e1010406d5510b00c07004002450013500a400d40701e180544010454100501440c100001840414100002c0c0c0c07090b54000e00310310001044c224030b0700c14a50014040e409445811290801201c401ca5594154190009100d040101c0d4110b03007050040d50305074401c1c07080c4d0360002c09903241000b000d180300e0001c100c13445071151807001c0000d140e00041d19144c4080c0ca0711441480c0010340c982d60a504020014031098906040e10051030140c4402c2040c441c410405040313403140d0310002d40c407450258000d0801d414014014030030a1440b40d1010340c1c900e1003d20301ca000d5058540740003050800d98a60014881d03025103825103000c1e44a050081d000d2900000821300c0e10380301c11f60170002d05807000c000020945542c420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 641970224 1250 641968974 641968991
    0x30d050d0c032919080d0f03020c03070c0302120114180f0a14190507090b040f05010b0a0f05091021020a02062508010e060609090f06011e0f080c04080d0201 69
    0x20040a002541c1c4d0080c4802c003240800081e400401d02d440b805038503080c40140003403103c1094001c2c0c800d140d2079091501000580d00f04018400280c02e06483c029288100b10781240313007046e802c031402400254000c091000000e880000b640c100c095080302d0403c299580ea000380043c59140103280a0100c1c0c3c0240700d242442c08444007084082c08c03101d028001003c1115071602c1c2c150711074910f8000c0050381501e030140301d0307425261504891003154500608000540c0d699102a10720f4000c0d4642c1c82c0041c2124113800c0300e05201e14190748005900420444c5884510381d000e840500d1212051016481100e94480c85900103101504402c040c42e0082e00c0c503454491140303101580c542c1002d00402c500b000c0d00e043c01c182d2000f54141035496003507519415443c0e40c00014542d02039520031940c802602d50810076800130010819025110030b0725440b400b807468501002e242032b2454107540000703441c007103c07c1d034107885480025041140c18209905d0182c60b0082c8030f0500e01c1041004d00942e4580320039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 641971474 1250 641970224 641970229
    0x60309150f011a0a1106070c030e030102070c090504110909061506030403080f0702281112100f0f0f0903080f0702121e0307090e06030d050d0c0329 65
    0x10281c1c04050100d041089606200000c1c560030200000c0b88030212011810070351882c0102c900c540400d000b14116440ca20301520018a000b50824040b00050691840c144c1e0500301402502c0c03400d50300001040e02e00d070a00f800c1400070400100151280041c8101e542c1c820b40702c8804103401110050043c0c51149403180300e8903034180000c03210078003403082003081002196001140603081141403400c103045488104040780340c1510401409022241c2443c111501e00c5a00d0000b24402e200c0c21600f221040444100301c1030013502c443d51301080c0c00c840d00919036100294401481943c44c01c80015064002c40039510813200b072485241d0016540d6803200341496000821241c1c00207640c24101424544400e00a45900f40c170f000a0040103c00b0559410f00d99a8014107001041c083c130540e0344070b00e4511002050204540b161024130304030100031691500b0003140081c1c5800707654a40500d42861004007400510135800440201965030030145101c89080c0ca581c411642111016503001c5050b104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 641972724 1250 641971474 641971513
    0xb03030706090c140d0f020103050406090203071e05060301060f08130c0e01091406030c040905030f030a06210503040506031e01060806030d021507050c070314061608040b0c0f0405060309 82
    0x40700d00c101300b2181811700103080994461292507081c600442e01d601d6500e016400b0f81400c01c0025814000c41c04080759402e0f40c0b14011030b403030507110340700d240c015614018001584001e015800002c1d010200d2030742d00500803a04c89401100782c1100910130f124176240c041d00302c0b03855046101083d80340b40c01084100203034012014200101401c5a00034140031001030380c2c40c2c04d41e0134241d00943d103a81d00c16081c0802071080d2402c007518201803959030304e00202130308000d00050150022803c0c501001c070b4054000000e00040d40ca03801b02c010343c50207040404004054200511540d400f10009400002c0d0b11a820b295600900f443d8a580d41f182c02e055040608000c04a0740b60021540001540b20900c0b4050756055003101250130201c0c1e035046840c211a00b050030030b4002074252101400300901c01d003070010700d02c1e00c1122143e01584481204510882d502c11069901510000704140031540c002031231002010035902c0d88207030901d002d50321008110142c100b140c2c4490035170000d4000da8032103101d805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 641973974 1250 641972724 641972759
    0x10060f0e091501030b06130212100b0313061e092117010b1b0714090c0a0e0424090501030b090d050f0304080904090f061109130b03030706090c 63
    0x80c09001281800350306910b1156051001402001550010403643d80710076540c0c1c25625420309040d560752051003071120010300c05481c114a0b0450000300000d110511000303403406150f0300c2c1040b0700c2d48200da07102c40001d00741d04801c2c450708003107245c0c500514000d9445141012072250710b1007020800801100d4000405110380f4109000001800716100030101d0a11815148000c20440c3c9940c01036a18480e2000105034046241c0304a1001181c010205401500240c40c00c1307441c050b030355171480e0241d0480d008080307200700400d00b0229580c4041c0380a4001c0400e010300f42c3c0500480c0d2a008250781c1500e0403990021b0510359560700188103000160310507a40c40385c0303014001d188860b25184014494031030140c03100c400b4800440403a080240c1c0c90704442546000800078042800035080080309804403100440b103051801110208410b8840140d0398402070090280004040c00503444000d41841e401c1c056040c04204001c00000300d0500c2803412282c001c11418240d281402c09072440c801445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 641975224 1250 641973974 641973991
    0x70905100206161806080c0904050f09010c020d080105091503060c1b030901020a08030a090f0803090c2e0203120f01081612171e0a2c01050c10060f0e 66
    0x48600320550a60000b10130880740f807403400c0e541682c0c8030715016515004441c1e089a0043c03c2c94180145000b00d11071250050144900800000c1001107060383e44400c00410600401c00d070750010030051a258a0303030355005203c504440260342a91000a040a500312400d940da40303000726045144501c0c8070280203d0058040c025860301c0c3c80741c00003035500e90602d0310040c0780e60300000c0000d1202589410401c03065070b01c042405044a02403a00b071071183c1003180d118900380f0030400b0030aa240351054500b0b102c0d6030f90380c02c80e466940c0c01e20b0001040d1412500e000082d84420040d03a400c000d080c0842c1481041c0c2900440c03d40d5051050070b1b07062621501c4050f0b00d51141d40707400c0c041c1e0019400e81882d9140c3c08114500c0400b040c0004c00494011840c1400d039110019448013602101c4900901902c02e03503940c0e400075800c1e14100d103840300500c540c040122800043d48005507500440080050051210454032104e1107600c00406035031040d000014161a900c000300070782d03d140c548071500541c16 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 641976474 1250 641975224 641975237
    0xd0b150306240f0a0e06130c0201050103031d0a05040203090309030f01140c040f0e1005090703050f16080a0f090b07090509070f0807140408100603020f0a1503020307090510020616 79
    0x380d00014100c4d1480c0e00515004249150224a9541d070f40810540e910041d404144008030908030007900820b4248030540100380d0b02c2d2181d603000c5c0c0c4c151502e040c000c640249800798182c01d00041c0030003508010b200719080d10003040580c900d5941002003802c1e1001c10710020580c01071908100e0b0036003401500d6140c2640d0305000901200c054803400600344c940c00c611641240d5140700384002c6a0300b0b2a8040c1d0b801c901c0c1c10007030101d403ea16400c1188288809415050140c03100d001c0b605018040c55024030004030040013003402c180d6260044444011041c20100380e04260b500d072019150400d0f40c42001040650900700040d00307020401e998411a5803e210491401c00c501c042c00054004090500308610301c103400e12083e8020f410f075000341c40400d0480320b02071510303004c0780c2c01012640400c0e8841c01c0011080d0540b49070103603451082e54240d521040f802080b503c1305401a41000c0c05240500101490210b2140c907004038844003804194010030590800c2080c0e4031900008403400700810a5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 641977724 1250 641976474 641976499
    0x507050a0e041211210a080726060a030b070f0206070c0b061311030c0a02010b150a14040509070f030b0316120302070b0a0e031006050d0b15030624 65
    0x110200c140080c03030881d041c200c1e820016180c1850400807401d003003d003100c1782000081e4000c804c2c3c1014111060b500d0b110345009444103141a500c1d40c51103102c120349000130824450030899040041d0390806005005580e000f5240da5400305806011030308040060480c0d8078583d00585d040003903035000720590510015003400c5460f5070010400040155000c0d00ca04e0020310000041d030345c41443d100e07155601171030f220700305140d030710041e039004200007001582084d206a2051502540003688600402d85480c17628170409403e884400c10942d01c0400c8080c1030000058a84405560f00e2061065903a8050100c09001016086401d40500c2d180651f019640b5080010000d032040030940751081c0210400740c403180740403460018540c10042d2440c00c041030007464207410040044680c13404800360780450008007140b000b1036180f440749542c0181c07241d040303a011a82101e800c40d0024440c0c0e051840c0082004086464450141d60081e01211480d003052410514000704803c008000c4170b00c0e03142d846 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 641978974 1250 641977724 641977733
    0x8010b090f0f0405040b09160810150308120a050a15060e0a0911030601090b130308070212160f060203120a0c090521010609022a0c0d0507050a0e04 65
    0xa1203409a014200200e2803100303556580c09500d418a0004005111034605860044900e18098420b13600361320510340030a80743c5d40300e942c2d0f41d01555524001009610510204d22014000b0490840340e4140d1401c00480801c4130303600241900c84c0020f002011509064110744121748004003640103603490660f000041e03901a40d054030071100240b610064074288400001c41582c1c1c140e0100004500d0021000100c91441e00075502c181c6098852203015076880c40801d03c6845480d0040310307a82c4101030305100041c44100606042d40c0040c203445000c01d003242105140000d000140c6040021701a410060080c40306010341c05003805201a50a20310108012005243c015002080c1076490b030141e41000e43c85007140d2401400018022005200e019403190901500c403000d0700915400c0442c00b040c108d00328000c0320f115030010042c4103001c40081c0382ea0103c0e4a6140180200c5001b02051500555528a16074407028011000350692500d40410407040000c1d5500000604c02c2c08410000440d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 641980224 1250 641978974 641978977
    0x302010f031a0d0b1503030412121e0509040614010c06090f060c051902070e070503091501080309090a05010f0b03090307150903020d0c121101020d090f1208010b 71
    0x5069080100303481e8a82115010421910b420050b085180c5001a00134070130f010741c90790302800441004070a10403000043c1a260f02c214040c0d80d01c03840030400381030001a032600d4090701c5141c07103185c20000145224408550408030480381000604049810021413805c0e20800c4000d04c450b0480402510069002030000030150308080d00c0310780d61341c10304028001401c1120513120b61048042181c084100c07405000e03600441004060000184200b50303c081c0000740712800d454003100042c0c0e0755902c0c10400c6030b240e400101922100c0c090141802c680c024800102c5001c0e1003100c0103140c8402e0f0050611803c144000c28403d051800c010040080b54158848002680d6034620465625500c0000c180c0c03a5101c0c0000c0200b004c40c1c40441c2416101d490750020301054407079400d41c0e4481100c0d0344220340200d5103810203406140308400840c91980035009280400c55404000340c1003c2c291413500782110954881a505825030011110801140c00102d03001207515082012040d418460900c689 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 641981474 1250 641980224 641980247
    0x10203040c051804120c0f0602030405250b090d030309171e120619030f060203100503211b060901090c0506190305040602120a090c05031902100e09040b061504030201 73
    0x5201c1b032091000e0a0041400f514001540c001c00c00759030704c0c03d081c17810f0f683e1030341c0c0041c91f0f040c4015000c1d20f20310324001c4922006c0c1115203030001c1e1403d01101c8010882c1c10581040c040b01030680d907150384400920b021a681042095112000f526070701e10303c00000180588401c2145481010010030140921504a1b950014800d0303c00d1000c507541070140100e003051139040035107002c504420410400401da0010740c0302e12014450141115652824956660000c2c08800070001d8881c0b036000c004154007000d05016110603c1405d4026201c001c1e05041c0700c0c080e40ca121060351104810018044080400c1c801400b081d5a140c0c076040c082c40021031081c0340341030344170105503c0314040360a01c45c05405451813115170140041490030b080d40110020301c000c0340216014100b40070700041a280c040342d19400c2181c0c1441c0100c80480c90382c20440c420042142d548140300c19845216103075120819801d20643c82001e84030600c0c14010100515040c174054030301c08402c420081480142d80c0a20180c19 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 641982724 1250 641981474 641981477
    0x406091404110f09010e090c0d050604021902101d060a0903030227010f09050a0b0304050a0506040b040501060806011d060f030d02030a0e0609060921010203040c05180412 75
    0x40c03814040d0004010b4040740340c0070b19590001082c1c0e45202d52100c0000d00030070100b40c1341c6092101c40c8800340900078200301c680701403210051082a1a210320342c1c101c6a48100300a1005180003a54030071102082140d12070b450059110020340c0c1072540c814031943c0840060750b130400910b00c0100d15440c0e540ca13030040c0480010303a1038044110405000f81c05580c82c200b1300300000d412464102c80101080c002c2c10f81c44070b000481d01150009072601804c0d1803001d80300090602d00e903407424810f601791a984007400440b00c910036140030f140803402c00d21405004034429065220326041c0742c20945d09442c403c0d008850340342c00034001004122000300040b200a4020690310160b5a100c40004042109060b0380e00c1c0c05001c1c2d03a4410603007960100c01400c84050544502c041c010400c002c0c48400c3c001c2c1141d858000360704000303030001ca00d8254901c00c01c001900c40150103201c5090f811a0076a0400e0b5812114645900e08c00d0045150829003001c0160880c40e8100c550310701600c440a2000d0391112400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 641983974 1250 641982724 641982749
    0x1080a03030f09022103090a150210060b2b05070c0512030708040b06210313080c0a030b060a0909050601180e0c010e011214090105130312051e1317040609 68
    0x80b0780704404d205450720008000c08c0e50b01c107195141411000d003000a54090300500030071061501c090303000e1180e034054402c2ca07007589090000d403074145488500b2003c828114079000d2400c404020105015942c4625a6aa80e1023500b00c881e15007540b41144a80c1c0c8a21022414810400c1c00d5a00207942a80b00390000d00f180e150f92200c80110700c8503402040d00b085484c00c013880d08130030824000010540d0000c1800c0c48003001d80d849078041c2d150183c0c42c100e80d6011480f544208041883e00303a1660704141d0080c1060901950303113652404032809a4012513558101400401004200040c100342444904105000d8001007094036911a0210007050b8107000c062032541003142d04c90a2100303007101c0b0340311040042106892100103000402c807160030096082c0070018059184150345021026810740b10000a25404104500544001000000584048004d110083d150441502e0149411143c10401401e103800c0490f028526505100881001004100314056200201c001100c41c51450407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 641985224 1250 641983974 641984029
    0x1205040b030c07060905011803080a0e030906182d0609010c23010c09080616020304031709100f120204050307030b090c0613141005030705070c0b0301080a03030f0902 73
    0x303005000c0c48002604940c81d1406403028841d480c0d0661000900031303112030075144d030350bd2418002d841c00c04102c00d01c0368006000c0201241031400c007802001c0142c504400040d00d892000c2408078045040030508000c0c029181090481ea07110052801303030342903070241d14020b142000078002000c10140200000b5000200c00311904411a014805440041c000c0c40a50306082c4020b00124142c01500d8440c040d150100304005103080c1d0b5095400d500d50041c60915246441e8000003a64200c01d0329100081000a41e03015510700d2002c070b040f1405901c03407010344040d1032001030000e100c20340410000742c0304010600513660000703600b030122a44400d040400f80c0e01c101d41e40e800c00c1108050700f81c201d040445d1500e0155a904e00e40e1098610712900301e04000302007410401040c2c1032034038400124508201143c80036204070001e1208a01a141c0c080d00195507061204040d0b000340d01003c016002581d0640400d907142c010540e15001000c0140412410703500060901003464140c2d00d640c1c3c8021441c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 641986474 1250 641985224 641985233
    0x40f0b1e1b060901020a08040b0702011e0c1b1509020307030218160c0305030a0b0d1a180c0901060c0309080607120b03030a020604080a05251205040b030c07 69
    0x120014102450040c50322810041d0108050890402201c00503000340000204080030503c20f440120380203a5601d54641c03180d4403507029004020b40343c00c00f195200e20541014800e601070214100b804480006403074046008001e0540030380700001c000341c2410030308080200c2e041c0800740c085684000340000341c9c66aa440004d00e400c003103510082d045040c0c0903180e41c201c031103046840d100d00e401c2035040006c0c1c80d42c40821281e009040d9070003000b198050021521407045980300100c54880540648184540c684a000c500590240c600d80001000c10801c00c42003540f0803a00d1a0a00c400d0060012510180015038840b81c140120f1040043d9a8003400502d480785806600400f8400140d40d081d0a149400824241c00c3c04042c01c09941010603011060400100715940118598094403d50b00c0d19594061242d2087e14200200041030020412541b11220310384503c00c1c00400c002c0f007001442c98014443d078800c44101c42409428403041241ba88046d0849611004c0010050b40d00c84051a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 641987724 1250 641986474 641986507
    0x1c090509062101180510140708040b0403090806040c0306180302100b01180312031109090f07020309041d070b03160f020a0602180a0b04150806030c03010e07030314040f0b 75
    0xc0c030900615000c03031000144017010448682651201105104032140b6102840710041700b0f4403c0d00c00180410006030206a18688858006202749030117003400381d54403803081c03a0031815182a16022100b840c00c10421000348520480c003004030f00110442c60b60750f24003a441d4503a565005a00702e4840b401c4401038cc1c4168840b201021301c512041003096103a050207840e4403d04203500e00484d02d000c211844400d22a0281c440350310000344225503070754809241d10400030003e4518400c0d80720500004445540c0c074007801c80506550b20519004048070b0003038614000150b40082000b0900b041400401903490140605258203401c110034600760b950012850101d00d5240039260f5840420504004142c9420190241408035104017000d501d507103401c41103104a1080d90a000710070559162450700440741168801b6004090340c8080341010301003420f5601d0000b042000307030408601801095044004000e8003912400c00b28201801c00c00300c404448114003c03045400004903040c07800c0c1e100c214 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 641988974 1250 641987724 641987741
    0x90a06030c03050a0303060902030105062d0f091c050312040f020901031208060109180b040b150a0f030c020604020d061d010204051206040210030216051c090509062101 74
    0x6070707640425680c0e420100e4441d400300c1c40881c0000e040c0703403000907009060300a03241683c200600c485c1c81c1105040c40c00704102203031481c140d4034807015400c3c03410041011010f0203048146040441c0e54202c10810481c2005003180c01f8485142124005004264008191070408032013604003000ca03111070503c01a00420146c000303500c0002030002100300301090303d13280d41d2140e10b9200e140c00c2d5100c0750015200d50303840307000301ca555410050b038224041416030415050141e000d4000101c03034003140081000d016101d24800108240095240e0754a40e01c43c1c1010100b00d1545802c10203044c5c200802074407503001034000380c4140f00c1c1c5001082804150342c004e601a40425411903106207a01d29540e01030340251084d24410000381901c034113200004200e407031095500504014040746c1c0510250003d400c04442801c0c95207030107080800260041040900c41640b0b007000c0000248000c2c001030181000341c0100d4000c00955040c8105138030b4081108075441a80e1640556410b02003203090300412410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 641990224 1250 641988974 641988983
    0x303041a0304081c060e0609160e040f0612020a0611030f0f0f0310080c030a0302100213050a060e0405010b190e01053001150504140f0a03060518010c0509090a0603 72
    0x107104d04e482044007035001408940c0910425130082d5102d0307040080302c04040f00d0702e10008d01e52603803201c0018403904010b8500c140051001500e40003031041d042c1140d1322034010180799621110624194604207035042c0082209146c001e03e1a0810120240c80c4e0081d81030741c070850b00c0302042d408604064030b0b041e01d015800440c60f080c1c4074680011000130650880c410891140150703040b182030390801158000450360182c0040c181101c494075030303600035802aa08203581d5018000701140503a41d004018009012959034981c050800f40d04020888406920140c1f26441c20000d2100010302d03002c84034818801c60a00e5406451403a0041e1018840d03441a809014041c96881c0d40c9a04205469004a40381003039503030603a0380341c8901e40424034082c003e050100b10180402c0003003142c03a8200e0081c070000600b40c5400201841d01144030781005802c11205980c4840401c0000310715074010402040c40c650007484030443c064005080781c4100070780d03a80134412040001c0c09440301c3d41c10810065910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 641991474 1250 641990224 641990257
    0x1002120d05090106090203040f110d02120309131514150301030c06030506030c090106030902131104081e0703080a27090e2814030d0e160f05060304061b050903010b0303041a030408 79
    0x84080c0d9984a6100320703c0030344109984016180e9511440c8201054600e42c50301030b51015040040700b03002800d21441030340c0d220614a02c0d0200b178601d1500530310f000b140b04030004072555040100290a5820050983c0d009911044105000d640c8500c1c1d0036046565a007000070315200b01e40045000004e18206016015017030481480d40c0c0b000c0240240101d48020054456001200810040c5d06000007017420042c1c0c0810401c3c80822079000080c0213083c0c2e50300f014903c1711a07a03046d19841c82072014030307000c0c1010b0890041204041c00e0240614914480010f8200c02e90400c00a044403503440500411605110024104114209450020901100e4105c0b41c56074140e0800c0c2c03029114012101c0c80900901202c1040440c00101480554280390940a032260802e001e010050304000e200b5600c140d160390144103011100e6000e200c2c1841942d403030f07594500c43ea030300b0f0609441d03402100b0350103548100301c10400b00b01a41d8110322070840d044881e640e262981e042412a501a4400d075400103500e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 641992724 1250 641991474 641991499
    0x1050a200708061f0b030c1b010501031b080d09060809030d02030123180c250b0a0606090e0a0b27100e0906061002120d05090106090203040f110d02 65
    0xc0050742031311508200d02c0c2c3d615501d04078040030340c1d000100e105a20300301c10103102103907000b002c483c003070800605506080d035002e6003441c400c2425500300b0781c41900d00f0076507140c000c221080e040104d10058031880c001800030a0300f0820042ca41d41da24452a4104a898408103103248402e008681401c40300728825516941c5413159440120443c5e80e10008104911074490301d5070a102841415215007961109100da0303404840300640c0d40603418400006070b034010082d896408015054421034000c03400043c182c03911a0143e411103401e40c00820900c181d07100c0800481115030349296028003ca14045140606800481c044040340d0b44604190003980b215840e0b80111501803034820940d81d00c110104a54480041d0060b000990380010303540c005500040580c100b08540c00050b401030710498000d4000651038140e1500901e042804003074440e024418403800c24001e01c0d0161417103001c21861402e240e030359200b05890024009140c240c0300608000156a16484a8080c94000d40344800000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 641993974 1250 641992724 641992739
    0x3030d020d050f130305071b0306051314010614150f12100902120105040b120d05071b0e01060f0201020c120712170c09030a060e0303070206070e01050a2007 69
    0x2d00b1200f41c00382c0c201680c0040d036a07100c19800a5100e941646419160003001d440b107032000281200c0058142c1f1090b4400800104c3c03e1003658071581c6002c0b80c401c0544150300d05400c00c00200314240c0250b0b17042403424082206000440280b00c982240d907254030301e8641079030b04218013840503030303030714915020510b0020304051060107880b803041e00c2a007000560300c64403101d0403801030361300a85002c400e40d00184200d0505e50f00c15001d0a2005148501000441854500c9c040000784002c00103003000c11407104010451070500c0081d482001c01003031319402c00708040030626052080804010500c035440704001e00031b60464030f0303038008402681c7c82004030a104400503840302000f154000340b40ea440e003c2ca070b845181d00e1210707004004040d03090394652040701940f80e002280113039814000c002510000550600c41c0c00b14185034440659200d03d45818041d080080080c4042c0a0011018200030303180e07800001c845480d802401e010800c2d41003685244460704034103a400c40e403413094800108050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 641995224 1250 641993974 641993981
    0x10f0918080703030c11070803120a0e0105070914060c060a05071b0f030f08190e0f030d0f15030f0204020706060816090c0c1e110d080301050906090708060f03030d020d 74
    0x300b0b490721058546031b0308a0f403482e0317034201e0f40c815900036405c2130148008152080501c2600b1800c5441c0200d545405041c0c0103084400a5905802181060303400708030403c2100007007135600c0307411915141440c0203038842c2c83c1ca0310001480380c5985656240003503100703070240343c90b034124845801030005085000e241602e01060030400c1540800d035445501c40000d40704125081c41041c501e03c101010070b00c0780210001a00504515003905e0240c4440481c0e480d000700040c00340c8024011022401e40068042c1c2401c0394420a12200e500301850707402c0c40071038110380c82b01194540c1074400613a1014a800d0a4009280f00d4001d810107006074022400c19203500b103502001d90720b00b688100f00c2c0c10078980007660b500d1a010300040859456180380c0d0380380aa1514402c03130b180d005550340184440c0b400009202c02258040403902c01101100500060030720381d02d520b40c0444181d580c1042810601c9020b00103500060a05200e1241300e40842005d48003401515a03442850354159218540d606409018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 641996474 1250 641995224 641995241
    0x81b120a031401050f090a0e2a06030f0103080d090c030516060306150311040504020a0203040e010905060d02060702030c060309100b10090320030717060a05010f091808070303 77
    0x181c1020810001c2d1058020910304980e0010103945042d1960401c0c01703000704c00240712040255981c1411071041206200c4442000f0350048040c095181c5641030440c1d800c2500306032401000b040c0100104c480f00804540d05503900304800507140c942521400024207880d500003043c0350301d030000000400800050810742c03000d005005a01a98039200120b04441140c0305042c00c0d0030051070010000c0b4080d50080002d841c0c2da0043c2482c0c80d40f20004503007a6030010540301e00503800043d040281a400206150151040500601c030740e08200000401020101a01900c0754000048050455408010740c8a400c900644990745070f03e0b281103183e8485460480c81c41c401404c2102250081c602a801140561201d4035203c0c8082d007542c48000d40b8800c003046005041c090070703003400d03017550341000340c1c100410618009295105030707103650506241011700354080140c2414010301043c2a00f070348001c140c0e8a242c00c0003428442c4540750396110748281c0c50281c0034810015403070b424543d158001094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 641997724 1250 641996474 641996477
    0xc0f0a0606052e0c032f0d110a031d1522120b04020d0b04050318010c111c0b0a0e0f0616030b01120e010b0916020703081b120a 56
    0x15001100b296810032040314125405910280ca003c03040854054520480d080c0d000c0d1408107404031054103012480342100c040000700f0000f115104040001c200000c0340c000c007003450a10099040307040e0056990b521074200509000007400e660321920f03020010381050300e90013040780501c0305203102d00500b2070780990032100e10015007016401c0d20811020074001162441281c94541038200d89982c4440000500101d13444011541801c001c03030f6030b07400317071070700840c0070304041e5503100700408145402003296481c0605101c80da04e40c0c030002c112100410711021206880307989400001000426422549460040104130904240b00c0c0c1d41e01300d5400001c100c0030000807910700398008929036a41e64021503029907221020103410300400c0c820b81251001b244103040c2094600c100c0c5110070f0030341c1d05204500781d060b0756500c4483c16501e03200d8038894105800086401146c10807400c02512030031540005890380200281d0b00c500780c04070564001007540440f007598070340110b0101c0907159a0107280c03100d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 641998974 1250 641997724 641997739
    0x2160507060903200307032f0a210309050301110702040c05090913030302041203020a030305010e07050409050907030c1d060a260c060d06050a080f120c0f0a060605 72
    0x20300103005115110070f40341c105180d221094071081806042d02880000e0a03090b02401500200240c1d9001e01200d41c0d86a5113420040c916500c180404102c1c601c00b900e030710a03100c010f82040001c0442013400a0b480c0d18200c2484841c000d03040079140e04519501c2039426629080c452020562440d0180c00346030701c01c580511215081100480700b0380100560395501400101c0480c609006948440508901c2030801608290307961030107841d200d83c586e0042e4050303044200004201a850310509015148020f40b98219080910b4010720b0b80c0168010800303100c1e51900070604010301001090011f603400000d50600c16107607000221035210302042040c10380e038010007060251408078081c00a40b101c2c10500d018070010505480c1c600b807071000d0015043c1c00760201d0030402c0d44500008000c0c0314002d440c045119440c04040c042c14040c1903102915a820107100c8884e151404101585a02115084640c0351850180101d0a2408080014140e4442d140040302040b030341d904030404466088420300d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 642000224 1250 641998974 641998979
    0x306150406140f01050d140a021209011a120106030b0a090c0e090a0b04020d0611130e2208040f30051c03020c01060801050a18031b06020d02160507 65
    0x15a00719240c01e110783e43c80020a02c48007050b500c1240504098081060007280030f0010650855900e00300b6608200015000940b401d9000c0a0b12541900180f880000700308904030185158240881c0c4180d140c80b45840004145c00e08030250410400345401c10241803650070203a05800050024a1080302e48410188000800001c84440644107a2544000e80300c04416075451009035100100101c0c0e0141c014040b5402041551086140b005801c4103076030340c1c03140340210500d082c111641c80481591144400c110041c2c50003043d92030100a031940000d01c03060985032508090081d074111610a08031180d0004080c010101070060010300c0508075290007041c9014880000c5c034a04c8007034031592200d010011080300036a8424203821f51454014140183e400416003550496071182503181e45071000d10825903400e110b034003400068043c002009a00b20381c1d0292031180070007010241041d0101049003841126011140c482c40c4801046607100c00c6019600c02d084080c00042e00d040c810200c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 642001474 1250 642000224 642000239
    0x1030b030a0f02010c14030a030c031107080414010320040f150215090304080109080c010b01081003080d021b06070906030e100b0d1209170c09040b06040b0306150406 73
    0x1a045182c02080c9041080c5140e001901c0742100c0301e4088030801109a005444c0000900151507544510707913000c84d0f0300e80b500b02c0013415141300c0e01c51007044801c10807103100011440c50031501252444008a140c6d44400f41c01600101207865801c40b680203080b8410400c240042c0043c810742c1ca10003100c0d0070385500c500c1c4071070800c4803071b0000320007590108011881000c428034015a12036003000c02c4924003901ca506076070070b48002c0c100840b800500810300d5045004203010b60504e0000070318003504140ba2041034403d02c498240b10241400200091800115582d5012149904010340308400400c821031065540c460084a00720005441c503003010800900c64000d1001164189004200c0405818000700081c60b5800d030580d845182c00813107078001401c03a070b1020a540c0c110f4888800b000d02d807550165000e0b00401100c00c02c0d8000d01c01d140b13003554503d65150b41041e04000e101513030790f0705c01011034000d2403032107003081d41031050208114501140201740104130100752018042d03255039661 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 642002724 1250 642001474 642001483
    0x9111c050609060613150f12020307090312260a0c021204170316060e0d17070503360d03180f0305070b0c0703112a030123040201030b03 60
    0x1c49903441880780c00031501614104010b482c500459040c10010349643d40e03519420420b601107103d02103240c5030569868a13030480c0b01109100321240c0705514510b0000d1000348080c901e070000030030a01d25607017041d009078410081c5404208901086c200703407807260080042030b054111200011181000c8030003517028404100c0c141e508004003610b40c01c050801c02510a070240701c460300b170400d200034082d10409052100c4c2617185a40180e0380022841000e89503141004d210348070710000d001d841072851242140c40005541d0190785450900c1d12521054040500d0501e02d491401c0e12450204001c25520085800304216254003002c41303801003400c00301641505e01c0d0400403090707901c1d00f0310418046400c05080e8042c003403107072a1031440c1c03002c2c4e0b68030780844810586083c80c0303029000c1040400c0682155a2020000a4a00070400c40428041c0c000150360202d01c3c8a00c0b620a000c2d010715036407008d41054414814020034034004280110008003101c01c100d80a074000781c20300c1c1d00342036035060110b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 642003974 1250 642002724 642002731
    0x150103030315080a050c270c03070210020f21070203180a0b19262a03090a1a090309040f0b0a032613061d0409080309060f0c2209111c05 60
    0x210407c1181d03484180c0700c00340f60002050749065000f02c4001900c0301c03910340300800c0001d00c15100151110590110141e00580110318000c4050b140d1090120f800e80020a40300d80c00118038041c840c0844000203c0c10421056011641cce40302e020a21800c0f1060304e119440e0550981e82c2e0b035002129540d9064159151107132910822400c0c0d900209000d400203804107070600c8030302d000401c00f000b08180d50b50f00d036070300864494015030030614050042100d00c2c2c116007000e04d8100740440e0241040030300c140d143e120310f140c0544100d5407001070341c2c4418a190000c585010780200341c2d0040c00d681c1d04146e5201ca800701e0300c81d00380c20416101250281d200c541901e0311840d030440f4400c150383c10300d1000d642d00044451103110042c00c4c0300e1443c3c400d9907a0701a03900e40c0c511030003a454880c1050207074a480c0032000340641d920f42841030104030505a2075000d8440c2c3c1c880c8240040d011040c907480ca2450b111f001c0d0000c2400c14102422002c900d58010020070b104461a10b5540e1a2208071123800200d59068 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 642005224 1250 642003974 642004039
    0x10b150a18031415060f0621040c0603060b120a0903230c060a0c05040e040807020604030f03110d0e0f130c091a030103050a020f031e061602150103030315080a050c 72
    0xc46d559090800e403001e080e100a1081c140d0001d01c601a45401061030102c7e0100d6440100505c140003069240c050b800080c2001d41515081c4940d02e2115450503c2c000c0c100e15201342d035078465200f4184a180c1c0704030140d03070b45040c1d680d45c021041840401c0380d01600d40000e09210f1000811085d034642d00c14190032411540d1118289803c0c03103040b0b54100d00141003070b10140410311607500036a807818000c00046118100c030b2142d076045450083c06410f04003c640c030180e0000920071070119042000e071502036500302d806104174004440000c5a00001d000e1012809180019984020f90449600360070340b40807904d00031b01c00307150b48404111484240401801a04030040100040c10039110800b90080018261817450643c1c480c41c6108040760b1614008030f5102105002c130307182403ca515282030103148040d0804110303059110150b00c40c184401410542d03500d8842000d041c614a0f038201070031402082d9020740d001400d003966214151410640b007000c03103050102c3c0c0d48032031001c00651040c13103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 642006474 1250 642005224 642005239
    0x51e160f121103071e05010914090105130e010e070806060613051003020408030d090209060604050d08090607050609030d0609020405030a060c091d0103050c03010b150a1803141506 79
    0xda07502c410020444410858062090f030342d01140b10030304510700c0e03142003c400050800c91494400010130401c5d06502c003051f2082ca1504104c030075200d048010307042d5482034540c14501e04082e14240018000180380322469403901e2040080c007000070130300c1c00c21140440100c903540e445d180e00b007041c20b00c42c0e0720f1842c00c00c01c04013a0401450410000300b4858403554103005003880d80da9480c850941c2c0c80307003200c0c0c1040c541e6408140304505c4c0469480c1e03008007082c5c8086082c941801d02042209080d850f01801000001c152180c06641e2101114412a40312040d40d1a604005420a40e1781d08088150000790b81894004520b0b90198030907a0304483c1d0040c011b12143c05552a680001e2184004032820402d03c00750101700c0341808064500d0303880c0d4500360718840c1c1d0f155062030303410811b0281d03c0c00d201c0d034100004425250780d01c0040200d4992030780c039603999a0f080018142c131040d0b8141240d149001c0e001d8000030500031040b44044c140541da1050341d0b80d8024059040343d16080480d4812391007240c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 642007724 1250 642006474 642006509
    0x20c01021c0e030d0b0312031608070906050f0f040803040b07050c040506010e100306030803092104050906011206150302030403081501120c05090a1202030f0721051e160f 75
    0x541c0d40000c80c06403005130a446a01c008403c00d40590740c0108c2d95480385503009c1886881e4680d001592070351000c0360f480d10600003410402d00900c03620034141041804d9101042464146c0c680800b181c004241a1048039551680c4264000c4a9048400c043c0e502e8004d00c4040011070415000b44d0340304800c16520740300d20000d08c0007004841d041d50345200c4201903559a0200c00900751100031401000024000c182800071459000307121051030072003010251062008005c80c0d140c0d09540340d0050400d00f4018002000c541d05c400040c00d03281c0c04200400124100c0d001c20541590096028a01a54488041e0340d2941c00c40d0003400f0401c84118009200f820088015448903480700455030581d18100c0e1910f4034030b000196040c0f18640280c60264540c000300e6045140801444440e00880d00150080b03519140e00d00c4081101c002203a041815070307962200c1002001d04c2005009050001e01480c400841c0070030723550f19074050aa0080c42c055615011801c1800101c1c05801c030344084040440010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642008974 1250 642007724 642007747
    0x109110a081302040c110c0103060f0512030d05070f1e121a0307080f0f060106051602040f15030611121f03020a2304270203030904020c01021c0e03 65
    0x110001c0004080c10240c08082c8010b03640e42c0540b2503940c02c60343e40c0f4110381c01080445410101043c1e00d0b0b505240c9040c2c1c007005000c101c005658215a01214036507200d485554009045214199503c01000c0c0780c40100401c0b07940101e002c884144a5540e800c101c00700d0070040c4200c41085042450100300c0c030321401c0e020700005070000c00d42100c064490b000d20900703000100f4584034031504401000e420503c41c25149c81410484400d401c24103800a2007254503150024015124950340b4110004e401c018200541d1203a800c80705c40b80302241c80c100001446284440c440e05001d0004844250400c00b00140d040740389802d480400c0b4a01250603a00c0e2100b1014184c1d03402601540c0340c1d44c05220b000003001d8ad403102c401d1030051011051710004020f03503841d43e5202640e810300840c410392030040f0303140c0900b0203180b4600901c2c4841c0030310b0742143d1140c00040c1c03640c0960803030369911900005010001030340640107007500d83c0302c0e240f00131a001210f012085c1030311f5045144003039661040c010300780760713a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 642010224 1250 642008974 642008987
    0x120f030a0e101247101d0114040b090a060302040b0a030e070305060910050f04320607050903010506030102070206070b0c0435070b0f0a0509030a0b09060109110a 71
    0x160583c3d6407408084100c0f1001c40400602d030408160b00c00510544503018030388604c1203c1c810200d0340031248500e41e041c080e100c41452280b080118046d12000d440d00d03402898442c161854030422291181e42c2e84c0c0b00c0e0311182d400100380c940035030440e120016856009000351020b6030740350b440c2c00b800d0440c0400110000c203210500e50901e0f1140c00e02c0040411424442c09001c0ea2200340a05400d401c003040c10016194050070035200c002c0880104408a454800c01c50803010550b8080850701000845055880c0c080c0c5484c05850b000d03100034842007a40110041140d0701d020f40c02440642d640000f050308030b000300b06019401840c1007068400041041d0803c55001d0282c13a011800c00341c40e0690011034079206e02000a51801d0b0025111a61103e40e0f01d118100304188003d0030000c2c02d1001c0080140034604054009a0340410058202030180e01a6028241c000e021114810700d01d040c920005070007590000c0c0329000315000030403114801d000d6526901a4050520724020303523500200d891 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 642011474 1250 642010224 642010241
    0xe06070e0301020d02030a0203060a0f0b0a030c020a06050906090f19060c0203070c03030309300503070c02031510080601080c1009120510180f0b06120f030a0e1012 72
    0x5550811034014054554170240d800b5051101d001a140e01d0501c0a00a00000035048940c41140b0000200300c6220048200ea102ca40780b46000308001c2031300038040e40781000803000240311030309110802000c941c000811920030000388086507041082071604a4561540e06403d1080d049189260008103150b40c100341d42100c1144100c0b40342075099190342c0710300c030516082100042d40341c892900600c0600f0361805c60301c11707504440c1e40c0d02040580c034550f0400a180c040f1703010301070007100141c8420b0255041c41c0c00b084d0007400f6a10755480842c01c5030b060810407540710750042010007010984403000213105058a040400600c0305020100c10005602c030b04441c50400c2101080c40400e80c00c1540c0c5005034140d00c900d0007040030300c4a80540c001500c0c113844500f03100c482d000c440b8030041500900c07800c28841e0003c22501d129282c100c007040f843d140000401030a41302d51402080303e50030000060003a50040c0e40e41a41014188040041c4460401d40d59800180c2064005014154a82c4019413 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 642012724 1250 642011474 642011479
    0x141b09010e07210603030e3715030b04050a15090e1e03070b0c03070c140f120307081e0403030b03101805060f010e070503221211010e06070e 62
    0x2030780f060f00c078401202410140e603d8034416100c003004c10403d60001010010a01c0848403a040c50441da00605210140c0d45182d05040203190b0558814151060100c40074000340802e40030385159042000e40541107105050780110700d0900080c5210419215082030007070300b80c1610381158901102c40d00509800b2070070040c130740240d0744102d2401b040000c5801080507403401035a02c2e5a0542040b50101a009049501c1c140080080001700d0364000c4e40001881d511051a403403e610380384600303141118034241c000c543e102c2c1070103078024a131045014611801195a0311015640d80307008000c0d001448071003018120a44001007000207000e5000040031072000b074203c460035a4a51710300800e58011240307480c0e4904051861605102c018811240d11240d843c1d0000441c4d403406084000d0080010714401c1000004400f00d29035074051031481400d14100c5011401400e280d05000d20000c1404610a000c40d03221245160076071010702514841d1800b42d0013a00c941c0e62550002c0d100440b40204095 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 642013974 1250 642012724 642012737
    0x5180904112812021e0112020a05130605090a0b070209041112060c0d0b041118010c060e06010609080105090c0114040518150123090a030609141b09010e07 68
    0x1010704002c4050360090a805900c88400c1e043c80c0180400f45101c031005401c8440340c200003401998004c030558402e0409501c0c01a90f4006140c0c0449580c0241c010b107051030f000e101e400080c2c00c1c0e44a03000d0200d010007101c50809180c0d49030800d90701440360f104002d41200441c000940443c03030190101004000107001d5801c0c0c4015441c80a040c01400c9034151000e0001240c400b1814100303125220300c1060640701080664680d2103001068017421580d0703a000c00403000500d6059200f03020b02090f050740a00180207400e1030282154840200b4051600083c400300c80000d21004140a280c0c000d4100b480907114010b004801150803403004400c00e100340004201c0010140c984090240e000c0400d0000c11b21141802e0381a0b02d007087d03003948030b82e04008035a104886105403ea108107011648120250358510007a40402e0200500342d10180ca00d44c034012980c4107120400e00045804030000c001e43c3c1da01c503400f04400c140700c01c0300d100552f004140480140302c00032000b90f0341078111000f400d149 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 642015224 1250 642013974 642014029
    0x311040221040308090f0109050312100e0106050c0d0e0f0f0402040b0f09180c04060302030a060b070302010e0607050c15040501090c061106090703240603060c0518090411 75
    0x70507901e401a0b40480010340602c0c00c01c8010302c0203121070f801500c5590000d0005500b66210f4556038090740841211600c0e012001c035070b1082c408c65426004020820251207950b0303440c1c4028116800030300b401a0345014118210100c0c610404a550790598000e000c1c0500d40c0010040c01920301208035142d8000d42d0130040443e1071000840649a1302410081c1c1d03d070748501c0d040c2441401d101c0e483c20411400110b00c00e0080c62081e44040d6070a554191070010703101daa5003458100030380580d91040001c01e00002c1d0f503c044c15419040210318900010445000d0f842d940e030111030f9489500c0c10020150419204250010303011035840707030018010000800d44190f1a15103855000da141d0011000c070390035041c1a00801c5003403125a134040081c4014212003031940d00d03011844044140d1003920942c0c2100072410000b00e59010601464125204000701c003030407174000c0c24580c001d403203811000c0c0c000904440507151080041e8400d550001300c10826040310001d00046014503a0402485091074694 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 642016474 1250 642015224 642015277
    0x10031509060216020a1a03040f061401060c030320040513060b03010b03010317030412140c10050a1a150a0c120f08130f03080a020d1509060803030103110402 69
    0x20305040d0383c008101034800d040d00d10400140ca60603500031003480500000c40c412016004003a258002e8106414a41c80340e10f03450a100188008880e08040405040000ca0102c2d803104070001014070985003000804803030740c0032444840ca00b841034404100e00300710030f1100d8200000d91000d0340c4405e4002052460300c543e01d884268100340c10040c0c04000100041082c0a03048e02c1002810b007900c01c01031316500f40741d207d1415a602c0100c024083c000940031074001e00d03196500315a20030a100781540d0096540711911406082c05a846070491070600c6042e600b4018010426030088a000708505d0310610400510055034010700060003c1c440300011000200d0598414480000c07142e0341e8000ca9214040300103004098041c000d101490304100c0400000380c000d038042801c0a40600345909107a0790180350034080d105544849002500785804400080041302c040415180784036424413001d900e6032000c41d0b0360300092001506200c04196510f8050404d0381c0101411800c420400510500d1640f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 642017724 1250 642016474 642016477
    0xb0a020f060c07031b03050f090f04090506090c010e18070306031a060315040b06040f0e01021809060303130b210910060b1305040e0705030a2405100315090602 70
    0x502e1021803000091240401d5445140001d54140b911070342e4000302502e0300c00404074003130740d12182e03460300000a50f6106503030b13038144c2001001802081480150b0151030801d44071201654001401d100320030905101d580981541c803400c18018040b52108602c0c2e20011155080c041d2036142450303038a090120120304851030291400d102c0040c80905401c082d0f0506203004000e1f0b1300090b1031f039105000d000c0007c3c040e0000c1070700803004507800706811035007664a10040a403201454101d610000c1d1a80c0c04548264240841110840711913031550b0b00c0b4400e045d12489440c00d41c11156000340c105005001e80b041c09440b03c8502c0146040224a500500e020291002d07500111030364014454403032443d10600822001d0014195210b0034031220032030000410506006892290ba2104d140c199200d8003000014000d25004003150ac0580050405000c401500405a03840f400c074414050480c014501503907005035031111000720700d90303d5600d860404842440c0b582d0758540d100c80348900450b00b40d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 642018974 1250 642017724 642017731
    0x708090a05030304080d0f0206071b1b151103030f010621020304060203330f130c09081504020102070323010f0509010c0813020103020318030301030305090120070b0a020f06 76
    0x80080c000c4130721b80c80d000b80c901307100540d45504561010082040180d4440c0a10684c0142c0150000c00360416180035407002041c0c140600c00c850100800291140c42c0389140d00c080902501c0d030701d12004080803c15220300c4121070314140401002c0c010480c0e51b00c01d1400c00d0304c0c13a0510400c403082032100c0c4100c4d4180e0f84250b809540b4036401009200181c80708250910503801345202c56800380707500c0b034011140980e500b6145441a207100060300300c3e98440e4808602d13018400041000500d00e442c0c800b80030100540221043c91140300d0280c102480301d06603050046030160000c20040389550303102c4078030041002140e5000e200702010b02c15600024000c0c29400c400c5d00f00046200c0c64091101c030300b11261221480b08102040c014850000c1d2050b10303900c405c0d9020710780542e99586109400d21001c0c882e910300c541c03600c0300100000c245076014003d4100050b09a944945892400c14020803d95150024048503002940c0802c60300840d000207028094850043e1880f0117041d80c4000c1c142b9104a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 642020224 1250 642018974 642018989
    0x305310b070201020306090903090907121e0c1412040f0609021e10020d0509090c0909070306261504020109081204030605010e090706030b0415230a0b0708090a05030304 74
    0x100c18846c081c0340841e036150784452003100031810044020001028100060410320601c18000a940c240c2141a04003d8642e0565401510003520301e0b44840b004211048221000442c00c00b400480c004803402214a00500300e9812001034980d5100e07049802c100c140304484581d0b403800700c4401a00c81d020000b80388540101d40a00c0d101e05074051040c44082100e0903001c5410421050b0b40058100c025508124810b0f5075103200d59982c040c2c01c05191058140c0182d00405030410444003540c59001071090700d40145211405560700816800c00603a04003000d0003d0300100c015802180c00c41041c154801d00500d004a11259540009418410b03189411080032000180600c00e0101900404d8014400048004142e28003546065100e07489030080508058884203c1d6401d507995402201201d0904540381c1d04550b900c82c41c0800c4c02074482c001451805500744001c001d494070300400030031102032031406403900b04150341d03951250344500748040c0d100c40014404240742e14200054000ba0105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 642021474 1250 642020224 642020227
    0x12180d110102010f0b0a0e102706151b11041a03011802030d05070501090618110301060308030c07020a0b07050c011205010b07030c05011d1c0305310b07020102 70
    0x280d40024251130414250b00c05540c10003400d02a6500c541c1380b050100d4075009042030307464a9801808040402c2540a00303400f2507003800b0f2054009200301289a4407590746d00400c0400d80da0000b0f00815010108080e000c641c80c0020f1007950608010100517482c8103000728403036554031a002070102e402d0349500160b03908010850151a050034810400410030f00074080d19111400d0340080e41d140141c0003e0f004205000c2070342400c00801750040040980e00520620550204003921051104060313001d96000c10040080d0003541010310400c0d05807a0442080c1c1d10710b03659400103488580c0004012600006070310742c0000e5904620003e0103c45108001a151032140540014000c0c00700140c0311100740e01c1c20004120003252401240e003a00d0b4141401c0404013585c0c1003903401813001400310b041641402e425480050380205010400c2c464a019561100d41100c40c114116282241d024940c030350ba5454210040d0212008103070b4502a2000c00212000790340c1d101100603400f941d0400c0503030340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 642022724 1250 642021474 642021503
    0x20904091b0509060d02060c1c021b0103020304050601091806050114040b03070f0e040f0212070e09010c020c0f04020c03040b03010e060405090a0303051f0303111504020312180d 78
    0x764080d2010040a0403120740c0c402e414160001116010103844c000d108a0f000144206c4810f014806041521610f0324600300c0c0510107413010391a80c103072002141d82400424403171012580039200780e03402103400200030141070f828071008000030100240725840004549075880c0002c0e00b1401018040e00e4000040504000140b0038001a2060032100a01c2504800350a01c1550ba08038040c3c000ca0b407180246030004e89850070204030125180034044d42252164450500d004c200150000843c0c916041368041603542450603801c0b1004088030038016081f421002c81eaa1030101003460259100074801803426400c000319920755070059100e1483c1c154080010040c24a02c03c401c958000b41c151828046481c0211107282c03a421902c0c4018245503944001c90b00c0300441c1d81070302800c51321400c4034224603038403410042e000034030702120030724a48035080d8280b035003ea92258450107a40d000d030081c00000ca0001c00b44e85180c1000d45140100c80040e10028403036600d500c0c07100a85402944050742c000e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 642023974 1250 642022724 642022763
    0xc0303330e0604020405060a0e150c010c020607020613022215080d080708070c05070e0901090b060d082b09060c0810030201050f0705030d24060206040b0106030506010302090409 78
    0x68010180b51240c0d20611042010b502c820003240e0b5041003a20f00f46c405a145280007960054000d02c0302c2c240c5034800b1440c152000c40560010200184940880d01d042d0b43e58501240d8961084070610500543c3c25034003c018140007412003543d001d0716040aa0008030b401e5444102d51601503070003420740f400202045645028410049440c1d05843e0600740f52800c040098030f1407001419502c10003407810303203407014000b05101540c040e2000280001d400e0601c003803400d0291000300d5040d030b121008180464000e00d04404002145a8030000180c200412004000d030000074880600d40714506082040d24502440d00c640800280b150100044070340c284003000703084103001400c00507140d013840070500c0581e8008040e07503a50154058801c1d42d51b4458541241140034031001038804505001034100b0317070461100021503064100743c95002203599100c04982d40d130030a41d0040e00b4000310100500903684241c010355881401814054070f00203100c008a4211911904252401d0394800748550424 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 642025224 1250 642023974 642023999
    0x902100305041509030512070509040509060106030f1b0c05071a0d05070f09090b0607150504050c0102060f07081005100207030501053601090f050718020304030c030333 74
    0x1003c0000400c0a1a615940604588507a124002d0400009000070380c0c0b0604c901d086964002e0090828051404c03e0303c0750a80e030b0701081c000c0b9404a4102880507410450911543d41c41e64490945c030170356007400181c261414008043c05440900408202003800381c0721003104143e46540742d10040c0c0c5c8a644400403411a08007401680c00c1100680c50200d046501034a000141c8100130030001d200340b5861300141c014410b07140000e04c03070f05011009408208450780304134410307070040041c1e81d0314504481c012a1500f4040351203240811807600460400c40c8140c001550003407603144520310b85521343c2c0016034015401d19503100164003540302403041060a02a90381c00800c80541100300007007060301c900d40300507150800c00107880e000d40440407005094000c0b0b4006508501d07404140d039292300700780c1c2e243d08050040d415414460031010069103210b10840e0b103e0f81e01f61361a141c0ca0049507030110081d12101600c218940500700c079010780701c5050a2013400810710500b100d45501d10348560b850341d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 642026474 1250 642025224 642025253
    0x3040807121b020918010c050403060b0f01082e080607030c030615140d05101a120f092e050105060903030f0a02100f2903070b0d090210030504 63
    0x4200c00b10440c03200792031840000c0d40d041a4101c0e0090b62555424101c01000c1405880a210740d608040441e40410307040320042080c1c900030341c001d00000c40b9400920601e00182c800c100d0018821000041c0c10060100854000200310001c20003160211400b05030120400d4101d40320070303002901482800f507054490b5070040c0e03609007028030000e8588910180003596010b905400c3c0700310210203403228650501242c5600c050780108000e54100408020910301c1c40f801001c1300401d2a103049211080504181d520b0241108450300042d601c500843e8071410014040151310f10850305d8850700946562802070349054071007020740d810161007000e0390594070103a02c49805114200000c40058130b0110842d03070f011007120b8000340d880e00740e04001c03840e05480c500300810091034801c2c44a0380e0306240d0440c01411402c0300c007001c0c518110490b0105680d007030082450f45684461300c100100c1110401414042c041d002c1c0000d000d8096030041650001130001103400a44e81e601000100b140b48201c0148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 642027724 1250 642026474 642026477
    0x4050a0e030901030b030c1206160306141e04141b09060706021e040f0e0916090c030209120618030a0c021e03100b040605040e0a0b0406060b0304080712 67
    0x6281140c01540c0342c0c400d00c05454101501c0303500025044d1020080807503071280140c00c44c811410000909915444151230480603a2614504c00401c28440d00648090740c030024400c09109006200704070100d0719001c0c00201144800f0416025680d541c400c0ca09085450a4901c1e42842c0c907014401c00b0804400014400f900140006600f5440b018103441fa160340c007007001692803c0443d04107007201420750943c030b010440050302003070440701070704040f045841050380ea11090700c81141840d190f41d82c8003900a02d1240e540710030003204c0d4098118000d1000316003001803801c80180c01246050f8a90504140d03c0c0c1c0c04402400140d19010504e441c0c1e1811440103582425040301d0300402c0c01102c0c644c040e1040381d005030b501c2208035082d159032181800090880790404400300a44020340640c0c10644d10941c685040040d0f203003480d0141403401482c40b0040d100d003803807680d600d184140000d801568169a0b503500400c4800030480110f000d0b0380680d071404d44810702860541c6203141140b12040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 642028974 1250 642027724 642027731
    0xc0106050a08070b040b220306020d0f0504020607020118080a140d09050d140709022107090602100f020d0603050601031e0804050405070c1e031209050319020a061a04050a 75
    0x1c440132002054406035101c2c3c80015580f80701040c03581513106401c0c0345128040250103000003c00c1000d40c0203110900d0000c1c13041c00b0030350859180d0402c490341241d010350080010405240198070071000311220002c000c802c01d10030380e25190714500d400f00407041110a1240310004900c110410000c0c0c41004080346081080a400d2002188260880b80c1004180040102601e1820402484800e0103450594421502d552421040c0090005041d00e0006001d40c0c61003c201551710070311030039080d510745400602c84021054a00d0004000304c0c4000040039609108034544240c00c0c0c012080210301402c0104286d50450038179004642d4a4421400c032440303260350620005403540251021200100d8001840b5915900c06407260031351004002d0041078252245805a665202080525402580c85400d03c2c84000c00d294100d80c0d001602500039441440f8034a11088407041140d2060780301d01c1651a000440e64404d03041c3d5881d05506031b2021800790030318007181054801d16070300405103c42403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 642030224 1250 642028974 642028979
    0x801062d06020a24150e06100e06091207060825140c0c0a080d02100212041b0e04030509040c020d0e04050c090a0306021b032118030c0106050a0807 65
    0x3950b12504203100808006000352402c0c013207421100c80d983e0b40d240c0740400303100070070070001034101e054403a0095007a0301c800380c0003040c12801d0034459030050090580b2904a00b40c549010401aa08954905a4800c40921400708011401d20408004044c2da8a4409031030802c001301d2160710380603440070000e00701c0d888100b03259a544407034000030502c170990030700341d1342c10881c03240d14108140c40b00c46d19000000c0d048001110f00300014685010103065082d0344600c40d0160040d4261700c20445142e0545603400042004034141120040e01103106403200301e901c5654400800285c00201d80036404500081910b8103e41041c6c044c40c1b011080905c09060902203480d0050103694040d8001c5010307980c0c4d0030018001c04240b40031a03107400360003022511620b581c2c1c94498043d500100c0b503102045403101c001c000ca844004265940b28243c3c2c10780e00e8010782c4041e15188182d0006010340300c0c000844146503944101400203256145241001142c45402c1c8014001b07a8011a40300749141d50140008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 642031474 1250 642030224 642030227
    0x90617010b01021b1005090603040f02040c0e1f020319020d17010b1207050c0327011b060e0102090405010611070b0c072c100317070c0302060c070801062d06 69
    0x5013904010216100c5c22a0150310310100e4541c010044103035040640002440140489480c50714042c80c421141400b0104540504a507900c0c0504909904010041500c92010f0b100680d4a8128005841200c0c1010400300c0c00060100540c1c1c140d002507005420080d101940c003c400d1103515210b40a00c4482c1e503d0001404220710130f181310030010681da500400c20041c840d50444020304884400c0b01d48691078105801042c006442c83c419064a420f258860705c0c0d40240100303900f80b0250310513650480751701e81f502c5016000d91141049503540c04c008a0342280d4071441014040d00c456078a040c20ba4a106568600e84201c3d40c020718904002840b40450ba07245c0094035905941c0d03540c10b00303161034591340041060107007079000d035031202c814400400c9680d800360303050001101d0082400c80d102c017450f00300c914682d01c110000030b41401a404810310260900100600c1001c40c1c070021104030070b944000307090858110390003800d0703641000c2000c2c4481d960003000380615002c03100c061340d0a45140010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 642032724 1250 642031474 642031513
    0x130c05031506090601020a0803070504060207050d050c190b0301091a010809031b10050f2a030103031b0510050601020d0503010807032306010b13080f100f0204090617010b0102 77
    0x495440f0300c000c480000e030f86910a00c442c070300b6030b64404503a80d224100b401c8042c20b00d800c10b000d000010301c10035800080c5458500c0003850059001009000c00d4903484049c85a804a1044100400c20028000182e100f10100045008050491700021305088803550f41c0e24007550141d0712410040c0d5042400181000813080324160040c0403001c0c40c0180080d19a00d007010784030041c40d0ba01c0c9180c001003080f210a1912203900c01c40105142c1c11781906014090780c0038a1450301381009265051006100080c001c80181c00d41148c04403500f01d40014070b1b5540392400341c8001c1508413880d114003d02070156010000028030180b00d00304581103604143c00c0942d04c6030544806080f861265140400903181000311881c0c0b10039050540d4815a110104c419007640079010417202800e51400c000780401c00031030400325201110000d007440300d82c100c0d10b081c0a0a41452460b0207160308200000e03461a1034420704004000340d02c05200d011a80790b411508681c1041011030642d046005045020454000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 642033974 1250 642032724 642032731
    0x30614091602011116031b08040b090f040e07080c0f0d0f03050903031602010206012709020415060905090108030304032709090f050f07210515130c050315 68
    0x2040c540700c441040404a0143c0003480308842c2040c4000f60b0001801c080c240100d08040c0241c48403503518400c0001400822040704016243d442c0c244018420400314000514086c800244030981b80302e05400018200c1303224600c211382c103920074081000070312010300155038846011250303040100071040c0840c8400d01100d500800ca090464514010180524240c800351840941181e4544880c800801c01e07407a0710200680c058800c01c4000074807400412000480d401c6840600c0b42a400c8071f11981c0050825414101c1c0d00a44a11401c50820780c1902305000520456445982d001d1070403050041611301a00308203c180c00c20010000070a801007000210250303103440c0d000503142201c20f060668070b0150014128182054082c8040c084202c20074054503000c0d000352103996600030046a0f480b8003d101d01c540740b13103002d0101e08400d49414218064030b405081519510b2a80c05000c00051804440c1840c0e401c0b0641a50710600440200d2500070701829401032280d586440e030404442c20004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 642035224 1250 642033974 642033991
    0xa17030705120a020d1806050a0b06090d030905280f03050c060f092e0201062d03060e01020705120403050c090402041d0c040e060c0706020c120406090603061409 71
    0x550128144071100d40c103c1d48442481217040059455607119009184401082030320403505000101f080c0303001910400b403a40c5030051495141908000612840e155018070a4042c41104500028161555110062100300c40d1900402040180f200600018004d802c0042402000e0000740002100015142d030703c0300d021282a42c590440000b50715140c45a135850360b4200c050000907401c0b5068021500b9000009002c5c074a44010411400324200d6400e0b21440302201c0d82d800d001c4541b402c811400040480e050901005055102e8840409840754080b561001303a50000d1440c050240a000052800c46c800d6903142c540b51039602c9040d07840c0c12420f1454406c10404022a04541da90707444429040e41c140c840d00d0755181400c800075150107001039068080e50601581c40c0071000301251462040e008060500c1c24800903442d42c50094100361000319482c81100080201e910a040c050030042c074040d0354158039941440303001020ba480580c010a0041c451381300c2d0003a603030b07503054032280e001550303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 642036474 1250 642035224 642035257
    0xc030417070b041e05010512041415090c090115020601060503100e070201060f090b0307090c090e01080c030d08090a1b120b09191e0c03140a17030705 66
    0x49546540c200140c42e80310182070100010001114150082c40385001104d2400070340820b80d503170b80152011300c660300c042c4c51200030705000100010141049140c00e4088082160800b000b0301c3c2c040310080009442ca22081d40c414000c02440345000c11195000d003456090800d0014004080690b545506000d48000e110000c0000746c0064200031800000308103001d00c812460030b200f00064000d140d14040c0701401e03404528045010415070081201062014004001451820003150000c282c000c2420381001580c00340001c42008001a0340d0181803a000030b03000c2d00d0b8402c6e00301441d00c80215034a409100910013004000c00004c02d2001003d80c024906c2e001d140c400c070f940000c100c500c50300b03da0000c0380ca09054006004248869910a0368050100c031824103250807501407845c020f82000700f0050401e00042c00111214500890709480341c07500418207512507441ca0100c0341101500807050340110000c40611034140e107800b841111103203a80b440c0d801c10074002803041c8a040d02c00c02c0281c14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 642037724 1250 642036474 642036509
    0x6040e040206071208151c0305091f05041401020c0f010c060e1002040519151d06180f0d0b01092c150c180d0f02090901020a11030c0304 60
    0x75107a00f11030546500c104051414040702c2409089072006071165165032884007140c84860030181301807a61085480300100300213149035004c5031140e02044405400c00611107180300319582c64810303500f010991784c96158880b41045d925800003c0990302c1c603030444d48900000e4407951130701c108920014000b0700c0c09801542d503a040c200041e00b50799091003228482c03c000784400003d998050400d13640c01f10b6240c1841c901c2115070344005038160140b001003525040c0301e034030514050050500142400c015100d148183d0a000403004d400c000c1d0202d001ea07640c44404007144c509011000d03809107044514103000d00a0340c032003800008050060040140e5a130f0030300000ca2602c102c0c010303100b100e4113035039442c8a030110040d16158030b400380d03403034000303040c000041221a00c0500c1170b9500c13044031380000c81319000c0d5001000b03614280c0301015038030b0b02c483c40f84a03805030301c0d50207403a0b102717606110001d03030346090104005000e0100c0c1c1042c00c0701c641013403101806042d80070044908440ca1100e10f10700010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 642038974 1250 642037724 642037729
    0x70e300d21290d05160f0608090706050a09090507050418020c06071b02030a0503090a300303060305010c17010b09010c110a0b070308010609050405011206200f090a1406040e0402 78
    0x400103500545a07229140f82e0700540c85602091200f46c910303241403060003039581e10066a1201d029510f41c03e07660802e450510074144900302a10012009142c01c0007020baa889103401194400d880000c005100014184254888a00c0d42541060030042c214905030031035441d2030321400013034810030820844a446401082107600c00785185500141510074a040c0e80c900960740c0e038007601c0b0700360240740d0368040041c01c041030300c0b000e0b07600341d60a894181440305e001003080d110426511044041c15a24000840429006d00c0f49520744055074590482c0030840740404103030f8200507807201a00c402c080207820110399109440e00b200641c8410100d0810400f28001103810019070003003040b29801260740800d2503446400309040f0b1b94035440c2c0c3c00465444500340030a54a090240c55000080821000f0000f2110350040e0825510403a48941e08030021318040d900f0391010519640701100802c50020074a050381c41d0300c004044090f05401800324143c0425428002e03480b40e18451035070400011f0564 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 642040224 1250 642038974 642038989
    0x3081e250305090a0b120f0402090c070f0804080a020a0f0b07060f06030b27060105090403050333090604150b030414030703080a05070e300d2129 64
    0x1044010103443d04d03107407210010344854001084658000320354802060f041301034600c5140c012600507054204540e43c00d80d00e4a043d1740040022149030014620306804501d681003d0700c09806004081c0000001c140100400c2d00c555800101c29540d14400c20404218500225010103500c000d012488620381443d0300c008003c160f001030301480e40a07003040303c44440400030440489070301142d13138813034140140800c1d9512424001c540e0080c01d880c01180110340100080c41d0700542460307180c24040c0c2030400b10700701d0134403c64018400403540c040520880c5080e402803039202400f61010800c1c500b0b40c44e00c41c803040c4842c0c8030b44918403100102060a000722050784070491a440811680d07281c44a250007015183d088a01002c0d043c5408041207803d8030600301c030707494000000c202260818020025500903100c82d60401450300803000d402d20425001e000303112405500d0349801c01e00c9110304c1259550010641c04038915649040781d0000c03c0d450392810400c09540134040e079020305281c4800b15244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 642041474 1250 642040224 642040237
    0x30c290115140408070e09010203330d0b01060311130522062907170c010e07080318061c09020f04020c070f050d02090a0509031303081e250305 63
    0x7182c00034010a000800042c0b25084032802102c000956850308582402c03400155401c4514055141034410018410f0b60500041c0561442c0d0000310b1200800050345800795070021240c24120500400003d60540700354003050000050071480c129111180106e402081d0280700d200b008018141410603108030091214131000e030004104080d1159020440d6004850702c000c500003072801089411002034050300c003895484180144071030301e1103540c3c084a801560f0000510340d0703039480c80c0c1800780f01009032070020b180b603001859442c44035041e003190b18100403155034002c8004100c400036002c102100403154580201d0001804646403000490510b0f00c0d5603415070060020488880c1010045030040483d60890319000c1e01c40c1d51601405009101d9090181d40017024a0021303124401a070401c0354060000ea00f628580914020301442d204c1850308140d501c1038001c02c01203043c904ac00c02c4042a2004a07030360303030f04107a44640e1042c0c1c10001030748810789204002094504140c011010342d0b84 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 642042724 1250 642041474 642041507
    0xc06071a01080309040c030e2d03220603091a0403120623040c17060301111201060305070903020d11040608030406030212060405043507030c290115 65
    0x1020350b90b0702a4180d07650850702c5143c5c0b08500e00303544000d07098003a120341d10300c00b0000c0014141500b078100381049400030b0440c032024402104482c1c03035200da0080c0010f04419a503d1090f0f0f12100d07080c908214202c1140d00450b0a243c0340084140c00700748059440781d1070041c1401c0b8030020341c1c1e0740e00d01150700704903a50480201505210020541c0d145d640e218902c3d400c014806030207003401403020001a10b240c01400c80c0414503080c40030300d04046044109511010280c00401c9a50089441e55031951001c4c45001a02c0030800c0180021641800b0b160f0300205a40740081001d8256000240100803d4100078140e0003030640f055055101c640050009002c82ca054a40703881e075500000d4060342c0300b480303100d8030203582c000004e4043c030b0180301e024015500a0425070600340090034030304040401c503034014280003103060b806e180384058000030280c241c46592510b03900c040503c0c08506024142d03280c210540d008600180f0b85031004a085411600c2800700394018203c1d0f03200650760180090344070352 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 642043974 1250 642042724 642042773
    0x3020715080708090111030c0901090e0708040b15010807030207060902091612110403031b15061d090a030e0609030609070e060d03080c09042d0e07080c0607 69
    0x465002400780e4400d1445880740030890303582015480c201c03405010200d0740120240003180e154546a4058583d290040c10702074201a212230b200881d48804032240300c002000d005c208010841e45c507041c6038100e00f075003108140007248000043c100f4040105907108044d80864101d080c81180d801001c41c598001e46903041500340303030b07a60311a40b011154540010680c221041c030031080c1c040c840c07018000e140b81c0007141070a0031541c04440c1d40e400e8000c0c80c1108441c003040075020540c50382d901d00c20540150f600003411403601814081001000424180403184082004646400402c43c0e818641c0e041c035001e05203804110000710300d03010764061590140300da075081100e070240008144003950401c05c03410100381c1e1003504200e00100c1c1d080c0d0060001d621003001c00c00e110024005040f00700d034020b101242182001e44641141c05203031000c816400c000341e000c10104400c03842900100030a103405407031003c2c00d00c11069a202c0190b80454003d0500050071018410200407a401d680e01c4580681c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 642045224 1250 642043974 642044009
    0x606070210020d18140603070203090a0909050c0a06051606270c270c030f2a031503030c080c06090a03020c300f011803030b06030106140304030207 65
    0x3d60760702221100d400800c048003403030b8202c52070020460303044484064004103520b4885060004070741001e4425025440103000741c1240f0390307075458a0340c081c0442074030001300302165050607850405e000584134001c04500314148040c1e0740c17000484040390740340c0610700c016151500d0604014132140c0140d4803410380502c104006e01030451401c26109004d2214803046640300c00d04605402c88613903e42100301940c100410018441c0d40107500107101034140043c600278011018025144410030f0b0034465070350f12141b22032250711281c4407001014540745c10864a005030019501c011803500000c0d0900c09255030501c10051410100e840c500b403403030280c0c2c1c80c2381001c49241e035a81c020520f048003d802618140c12103030404400381039107010450006100d0010403014541032400d00c1d01229114004e0420340081b0720800d001d0041d0110081c8170020084c0b1303041c20f006049800d01040907104e0390040004000b030940c001180740f54242d02c17400a90f80c9890b2480c0c1070b13103818240e902080500e031040388403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 642046474 1250 642045224 642045227
    0x907050717030a0608070f2114060f071206050f0402090d020409060209030f010e0606120c21010c17070503070c0b04081b0a020a0b0d060803191b1203050606070210 72
    0x100c03003250307440700032604d441f500c90b07011503020440b0317002d8180d240d00c3c0c204001800d440865044038286d4000c01040e00c00340c0440e64011b0408034115910301a40d200c00742842400381d40b05c11011181012903104019150030103001441c40680c0d400c400d4070668010138040490f9440e802d281003d590700510400c040340051400c440a9000928001d10034054071a144010100c10b0080d00d10007100070f0003800d86a50348504000c1c065002d000d20120307502c501043d141440d02c0380031400c0000307504503125400354000301001901f592a468210700801804109044d180c4144800c099004005802d000d502c0340e4840318116001180703644098401c00c000300500043c03104880060a0419503488071030200b07500c40c118550f40b082009002504001036a40c10408030012002410005095490200b0903035500d039811451600111009510200802d0383c2c0c5422a800c4009052042d10300c5c0c81240301c1400c41e0b00c50740050007100b060b031020315803144005562599608202ca10196004024080b1750082520 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 642047724 1250 642046474 642046481
    0x9040204080f0c1c150f0c08010f12083406050109470618031e070b0306030102190305041a0c0702010c0c0909050f1203060907050717030a 61
    0x9804000d0300844098aa090800100304e03000410b00814007060303040e1a6aa0a812040c1c80f410054055034030340c0480030004007402000100040761740d400750254101412420840d455900480080c0c6120801b100000ca10506585400d09003011042400307084102410307104201e5104952004150a02e000400005a2116050340c0080108101450014204080002008403000e50045019290081c140307030740c49a80d9500307400090101c0e58a03504402241490f00b2010410b0455100e00700302e004a810200041b80090940c030300301c3d000c800d06084025454074414011006502c50000000c0c02d1f0f1788094040391ba02c3c410b008401040c0304c9617044018010801560200c0d200840d25010710fa8224112901ca170148050442e004e14000c000d80c0191543c0745040d9048581c0c04080c03000041800b041e1007001c1019014002a01207500010079441c00c1c100d1301c84c11464070900500900c00b1640b1100c03c074542c4100c8030708041d5a035001c0c80c181007060290501811811050000030002e80340490b41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 642048974 1250 642047724 642047743
    0x60b041a160c0f0e2d04020a031509140c06030112140d0504050918060712060e0717130c14060d0507050414030a050a0b1b070302010b12240c0904020408 67
    0x1194141c81d40310381e40c940e10750440d20111884080c24a10301350310311704040100c154001e84014044030b00c1640e43c1e607643d0b840e0b000c01c0c074429022540c0d40100300c080c80082070403501a84501c0340074002e185000d800242150006000b052461030680c0100410800301030b1012100031443e01c02c690440c000650018880c1d0311a000da1401800703100c01048161101001c68020b0101c004060031569507080b1084810a045916480305240c496000041010485448901904850360381440c0744206d46049420001d0203010419880c3c0c075030b0402404520020702d172400340c50340c071010b02c0c010010b000009000381c000c080c403441d007103843c10050100403504000184100e07010401855103d0104808141e01c0340084900039010760001452440052818840a50b0080100c054050103400d0080c1c80c5050b500400400c4015039502c8012501518205c2500a0380003c40401070500245424500c9812600c21000d1030303140000d000850250f0030740c2000d844100002400840d140c5070b03a003800c1560b40d001c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 642050224 1250 642048974 642048989
    0xe100905150f0f090a050903040b070c05031204030b040b1b0a170108070807090c05041701091a0105010e12030c121b06220c03170d060b041a160c0f 65
    0x6241440380d03401d200409003000c19008203e1300c1d160b51001c10b241c000d400018441b4410707003c108030118020303941c003010704460781c011412650000c1c1000f05040c41c0c003a43e50303041410604240b00410000c3c0c0d50401c410ba2280c0d01500501032074595071020700c10b800f600803101d8841d1102050461040f82d01c0301e50704540410401c8165103d99039510520b441d900709001e041c046070014103061204030050b82058840031340394509140746c80c3c0d036400c020403428103442408070581d454a0b0003000313002c011158405145400d044018055160400107414284002c0700c45000e0b000c1e0001c00024048240162880e04171500180c4018101600c40d46c40183e0100304440005a0034030303418032401d040051854410302990101d070698020404c0031034005000e00e6000c071a04641c501c4040009500381200803036039400d0310540c640350445081c1d8441a42d280f0342000002000a100400c07031030b606000521030424240010170365641c00c1d0b011103540012540710150185074114400a21460b101034000c0844152 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 642051474 1250 642050224 642050239
    0x1a01021203071704020d0b09030301080c0a0605043312050f15310c02010e12030105060f0f03010608090d09140402030a14070201020c070603060f0e10090515 69
    0xc503190390014041950404009400068040102070126035010340003070005001c101c3c0c45840e41d5541c10003284c00c468040982d003000c80100443c00c820050614170075021a0b10051041c00e0150052860083c0d101e40748401c6c030300380304c001e038009800900c0c0741c0d41c140906101900100014405001003900050b1040000e107410002090749460f09885406445291086640b400f4a04104801c208502603090610b141c1031a04110000c0c21248180200030201008151b4250411029084a50034120307411160003554111003555209001c0301e066a00884c0c06540b00e600101c03440b0001c0c01085003840415030004004181c0a03085000c0c41e02c24440842255040d04018100311031900052080034800016480000350618058007d0340e840304404030009005044400b00000e01c0800b031b10042c025075400507551010500c240a5100545110f040500c000d92500c8412101c83c1ca4a201d03400c21900009c008c2109540c000701d15000a0185400030b00240c200103140903454800408101c2c4903c1c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 642052724 1250 642051474 642051493
    0x1f0c20030a0f2a031403250f0e040e03071e021203070b1603090b16030c02190609050c0d060506100e0d0b0402010e10080a050906010b0a0f02030d1a0102 67
    0x4a20040401c402074000b41e80350703e190580300101d140311601022001d00c01c00d03000c60311940c0b00b100051886007030b05c00c3ca1090003080b481078000610055000020412440310010500d17180c103d6004402c0e000191000900312100c903242c5401e5000e0194000c250300072140d00d000c241007145105484041c0200d409290040300080015902e11845c00c0080c58820b1100026192114400c400c225181103800c1c041003507500c0355a0002c09420807141e0307280800310624080c40c05075151040910145036030008102509144020000c0e40f0703002c132002091a41c4484410301005003c4c00700b4030340000082c00d01030a105251409501500003200e41a00640394060f940016074030036245440199000350200744680034030b88801d1201c680c014003d905102c1c00d016003440e80d4990040c41050072a80c2d903241d010314205507820030244c60340a03003411a940c0c0a000144604000d880880b16110034500708040c145446540c2603044d03002d085001d030a40c074607242644181c1084a2800303c8005026400e8406055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 642053974 1250 642052724 642052727
    0x9190f080102041e0515160602030103080d0b04060f1a0f03071112070209010303180b1c0f090201080105061b070b0c0d090605041701090203010e1e1f0c20030a0f 71
    0x1113511940ba030110040d0190110400c0c904001c207034105420418080d841c40c0c94075203000742e0b402039004075410000040c3c2941140c02c0b900c10b10b290741c40d0480d400c1c00014074180c1083e0707000009000d451810110303000d0981140d0803c60440720205840c2048903124030b0b103500058000506007400c0c2d00c0c41d01454160a41c54000c00003241c0c0040d9000b00720740e25a0b400c40d00c040783c55170401c88458900310b130311400209801030204050a07200d00c0141380c03400010f001420460555041c0b180c02649603040034031500060b0f80019150741914070594001c2d4807902003d01441c000840d401a03c1280e009a24011503560010001050508058000c51b101e09904002c00c48031801a4411070002490030300040c1321541c0300c628400c0c0d4881e5040004544000d06400082c2140c500003405805a400a00740006005c40c1c1010b044600000c54003500c0d10701c0e59203283c0c8540002e0304100710703042503541d01c008100034054002680c605150000903a89505001440c51740da5100c140300e1008141001c04144816 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 642055224 1250 642053974 642054029
    0x1e01080d020d030f02090d051023180a0b011d010815010b1c15052106070f09080d12050a1514030328080a0c0509190f08010204 56
    0x4103055009040c0b28a0034038044008000c49031000012640802c00301030b5903034030302d04e0500145003c0c401510a20480b001c26004403241c6e1907507102c0c4103448128490031594090000ca40c01041c42090400748000c0340c565605040340c10800400825078500081035152103d54114100c041102000324540d880f40c2030180d4a4034119078080c0344641c000d006001c00140c1d1030141c9800c8980c8a4440303203104407403403072405070340c130003811103d444580c070070100700030714104414400b0302990f0b03152000c0c0c120146942c0d503240d800050604040c0581e03c03414450941c800d0035410f005004480a0b113492104202000b01194400102c0ca00c0e0141040e02103013000715240300c0d034440410110070b42440c45260007034280410511075541036040c08240701004510f5080c03d0300091004c8150780b070308040c054490001d80651006496520001d1509854008403500102281c0d400c0c14221907800f050268000b4540c0101800d41000390162014500010701d078105401600541721105048500ca030300d80410712104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 642056474 1250 642055224 642055243
    0x5180604080d180f120204060f060813051f02070b0108070506041e2c0a150302300109030305060916050307050702060406110606120d120e061e0108 65
    0x2078204402d2000701901810f200000c4540c41100fa8403526942c200105101142c0d5003e03d040c020400c00346411440c062058001030103001c14803501c014200313070f40180074140c001c0042203107c003540e204005100080010b81106100e0710342d59190402440ca415019401c29030301103840131031440000c034013108045003035425660040d04403030400f0b01d04908a0902d40d40c0a03041110030481070004504010380b405503140f514480d5210101034900a24030911443d0000e005407021890201c00185071a44c41403107000b107035011200025050b100c0c2407000320754240c001d000f40c000d14003120400c013102010f4200b804098000e413802c00035680d0b1a0140155401e0444440384640400c0c6250800c080c054405540c00c00384614200341024056408180c0c0c561040e00103201082601c01080180e800800140780e10020660303603818000310340e035030083c0e030b41c004001e1348414007109440030200740c000383d070011072140c454000320342450820100118824048005429403181d4010001c00d880c02c0c0001c85406 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 642057724 1250 642056474 642056489
    0x130903031a0102060c0a110601080601180c080106110c04051009060515030a020a090308131a0901021203060f04090b04030807140d1a090a0b01030627020708090901030305180604 78
    0x551796220360f03034085950b00c0520074400780003116254062038082000f24034040c0101c500103110075410300500c04105040703050055900d1742014841c040303940d8003280547c112042c9050801d000ca0155480038103110300700c690150803c1c945010015900d084440000c110798084500b00003254540044c440e10a28404003000b0070b900410114a0501c8603030300030a054182881c240b1152070b00c942e5219030990100844180c440301030314060002c036000c81e0100d04405410344801e032400c201e050000c3d45505007503180010303400020000030010303206e00e501e84141c0900140b00f08544038203480c01602c408800c0c5c80550020306050000b4903a903004441940b507030f1046803085420718811440c01c05c050300c085101c026030182c400c0c1c039403425601c8140000d030041880481c08034051500000040864100b0b41c4030100107003048500115208445060003403140405001680d0340146080000c1188900c0310307266000700d4003400000603d03034000094200b19540307929501484182104100c84ca019034081d640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 642058974 1250 642057724 642057733
    0xa02041e051c050316020312070f0c050a1d180304060c0c08031204060203040512030a140f16110f0d110c04060b0409091506090c120203010602120d0902130903031a0102 74
    0x200d05d6440821031541e160710080803120754400401c8041d0350385e005000102c5000481603466410098001c10002c0986030039140340c20b4503441c02e9145008200000000e42043d1090b10100356141c60b06003103980030840740e1040f02d558950b500802402022509400c1d00d03400903644000c0713862080401100d821807981c1841361081d031030b1922031100039440039004903940d114410f0280c40b0002d0941c041c603c034000203400061242901307204d00c00d810400401c0403903503940f040d0810407120f00c8141040b802c41c0c02ca15000740a8880c00c21064035004198012010501c10501c0d440e0940b1b81c000800c00c40e080c024020345403290504024001500d280780200c90b000402400180005205c1e684034117007050203402d02c07040445000c181c0070100c80742030300500c200e9600c909070814000d03041500341e41d00516601302103185615244000f034950341050410240d0090000700d42005007103c2e0000c48400b5001004113640d6491900554000c0ca41d42404501003800d00100d08100c003502c00c401e406082042c4c0280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 642060224 1250 642058974 642058987
    0x913120c03090806091f09050d0c060f1116030918051605040308041203020a020a0f0f0509040210030509150903030a182105120c090906100212030a02041e051c0503 72
    0x111b82c858100d4200344005540e03401d50034003099040240d034203e035515441d0700031140441d01f41902501d4500000320825820009481c0014290381c003110050030b0151024070710702c0e902e840c040703691003000e5000c010300101c14040d07a440000d2540c8620b003c0c0d08102150707039500250200c2611240550b22018144480034002004200b9100c040c6040ca5842481030303403000c5620f036000038180d81041e00204030b9020450414860600f002d880000580b1040390390380018501039000884d583d00c4140e0003070406880b44045002841c08100d1224800c240c60803052051070841c0050b5542d8004407003501006051501b0007010840100101030000c1d04a516441114107103c0304503801c0c00f5000090041010070490710485440850b041382c0640c07a081140e0340c0e5600c141040200c456409061180304150380d02c0510440e80e00040d584501c1102004056120707a0ba02840900a0240f580086c00b0710280031343c04000d440030002c0f4401640d60498550001c040d090000900301c4140160007442c1d60b100b000b04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 642061474 1250 642060224 642060253
    0x60f010b0f130e040f0c09140411040207051c0219050303180f01090b01090b011806030c0c0f1b080d091403010b0411120c090f0913120c0309080609 65
    0x9014881c10b0001c40c0e241c10f40d0310b0f038190044850031101070350424602e0a08008000c1c020f50214001c000300c15060080030244600c00c1030002000d44010300c1400c980c112803001da151901034a003d0758002c01a070320740c04000e401c4012481a44c04c04407006004107114054552000c050440d106a0010025030550f9150007103403030021042c0e00445914400c4400000040d00240640641c00341729141b80146940740c404900159060404400e0500c02d510104c60b148400c12802030b81220940d140c00b1485103003916081d660250ba0000140c1040d2540040b00203010905485000c00000d0380e03606031603d603030707841c0d410740b034211104044000581c512400c00801d4400c0b440041c207844010000036035043c50a00181c02c42d580311058041002d0046a0b07030400702440400c15030b1003a000d20302a443c0208039030008240b920700101d41e03803150480001007040b00c4883c01c14100c000b64403001115841400b44005001010701c0f02003100015100c94020500d80c00c0450f03014001c0040100404c620780390f1641 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 642062724 1250 642061474 642061477
    0x60507060b01030e030a0c050c0319020d1a041208060d150e0f030307090509071d09040f0c0e1b1206010e03032203060f152102040617060f010b0f 64
    0x241681010344410b0343c0080d5040900082c80d071011181c5441c1c7d1841e6061801c2410030400b4441d06210350482050220381c1160a0300b4030b5065941141e9244501c07002d4904902c106041e00b08100030788802d44100000c02454500b413140c55512038440c155295940003c1048a000012004102000b4072100500600d0380d130b08400002d000d218140c4180380c2c1c1081c4010301d0341d002141e006c070004810810400117418012a11134011038185010001c00b40d04c0501800c0c9101e0707500c0184d0141c2107140005082c014440040c03480aa0b120503442211540c4010040040100355580759240c0210082c0e444100488000c03500204e8403a0700f80c0e070841e581c800054581e00c100414094040c00200401c00c240000d900d0704c20316018102086501590070340c28040f04403410456600720b15454546098408819502a0b608075030344500f0b202840381d56107401c1d21040f58410700c001d401506180c0c0200d400580191000011010481100c8540c0d40303078199003604036401c4c4580e076030f046030410440004080800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 642063974 1250 642062724 642062741
    0xf0415050c0405030f010603110a030803010e0a1b020f2404081e07051f021213060222180603020d0b07020304030b090606011112040b0c07080106030309090c0906050706 74
    0x1c1e00d05140d07071000402d0415103148031250b110796441000340304001c4850101c8642a100352060100c007421039440b11014401802104c501010400004003034410f190000300341c04140200d07055662a5441c000382d80c4d02007000b401c084e1405000380605e00c5580d1140980c070b020150090801040e162a01c0e01c82c03855100e9110302c0c0c0004654200d410914124000800e0a144600010700718011150194000014010400e40c00301d401002540b8515800406607070304041c0046400e030b04a0180d1611b00002d100f40000301a001d0102e43d0601514003142046104a032502051120001282d011500850340c880c0002075101c00300e08902c02c046078031000b400380d02121900440349400d4481e01c51000c081412140038141d03510030803c20020b5607121000300c2c00440303004001e0521001e800820702c0a4003880c01360298010f00465078200070f40c0100031160003018400f00801c8910385a04006209140c0f60260303400d0142005481051301c0d00c50042a0708650103513840034140702c0180d0364030010b06040f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 642065224 1250 642063974 642063991
    0x3020f0d1d1306081e0109020d022205150103060506040b030708101208031503061b07030c060c0507051504020307060c15110910030603232803080f041505 68
    0x80040b20011901e4820030014121900052012100c14020f0041c6004003416031985039040c01100d5005032101c00d03c50f582268106c4404002c4480e5000310040d400300b503261440a18102070502040781d01032081d030500d030305003030340c0c28416951944203010881c81540b05078460a1801c00c00600098442e070310b03058200c0e034030410154403150340300010440003681400980703816100000380b00360004c03010714000003540144d0181c0018a050402e010060700302524464008000040185c1014801c0d81d601150312380c040350030041c003142c110b4000c19030380290404485900c2550741ca042e04044200540d80f14a0f0300500900c0c040c6d08241007201e01007075000003107407491046029000d01104d1802041085250810010b4941c110001003140b0708400000600915103002420300100e40080005503001c1310307071441e8101c02582140f6071407a01c1e8554012030b2a800c00c80018010803070f0010404044d050099590328860303260211003552250050300c1c001c000000300415032103054060b410181d4010002c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 642066474 1250 642065224 642065239
    0x70303020313150f050f1003060c1106090705030d02061b131206051902070c14010512042f011b020f04140103020a080712081315030903020f0d1d 64
    0x2103540b03c080e4a100510f044003050b4840c14140705101c900d01c41e8651066030010602c00710b003441c00356842c00049030b010182c00980c03101c45034818180076000b1b01003400d8140b012501c1d60700e04100171984405490048030b01c00c0c0201d641c188840b07072000400307a0182e004c07150111a502c281d2803803079815074084008004076542d011300001c0c14100310a0b40441450107840089164900121944101450300c0c01a8014501c140005030210b40c070030300b0820030707201c0f400c0c1d8611814008000594180c0144d00000f0040fa0540042100304907020140791084c8040025190403443c88141c1140000b00d21a240c5000881203080d0041443c0d050380800b0704580090700c001034840702d140109043d50408401c605240c41c41074010800c40c00c1c0103088800400c4940301504460b41000286c00340b040c401400a404030074040740b04580308a4407890a0024500315801400d80e400981001d000341180d490264003501911030741d40b1040c1808074000c054400240d8911065130100f4078083d00c030302d103801034054100d2030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 642067724 1250 642066474 642066511
    0x20d0602040b0c070f141509121b010801060e22050709140406060e060c010213141806030319091e0e0c040f0302040906022205030c150703030203 64
    0x426100920240030007150b400d0791450b0340320282e440c24180741d010b180341240f801001c01c0349149220105207031041c00c0360303c07c1c828510620000348601a0003000da505c05562031a00c00d5440e40002d02a0404010090049c4040c0e08407005540300d1342e0910409002c24080990004240b400c26400742d403d882c10700441943d8088000f0301c60440f81304550303100c041440040140a4400b045d1190450807108650602003142030800c018980703da82d60825010b50800310700240e40c11000e4044d100d80c4156207000340242076680e012000d03280d010054403030040b80350f01c0d8001c2d1186400d4004034480d02c00580158503003845880100c06c020424900c40d002c210015002050700090940203040201043c841426042d04000032000007581c00b50a01025001c10441004107c00f801d080c502107940440d00014a1016410030350080e1064483c50030300300303d5415604420700c180003000020364a0903001c4a442101c3c82d02400f02e100b80d0101d4081608400340004c0000074401d0700115407100402c24440408030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 642068974 1250 642067724 642067733
    0x12061404020307260613020423030a060903020a02010806040c0f05030907120803060a0b120103170d150e0a0911090402040905030a0305010e060103020301050609040905031b100e0109021c020d 84
    0x24581414800d0030f04d0344800380601c0d0329150402d0010080425800c51410f80f03040444290aa6500c1903090129000d00c24408165024000a000740740c004000f8064000c207403800a441d04000f41049010440d0344c004961a42042c0c49240c12105e21500d40c0e0308000c091040c10340c0d03190401455544d05100301180452601c1d8407400005603144a40001500c034240701040002d01c110b29005046048800d201410481402d4800c160440f034004883d03030050300402003d101644540811641514203080c000043c8000400e1120100d40100f0041462034036195100310076103d6040028004802c00c25104d00c180c644031141c80c0d000703480144002400c1d1415510340c1c3c21074000100a0022a40d100010803907102c1421616500c0103007403804514640c10180082c6040c01007e03801e500545d50f54070781c2c2d810030100304201e0314500207541007808111300318000c0750341d100f26a480c0e2131541800c1c100e00001400f414040c403510194000c1a080c0403540403c80c68458445010301642e001303032640d039840c003c03c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 642070224 1250 642068974 642069017
    0x90206160c031a04052503080a050901090f0f061103070b160905091603051b0310050a08010209060f0d140f0405010b0306090d050a0c1b050112061404020307 69
    0x384100d190300e09942c0785003001c0444074140c02450301d464072440c007000700055010948441c00c0003500d11307440420b10302407401c020a0a154000502c0e2400000e240d01d1020b40182c09054800b0090342c0c0c01c0c86040e01c07888001c0d0f03a80003501c2074916030179017490700b8401d450060f108041c2640100c003c8070300304a182d40701c00107031841c260380e98841c081c2484102d43d13986a100380500c000d44000e58061101c0e0416841c040e1078a403d2003101404c040e600e20200d00340380c0c090700c00b41040b418400e058646a041c0b00428240121803840f442d0322442c1c40e030700001040c00e018020307200300c20320050903e070801f24049850ba14a90000a00c15110b42e0384000c3d0070300b9100d03194140c1e402403611754410350851809217085800c4541c07100c140d0340b080c0e00641c01c11014a02c0040c1d01060041c0c14a08980c40d41d20600c0140e88005128030001c01001d40c00c00150a0001c51070760000480390300760781d0000013903c6d07035070300c8402c0f1541e501440d958000000081d20302410140c005603044003140ca40507a50b8005141d500600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 642071474 1250 642070224 642070267
    0x110c040203010b090108010e04030507020d0219061e08090a230102030103030818031207050a110613050706090803070f02060d1406100f0c02040b030a02100f0815030c04090206 77
    0x4808003065500d030745c1d6070000e41c49014080760405e101e89412329071409003990060000007881000382050410464507100c0c51410740c800600b4a614280340c940d00f019241102802500b00705040c1c4442280100c0e100b030b0074a500481032040030700240350b000c0d07c4403486c1c40301e8922035582802288900c60180c0c5424070003140210701a65a0202c90b08019140c1c140c41034010580c107260751701c284030405804003134084d07040e0400300c9801c0c0203907070f036844d00f9003a64410700203480074041d400790344200001d2105400b5072001151090f4141d80550742c582c102550001a24041d41101d0f61050140000280c04000700c4c0205034001007104e81001c120141070400d03264000400d1f4804d44c0407406110040c180403e5080c40742c021401c1c481308402440100030051f050601d4003910494980303015020707549090107941c1d81a9005040078410444646024107601001c452681c0001d85940004a4800990311078400781000180600312240c011010403014000b018800e0f68095000c200c000c00400c645400d8082 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 642072724 1250 642071474 642071489
    0x10506032a01031d100b040b0105030609090712060e0613121d1f0f050a0e041802040e0303100b070206070b0901110a02010c080a06030b0601080c0d0212010315110901110c04020301 79
    0x1501707100964400e591400c1160380c025400d00d40c00150070380e0000c007602e40c0301c00161429041aa200d650746480c0200c503a00104e08403106102a10a00035541c200c03500e86a0a1411a6138503203509140d40040700c2001d901400440008910240f10f62250300825049030426182030007610b0040300040c13490b8088030f902094000b0701c0c40020340c01d42d001003514140441c0741c2009418140350403806014450881c203842e01c125641e00054a9503900a040c0500c4141c025008000300050380700540c0e1340c0e80c0141c440c009e40d0080325000082d111285030448110030340c0503205908003681070380e541003030003400f511400c1c0e15501c40d0000300e0010500e5015040d41081a0b0001c00c0284081d5806004000301510b032114403400c050051000c01c0058500c00d42003c401c0c43d20b0003042d56540380e1445240070f84514900300600004007254800e40045881c0e06890098207250603501e10781d4105000c4881440104a43c98401c0c4400601d9601070000322450220920561b04241040030010b0100c3c0e000340c10120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 642073974 1250 642072724 642072733
    0x20406061101150602101e0c030608160803250506040507090f11160c0e090a02010306060507020102070509180601091b0516063308010506032a01031d 66
    0x2007801d0144000b42208221501d04540c01c03c00001d4a554100c2e103503020860301c8102407000000340c10715120703000780540400c212030241844020040d1007180f15000d050700c40c1c5500310003000c1c2100740c203408454110000718a812998481c0e0b800c00c106940529858603da26100030100d202400118402c500c60b0f000317031a000e0706000307084040350b609001030359209281401044540900b24101c034031546040d140d80366070804030301e0540c03c01101d5400186041d1601000d0003c1c540000031b00c2c0b02c209100b42c80a101c0da035202c0700d085440d030140c40f8002e070050b03000000070007003410010192134101d5906a82c9a401041490000d03140020a80c08588180d5540d503c10740ba0783c16008030000403074501c0c0b522a142510300c1170300d40c002109180700600385690f10b0ba4a010f404040744d070009010b80d400c8141048840e42c1980b0904030300102c0c444d620503542481c001401629010a4000a000480440b02c0c003160100c0514072048020f41c8085042c1544c40d03a030705035580b1b0141004542c5121440040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 642075224 1250 642073974 642073997
    0x170a0b130504150b030a021912060608060703050c070221010e0318031609020a0c02130b01180b040603051803072406060e0607150614190b1903060302040606 69
    0x9012808601218901c0035151844c0400280d03400b0580101050301298141c0765000194411031550781c2952190482c15012170310740f020044650000f1045502510076229240d80b50f2000764140d5408485d2000b444c80704000c51001440d20507802060507425121714070424241010482c02c440259400196079070001c41c0180107120a14485041c4450a9000d08280c4903944851180b8882c1c9005988840340c0105c0c6520001c4c0c402c00e060741907a03170018820503281c0c7c0e0b070302000001020b100d5422400a82406d19240894402c22a03c804880710061101d02d050f02e4040c4c21402401b02a08000140700403003441345c0c511900704003915049005140024004030f1042d42400055980e216054106040c0f003801c000c1c41d60402841c00080d54150749055841445240119030400c40202c1d50b54014239004010641c5944d5041903034210500303455016a1a0720301d40d204a80308060300c00c0d098404410000032080202c08580185600c0e2a4100401c0690302e99001406441e03130358001c90b00090791040503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 642076474 1250 642075224 642075233
    0x6070e0306061c14010e0601170c03010b0a090b130603050c0a080607050301090c0c02030a080a0311040f0605130b0f0a1b02010e061c0e0c011806170a0b130504 70
    0x403500000100c0f12003559003e90760540e90390281c0280003038002c6480080342e885001080d01301c05103007890003080c0e8101e5a10340d81071160019105602540310700c80c05042c000d807401c051103042281003009280e800d440d0f150000802c09002a814455008083c076610000d095070341c1e004180c00343d0700c104007400c840341150b02845a803200c60f502142c0944c2c041e005000b0132541000880e0b055076a181070105189100400c02c1e00c1500a401c8000e4162150103841c01c1031200380c601400898046560520650f80000e100403040c0c02180622608440414820040103000310024006495a00c110084a540c0c03550300120b990840101d010480034009514035401c0d60046004004540130502e00074042c080781c000034481c501d2103070f14900450000031007001c00e00518002503106401c014081c42028030140c5040d850307144640d074140c0072910040e000003051542010030010382d00c5954880f0a025007a002510040701c01804a245143e41d40511001948030302402100819901e00c0124080c2840d180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 642077724 1250 642076474 642076483
    0x4091a070207030f08180303031305120c1f110a050301090501062619020706090506070203030708070518090406090c230607150507080403030609060b0d020c0c0306070e03 75
    0x3040045400c000d2042c00010001e031888401a41c00070100303520303500d5045803030b42c0003580b1416182d89444040f003081082195010b449607414410704c16030b16560401c1600e100c4030302071800001a03d0700b0234001e105240700f5225003594420030003030002c610041c038000145100c2d40044032400c00504001300500460f03416006503401030840345450011800000780e0003c05075101001810414041004620001450f41456903540c5a68108540d100464600f83d80107207640c0104840b0790140302d001500b214004015644180e41c5600e80c1800d958414808440e140e1103200350200c44980ea0606075115141c44c7c20300e505c11485500d001075008044e003042e081c40c020369400000c248122600c0c40c00c2040140d840e1032a020425281c7c2621150b1a16000c02c0034006250611901480d040400207466408440385000342d0003174804110741512450014141c601d68003031500005020030030300040104503401000310502c01002d45203406108000282440b2003540c10b1400901159410000d0340b40500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 642078974 1250 642077724 642077731
    0xb04030206060307120609050717070e13020901031704030804151206080705130905100b090a020702150901030e120a030c0810260a1a0105011b15020904091a 69
    0x10b00920713420b450480080d071136000c2d1000003080f03a920f03485d80804000c030400c229009000540700d41407440c407680c0403499450545118401d681132680004c0350861149510b02c041c903540183c14501036a095803102c1084442516032203500150820000010a180e0000f40c000740c2041c6404420356510860002e00350119980e1b40d4000c0ca15201e010007080300001003110442d4400d6a6404118103d136007070800910000501030200d005a000c0d140d1044030031b50004c0132000b03041341c0c801817680790f0503000b00c100d02600c00002d41040402410302e05d000d010002920400205240115000580402c806d0400280440c4407001d6400424690f4140c0c0d0580142c211034581807528184a20340b102030b007580c0c040d080c82401940000055000d0030f200c0350040310180816900b040b0380214080f0318003160880f07411003031700a81071101350000c61107620515400312003203100729078081000040c1c0c42d108030250b0940e0141e601154204480300d01c07620b45000d060b848134011050340c0b007a9134948804861084005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 642080224 1250 642078974 642078979
    0x903060509031314010e04060906031209080705090a0e030c010902131e020a0c0206190e18073519020a020304061b230d0e0f28030b0403020606 63
    0x24003a00b8004102c0b08800f0080301c1c440d5800da112480c2440058502100703040000c3c0e0028104440407179401501e4000000700ca1142d2070660b000316603005e08846904450042c00d04581244108001c10b25005074031503006600400001156002003a0702d918541c86048000b01c143d440702d02070410351070403d40010910b0b103000014006400440181444214040c40c03415069902048011085100d5500d150f03110354007500c820b03598002c0d1612079140e0b10900c8003c40029050060341074042c1000c4c845c41d004502e1030b9844a9464540700070a82d501100e6804442402c002c50803600700030010141c0b00c9140817050a1801054104001c03020340c500710309135090600c02d00402110404e130f0390010840e0101c1d60149840e2040c0410f000140015001622313000d400020448e40410a0300529004000301000e00c2e81142c00902041c28161100f001c2c114071254800f0004d0a2580d250034080c2d0001038410070104ca401011841401c9007010407429002901c141c1d007a1402c01c020076404200c0c00341c01c072004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 642081474 1250 642080224 642080227
    0x312071707050c01030f0c021e070906030813080a12031e0204090c02011a030c10090b03280b090604021809040515100506030a0c170103061e02070c05040e0f030307090306050903 78
    0xd071640030f940d43c0d071040201b42700210300240a0f41d04000901059010380300d8600d00307104070303a03580c01c1c00c444e5600419040c807001c02104a00180074540041c00d0800c903a8000c80c01c03090210b01c280213900606001306002c44041480f070702017403002464801040a4601d007000051546104207000f400c40303404443e05642964501c0b4000d03003c1d60000780d20a254001145c84a041c2480484100e8108003964040b040081001c020300c851a20f00200709400c103001070b80060117554007803801030255500015083d42050b07094000c651982400d80091032920220746110038012810701c0421100c2c4412141580e00c1d802800120211089803580ca075001442010944107d41c00c02c00000c105100203406010500da0750500c01250b107010305200c402401d44080303110ed05694909049010f00754510140e034121184c103000c4148641c1c644241e03001950071000b260a150b042000b4403004000d004a40302891080008103908441c0400086115102c02d980e40c018642c95460800c040c0c9001810705e0020307410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 642082724 1250 642081474 642081491
    0x50c1e030301140618060f0f0706060312170118090b0a0f180b01090c0306121a18191707080c0705060a020604020405060406050d060509100b0312071707050c01030f 72
    0x217001d07100500d000f04403074403945e4000d256014241c0c0d10030503113030021220300800c48905001c04c641c004400ca90103001c65020006030014101e44603413500c00b40e10300c00031100340140101982d010401002c070018000010704a000c50311203d229400445640d06841e4a80301940c00720843c600814614100c14842d02c0c4001119039100445c0c50070500940d510580e5030b1621403441c0d4441d0b00004024016003411203034207000d9052084103454010110521012001d011401120700036829072030161010015218544606c01d0114040c4030900c8180c640421a016008152011600402c3e178548203042456030f960703282141e2810020030ba8847c2e40310300400e002011121b6004161668010740c100c0d00040c0c03965030580010014940c0d41c00040c0c1002d02d00354110100310055000f00d0240748460110f9545e00801d8201a0580d501c401d10a50940c01030079000000d10300752005000068450841d844022030000c0100c1e40f07a0b0420072050750a45e1014584000e9035800d8800d03008241c002100a011030761 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 642083974 1250 642082724 642082747
    0x1a18010303080a060509011410110a03050702061201080a0c05032d120c0f0c03012703021011090f03060403270509250915050c1e0303011406 62
    0x14440038080c00b68100000ba422215544084e002c2e20b00100440d01c5543c60701d908210340c40d412008540100e00502d021f0130224003070b00c101e883c0180c0038001041c019034a070341c0464554004207001ca03000318050050b44840c1c0000100503000c0c10009008100e56841820034018030400350b4804c1e8001c1d000b20480c0c01c211400340400c2480d800384076410321310341e1040310409071174041d0400c0c0f50416680042000d900200b0049440340c9203031000f80499910b00f9043e0101801c8504001c07411422207850340c910812103928040301d08100c1c0c004e0055034881208402d07400c0907550504843c0180001c0011410064503106100040c42142074001348203d140c1564040c0070b0400310308030400c2c03031000794400d2070302c2d01e81110259020300700c080c26600441c200100410388214243c00303038078450184141050109480340704060121000540c004020702c09218068489610105019200e8043e0001c1e0308810b444440340074a0460b07003180150340d42c0d803401c02c040041c074000e615540d11400301080b910703080300c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 642085224 1250 642083974 642084019
    0x13080f100c081b1b06011a040510080c040e04050c0406151d0a0302040f020705150c0904180b1006090b07020303091306180b01090b031e04050f03040305011a 69
    0x15108143c1c050307a05001e006101c805000e03041c10342d441e0345020210702c0074802d004500207040b1a02c0c0c1118071481d18042644016501072406042e8008000d1018511100d110785101600130f2150340782e0520f0240c603440c08260a1100312030546859222822599560900d88a0700000342145040d07125000b0918a000b05004030002c1c4444101d4802d484d205000c2c3d841d1907150008560003802003024950312840700010750000b8030140ea150140040309503140e03107007406261090342c030511003d20b4444a82c0410005291501c240b011003810300b01401c000419200c200307405a4041394400c40c1e603500e4900002d2400320181c00110420070305001c0000107840020503a80303042d508a440c00c140003406040280109800c0e0701030640702d850380b80704080b805000c0d4402d0701089020317610445402d4481d001ca0780d003444142c0d20150706021103540c1c0000510900e45517a040b07882041a1046030322000358013459138000703400581d02659030b0000c40d41120904140d01c100d8050a0310240102203644400d034540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 642086330 1106 642085224 642085231
    0x100b0c1605011b0339050f0c01020c0904060209031614102001060e0a06060314060105070b090c13090201030b04060f050d030513080f100c08 62
    0x315446000e40c00412a580c100010740e5500d2a6405c596524403400001e2800c00c3d2030400c10109501d155070080a440140c000c541089281d003412420405000c04890710303544094499401c60340c0120b58113842d01811940f030507042d900c60030501d010b441200c60740783d0306000e50341084288400e0900d07040c040e1620076072000100404001405803040c0c01c0c000e5030001c26407a64640240840b080d800d004105000303000829410780c2c5111005111905654810ae0f154a03414280075265040c46900c0c4003a00451130800d041c1020000604144580c00002c0c1c00b45404200160700c00808001c5400c12075406001020ba0024402095000b0f00c0d07500c01c101c0c00682030058402c6079242c240942d42c1038508640c140b40b5180c1c500810800040e6482c4422804d0020911081e10307040300740d01b4003034000d159002c09409245000c0b0081820035654100c0d58005901d050b0343c400b001c907401450907a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 641906474 642086330 := by
  have h0 := BRFrame.cov_init 641906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 641906474 ≤ n) (h2 : n < 642086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
