-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1875
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:59:48.939974+00:00
-- url     : https://prove2.me/submissions/bfc3551c-277a-49be-a1c5-02938a79f48e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 337050359 ≤ n < 337230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 337051609 1250 337050359 337050361
    0x90e0105190506090d0b15010f080c040b0f0409050a15170a15060e01150909110306040b0307081b030c010809120a02070308070b10090c1403061309200f09 68
    0x1920340140141468130004d80810001c00c1180c50300d0001c14422120350f00e811840d18062046076a1040e1514070020607410800003d050507406001140144e0252000050001a400f280002140c040e980188402cac5001d0200d0300c4c20504d00c0c00034007451004121070321002c00e00401d0401e0340b65040480101040c0061480009903181d00b6040c01d070340d1011408003603840c0c801155480e6880d5005018061404a024070042e207150020405102507001048062074001c03080c10790740c94981101d41082e400ca0700841c0f070209000c0004d041c03880c0c6030b0000d2114400c0d840281107016203000301d008200c0044050b07954203c1d403400103448640c030807110064160010012102800c0c501c0000d40010559441100c1c109900c030380d02d40c0c001e503200a40135a101002c0c0b5040050a101e400321440141c4640c10091158501c01d41c000f601c002810640b40d2054000400011116180d100422520100c1e800060112000604091402e042251849002c0200e400c12000f6039041c400d070700520b181e0002c0c100c4422 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 337052859 1250 337051609 337051619
    0x40c052107051507170c0307050312090106050a1401021c030f0b030c0114071a04110301150305100c030f1b1d09060d030512040305180d170c07080706090e010519 71
    0x641c16003100521400d40612000541110802c06008c02520660085650708403040e0146940ac01c010030750fa040b81c0c1090000c0c032131915079014010445200e02503c0c0c11400c40300d00141e0a003940c1d2161210a91103281041480607415000f0348458204040c0800c01d01103032000b41074486600c1c010350360100c1c0c8180b24040e0300c5c2c515080101103980c0103800700202500c41031a025520300040c0c4003034800803e000d50480c030610b000c0c82581c0320b000101d205070b1982c901e95a562510303504c1515500c0d14440c0d403400040541402900f12407000c1109610070048151200c042205801e090742d01c800004100c4582c9030315420740a4450740c604640103020040b40d50f00c00d02000729850315407000300c00300308061020311481c0441e410402e0186110740c07116505c03600d044985114582500003803501c504541c90341e10300481c80500003d40b02200c180144c59840c0b0f1071004552602041e80d0040035244907806001441030b5000b0785c1c00301034032100d0b010494030381d0741d8038200440c640c0c9600c0c00c6005c4410032041041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 337054109 1250 337052859 337052873
    0xf0602070b03370504061a0f040c030b090c0a0f021605060a0509030a1104050703090206090904030c0503040e340f0e0a0e0a06060309080d05040c052107051507 70
    0x205110a444003185030b080c4242c56005804614803c406503d9281d40500c0100f1030035006050890350181d0406a5180c1c9020000b010b6060f4a014107005c0c42d0b0310041c208125110b6000b0011908011300400301600780300caa00c080765481030094600250070b04551034812840840c145003030495808d0400c0005007003004001c0541d10840011051040800c24440992010321812294901598485503c9c000d04000c0c8403e5a90040201040620b0564901c0041c3c0d01e480a4840058003594804069919490140c51414600d40c000e019403002040c005a90b0140450301842b074040030f0702c808080f01450b00e40c0741007402d00b00d41680c443d215211070307042014401c50316824150828901b00e00503281c00d002040c02000540c00c601e0075032000c00104004119540280401081d503840c08000c012215110b0310501e0060030000d0301d90a80350700120b018818420840700c003600c070080c8608180d03102d483c520030143c814888568401d010303d003000a00752410116007034240e500c03031440300d02d05144c03603a0f120 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 337055359 1250 337054109 337054141
    0x19020a18020418020a030e19080304110904080304030215150121020c070306112b0906020a0e100206091b01180b030f0a05041509060207020306100f0602070b03 70
    0xc4016582440001000c4128076001c803404420000d0042c2da400200c1d000501b0384070030000e0951035500107002c100003030740c1c91002c0101c2036801c180065120b403198544a811083c06110310303640301d02003005101c00e000f100c00003140030318425001c98414114850031006503131000ca805401e60002d018007001d1070b5004224000200d2160b60400000c100590742c030104a0308612030000036584007030028030402c051485000100001141028180b0b030048041d070303442d41031432359a04200c2a010505164203113810f0700018000365010b0301c2551100a100c0c001065118940911440380704100b0305d002c2c070342e800401c2850080c460a4003406464400e403023010250668014035030b04010b425030441808101e01031101019111522141b956403d00c140802c0f044d44000c0e01201c60340e40352006000000c0d45404450303621113102c6502242481c450705001009004096000e074040c02130308108000b010b010842c1070309895aa1031201d0042e520381100302c0c2d84490b03902907041c034040200007040d01e918151a40c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 337056609 1250 337055359 337055399
    0xf07020304231513230d0f0f08040f06080c0a05071a04060212060f100f090b13090506010f020c0409020a1d01050108010b0a020307020d080405030a03020c0a2c0619030308060319020a 80
    0x44042861590750f40d40c2405030323610341542c2408000c1000c4c010100c81001c90b1004014078070f40003500d820801c44d40c0c94a0710804950a0a1280011388d90301081040525418041c40d551030810052429003403040196210070841c0689a40d22400641c82d8501070760b10205000700640142d21000d1811802d544132a0040744841c14024011070012b031400c278080080002040c0800b12505a40c41d129409040da94040c0c1101d041c4104074012810b0a079000880d880011000c46007c10225000d00218254140581102400e0303c403d07440388800e0506458020304840c0e0a036510250f0b030780e031030881765100d001d100ca0600c01a001000340c0b5015207401402441101e01443e412072400d991039000910705000f88104502581001c00c19411924049000704002c020b04082840c200d81c00ea041000c4810760709200d0000c0c1d00600c4080341061301d40d00b003611030740c1444901c90a0415240d0601408622040700d013540712780704648030340c4c694141d000480103445902501c262403240c200070000360401743c60945 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 337057859 1250 337056609 337056623
    0x15060705031c020904061403070909020907180e0a0902330304110405130620030c1303230705061204030c050c0306040b06090f07020304231513230d 65
    0x4d5015a40d114070a503001004429841c03141c040150050608054582d07010045e0030303280606910140e12001d010aa0281040c0350150042d001c400c0f22080c0c82019420080d404c3c1e07100420000103034078960040075924002c41e000d621b120b040001c8004540030b4002c1c0d020081c5006181c03880303403046010103145c110b071082c1400a14003044c000848d04443c0c080700d0107211600c00640324010f20080d48a680c80710310000c03001010780d4142d00d0140c000352002500c0300090b8000014405500c100c04180e200c061940040c80e40014003284505000e20b400c060042032040c091907000041e00e01c0c1030402c4600c9102c65080c00512590786460036174403d61503020a44035401500c040c0f10b4141e400b481864030941c814613100005041c618207005648a00070320705440929440c0910202c0e0740c00100740d41c101d4102c00c041e004040042542e10303402141d8464101c3c0c00602c0b92062400307444248000e40301d010700ca42030501c48a0399841a41d076201e030744101c880d00001c4d01d640510381981483c4001800c00380c09090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 337059109 1250 337057859 337057867
    0xc010e030102120c040314030a08040b060103091502040f061805040c0221071101030b0d060b1311031503150c1b06070f0206060a0806010b131a0315060705031c02 71
    0x10283e0482000c81d1942da12003c002014401c002c0541c600c640390071901801181440c03d151800380c200400a030000d480505400c00040c0645c2c42a0010107507264850104442c440068140308061b404c00d01466560494400000c40c445105010070f051600907503003c0c441040c0b4080c1844010310180e44840114003071201455003403c0310384410b1082c4d03009400b606607980524102f0719844d1060000840c1014182004c09015648540c0300c226410b4000301c000402040303a80001b00303000030303000441504504141c00301d86080c101c1da01944c41681000210010007017460308050b1201e8011458400191507007002c502036101c00c2024008017030181240740744822071001c503140f411000301e075041e0000340c0d8941801b1025a0521000d5000401518624a401d01b4022b035580c60740f005000380c861050020450051100d0f0740241a0010b05044885d0700403414880b43c81c2800b50310407660208580405182d00b012402e2003030440f84841d42210245091803000c820a1000044c80d20109002a400344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 337060359 1250 337059109 337059127
    0x305090603012403092004060914010503010501080f1c1b14010c0503100308281112031005040f060b16110303090102191406101d090c010e030102 64
    0x560207401000300104645032900040300c0f0b15211062440100740c104140500000c0c4a000d5456814028400c5820b607140074401045c000c14071540061207040c14801018a04016140b03100c1c182ca20a40c001d029581c0c07585450b0350b071a41c004202400584c07200e49603843c40700301345030304018130700c0e07140b07080c030f0440c0c0d00c1c01000709044030074020680b000301300c03424098505c0302c2c03d01c0f07080302d180614200581145084d09010703660441318031020b03040480010b8049041d0f841d00044020040d0018035001d5450000d00c4001e20081c1d4000168041d44155007100c01400c003d10160382c40354a0b00004841d02e50305000920019044107030729074800c00e0321240003042d081c2018001d098040c000981c900000c896500b0803141c47c0c01040462402508200001115a40e004ca02c0511642c2e4050b4100c00200403890540e450350668040c0c6d14041c042c0c4003d21110b03a0100c00d2404c1180c5c01400700c11034640600ca00741e40354101c1a078000546600c000d030000219401140c0344069140d00400042c1450321035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 337061609 1250 337060359 337060369
    0xe01052d0409050a0507051b120c010203220b0105011b17030601030b0a030b150d0b070915020105090c09090109080f07060e06090619020705031612020d0912030509 72
    0x10340d65408500201003018814080a07101d425030050407200140060301301198040c0c900e04c1140341300071b501c4e007030b070100b0303800c001000c004e6030b1110320040310104c1e5a161010203080c002c0d001901c034002c616401301c05082031100c2100d41c0c0c009168000300c080181da46482c1c0192001700001c92021500c07919508020081590007020406140b0442c0c003280c0e8a10b400400182107480310400c65205420381c09050010232010403465920000e4041c40b20810b0b07502c140081d08145454100524400d4070380104440795038040c00c2c0a0484901141e120490321200b6026400e03144105c07600499513015640d481c0c003603d400308045400c40b00d40000003421406035100c030451135001c0c000ca003d01c03407000078101c001c00015100325964100c0311005807800f401c1441c1542e4554001034a80742008010a182c060000f0403641101c900503032050450303544140903504110134008aa50546a09581c00902e580181c0007180041d100c005580e2490300d0107050850206502d82040015010840d0901c42c0d14215221 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 337062859 1250 337061609 337061677
    0x20310050616060606090f090c0201090519030e0f06030f0601110703030206060906030f0d030b06160f0308160221160305042309010306200a050417060402010e0105 72
    0x200c940007003292440381084010384140c1e610174010000c580300c1c100304c0760300314101c1e02d010307100006030110b00642d040034100e01400e40a00c01401600071452a141c1c0c9e05500e2446030682c44c1701340c8a406070320000508201145d043c400c1c03495005481000003a81000142c06c5e440e41c44041414901504c01c101c0b25400d103446060780048000d644042d0070300000f4135283d0440d560041e0114003c14020a200d0001d980f109519800d810031b054491910700c89903641c58090307600e80000e1381c01c4050300e0f0303445091554500e0322000b01a804140c038140840e000070401018031515541c590010107842c100c0000f8481c5510050f102161418000c0c00300c134002d10000302d90383d20554002c1e076807181c403039051150000a00542e8600042c008c50110041700142d160002403a045a03040310380000c01030312000000b98207011802c819505040005469400981c00030302070f000b920340c110115030340e4910003480c0030740e61101070320064003142680060b42801c2d803059009220450002440c1d61290340340828061204035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 337064109 1250 337062859 337062877
    0x219121d0102180904030e010c1a0f070f02010c020c010c02010915050c1605030d113c030f040e0c04030c0e04060b030a020901060302030a02090a1221050d0203100506 73
    0x140000f00c032400c0c401d682d41c08503845101200d0303001d1030f410140d801512413480f445103107040c015580010f10911140100c01d0b4541700d80003a00000500d00021040314111045a1250103e078100300c0071400d0600c144500d21121550350020020740c1242401541c200005401c200d0400c001000085244c60307070300b02e002da1108410b40340c2c1a110406c6180450614054500f120030348600c204d0300700208d950004060401a9241c181032140302407100c401810000e0540305007003c54500c10410b412007a0003072040300b8004421104030003202114010f20b44900c1858449507004e4410f102c10300c415012039000075000200c20340351380d150550b00d0b91540040c030713403035071000540c64804c808106c1809914000c243c2100001c0700980500e88030f43c0d0000b0710003007040c06020b04240d400310004025030010307411034029900080c031010000d541d44206070102d110025040b03e41101d01c080404100c00134910000034100c0d692101414071910710003030002508000c060480c400503000d0001410b441d014004c0c60014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 337065359 1250 337064109 337064111
    0x13170304030506130804062d080906010b0f030609090c090c0406170906071d030109081903020412151806020d0605090c0f0c0708120409050601030219121d01 69
    0x5807075401c1503801c0c2035004008803d65040010b200740001c3c103a0b4211820f540319400c2034807030713002040c4402e0b40c01312541140e035031004200744000303141e141c2000070188201e521100311a01070303882d0512042c4500a9002c41040241c003480450894a13003010050340c4040320a0440c1c1d600c011000000700720f00c42c203607000140c45200090912285030b012424070740c1071012080c14445410441c50041d41c03544024441c000f0440e41c0b00004c062a0f221203503840381d4020040080c0170101c000c0c1031032071203036000e181403d0313485520f00d6009400c140a4004d5070211800e075071803050340d0301941e02c842614140d8481020901e0365916031600c035000c16403008441d554011080184c507515101e05203000c907282a0009407040940c90f042002341112001100d840350b440f10703490398580404403605854a40140c20966160040c0d00b10104d40403001c0025000712080064240015191900198124070441c104014078240b000c480080c40da00665027200001c014100c00180c090340c020300310500d81c2d003041841d2074513 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 337066609 1250 337065359 337065367
    0x50c1201170706030b0109050906131b020c0a050a18020715060815010b0307030e030409021209100603030e01031a0d11012a02191208030103030906180605131703 71
    0x103000812840e400343c00030382002c0050202e00310010300f945449226079449110050300207030141d265016024010300c0103907810b11040c8907140380c80e0b4000840710010401803069025040c0c0c1403811851040880d407028041e0309072503003400c0c1c1540c18032145900400c16903400300160300c0000e040c0c1102021036910742c1c0002908a0800008a003021103038035030781c41d5010340b660040c05100313034500482e03800c05200c3c18000354148110407890300314000c582c0422000ba2001c251032000084003400b80c0d1140d00c2000c1510f000034000c00b02d045c122045400b010700000c248071071409507540030741d0001060008980c144141410200001410715141d2030044404d002c1f503011000855810110029a030081940300c206600f40c0c052700c0c51139007410448060312507100410401040001c28500e5009800c0c40512007045428500b44016281e20070b210840c00202408400269284034004141d103621100080d5401e180c58104111130304d800c48124003400300000440050102c50100d00220919107080141da00d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 337067859 1250 337066609 337066649
    0x80402090c071b0e1032040605040504080304020f063a18170a1d12030f030103110a141009080f07080f0304050102120c070e0406050a0507050c0307020103050c1201 72
    0x81710582c0000012002460b41e104480700c003800442c405030f8580090380f040c0d8481c80014010744420391215400ca07282c1420b03c418440407000a5118a0095415402409950040c00780d14407a03040034a08040032039461000d102104245003403280010f080801c00140b03103e185004483e0001521a04102c02c25101800c0101080101240c840d4030000541007015806000c1d1010041c122501022140301c00a4049542c4a030300f100d880321103c000312174561303c03a501c0001152707100f80400e8030f5424009aa0b04002c0c40d0158060b41a9441403051000025503071042c8102410001104001e00c03140e0900410344641c100100e0f0000c2d406200140740c100d2405007100e0801514000190842d0010802409240d80016920303074604d040b151001c1c0e0310101188003900b441d0729500144038401644050100f4000e0341d410150090030044801c1110351983c10b03050328140308400008035190411300001c009580280d01c109c3c2d00c00240002c0034076202c07038075600d401d100e44260400c543c1038641004c1110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 337069109 1250 337067859 337067881
    0x2090c07030206070302090d02010e06040b1317010501060c060b211605100207050108090c03030403030906180609170703050a03020f0708120d1d0d0203031501080402090c071b0e 78
    0x50003c0e00341c21704500d0043c011020801040c295140607051050015108006849800072a0000e010340003480351240c80d030748203907030942c6014420f0818032400c441041042400600ca02812220581c9912a0504c0c050b61840041d1540c80c03d1a50b21004040c07180b0540c00244841d410400000b4016040581c008811127480160075000a40174103181310203c0d20700754001907410142c80007400d00b00390660703c3c03110740c42c503020301115400d80500010a0000426401000701c9066030740d991181113021640003c5a60350048a02c1150001081e00c4030030081040e1114040e00440e2000c03040e22031060f260744403985011802030003100182d100120069001000703200d00d1016102c03d5000c3c104001c0c05184001d124000c4003102c5903495a50030900c8402180c424081480b81558010b440c00e1400d2181f019449402c01c076000016480c50361091180c0358031540c00c580c030036a402003800699031207814018003584c0041008031054045c00031040c40b401d499040c15001001c50020132070441c5444a2480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 337070359 1250 337069109 337069111
    0x90f060801051006051c0c0906030f0e100b011202070f0209010b1e0d1404060608010f0b2b02361509070e0d110906010e031f0902090c07030206 63
    0x45540c1e4548014040c5000d82148681d0448a951a24a407038080800890510765100c1d02107114042c5001e04421400340c00070350040858540381c904108400150f52076500750358110088911036002000b100e00c04500d9075100b81c061802c1031411140c4106ca810000003207903c8910141c0c7c1010449030705408618180300e0040c007600007444a94105041e02c000e034180c0303210000c4840040c3c8400705850071901d1456104a803000e2210070002d08906041c28000010000c038098005c940d403c2c64001da04040841c0994120340c100a44040f69601452000141c1c40e02000090034009009001307060150382d400c4425080d0642c002811054000c0f1000f00e80c91102c0c039800401c03802ca540800304200c002000208004203901039942030880e9691100c11507015100311455980407010034400802d011400e000403816120558aa410310388490005442201c12403440580c0b582c840f208004c1915024940c4403000c2403a0300d030205100c0c0c807580c00104140300403941c00f203000b440402c0300018554100412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 337071609 1250 337070359 337070369
    0x30f060803072312072001091208071b1d0609070c0f050a080307030c020c03120301060f020109021804020f0405060603160512090a03110102030705041203020a020307090f06 76
    0x150320344800c955500e0401405071000c00080d59215000c08080a000d04c03914a03c4403c1003010340d80c4840f1032802000d83c4103000c1c2c00031803851540701d0400c0654011040c140940b030021515001760815541c801000d50700c071403000c4075031015000300384105101c2c50000031b000d008040c82c022202e003d0210081150680104000e12800c40c680500080340c0d040110007482d03e0b0440b00c0305119240b0760606034606100d0040044c0154000010040d060703a240d80900102c007841d070b09580391242c007281010b41d150303400216007110318001c00040014900a00070960703406164000410102c038181c0000c6e180b40b4410b00040d40340141c0904210851501001d03410440c10201c0e01044942030900116501c9e010050520811000c0c4220804400e0300907801e54941c2109050f00c90300500d4091015901d924030030303008030041a00d4400c44500140103000303480c440c0c0d015039100c506107403404609100300301800000390254010303003840c2070150b18103200301b4000d04020480441d41d403c0310a03d03007080750308507440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 337072859 1250 337071609 337071613
    0x60904090305040e0c0f0d0e03090907090504060807031a180304030f0c0608042a170a0605010b032203050405120c01080709050f060930010b0603011d04061b030f0608 73
    0x1403a0301b014440341910b250400c00140010340c074130340d07043d160710318840c0980d00d1303500922090402400c0ca0b03014a1080645000760340511149581d004056500c02c82804010400304008103e021580d44004205a101c0c4540f01012044101480c4850a6603c150401c0d941254101208418000c01d101e241c4018201c1d4600740c00c0c20f181c19211130482c0040f40480800c41d03580d000a1300703040074052010308041d04450700070581116049150350340e23808207148110b5005007810000260ba00f14102900d100e24510f00c1d103256000180a0300d034881d1320041c0002c8080c00f07414480410140c4624200d0108a40c203080280f0404030040e0002d01240001030550b0304100c5a000244900c0d21a038651070085241070324200d07141d116040000e11161649402c518607180f03034000030300587c0800c0101041200c811350082081110700000d110941c4401d001d00700781101800300400041201c5429254454000c1d040004d806409101540741c03031200003c00400213442c0c5806911900c07162051400030805200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 337074109 1250 337072859 337072867
    0x103030e09250c080903031b01050c0a090b09151b010e060c27180a0c0c020a150c02030106120309050d170304050109020a0306090b10030c05040b060904090305040e0c 73
    0xc0507694410b032002c500c2c100007020014004011100703040d180c203004c000f000d80c1c1d2a07203038031110b201054448405619a0358205804034008040c50001c58844044030f079242c903101420501700240a50241010f9274003c0590108507140002c4c0501401c088040f800c45c5050b1070081c1d001c00c0d0300390b5044d500c2268035500010284035501500204032944083c4120800740030106400c0c2d40c100c00e02604854a401c4402c0031035090540c0d4600000c0b6200d185409801c101d60411a081141c05d0140110000c1d08080c452600f400b04804890310101c03104250310b0106c0f0300c00420b50103c0e0075142c5682c0034011414040b2001c008154100344840041c00066400b5074043c906a1145104203140c22f88441d90800c00001040c140402904012801500601900085039503480d00390001e10540405031600b05681c0045122403d2110000c0f0450303800c03c030342c1c1640500f0042004010103a0400700ca922007000c200c40922a1254080d040d1140d000740c58203500c0328900300d0003042140c8000c0c18002250030401c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 337075359 1250 337074109 337074151
    0x180506040603050402030d02070e060d1703040b01030c0e0103032003070609080901020d0809100506180405150106230f0c06010f06140403031707050f1216030e1f140103030e09 77
    0x2b80c042c1d84c0100119100492002c103818081900c48213401c1c458011a00001000140800e2004260480c0c0c03040c40c4194959584150f0700810f2482030100a0004200070807402103404415440081d08410348140ea01d4941c080c5d9503030040315194481140d03025408a1080384a41e0103110212564403d030403c410140307004945c00da102c903403050040209580d1040415800d4035005a03601e469100d1100600d4070b81451300700259030b44190444102100900d40000c1a140e03c500700149070159640f04041c038140400d4401c500e541c01c0000e4090440030140704c00c0b81e5581003080894001c050940790400201c0c03c144004005d000d6a1094641012007000200000799102400d040f55610300c1c4d1290440713480c1d00070112414840c0035400450810040b6207590901402700105009070b00c2d00c00d091141903541d460a030b09071404004071010540104500c1440850380d001400181e1114240000788004120010721800f10280c0080d00016201c02e000c5d9964180381c92143c1c2c004018802e80d0484030401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 337076609 1250 337075359 337075379
    0x10b04090f1707050a080d0c050903030a08090c0d03031a0d0b150312030901050f090708031602040906060b040f050607080403152d11030c040501180506040603050402030d0207 77
    0x22038070051080401000b05000001a41c00f500c407070950080555020712035074104020310f904001d03010040035241a1003001c5003801036088074000325015018504003d000001610150300003083c5210310300441c000074042d55030300342203045a5442614009612000c07000052074001200f440103000380909087c032408904003501265001041d00007041202540d040468184000c80803030a00c80034002c410b121103202c041d04403920036040350214404036a1032a80e10351365200f6500c80c000240d00300f0000c03c000c40d0540c03243d08540038005000400c00b0205035a0341e0f03040301c459500c4516075941c04075007804540c40c2d21340047e0080c0b41c1242c0e01c1d4200419030320750380c0a81c411072000804042d06050390009042041d0025140b124a0082c03121034000900a4003030b840ba200d984602001e807070401414115180002901c0c0224404804c090409003001d0054940c00d00c035071101e00d440151014001002d640740c0c40284064482030f07401207250309292051500c0c10780003446500039500702c4c44bc10302501001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 337077859 1250 337076609 337076633
    0x304050a030f05010f0f0b0f01140a0f0903050307031e020f070e04020d02130204080d021614120d050a1106060f060f0c01060b0a02060108061306021317010e010b0409 73
    0xb00c21861034800d41c504940103010030601c90305031604012901002031206e501401180c00b0a4a5818454400d600115502d81a104000200d54814071407040c0091055428185000240c100a10307115100c0d1526440c2da0056401100090b42081d61000802c80a00c1c800119034194001000d84c1e400030708005489607020f02a6100c08001140050b09558038500303074001342074001e024540c00d0300200c070782e00c1c010b0741c440d002c1d4180314460079900210440c40000c0c1c802003500c0c115580c2c00501e0904120066080009411070f5015840030030210030303c4e600740401c241c82122621103903552f412a260117441c2040305070780e030305541d0029020031050352102d03140300d0f42c07000044484603510705412089215501503000c209030503610b46000402c110608000424550509800f1604142e0303881600660f203040803503186954900c14402c81d800501c2607006008401740040c85541119142c1748900f500079103d90010080d81c1d150038002070b00308002e1096584284040d18140803010311502d50a6038181 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 337079109 1250 337077859 337077863
    0x4090c05070b01211a15011407080306150309010603030e0103090b070309080412030c0b0112030c08030703180b060103050106081006050c2416030203060d1211030d060e090304050a03 80
    0x1680026042c40f41e29407189180361a80c2c0105c600346484d03000e004000e0750350000c950004000c503a90a6400c0390b580501201d8103011541c40711711780340442c0f65403000403a81001d00019000003603017503406040c000000c040d512403090030000082444c80d42c203000f03108400c80d10b01c1302c2c10300d441c3c4150000400c2c00c0300032050340424542408550600c0c14649801184111351010783d01c00c0420f0080c0c0c041507444104101c50500801941100da601d54520b80007090035400000c0114001051040000e0b85c0c7c4000b03554000307414100054141d60207109000a044010400c40c4d161560f801000560360f0175109481c051305440c64059074919040c06d20701c2004a0500551061010104800380c85200c10000700d00c0a00740c10b00c1d200c8124038002c2c2161076048003a1940c128030300c80e00b1070024002d03100b8400e0741d106040051094a8451041d00d0351030958503d0070007542000007100701c02450074002c03c010800300401100001c0d000e441d05161441c2028007914040c000e4108000401040c0d84000d40442901c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 337080359 1250 337079109 337079129
    0xb072a020108090c031204050112060b070b100f060306050405330d060e01020304031b030e0f03030d090b1006110703060c090f081f0902090c09040b09040804090c05070b01 75
    0x9110060f546280544d00725110360705110f50f80015990220311009001124020f8030f41c1c04540c0004a10102a00c620b80107100c01c0080038410030f400b00307181100d0300781c00580340b04031150304644550140c20058200e0f085040840d48525082000c1c2c02c141c8501948854402009840300c61854081d00c210141121003000038500040750080c142d640714200042d8640c4107a040203001d41400c074150103500200c42c1940840c07100c01c0383c206500158960240d0b06a45940c070b82d5000c141c904104413003814100381035601407000f030207c000b2208680c4203004195015141a005500d00f204112160345026040001002007442c400e42103c5400520881640d42c0700300e01003070f07010141c402141c661170158015200070302899400102610046001d0307107101907540c102007064480001c4032013a15504039000f500326103401c1c00500e034106000c000e010350410084c004200c0c0400c1c074002641c040c0007070701c09480c10710000500700a20704440c800d0f5840b0540030b00300203081020640340c2602a41c3c0c1441040d0b100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 337081609 1250 337080359 337080361
    0x8010e161409040203040b0f09070b0301060302070314160c050301020a02030f09030a0b011401080121142515020708030d15050a03030c03030e0313061110090b072a020108 75
    0x40c464101c00e5840c24140a4402c40d02c920f42428603001b1150140e030748007441e10000740862418107001c95410305483e0003180351459079207040c8046000394402c0380c0c01d404110041c84980014424a8010644500303041e00341240008203081451030001c0a511803482a0b10401c000d20041d0340110a5034800000c410605407200d0341403000c2410003500c0d2000038a85181040080703510f415104c821610100c1c00c1e0f0301d054003a07880d200180301c1842215801046220f28840002c0003918846040c11007401c0300c8140c0ba90804069081110000c0b42c1560412540841105100080c4030300d0b0142c2c826006803000f44610340c40c00101685070300c2611310040c1c00b90341f5010705441140c0704244100c01001c0c041c0c0849407480c2c1e241801810100460000c500080c01c01e030041017800400400d44d0141d4924640441030302d45050340540342281c0051050029009000c0d05010121480c8a40a000c0f40030b01c030941010300d4035800042c1a15641c502001c120106840f6800e40c0c40c44229404d0401c580c2801d0050742 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 337082859 1250 337081609 337081637
    0x9060804060e0109030203040602060a0917090109090e1b040506010c0219051003020c010b01022e0b0d0f14030f2b0e070504060506040b0f1c020d060608010e16 70
    0x7030b211480000c011903080c403003042c040550020040049844075402c0c0c0d0030580721000b0101c103441c654100600981c15101c001c0b44000e03514001022600d1050600c1c512841e581c0c030040064490030082044a60003080302c0d01c1c41201c60003551031611404071000c0080c0c1c85d000f00080d29221108002900800c4c1400b828041e40211441c404003504c1c1c010000f007040d0b944070200402950200c03642c40a59400c06410708060350001601d1100c150391180ca0140c190840d000c1405c1c03010146030138040203070312150070000325101c543c1c602d81824010807022074240020b08010301780030030034101035249503c200840181c1c42e08407000c0d61801c0590707950101c144222a104075004184240f54171a07a10f24111110700c452000090320000c40b00e05030340c02d02803969200100115402070b4031480d00c80b030404011911a0307100b510000c2030b5154400c00406403159040c0c204400302d0704a08549a003483d5900414030000b0741110304280100308031144003007a450800b0320b4201d54050802500c0c18400c0800510701 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 337084109 1250 337082859 337082861
    0x2060103050d141e070303230c181801080105070504230f1c0203010507140d230906190b0607020f150c0a1208040317040c0e0c0d0f0c0906080406 64
    0x50004e80701c128a10398464500303440c41284d17018020403004207103041c00d007051a404d490050001c5601c8040301d07442d1683c1e00301802c1c2c5654040b904c2030000f03002c4d465004002c0d6465040364040b00b0f0207a1403204c2107605060004c1e00b1594089c106000313016003444100140c1c410040700e110061000e001c440186c1c0019004199600f1003541019482003c40e0701c1d6a0303a641c07164407004000c0d8000c9000303120f01d40750410141c40c0400d005404018101041000c41c0f008480ca402058000c00c0c40b4044002c40c0c104050b044240020035151000650003200074490020b1217000304044c4022406001c20174950710f1030000c1c0044c8600d0b04028040c800103900200d230b603622800c840400e003400300807403651118080c1d1401d445150300001143d10589190110407003c4c840e8100300d116030780c0340e00c5e8031280702c04a4140000c0e110006100319a400c1510340007241455801c24418001c0f10780740c00003030b181e42c0f644d840c100903215415006c8031114908800c4134506a1b001003100102e50403804e000c20140c03101d0034288 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 337085359 1250 337084109 337084117
    0x302070b0301150201060609180513050d0c031107050d0b07030b0411040509090c01202514030604020a060e0f04021201030b130c0e091504030206011502060103050d14 73
    0x1040240c04000040c5081c48402440f41596040c2d0003000410b844002c1601d0b00001405110740c00d42003114040102050340d0700c599000b41100c080e20030801c51541c0c4940c0f804540050100001e40740c04019000c040c3c21860000107200100d0240c405103003001d011445261a540b400f6010440f25408500030b14025400941e038840054001d00c000040126000e40315405446201c1c080c0004a001480055010540640c84a0140d4420001c101400d1401c140b01c90b4209981c07085010f4035100250790381000d10905982c110502c2800d505925084a516411791054051402500003904000060791541c41ca84c05072103450415180101c2400701103a00c0700c00601400c0c0e0014400183e00c1d021564100000e4101d0f8480c03103035840781d42d498034040c941105261500a2648288100900180c201c604585500c412181d044a00550b003074540c00801c2a030540b41a40960800001404072154281000704501d03e43d000034000e5501d035560782d560b1110841ca008040009142030030b141001700c04116 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 337086609 1250 337085359 337085369
    0x1b050a0809130c1e111213080d080124020a0305030a140f0f0702071a030c160b0402040b04110316050c0a050d020705010f0e0108190608060f220807030207 68
    0x411140103a8030f000b07008100c403107980f24801d0a0300401045200d01c680c046900940c0190060300b6690b000d061711034920b03003044107602d0158008200c041103100702002914101c02c0c2c0c41c1d07a80c0b40366514142c03069030920002c1c408055041030025101103240d4001400b011b00941c1440c00f01d5480d0303101200c1e100102520340303010000074505001d00a007008440c00d510b0080303074842c01e003440c540c0341c901c000d9a9900040c461581015a0540311032031310f4909002569000b945401c80e60301c0e02c605180d65a80080740c84804480c2d0b0700205060000b9418188500c0002e1603040d1030805c44c4151100080c40180130080000700b200c90001d055410342072040b000d84450542000440d0301035045407812030303110400c402400c1c2c01845040c40000e002d62180c0c001440e844415110001c4c65090040110340c0c1100c000d00385910040c4c110308409020f1864403c0c04000d1103804050701060400c686901c903401c1d00030342002d03160010200520201400314190210b086d40c03168074190707a10700d10f103400d03420300300c4d50380c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 337087859 1250 337086609 337086611
    0x905040501120f1b03030518030a0302060103030807021002070302030c101806020903030706020714060606030c0d0213030c06111608150a090807120e0118090c0309050604080a1b050a080913 83
    0x130000c101904a800352079003a80d84182e0b0303103810712840207256540e00707200009001a4070100041001c28003c0952907000303055481034640b03a035040c0100c103041c1d90015200f140140e20016130b0107051a0203011404150320042e00a22502c6150103d44120120310312000d880903038005581550b0303031340400c11180350540c001402e64803042603050450b003440b0120507403113040c0202400a8424581201124413035942101502c0c2000e800703c3c001d400942296000d40383d600f21005010000c11042404e070402002e1a035280e1030415500448141090110100000703000c4c4d43c031400380420b000c04244070031401c2c05000161000d55800755494054925488050144130b0001140c1090108520303184003132425503102c507103c07048a1401150003c002215400b070320164034809210b0b204241e00600c025002d0f528000c0b0750001c035611740f2810301c1310aa07400c89450740009034112165030048140190040004400040d52119846083d01c1c0c0b5100d2030003d1036404000b41c0811269604640e000076000d1201e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 337089109 1250 337087859 337087913
    0x2090a0308090a0b03060108070c02040e0f0303010f0b0c030a0c05030403060504060b040b0f09060915090c040501030b1207060311071203140c09180603011b08010302010905040501120f 81
    0x400c00416444103102d540107060b600c4001c00c140b03d81c401140c1c015071040c1d5891820f82d423084000c98030702100603001c13680a6115481d406000404015214429a0403006507903a07502d84a042d0981031f1040c0c0c040c00c1c00203818080e10b60714190100540702d01c0a5141000d208121444c07030175a04500c100c0d080140000c0c681003e2009001a580c4280540c6006907000c0011940e464100704580650b666100e030b008000034001401030034040b82d616002041c9121034181c0c0008040011074001003107811103800c040126081210f5039040c054405070030001d95414075185c0c9144095074640c403042c0240c00900d9200c0302e21902070b040c1d10302150000b641001d07001080120250005020b8540c5481c0b07101c0e9010380d580402c0c1e100800800f15100b80200030201718038285c000c410749000d043e00803c0f995140d562100780d0814820100307142814140d46a842d0200c96040d44000741080d14140c020310f01513417900f80148154260024500b21040d0009203802014500c0d18028800d402e500c11500c900b00300100c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 337090359 1250 337089109 337089113
    0x3080a020a050415020d0909090f0f030203090402071505071718070f0306140132030c03071e0812030606030a0603050f0d030f0e06060603090f0703080403151a060c0102090a03 77
    0x450703e44100c0d0211f030340e03416000f5900d4221005039840d1100180c014804100040002001031080e03040f12032280c01601e04095a0400180490308400410348402d4180010750043c04110720416500465038240f528404c081c0d6201503c4d1030030010100400c0e1921340b408010b154030104000700040c561504a204141c0d140e2800c3c034064281c0440381d00107000102c00202d25040807405902c0600390b44810702d01810112000c1041e0b1503560381c00f01d5010f0148035011015500d044c82814060300108840300c0440c8481007150f101c50300c3e140c0c400140d58116682400072155a081125080a01110081d8981d1a0340d180080101000e505c01031a5100b981414203080001080b400c0e07441e4600e8404004a4110a04200646100050704840303504038000150091810002454110305440110b0f0414a031205100e0710741a011780081e1504a008201001040320054038145890030010040c00302d83e410240d03040d01060713400c191500c80c5001043d062070702c090950550310740c400020301d103490940c4e43e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 337091609 1250 337090359 337090363
    0x803040308040801050a0e0318010509040f0608241b090d050d03150308030406050c04150309120f08040308090a1a0103050c01170f22051e01060303080a020a05041502 73
    0x2d8410714005501305000108480e000c0c1c45060302c0395110101039894003c1203151102c840f41000250350610005105030200790704d5a02c5500c0070b08030101d80004243e4104000f00f8504910000c02c8500c1e11003002e170072114007012800441d0000850703421502c0e0343c00812aa50351601900c000c803034002c1c0034a000f103000e00ca800152080c804840d500c0801403001d40b03401070b004034256800064104001040840c000640c142e010716130005858103c0f505080d12544244018412011403800080c0c41f40d0300001072084008800180092600f002038031200004c50180041034024006824405408000b0362489024007030348083c142d0007154107068840d14034000c11001004c0c0801e50b202d102e007015201301c03540100c0d144009007201006440c0c0a640d001c0c41c40ca50340b000206010340c880c4001c00c207a0048600032011f004001e120b40c0141c540c0d440f4904180d40051b1061121251070fa061803001c1011036040891160050815100540e0300c0c0c95101c1c00b51110700c12540a41e00035100600802c3d80300c2d0380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 337092859 1250 337091609 337091617
    0x140103020907050903031b0307020a150e0a081f110a0201090b070305040503030109051b12071215050d0f020a080708102702010905210c060c060415060803040308 71
    0x401c0792814407644410504880d90b00440301007035010381c0200b0103444036000031007140701006140c20071a885d00c0003660106201c603126034070503401941d02d9084c02c0d0440340c0240c090160000255a031000d614504030a1305e90300e50003c2850000f00350758016081d138111483c0c212035182440e600003203507070b22440c0b80b009000303249101d000d517403071006003011440c0346101c0e003d1280101d41200045003964203080403c03008150207018980c014245003041e0810403841000342842443c612545e151a240410700a4552032540c4645003880c5e01c0d2540003000c003a22441c5407000d817041a034a6801002d414540820561034030880131f036010300d0031309000a030034a00140c45c0d030a480000781616628083c111504d015200140410310801da900c01684881280f20140d4101540c0145400075410ba5070b140403d809120841e020a616800b08800c008800030401a89a98001c140e904600e4441d01d81059a01c0350006800200020300c0b0120728071143c2540d403c000701802442c002d4940d80c0d5940c2c5409812988 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 337094109 1250 337092859 337092863
    0x40c06050306031222050303090a0317130902091e06180a170a050d0e1c06150603020c010e07050d031b1e060f0c0e040507200c030f030f04150c06140103 67
    0x14805c0c80801c40703080110541300c800401409105449085982c2e41000014200009070031150502950021034440700007880106045c4100596818850f801d022500c520030302c0c0c8a00440407051120041c0d100d0600f00d80c4811507000071813a1a07108140010000021940b11100c05078141c000b0380341810001c1041e14403144168211840c6c585c00d07560580d000307050840040c0e4000c0b008000060f4518107071102084141c4901c0001803211060785008911580303d8010100082d400300b80c4440c080c03c00d114004034540388400910056140c2400110001c4e81c220004041204c100341d20003005010b944802c4d9010381c490500140d4610042e41d1002804071403900b0f817101405c200311041e141440d0320481c0f01ca0340d05660f81300c400c10a00b03002e20001d00409090724042020100c44201009a284950b4405803010b0020304001c02c5807104040c6080c2c10111418141d800810160150b81451011541150740240140600f0608a10251919014002c0243c011030400340d07900b907444a0300302054141d078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 337095359 1250 337094109 337094167
    0x10b12010e0c0108040b0123030a0605040519081c0b0d03022103010e070305060f0d11040f0605010c11010903061103090d02070602100902030703020a17060c03040c060503060312 78
    0x10000d04011210513074251009040440c4000040c0025007800c4c0144000009403a070420b200b4413240e01091401c10032074070030340d0b44aa940c0b0a0108000d000e0120310040482051303c02c1c903001d00c586582e0b000f071142c030400c070a03218004084069010074136000545c0e181030092450303e280304182400380d00c1d0440381000303130101d00315100c0c030b032060103840400d582c142c6036108010041c545c0c070003000390000c0c0409410ba9074042941c44c02d4000941d221210380446521a6100c0c0300d0542c1d40d002440f0130780709510003040540cad04080c0d0601959a0250f4100800c0d82c0200d05580c80c024400010b83c0e1030442c2c0d42015100c0c0303091030315440040708c146000b1401108421304517408052040b1080340c03540c10902400d00180c10103c40c540c000074881e0008840c160006041d01d070301a13500d0f400034401d26000e901ca00401c2c51340107288942503030709100e0030780c0c07241c1c0d801c0c0e00038a0f42c03406580c3c0c040d08441034000d05060260100201c1c146482c00c12110300d0700003800d420140d40d982034080020100300182068500c0d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 337096609 1250 337095359 337095373
    0x41e170d0f0f1b031701060504030204150509070c241a09010305030307110c090f093307170c0c0c06120414122a0303100314010b12010e 60
    0x1207407062201e560042d110380d403001444018184816620400c0300d006804110300c418014051004038a0703013500030071094030340b140d8591551050005591131020403403401c0c80641d47c208266120010081d030700040b1490032030f5440506207403000316801c45038401c1c2e04028280700e070f180380c014542d07201c0b2040240d05080c450141141c0c1040015052003404000d205030402e01c08500a580030b0454110f020002d0070036641ca4007494004120704510846010720410810414400e40b45000d02010304508400701c2c0701e003001c100780d580000200006100e691400302c0391030001240b040c0300d25842480c00c10003070400102030030300c0ca1041d1019000341800c140c1e640a180402d0310343d49000710840e40d40256803050100b0961b90b507200d803c6440b140940700e100c103000710841c405514005200604006c1118040c8100c50510000c56080c1d0380c0c0c1c4403100e12a40ea00800910081a00810b0071f03401b00c9901456a418134000800e02d540908405800741c2d420414108540040d120190820102d4125800c02c0340c41c0e07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 337097859 1250 337096609 337096637
    0xa120e1206150103020f040e10030b01360e0604031806230f0c0703080d0605060405061207020712030206090d03050105060415261501050906041e170d 66
    0x68000a4542e2008280e03005588011540250082d00700706111006031401c065071030100340325480f002c4800000e44961030350305208015010007a2405040c005c4841c9100c285032281e4840350400a8509901c2c0010000da10790a90526420900d48601c800003500c071941014940074100d114902400c000c140982c1201041040c49419225101c90060741000410b621158035481140c0c1318035440c58001904112001c1c201000b009804d00941c8920348281e6100407038084601128016000144100801c1200b00440c3d42c0341800e80300382501902901805850300d010581c40d000043c1d100d040c002001d10382c40024950042515031049841d0340586080e04010002182120404d0080729800340003400b003030048202074082061180c600d42840c040c1d0030000c10115600c407041d581002140300b50401041041090f0120a00107928207080c00b03414041110001a00350045020380c6043e9074510124807096200075081070000c1c000e0a003880034030b040031441d40d9116250714060074040742080c00d107455 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 337099109 1250 337097859 337097863
    0x60602151503120c0f03040e04050d051606020d0e0618011d0304030f060e070f0302180118020c030f0703050a0801080a150e010b041103010801060515040b07050a120e12 74
    0x81d190344020041c20095000c00d000024a42040308004802d12a018011049040404c01400605406294401c003458603242082c07920a00c9201c02c420040c060142c801c510120005102144c1d0380f040d40542c41b02c5410308903000410940284006a108240c240701c07900c003425104000000790340000303110f110000700724281d030205c4802d084541039104000420110700c0c01204020b29511400c00441d400424240203803800703007580c1244110f5071585000b0021403901c440004608410014251a00d602d042104450311451103d040441a000549000b070308400340100c410740c0c0f50094800e52035032410704004103182c101d6161078000c1500325001080404001802c00d68607580400941b03602d858000c1030401500c504540347c0100d40d01c9440b030700ca45075658012a41c401d810240c550340c69600d01030401e801d413a106c0e07002a000f400045444814a44000308550599146500856590b03141c1d192891034590001070290098009030010880142d101604284640b01120007001600e48407442c55 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 337100359 1250 337099109 337099141
    0x190609060e010e070c140c13051006031505060f0c07060c2d02120a03121104030210050913060801050708130b060a0504140a05100806010e100906060215 67
    0x210007401c00c00d0040143d000d003c1180e650102aa207454809501c841d07642c00450801050081e109400018541e03180307080045c280090140c210a0502c040d08000c06100c04003421401500d003011b403500b08664501a404244600900d4050960303a0307104020000140e580d0841e642c0003101d0302a420303001680340c2c491000881c120b500444441448148281000502a40080403411904a07540518056541c1c1820500803045003400307860300000c1703880d001b80056842d204442d101c0d4501003000c02c1084281054038145c176410345101c0200c40301034005640501035421440d90011440726180b1240e08240c0004c012114044024000c135141d500302928800001c5400b940d0002810b050b00021844003141160401c0c80075001c80300107600d07a070206055840904510303081e40c00040a0100c84543ca11074954041a2034245525090606140315200d40040c40741c03042201d086404140311254034154000102084201001407640e20800070b0348414002100100924100c800034001841070040c003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 337101609 1250 337100359 337100369
    0x2010218010f0504060302090f0a0602010b19080705010521010f06030605060a140310090507020c120601060507120207090c0e13110d020c1213050a080d08010501110f010519060906 79
    0x14200303410302e05c04030000e41191404650060103550001856200d8840f4000034000c541c2c00412143c4881050003204030203130f04003444142c1000c104210390180030a240f425150240303002c0303640e03030301d00c02c1e8000c1070400020b8040c1081103100e00010700c07940d4290340901100d01d983c60911082d0340d550108a814001d491101c00865600c2100b00b10113011315009503481107821382410065501c44035140d040307500c02c0b00c0300170250b400200402c20345d107800c0c19039603401c481c050020005507042500082041c090f0740c1c0001c200001d82a1400e207494024010754001d000700c404100180c00040d100102041c8000c0311450080d420040034103c00c100e40c2c001d81132403000d030884051130a000014004002d520440e141c2003907000e44043e92408801540c010005221141c3c0300500d0316003480d0400042e50150340c0142d130b41e0b80c407a4070f0200c5007035084104141101c10908003c0e107041d142034103190403c02c2001494450b5403a01042000001e00140198007334070000d4000c0100e04d4403078400104a84581c022 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 337102859 1250 337101609 337101617
    0x110c0708010605222408100b030d0e030f0609150601030c170606041d070806030303042f040504032c031c0c021009030b06060412141c02010218010f 65
    0x180384c110503150340c07145007410002400942d015450780f821040100203c50291800e169640412110310304000441084845c001300300420600c10000955035041d0580d030300c1c03c0c0081d04054100c0c690f0280024030151041c00d044e030f02a840d0134441940c030703500070204008080030b009000c03510a500c43e101d81d1500000c0c80c1c0b203001c030403060034907405a4114001e14990348903004100201c0c0250880e0034540728ae80c03908485060605000c5405007110400030310890091380184100b01c081030200c1217440402c154501d405011030b0405104280091040c035029400505081c02c0c00b0403d0b5111035612090a120b03c00f14104440309100c40b09520201184a81e150740880081504009201e1003058024060f00384103601e5001d03540401d00322001c440001012410f410410020f000022000300e070b224004803583c0c0c2c546414400007a880c0603414902510351600c01c55050702c15481001503116005840100100021603410300034043c0d0b1202846102042030640c0800d6254020ba13907038000c560154032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 337104109 1250 337102859 337102879
    0x7080f0a2d06090c030e0712170d06090c020607030b10090b030a180308090c0f060a0302030604110d06180e030316030b100c0b060d0305180a0801110c0708010605 71
    0x2289031100c507014411031500c0c0e0341d400000d540a40c910030784048200e00e80b0085410b1041c185202d04108041d44028040384050a0b12400103484017112505509440c06290700d440342803d600c0001c20f01c40e000198030524200c8601002030b00044c0e03081c403a1a82d41e4052110381400b0050083d5042443c50480104222a00c00d0254085910181d40d0240241c00c00003118a000c081e844c03041b199210050740814201c41c00d00200350801e01c00e010880106480000c02040301c40d010aa1502c601c010b1a0100f59021011911613a265001105d50410341d801094940d0b0620b00204001c06181c411407080300c40000709083c41c40090b00519181034007480c065800d55407005040c1c444485241c40700402c040d03450480031429941c034000407920401c180d441c0610700b501450142c507000d5002d003040d880f030301e459024000000c1d03011007212020307100c02e03c1d01d00b0304100d20000304020000581000c5c120b5401c0000305114040c941d03014060000080003103607003990741c400c151422254540141a004201d0325 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 337105359 1250 337104109 337104161
    0xf0c0806121603060e0706180b03092b1205060d06050405150901020307120902130b0a080303161e020a0b04080d050f10060905030606040e0f030307080f0a 68
    0x1000701d810180070340180c91040708010a5004801c2003038000f00c030107a03540c01010680b4202005020060013840c00d206451203151100301c060000d040c85441001c001c0000014081e200c288140e01c49070101103044800da80050210581c4100c41410003800555000c01e201101d000c1400703218000c05001e014a0038060694585401401c1c004000761590710a100342c510060f41050b010303601c140c0b503039000141c41e03040c4494020440c2c0b0102104a40050400440e100965034603603100c0c1e0005080c21002481c080b040300851f10648459001c010a8040401001070040b05040900342640700355441c1c1d8490420710264441700c61419082e0001a441000d00c0b8000402010595401a001d20302d81800e00d18400200302c10b40e01d0481d000780c0c03c115100140041c0340d40ca0344e4000058200b0341891807447c0e04040c04030395204001031180307205586503110203840d194280079110103511a902529582d02d4004000341820100707540c4082d8004c1d01c4c1001444041c3c0a1065039480b0031252a01c040f403003080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 337106609 1250 337105359 337105369
    0x41404050a09050f0f01050105060f1b01110705031801050301150f0512151201020a120504021201090f0b0604090305072405090a05011b0207060c0f05010c050705010f0c0806 76
    0x4005280456440c2071076404160100084095000c6110003002a1154098003500352441a400b50740128018031507400c2c04102ca0098610cc0302c155400c0e0b8144540300c100c56405024285480d01c0810f80000c1c561017031106c08002406a24070111590045502041c01169140310074401c6e0a990380350107070610f180c240f02c1c40800c07c2c048140e10300b00d4200301136803850089002c0207031140420f00d0540b401061640c2400c004881c01c0010a2008509209500001a03c0240410a8035a100c1d030395000007411503a0754072500d4a5003100c0d1000b000400c0080c5444400107034140001d40d81030545800141c402e1070140200c4418550641d0b8960501500f03903149246501d58040c00c4040c0200d50f0703080c080d2400c45204081c481d14014006060203880e5041060851328140380f04040250b00004120020740c002441c042229170a00d091252074169041c242c030040e45907031005020f9400d00c00e00310304c199840009410000d02400c0200000400740044034101c41089010401040102002407480d00d85 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 337107859 1250 337106609 337106611
    0x1a070b0c04030b160201180803070c030c06020f0c0f0c01020a1104021204210c0506070c0314030f0a060b031924180b010f020307081804020a0903030f0504140405 71
    0x2598200394105922a5503160031041c0482e0040b40c003c0c007110711481510703070900600c200e40401081c15906c40216407180c041d50301c4001c2011041c40780380c2641c0f900f0103102e0f440310340c03650350040411511001040e03410051540099a506071b24451620300402e11007021800e09030001058000301032603405179440c11540d14500c00038030351140d401c0c001000343c00e141199503403085208003001c0c0c41d0b4090303101e9a0b181c0c50004210000400c038901101e1300000300002000e980150003070400380442012807404035004800740c00d629030b03807600c00b0003401420400425407500916203c0300500c540354440c515108070b808215900c20032043c02c841c1c078074150a030036807000041c0030bc03898405c3c1d55000d01c50355100050010364420f20000f046180001c004c10344610640349507030030900c0e0102194070300105c000e40e41e0061940181c461000015050038242c0d0000c0c401c910f1141c06401551107801486026000e0800c0f0310003a400329501e5a44c1c0c00009204404407801c0d54556034003203c1d9402c00505004c000c1070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 337109109 1250 337107859 337107871
    0x1b100f0f030e0109030206040219051e030a051009020901150503060d0804050a0308041409010602060a0506040f0c0509010f020705060708130806042904080712030b10030906061a070b 80
    0x140d20302d144a8906028000d90b51928001e80041405080a106020742c841c440f84000500c02c808001c280701c07541c0c134640320032003a841400c141030408040b100007905080d01228014604c2c441c10030042000140c9400548070740340210780401d101d0713a0f52103954081d122503460a5001035002c00001c1c4852905180f4003410b64007486c0d1642c1400c2c0c403440890340040d11a001600c4242000c0703401c2080d00d98070b000d0038030361150960b6040015494414040e69401d80500104001519207000802d01d4407287d1260301078000800051010600c4000007909560250b600103000400c010403010131b1500010f5a10300b10342c0701401c05480d00d500d50311401c01c550418a1864610350888000240007101048145e0080b0301034003a4070100c0f100c4880da50b44112880c0840b00800d841c0c00200404620740d0740030344251940000c41603131401010b42088000302140490301c0e0348080311a0500c0c1c0d4685d4035600448400c1d1007881c003000146c3d00e81042004403e010300700d4501d40c960030400040041c020b100402c0e0841 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 337110359 1250 337109109 337109111
    0x7020a02010e0d0f020406061d1c1514070305091b030706050906040306110903210304140102090a0603050901180c0504020a050d0609020702040615120203070e060c1b100f0f03 77
    0x4c001d44c0050f060b50241d030b1003c0b00091115a01543c5172554015814000d1421510003002d8050401051074649840901810082c1e9880d4000200b04840d007110070002800c2086046030315080300c020380203040c1030307036402aa4401c601000f0158200f031044c54078040300043c001c003841361411008035503941c031140d2400d801203800e1200200042e4140501c200c0b802003a2420f035110040c0b6018545841960281c0b00420600c600c0710b82c40d1750455100b1a600f1503044520406005050f40303040340a03106070540a0780180400c60001005513060b440b5500407000071009008204000300d600460203050100038241c48440c1c002040185010350040c335032810315017409414840300c002a241101c03940e0341b00c0300c4290f03000075071902103150520451028194000b00d80341d10380c0c03200100030800d10092550003142640000800c04143c01600030b00051000204000e0791030041c803224507103800b140080c4211607403148000d1041e5103000c0d2880e00b2001d259950780b122100e102c590840c1d90449610804040c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 337111609 1250 337110359 337110383
    0x6010c2102120714060601052d19080a0e010c0206010e060406050306010308030702160602100b060d020706020415090515130e0c0703090609080c2b0b04060507020a02010e0d 76
    0x642c044001510105004115a03400540000d034500e043c100020402030401c03e007080304856003a40580c11040100c5090102c2105200e541e00802503445441c4e150440c020056445004103940030002c00d101c2d07071110b4000c2c0701c03216890b41820300381d0322040b41d20405a0040d00c0140110055140180e51087c801000858071a80e00c9000c641806021303002a0b6424000004000800d601007283c0400c601a45103542002450410029198118500c440b0b42c2c1c2503c2c0c03200c1d800700da91148240d0781da80d03040d9402150399960034905040250300c14800c02c0f80300610010008a00d5025107412021a81e010303041408608000010444507841056042c50f224820800854280ca040c20f0141c8140e6414010f00d980350700e2400c02503c610b840c0c4c0d02000070809203c50a1001c0c5c80e0100308860320080030789a0003000c252880c0e400c121007d821502c0100003252111081c244940703441d00602071806080200955110713588101d840b84c400c0100a8080b811030760120708641080c9103402810b60041020f1864 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 337112859 1250 337111609 337111633
    0xe0303090a09090809061204120804030801031e1e140304032d0f0303050411031209060a0e10020a02011b0803040b040f120203031501090e0f0603070902071a06010c2102 74
    0x500c0d008000740522000700c450030442040505141e000f030340f1103030f1b04012b1a03a1426a4005050000c1408024046506800c040110600d0303a0001d041c2550300c684004000300140c5440800214440f0068951071102401a00c2440c0d0200449041da074004614000c0e2146a80350085510340344180f0800c0d20129102d0b070004118001104d03107035984266804100c3d410036060202820011013802c138420703080700c44503c0e040d0940300f0454500302000e46903030391109120142603821540c0c049116800004034042d01c200c40c2d5010030100c170164400d8a0b00042e55402117115080004c10800081005a04001181c042440c42d81c1c0c2c01c0e802807044402040086070f55980003261084089031502681c4081f00384620100341c5038907203020010030f2030700d61092454264045846200601401140f070381c960045401902c0500c001009000905030643d40c0c0e110504d007111280c06e50342641c0031384205c14004100c00d0746c4a04017140f415500940321a1480e00b840d00020751491060076100d040d41315405103054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 337114109 1250 337112859 337112869
    0x20a051506040b040203090601140102070306060f06140a090315020d090303090b09030c0c0d02180103260307020307060b010302090d0f02090a0b01050d1e05160e0303090a09090809 79
    0x180d20102180d403110941001e409000030341d07215440d0544218018020046002000110941140d1080c4034524102c100070006038103004103a000a0561130610b1070220b440812408202d049400340c2e5513482d55a81405d806c01e419004d03003d50040014034a8a041001ca0081c0540c90080600f0b0750b0700520b01040c680703502040b01c8000c001200403e0302c516400050280080c00107500900c1880610315204080c02607070f0325030101104061044030400c281d03106540721420162010701c10949528010b5031241041ca8074556a4604890030568951525040e00e08240c1500d0003848990002d50610768180d0302e031009030080f05070342410580d080c0300c2900c06070b884c4032803158541d000b800341e020716001a0052110b4444000d10b0503046c1c0c2d05050074045180d078054200e8682c4c85212900086242c000003042c030b8003004890f4501e20103424030042c000d80000300c1c3c0c2208804180754031031000311031005081c10780341c0c0104074070700d98454180003042040c409281c00103c4404e103d9681ea620b031040303200020b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 337115359 1250 337114109 337114123
    0x1612020115230a0810051b0703020303090601050109030c090207060e06160216060e1011030307170f0106022e14010f0f0308090402160f050c01020c010503091c020a05 73
    0x20300601c2003070310380d4984070038070b0b4010800068040c3d841040300b0f810400425030761401000d070003e0300c654443c00948072074405102000c603550215491341c0e40300407a003002590394105940c0d21b0054047e8800000c2c00f9805806010f04690303005c1e03260030300c00d1f15048084e4001e40125105846083d2503651084016400781318151146a032803521803020408074100a1511a28a1407003140450b250814071684e40c0107100c800388d58500b00c0c1d0130b002045c003040c0100c59103400741c1d0f0780d107009120110602c8030b01900000c001400702d146681c000095079803039400d164002820320071040960420034641c00c0c0103d0b1424220280c00c405c103080c0061000c0401c95a084500d04a85420071000343d10041c81110b00544545008000c0b03e0030900107141151211011842030f51850703403040b030b80044d1624040400a082c02183d9400040f581164503050030295224513501d030a40e4018001c443e1442041c1d0302070820380b80201c44d80e000a0550040c4401030f02035101107001100c00754441d610410740081d4040040c1c3c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 337116609 1250 337115359 337115369
    0x203041a06060d24090b0f040b12030d06050439020120040815010f060509130e0c010813030c17090901030309090c17042a0f140103021612020115 64
    0x1c40440d01c6013010600002c210340c000520807800c1c03084603213056517100c81c02c440c00f082c21900087e00d41c940c0c00001e40008480314a044141c040404c410b1694000380c0e1201c021140140e50038000c0c0c8618499480c4140f10f42170400e82140c27456000420b0412000000d03003600841da0000244522202180e900302030301541050b01c44040008060244003020302018a4548803a01c09984950425004009000d904e00450b03007080000709014406a545001c43e84070070100180030407a40600c10861916180303ca2515404a094000400e0040c011052a48a040d4056942400050469807117060310684400d2410550000b8030100c07801740e86607003106009600c29281d0708405403924681038180c0721401e41c044244003501c05085001341c180c038881d99000781c0c40801e12030741100b0746210300041840c86c00f60640603401e01c8000305100e650036140800780c03412180f100d00b07004400f9004400780c3c4206d888403400c1520060359032000843c5001c00c0441c0e0101c0d0300011030314200081c01c002840c4401c2c0d002c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 337117859 1250 337116609 337116641
    0xd270b180105160507080d02040b0711030c1c08041d0106030e0705010f0305180f0f1002041d1305010c0314060117010b0d02040312020a0201120203041a06060d 70
    0x34403100d003400c0c020100c0d5222400000740071601d003020740c070701c050039620740c4100c14024005849020082c07607a0031165480b00d0342a00f10344854480780c44240310781040000300e40045451100124901c0c00007125000c9510080211700c0420200d0100000320079860400c80748414184008600b105004100c0d003810054007100d000315601d0300d14010259090a410000c1d0b0b5045400284010b90780020703801010480c2d0300700400d054495180c20480c403115010b4060280c05000c00302c9103244030124240c0f40d40c003404003c03a0600c1c1c40c2580000c0481c412403054030708884121a00902e02400c0c003c6040d400044100f16541c818800d46482c1e00390b604e1440d04000095565003030030000c46a54000d1a0007950170318041045c2c400701242c4484801042c00350f42820344d03003c078885412441c0380d01103402079a03200c1c006040d40703000584060750b680200c980807400310340040868002c0e5803c620a903886190485034042c0440c01c424403a21210101614075078000f9410050810700e40c0750b0b0b000d610410b50000e40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 337119109 1250 337117859 337117861
    0xc0c1017010b07030206060609030a1b2d05010e0a0e0a0510060804030c1103030717030105010305070215010b0715020c060703050603010608070308130e0109020903010f0606050d270b 80
    0x3410500d40c5405802c40c085812003404000040ba070f002442a42c000010b40e16190394511803030010b450304e402040e0041815134001210310318030301204210402c403060300010804c0f44014920012280411210310381030103905170010401988aa8407440c2c89840180c6001c1c007082c2c50300701545031060304442060005840d00c0034804c00b883c4e0380f030f080c40040c416854107400c14141581c005160309992030340940148480401001e803954240101d940300d95100c0c4c0310361440030404600d00c2042e0024440d56000c40d05d09000100d115001040c180d2441c6071200c01500140e01f080f180b4401c540003240c0c185c84000100c0101440c4403242c1c03000342524590180181402c0c80d00d601c00506544004165501917414a401080040400601c0905032507211484075140c00130b4007440c504010301580021070407103806000145100680e801080c5820044c1c0003800042030080b00241594841c1c0304880c006001017010941400081c0d01229440400031400e40f1807003a91030a1168852600fa0f003600d91040d504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 337120359 1250 337119109 337119137
    0x1d03070f2609040515060706050901060b030c040303050a032009030105150310020d0b0402042709080306210d030209040609050115050307180e0901050f0f010b0c0c10 73
    0x1c100c0e46181e41450080c52107220740828030156900820094600031a1500c000c180381c4a41e81c4803000360110040d00381d0b516071040d400c210020b0007054500e40c82d55483c01c40c02051205128007143c5c85817a51941c175521345480c641d4104c919500500c10b00080555640230801c2d007400704d00300c3e83c8607290200000d50319603210004060840304041c02004140b22200d4061007181c802290b9540740701248000103071500504002c2c034024000303c840f0180c0c01340c4005004601d0403640e010003071450300c0e40d02103640818196140c3c00115210150081c114201c03e000060b964540080c000541c1c0451501a052102404c00d80c54604121240f4a1001c682c010982c03007940d0a10b4400c031030040c40c06010a2003694503044195a20340c5103002c10f0f404100c000000602242d0040d129942c0903040390006480455403070f007032480c0a130717015200e41d0b01365400c000204d00380d2840101c4035030147c840c9203011021640b80c01d00218141c0d0000c030680300b881c010380e00300100640e198001701a91914584440351040d42030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 337121609 1250 337120359 337120373
    0x60a090f091a010206151306090e0a030f02010203060105030a0c020a051c14040f06030b0a1809030f02010c210608030f04031a01080604020d020a08101406150d1d03070f 74
    0x5849050456000c035040200e60017034411b62081480007a035109030592002c82416014240c103820200c00c050524500c003d511a0000740300801e80d010380c0d94104104080c80c0205d00743c1c4010f0303403400c0c0000d0040c80403403a03201040c1c1c406021b114050048914408a81d525142090140c0011440c66046d41c85200103254001c0d040c8421800e90030203403840c0c6070a2403207000c013110b0103001e55400c156a60041200c02c5c1c440b09a018090401c400b10b00c445a503144810f140900b85c184400c40028110700c0d2900406401405040b5540e082c40e12402c41401e01c0030034603603074940d4030b0751450502511403134001001202031005114048140000583c2e403421b605042c86044030a0007200003805140d0300400003100049005c07034010780c0c1120300c103519040c10300028102c070040390485892401003400d5607454042c1c41d8800403903801084400301040e55007100b0080c405140b03000200c41840d007000145414180c41c0c1c8003000401c008250780f1403010050f001c0b146150403d000031100c20b016070040b44140140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 337122859 1250 337121609 337121651
    0x20a020f0102030c1e0a080d09060606090b0d0e100606080105030d170a09020a090c0518060931060303080901050c0405150711030d050d0506040902010203030402060a090f09 76
    0x2e0008628049080501982e0350b040c420b40c0000440344c460507032000c1c450511040752030039044000c1d2902c56881c054110300418444000310750b098506140012500c0c081c10b004021114440005070801c2c1c03031405808068144450300d8031941c06502d600010480300c0348207039006004550b88450096040c4001c0c54a0105008001d0080c840991107808100301d504e40f20348c0d8015901e010115501030a0f2000c00d0700d808454001903a010f05103a0304440e8298440040c02d1500114030803420400d407103a0901480e4814100d51a8120b98652070801003461a031030100030116825851201e0800c68102203000c503030b0f41d5042100003610050510504640c00d000320b86d0008421841c0c1403916180800103140d56105201701c0d510f040f804502c280503c041d402c14800300700c2c800350a445012901d40720003080e0342c3c04a03040c1f03200d0740d1904002c035456040500c03450f04c04d203506800461030b648031138082050304d41203085910308000d5180f10118245910444040040403000c5010802c0c6185004401e10000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 337124109 1250 337122859 337122889
    0x604080f071703031602070b1206040507141602060d0c030207121107030212150c0301050a06081009050606070f052404020a0b0f090d200a030c032907020a02 69
    0x2e2101e900c512480008011640c000030210000340c05070701441c1040c1c1c1041400e41c40140c02c0440415007030402e80b0302840c1c0034483c010031a001c01c1180d45890099401c00c3c06000c0c0040700030414441600e10f0f059172040b0040319400140301c0d5080c02c0045040304141e9442c4488180003035004581e2a0800040c803400c01002060b03800c01d0707000394815580455440499110281c0303d454503445040500b84140700350402580482c0300300401e481d000001f504a42c0c030a100b4075000d880c049400084003031060030900e00815a807043d11030407602d40102d15014200c058035043d40032100f082100b0000704c1d0400d114074900d11820192402c0082c0c201707181c4a00b45000c40c0c400c0c1b4030701850704000041e0354400170107051343e400f0710401d900c401c0da14000c1d19103409550100703900402c20007515011710103803500092640004054180748201060103100d107802142c44001d2203080480030910008400f600320500b022100900c89030801e480710700062071854142d54910150300221050029030900d00c4020035041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 337125359 1250 337124109 337124129
    0xf07030b07090315090b0f0f0f04030323071101020c03090603090304050319060b180403110705030106080c0a06020f072706261b0103050411030a030807031a0f100c020604080f07 78
    0x403404d56181c2045688c014010358450000e00009010180039500c03e140360700328803503058044040c4500301081454207489030800319203403850310b044c104014000c850340f82500703002071802c0640d18014070070540c002a01104041c00f040c0004103283e2003c2160920601401c15200c503144d070302d82011000c50781c000d42100d01403240005083d0803d0243e030401034015904d407408440020b000d8121504040040d000b240e459400c10301c002441e00400590700d9041042110584030495440c2000d03a07480824030580001c54102e00001c01c007107008400b0501004142c03c0051010009111034002169102d80203c06551004c01c4155600341c02e6000c010640c5003140001c1c00903080c110070034072600141c03070340c10707410540c81d20002001c020040c001488004006000c840c20111240303000f03061040100c51580020f03280048682c00314128068401c500f00b00904907454422049080c0005030b6200d4041c030f42401000d03032441c070060701e40d0305c0108000c00d040d0025211040503c600d25080840c030b60301c80503284c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 337126609 1250 337125359 337125361
    0x3081f0308070b060109030605070c02120c0d170409060b0315030115090e1203010909021002120f0304030e0a0602010204050a0504020f19020f0a03030510080f07030b07090315090b0f 80
    0x5141c40c00301d84549802003040c04503a40e8040040341c56402d81d8000401c010b0500040c4400350350011405c012441c4200e649201e07500b03040311042c1c1d03115a1442d00e59800940321031540302190032404180e50f0b1902c1000c9280c9441d46404040b800d0b01c10560200c08000400010030100d0740c1ca411911a006004800a02c62000e0003040303d0b44d164580d0041d0000b0559801c1403000c1c0c00c204004003017010034103280c0c1640341d41e074503492480103208449051b070040c0c0340c0f13005881c241031010403400f2480c0d0101d1904c508040c1c54016522310307900024412424821b0181442c0150380d03074251034030002c00081d130025948504000500c50342380c50030351200e4010350040c0701c150345c1c200c0c403138055404604900645420180e5030b4070040b49051803d0f9403201c1c1c18000c1102c81000d05500d0740141d03200f0f000b0800d01d9130141c0c1c4c0d108952643c2d0906964075030303299044400c045c000a459070401c40c1c0c00a455207082a000c680300d8913841d0301440120881300d80d0079580c01d401307000c100c00175030700b03a0307101450038000c03211 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 337127859 1250 337126609 337126613
    0x2130510060f0305092e150f0b04080613020406080610091d030706230403081b0406051b010e07080102030405060106050301061b03021e01020705010b040b1c110d03081f03 75
    0xc0c403061408042c52215102105101062101e51101d4841b05c032840f0500001d28500d60100d40072589004191003245240b07030104207460400708407011121443c0042c01d07959030788280310038010441603080384c0c00b5032a0311000504e08010441d80d40540310714076509913002e20700100801280c064800300c90b002d10150485a41d2030700044140c40006812100100c0d1203c5001c040d49120902c402513503205521810a1205143e84145110310520b4000c4914410080d110004492409144903800004030b08100016101c080303a6406444207000000100741802090549801c1400c02d821800e5141c4d40401080113011741045a2801800903007081403071541040c2c401450110143c410b403094110100c5003408040c400c020b0b07000b003c840684444501e0f44c405092034080c1d8040c1200360390030741c00e0134000300651401d03109502405100500c0060343c2c6800100d0320075400760f1444243e0341041e007415050103d8403420141203081c0d1003a070b42d096043c0340140c8950740d4800000001c0741e11101050301800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 337129109 1250 337127859 337127863
    0x170a03051f06180e0c0a0e0a140607060b04020a11071202032a04060308040302030105280b0f03010906091709102f030a0909050402030c010c02130510060f030509 71
    0xc0e0b400d41e1819200032107104401c8191824207920090296140300100981d01c2c070054042d016400c40c1d82c1e1030300c0120b611700c0304109440400b030080754600344c0080070102491800d00001c0104500c504030220b446801180084c080782c102800bc00e010802910712405003550500c82000a803884440c04404425950082a40c039145c41021030384550000200006245081070300c42c41c9120005e0040c05040d0326403a2041240d01b2500c0128000e600b00404540b490003000d0702d1020400c030002e1803074030320140d60100001070010018605d400402c01c090700c0d01c1c01c0d01c080c02420300c01340c011040810701443c98982101807040000b00680c0c1c0c0102801030301007c2c0e40b0b004240d804042e462501000b407140f40004010a030101040316a46640107102e105041d00e000b10140000c40d0190302c58441860ba070f8044042906c81c2240c009502d0341100404068540c0550310380f0140b18000f03407160380c411546041032400c0b144103031542200303040149001c002c03803503110002c000541024981030000341004410b4907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 337130359 1250 337129109 337129171
    0x6110a031103042310111207050c0a021c0c0e01080f0a030804030309111804150204030c0920030a0911040c0f0e0112020d0501051018030305030c07170a0305 69
    0xc05130805040484c00702400401295030000444801040074a021005444996000906e125216906200061003850140013504d5500c000003002d00208003c41e4200201ca0080103c2c84181f150701526000102d07044004203005041002030341400c0d035052900251500d1007401041030740b82d0103038040000103a44088481d810030ba041c140031614540c280307041c4c103c10945c032a440d50003480e046081201814a002d00c14000c134003550a1aa100c26203492000036032059001c003900510081104110320011980185da550300c2c80c88030b4000038100d403400c80840364410340700c120b034083e15191610705110030030303004040719141107a042081c0d1450b0240502503100c14040001846013032200a800359010301c241400722032004100f1035580e6403041003600106070a0190b40e001e810400240010b05026010058107101008a242207091942e070302103a1950004020020303420080c0100c50019500381071000214460703006081d111030038180c0003000ca501c01004101d4400c18400d1040059810038181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 337131609 1250 337130359 337130393
    0x70906060c050f0d170a022713050112031d03011d0606060307080c1809090d0318241104090504110103051012030e090406060614040f150c06110a03110304 68
    0x205c901039850410050003030181c1c4454842c032400d5034400d510000ea442c800001d10041c1168201407a00f10b699500b070854009000300c01c410355090110b100401d000d001d00c40d10049140310703012145004200402c2c2540c0c0046000410006000d00e1054a18000e02000e0f5000c0829581300c0d080d1b10b4003110060899801400130950010300091800f402c14100e00c40540d07018000c0d0101800c1d007009034419960320007264038a400240760071550f10203100481000ca0940350012002141d000d211075404003032407203c81d44102d107140d54901c1c41c5100311201d00603000a00442c10700160314a06410034040800c0314806041c10540380c43d04002200000003030344020740e24400907500500300030b860251500d081802c8085c0e0304c580c0c494100010442c10390440401c4c0c5520369100071640d965040805418026400303071440c1c000855500b40090508172000038020a081d1401181c500d0041d250b0200f02c4d500381c296011480300000b44420210780600500c3c044282008682e0320b1850b2580300c0c141240441544 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 337132859 1250 337131609 337131647
    0xf041d10091a061b16051212090f0307080a030f0905010e13180204090b01090b01081009051027110c030909040f080309010b180126070906060c050f0d 66
    0x1c04148a44c43d103078107031803940710300b2603500000301e40d802c0d441c45180784581c5100300c2030384204034000d500105040340c810040300403150a00052004200c8a0074280c200250144212000091224401c0003403003070141c042d0325a4816081d03a070b00c005203440f0954010034144421400e02c5861a214494480313891100c4034000107005020002d00c1240000d81d01000e50b0003400c16851105100100041504850000c10304114800005005558190040754140211920400304100580c11600320343d0b4000c030120b078a040300c40c0d01c4a00c04003c0f11400c02c401019041801c50314102c02d0782601c60141c072440c0c000b1095040c058002000c2c2d5480c0b04050107140582803000101d01004004007003002d050b60700201a81c0c07240b80592201d402480c9003d04c051044080140c5c00d444890b88010741da060350740c070420f010315122046240350143c2207801200800b0b4071807075a000508108900c240b6010780390356a21445c0c241c41500f0001e00d44a141100c009407500240d0012040ca900138625590103111064 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 337134109 1250 337132859 337132867
    0x7080103030221090409080c07050a03080d0e1c0c02210a080c0c150a020c0402030415090f060213180c21060308121801060b0d020f041d10091a06 64
    0x41614084c01061003850700107081113600380420400c00060708001107404215200e03d6070b11020004105264800505402010005141600c0c5950800303009200704c8812518816280108600861410310344480000c85040175a8214645070781e0302c01d1851000220103041002d10400582c450100c1c000082c2111000120280740f14824010301c010481c0007061130710000110941081c19a202e400c18200500944000351402c0c0740501c00d0f20700442d080540c00403c800d402c0300c050010148250103543c141c909c003a4207070005240740018803150f4945008281407030301c2d00d8081c0000365080303440119103608101c01c10741940e80c00300001c8020604480e0f4242c540844012a2004088035080900800d20000302c2609103002c101c991801000443e00e00030325228407020460807500303203018415071a130040152040001c0c89070060860a0100c0c88110700d400d83d0341800c1c07041c403840300750704400c60202c40040040c9540e00c250004018405100c0a0141d41081074803410700d041e180b01c19901c1414041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 337135359 1250 337134109 337134163
    0x501050618180108060103151a0d050c220b0102060c030601030915020406030b0f03030901091811070b06150c0a0219030b150f0105040f2612090306070801030302 71
    0x8280c0860103402e40e9401c1d095610790000c1074560209000645000e100d09190744200c1030310b032103241900341000c00c00900c03c049070010441c0c0c0f84007004c0c00b030703135030348151449140140d5403204280da092400709005050402400700031030684201510550540d0884010001450f84a0040301d0b4403000905e00001c1c030303809602d01611444803007100e1100d003e10218001c204140c056000810560301140d1040b440f540a8080507945d1068511460018403049010880013a00019408810301c0000c0c0200305042010484401600103600a44441c0c0001060020358200024507002469044401d140b5266803051641c2e0b4a1304040e000a000c5d10754100b440c940c001e40740364040302450f0300881d1070005007081d9034041c01ca51003075604280f080041d01121151980120102d138112107540c2c50302c0d501c1610f408851407000c10848080705a415100c511000e61000601c214403540c65800011519010641e003072610b4440002c00640c213009561005001103500082e1460a843c8046400409400301d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 337136609 1250 337135359 337135369
    0x302061608070b13060605060a020318130c0201021e09060304080315060d0e070b0c191406130c09061a0a020a1403040501020f121902030702030601180f0501050618 72
    0x188015140d4883d4006020900642442003440c0724016102444144d444804020052042c0c0103513a02517401042814680b480b140061061a1402002d28110340410041b40d410744160460000042c0d600044900c4c602005d86010704501408034002070500c0100070114030144409003001d0080035011000480031041014103a050440291507151910085a01540908500214000b43d4064424040b8108420320b090340c110940c0980100784003455407a02c1e030141d0010f504103076401c8a480c00941c1c02400c0c200070ec0c0e40034640c200e0002c403000c54281482c107401d41c403c2c9c01c401405e03801c1940c1000a00e00005140c0803520383c142d01c16982d04c2c8140421f91414809044c020001161030400c40340066010019104841080c0c00350b50b02002d00d03100581e128911009001d007001c501b03115010001e0760031811180740700103030300444c1d16045003900004d1030041700b6403120100004d8507680103130280d818010305091080c1c0c00300910040d41044000b42c1a0b004101c0c0c00d591462640044035910380e94 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 337137859 1250 337136609 337136617
    0x11130603050f07051e041d0105011e0f031a0603090610080d050301030605060103021603020303190e1c1106090a030e04090c05120a0b0a05040b0601020a0b013501140603070302061608 80
    0x103003584041090112a800c8124410274490b10340410b142076001514464845080604030b0030300d5403220314181c0c825006900030726141600c50304420083d08410102d8441e000154007601c0c08070300a10315403426581840502c2055005007000c0d4008001c0504029002001c2e60306596120401017003503900c440040f0000c0c001d000078a04141d402000c2c403001d1540200045000b5aa40001d0071611315400781c615041c3c552900c243c0d031080d8048031070340d8810440c40030440c041c1d1030300c0e00d03200d056200305200c090700e410001eaa6180f82a000000c1e80d400b0541c10400300452080292000e102484158554240c54519031042c2c601482410119880d204014890b102116600c48042990b5080c0703a80c045c0d0007040b040301d0890b0008035001c0810790320342c00011034014503507000400480c0b503801d20350300ca00e090f20103110340c0e510102c0c4800d000d000102000c1c0304800907604c1e40000190340e803444228034040c010203001c0c60f010340c0003a2801d00c00b60300d40e0021198007c400394100c401008003031600c0401445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 337139109 1250 337137859 337137869
    0xf070e071b1502160c0306051f03060b0621070e0a0e0a0c03111309053d0905070c0b01061b231615050a0c02120111130603050f07051e04 60
    0x1e60413219410440800c1d03140080e28014801040f641d520f000303200404510724007440d1342030174021000b04001861904402c0170340e103000d0121070500380d0713012500304c401a202c00f2009181c040082041a03155022400130300c100340c00c551088030949068500e198101014200c84c2105880f003103c1540035000380c00180002a40f065465030300e1901d480110102d02c5c00d801402d000c94109070128151032250846001482e0708424103119041840520304014803d5245503e850304501400042109031880f45610880d035540703640e101100b0500d00345400180582081c1c0a00604c8000c10251107001d500844070103510403d40758842c4036100383d0320100011645040c0e1170307220b01d41c4451305401102d4444d0081b503241c1006c20300c0102c50071200383e80300d0060740003800000d01610b2221026240503840511800c60f0400000f662140012a61180c0d62060071500d00840d8820001c00c003c0d03906101e90b591210744000a07004a081040c0c0080640c072800100900381c40041e6001c0070b5150302501140c00400b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 337140359 1250 337139109 337139137
    0x2120a0b0d0b07020d09050a0605040b071e03050403050607090e06130e030c0c101103030705250b15030a0803060d03090e040507180504020f041104080f070e071b1502 73
    0x203c0c080304004d58482d01144803070001407014000051604068070700b0001e41c2d01c0e58079443d00341401c064440656030841c9070260346281654a08000110b10b801d41c010041d80665a46540c43d130450401c50b2030954098000b80812000d90001c00001ca407641b03a16400c803900f125803081c9a164509010054401c015006045020010350003041020001c0c040228810a0b145280440e044081c207981d42440300951801d903400410024035014810001000c41d8011300c0b40040c0054000503c0d40d1240c1807031101202d1030404041806044002d40601e1200307010114014100b04c00c0e182c2e6000c1603800080d00442c024803881012208050050041c0070181101c0c600d03d1850b40b07000d08001d40d42d15014865544013503041d80c00f5041000300d50040d0b0384226006400301104403000d4061000500c1d051101c0307889460306002c080381008041c02444119000ba00080c003829050104010708806d014004405008110011031800c01c08914815040d5410011a015031403c1d000284040d205405a0603458 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 337141609 1250 337140359 337140361
    0x6071211040e07020d050c07060c021201090501060f151d0f0909030301240e1306150e030c041b0c020f1314090c0303091201060e090a1502120a0b0d0b 66
    0x60701c50b100e00c192515030031074010310982802503410b0710441d840000c158008140902490340100d200f4a41c243c8058004c001955010b03d289084403010b200c112080e9441e8041004103128001440d03003d0000407074910031180c02010058001d0764070300e00190b002c1c6407155000507a90f4504815640902018010300b04a14210401d1901c81c2d109018280c00446c40804511604901e00c84c001003c40303280e2a40342c207107a4100d042040ca40c407858a982151600e402010503c1c40c00400041000840c0740c42c0c500c021300c0f0f1082090309003050030366a50b01461805807100c0e0700c012050401c01c2000041c1c03c1c40c40c0158464008242e00c203030008002e5402110480078854101c001e035001e9410a440000c0046031925443d042c04c1d100c1051100b5580c0c50b60060000342504d15018902100000c0c0c010000503070207540300780b495054801282d141a541e00600454010720441c813145900c0301d030802d401140307802c0c2c0265050901550142c1500c213007903580d001341940341d1602c0440c0070040d0740243e051566 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 337142859 1250 337141609 337141619
    0x41a1201030305300402060715020c01020703030b0907020d0507050f01110d05130302030d0c030209100f020d03050f0f0402011209080a030606090e0c220f09060e090607121104 77
    0x16800512101000b02d1400a9506001c250701300031154010989007040c102d449903000c100f40758000d003001343e40b106030901252440f07202c50710060642055030000940c803801c40b828041c1c01c44404941e024060001c2004100405a0100d03a815289201e030808944401c040c4c1070030361030450244081003170b80d880d25525004d01008040500111440c0c840c05004603070b14100c000b00c00b46100000100983e00502080416400710b400880c9000283d00d0014203041441001800045a920740c6602080022041700e17001a070500c480d002c0d207501401c0c1401141494880c080c10100010101440300c11524003140071603200d5640e04079507501048041c0800034040c00d11081640c030804014002c203240810005150340140e14a904841025040da445590f540414042c00d5008401c04000c0d42c60301300c00c10302c1004045100310090071201c0040400c1d01c0c24481d4042c1118a107402c083c54103d409404c110010000040040c0c1c00020340c079102451144e48a00d03040038010a20031182075003008a40424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 337144109 1250 337142859 337142867
    0xc05270c070c14030a0303051f0b03040b0108150415090204020a030b091e13020f0604030501020c0118050d0f09050607060509010c030510090b2707021c05041a12010303 74
    0x10001d4010324440740c1c0c0b00d40e55032066145003080d103842a0190841396040003c41d000750322041c0c0c00b014100146280480c0e0f90180d40085039950031440340b50720040180000c0c406200e04640c0503200544c000d01400042c0c0b1003003d4088801000248050580710310203440f410036400011105a020300203544401101c0000b50140440e410354602030082d240c0004c1c035a00005942c800c034400078070301480721500d900310041c10315503010300240c0c0c0020005201e0112a01c44a00400045008030300042c1c171600b032420080e080d06d00b80d0040b010340020325000840446c0000c55192166420360500700040e06075814240c2c2c0c00c410640c03100c0d9003c00003048440034441c440d003101d031054401000070801310f030a04505404a44050b5896140c4000c020340c240406400d0380d00040406000800507400810300900003903044200c03020b25280030884178140f00e035007901040640d10a000d60903051013001c40b141401099030180c0d101d40c0d0030056100c0880480900d110040302c0c0000214000746c80d0642e10703030034090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 337145359 1250 337144109 337144117
    0x31d0109030314060a0501050903120301031506080a02060d020307020f100f06120308130f0210170610080c091f020c15160f03050910030b0f01020a0c05270c 69
    0x1801181c1041c20440c0f00540f4601114407a810040198030007a040000455460700140f102d00d42511a040032509880009405540218452804c0045616409410f02e0a83d0103542c031540b0700350f00105040005946030700c1614141c840d0410011f8990341d517080102c0c030b000c0762000b030101c09000e2a0901c422040342500103009020706c248041c031400d41d86d036000d500595010500076000238155004550001d0001541c0c6080900800650f50b003d810b40d00002c5c002c40032489400081245d0b04d200d83c24040e04421415400b9404855040b08082d400d0b01c090008400101540c406110005500c012503480100e65240d8160203007a8000349522100040d603113020700101c5511902c0c2c03c003200c6d40c0c54060b10007181e0716030285188442c5808000d0792014040da1800000301d0611030103005a0940b49c651240e030481e000b031a9540868ae5001610034003031000406030381141150080043c9001051841c0c100300704a560659480d40d0940c5040c4031400c3da030000e901c0f907090f5a1080002e10100418600181c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 337146609 1250 337145359 337145363
    0x50304050a0608010e010603090318060504030c0b0306030c12011107080d060510270902031e01060203070317060109080f03031f03150902012a050c0301020901090312031d0109 77
    0x54055984644040d144048244034217540044000d005001c8103100f900050302c0d0030f2003410b00a0105091500f00080e041103500810b0004001241c20410b10410440c01e000401620004c5807071800c140340403988602546400c9802480540003421400c002540080d80c038044040c60141c0350ba003a4500400d0607400000001901800c000012882d841c01c106522140281504c81e000302e03070b5100c40100c01c1040d840e84041800d02800c01d000540200d90700003540718168459003401904826041e141c803011040c0c0000c021940103000f00c0000075004480e0083d001941495400e0076070b50100100d4100710943c0100843c1e024180c0309129201001001d140640c02050807440b04280b140c7e911200c0a500384000b0f0160a494006030300c1d4003469a0100d22124010b26141101700c1c0026510040c0f03c041030304202c0080c1d21861024103018060241080782c0000f180258945118040000c00d01d20320b901000c0c2c0410440758080c0d90141c002e030301400ca40b2400e10700c800d248038100c4060b180286082402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 337147859 1250 337146609 337146619
    0x708100f0b04141f050d050309011814090907080a0308040c050f0a03120309080a21060f03021509100809150c04210203060a0506130c020304030f1a0405030405 70
    0x201c4070309251a01981601440240d0184000c0e5264030507403015a020100c45031542c060250003181c0d603164000d0403144180100015a5919540000101501100c03205515070702c40308a01400481c56251807514405400c540c2100349440300031040f410100310354480e00091064903580810107070040c50303c51241e0f020b52641c0b080c40d40c3d90402c1c03001800b00f071082c142e030003140d190080c000113402481051845842e4940040c440906550740d01131640601d1210002c44d41a03400d040346440c94580c018046061408188540d0b8940b0000400e048243e02009208841030910888800d4500f000d4a40d01000108000401444441c0c083e00749201174030351030000c0c011003200c0540c840f0744254032400790690912171450240350036880428030000c4a03407028262a2541c18070f0141c1d808009150080d40d1800c170004050401104000403202c0401521244c581002c54510001d50044195000c8a07081030707480c5100d2159241c01010b0820a0307440c5400340303c410b4180400d000c0e000025005035a03003039070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 337149109 1250 337147859 337147871
    0x6082407090509071b0209011e050312040324060b0a08070f0c0201030b030708030c0f0f07080d03050406090501020a0c02040f0b1f020a05030429040b03040605090708100f 75
    0x40d04072821407081c0640c0381c20400e04000f049409110f0400307555804200000300032480416400100608000c0e8411280f420b40304082100034840070001c0d0004060480052141081c50582e20304140a01c1c40042c01c0c2640c00c1100504191214030783d0b94140b58129070401060b80c4508040e043c940003050004001800031000503280e034080c500303942e041e034016100c039140d94107254011809408a10b004a8140c051100000741c941c00410251800001103405840d001140c0d80e01a0300c0c0c0754480003840900e41c0030000801005201040c40e12064003186404902036580341890300252800c40e00c020036661000407800d2065a0200201071818406c60b000e112003800000e100c4261000071158a0b0b1044401e00d40032044e40001902a030f842c501030040ea480401c49403980307810750300305900c540d2428440c61b500100000001c00555058216100442d04250402c58014030a000007040100229034a401103603804604000b91002059000116984920701c01c2c03416010704400102d107020141030032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 337150359 1250 337149109 337149121
    0x3041502010f0203130b040201030e030a021b01020d090b0c0703021c20100804020d050f070303090b030f0a0c0e0a1e05030303060105070209041505040804030201021005010f0b090103060824 83
    0xf0084034041e4210601620800600b5201c2c03030304843c005002241815990f001d02da08402040c0003904030070704190007030700340e81c00c8503004113034415240046641190845510651843d070412065001c2d130320903050003502c5a00e03000300280340010540019600c440d9054105441000f034010010006110f07002003544822840e00402c43d2100742280749034424200741003031504a01c82e075203103a0b10900080c4038000402403074a940f1b0810030b403c041070300302e0f40000100b4002d25400000c00720050100b803480516519100c00c1410440c83c0203007500c06c2c4a40c690480b0601d8034403071030840701700c9000104804e41140d0344440101d60050f0f0b00070040800c1100003c0000d0b68a80801030300d21071034040e11240d00c0d1610703990070020b14060080c422500d00054440500c190314282c400c0c1031007507110340c1d91141d8445c19800007a19024285140825440c00c010040c0b06603583c1400c603908960310103081a8650100c58010b034003400311600042154410f500f440801c0d883c3c04050f018201400f54181c8660343c0b189 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 337151609 1250 337150359 337150361
    0x203090f010525050d060b03011a0333090723040308030601050f071a07270302010503090709021c150b09091305010504061b030603030e0d06060803041502010f 70
    0x4480c0d400f29104080c02400400c401c40070711081d00e2502e40342262809280c03072510411140c1c4c541101d00000008801480680760482a400f055101a5040b60651034551200c1840000300348028030081000031003a211807034a58948c655106000f4262071903807404100080400b010350040356010640900d84c002c06102031412074040e40c0c7c01040c15481c41d510600150b4550340304452401c400c0c9000c000040c0400c607200180003940741c0301c0014640a041c4000000c0184205d400e0140e10500c0d088101c148400f05ea00304403044031390a007002901c0ea40d401a110b0708044c2954008030b074460001400900b944c15241585140040c01c000c1041b548480c0002110f5925441c0181001c01c4030802500699203882500300da4044120f80507281e21440e10f0341c3d03490a44005503411075181c0d0721980142c2180048103200c01080310503150030046a80f070b5480080c004e03903540c2d03482030081d070082000c0401d102d130a41001d80901030010840e82d903190344031819061584c030100c441005500c0c100b0402800500c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 337152859 1250 337151609 337151611
    0x19030905102012010317160606030201020d03230402031e150703020f030a1e091a090c0307051302040f03080a020f03032412060118054002130203090f0105 68
    0x82084140c2d0f240e007180e4854036000e401c2ca440c42c50540003444681e807007030b070414000d4005510901c0b000c0740d00751952001904e04024075248406250a1885031440001e813545d4184000c00c0680100300c01d80c4450011034113103400c0c50000c50130001014035100c01c46600180c14060000852a050300750b0f030700c1c0c800403022401284000615000704001240102483e40c0101002550900110484080c071100700801c490550200715030b0030b08002c0300000c40516a4850940c4042801c0213019080001000030ba1503031071501502e40311f0700483c0c0d801c84111820340d040c0e40192500101401c403180d1641031090094104814040051042c026941c80040c030100c1030f07900810320000c092515400e510011040d003c10314482d00d822050304c41c12440c084004100e054020300e1101d0316403c42c0024070943c8025201d005040401001c00c1c1d10255a110410742c3c064a000c8805813025000c1114050401803444440c4201a5105818005261580d500c9600031401102040120340ca2140c48050301402e80e50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 337154109 1250 337152859 337152877
    0xf08130501021005060f0d030207080109030806010305090f060a021809070507020310020901200f070f09060e1306090c0305060108031201061e140c070b131a190309051020 75
    0x1403001481d0b036081c148100801d87c003030f02c0790042d1100076481d24109404c42e810390b001070300001e401409201c0c065805104c1c541d081042c0f04050000d0080c0c2481850381c400000e0030254403c2c0c1d00003919421924007448811500a0080803140582400e00c40101142c21480e8160b00c2801038003c0844c51144c03600c00c9036003281c81a112548103203401c600380c031141fa1440c00070b61420b01506c4c17010b55030fa040500640300a040500401700e429414800c03028100d07001500b00b00c061008020500c01d401101c403400d007150991094000c61042658a0503071415011a1320050003440b54a0000c14482d0010018060018881e031800c8003a170b03a102811a44842d018450080e031a0700d4103500c4800300c5c0300d040d0140d0f00d016840c014514060050f1a40d51078003240b40d0100010002c0414014110541c0c4e90805000b4480c010241040000d9103070030910314410a140b8290141c00c0303080e01b4003501d000380c10041a8903003260682c0c0f085a10741c100100a8680b14403500d41c148501c0801051411494058035a400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 337155359 1250 337154109 337154119
    0xb04080c25092a0e010302070614010303020d03060b030c090a050d0503073809010612030801030210020c03030a0e0406031203020306030d030e0c011112040303021f020304080909040f0813050102100506 88
    0xc49240013603c002d901d10030b0300382c109502080b121020441d01c0c0070340c020b4160074580c0082250f2440c2002070914004440c000c080604042040050081711701c1a42d4100071005003142e5a0701944002500400080d8081c41e00301c4444c1000307005011000c805480e0450160b1017440d880780d000800050030854104010302c40ba16030103008014500c4051165074801c0030744000107100c41c1c560001d4070001c84100c10840020718440c0c018000c41c140f004810800e1101800140400075071400000d88902503400307803000700a81403044074140c1c1c1c0d55410903002160485400501590041c40060207035000300c0b401d900a02c640000440c030759100340702c1c664003500b002c00908010309110300111224a40c05680a2407403055940207a008d8160303000900c0114881d400404001c03969003001c104c00d403c41d40200051a206204000c0403503100320480704030440849000c2c80035502d600e007004411500d0b92001c0c104d148046480f015800c1c040f070060098031800d800b00d4a003600c000e04010162a0212840394101c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 337156609 1250 337155359 337155431
    0xa03030c030318020603190b0301050103020906130908040f030317090303010b0d0b03060703051e090703171201060908010f06180b0a0e09010203060f0d0b04080c2509 73
    0x801d00c290711410505007950385611843d41d90781c000440c16001501c2030341c011103108510310701e81415449078018090301a0001c1c496585142c000034024a0028640340c040c11002c035840c00003600544c82042e0066005a00e9921151925000c540c1072040c0d01040780400c510101c04210600d404034000c0c4034580c600021441c680c02c21074100d2454001c1400c0344281038481e0744107459a41c05200f0b65114020071b41d0b000489103030501d0407000d40503500da020041c1413034120074480c074414045444401d881c0c001d280000144262030782e080280c42078031003000c1d0c2c0603121400450041e07844840182240c2c2b0074002400003600300e03a00c3d1400c440d603038811072016201c80244ca55814600d90484025100b0041c83d606580b13039900a5040f1703075407088894140030b95001041001500e40400c5910010105540c0d00c4502c862550306c0c0c418405001d0005080d0000c0800c8501e025041007140c80c14402c0860764400313545c64500d40000c034080b1640500c0092600f82045510044001c0d0320500302c0507440d1034240d42c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 337157859 1250 337156609 337156613
    0x2031e070809101a0a080d090f060503160e0d0b18010b0a051513090203011e050105030601030f24030b0a0c02030d020702030703210e06090d020f030a1202060906060a03030c 76
    0x205041030011203000040c0c4c0500b4150390342c0c0c030424001090480003901e00000e1503000203164030269008681d00303004120017400a02d50040075a0b07801200310711050040c1d50310702010703156000318555541c0c1c0b040b10700024004000f0350015043c05a05d000c2a203131048898044d00c1400c0c0c608070010b403500f0511040b410083c41c64480300712409144025034079450b000314140350420f03a030700581010300f500e500000104420082046c420ba100d40c201440e403480303141850002403561002a001d90304040e128140303001112020303031080c50000d50701c1e0003d1080001c0340030240c2101c1075034407040e500800500d0002e40c0d1510035014000303079810103502461404550f0344050009402c102403d0740c0620402c1804400120075401414030b5500001c4071481c2081a03420042400e201082c5040c0a41003c1c00205100e840708a0361380b0660740e04540c00103000d0007610110b0301d0f0151003140900004114007001d1542d81c0c004c503845000e02143e00550303200ba9940320500a1111107448010001000b421003000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 337159109 1250 337157859 337157861
    0x50c090117040f0501050c03010815070801030f06060503031902010b1e010f09091107061b140c0a06020f040e1f14040f0608060106170f04081c02031e07080910 70
    0x10b8450722a001104440c841501c070b05003150400c5804401e004000401404140000c102645102107079100744209441d180000a12001061100801c500c0c0b07071014000800c103540c0c0005014020241c00c60b0389903000d2449464010810f50403010142d442d280c03581280b414004590000c807080c4000d50280d91601c5001114000e48800e100130411100320008904143c2a01900c40b0f82101001c0c043c9c0c88600604010048640043c0549503c94200d869480c030390381c01c100c0742004985e01509454841ea001c2040c64100440b80380d0042110707200245d071000f45014040940140c51a11031180c40703650b6010501c41c0d616440d12800100360a01e21802c1201c424000060548164040c00104040c0c40325010f170400d0303400642000c400c603042400140b007007541c408022000ca645070000034280b402c0910b42c00001c02c90143c00540100c40010b8900501041a01c001e8401030007403108550f2407422288525100b81440d516101c201000804501494800c10b4441d008052a4029003112403580e60030350 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 337160359 1250 337159109 337159111
    0x20d0302030c06070c140f1e030c06180705030714040902040605031603030e0f060f13050d060b010201060501030905061f0824010501140a030203060f04090f06050c090117 75
    0x181144420004000310300010f10009000300b105841d50f022441c4c01d45805101c40e00300801c040f0450784000049403040c2d50004c2c00039484010035003071041d401c103500d03449810b40c42100710b074895034418030041c8007998210040c0b40742d0f080da501041d0350029481d9010580ca40c07889120714041c1488032240c086542c80c0c503912483ca035620003440040c0b5542c0d500082410030318521505c00090030310b03604c10000c6c55000b1030394001c4604c00703c0360552010300740d00005a00d8083e414a9400d281e5002c074030300003403101004d941000b03004002c1c00c0d000300782110b28154014201c07440c9907074015400d001c0c0018055000c0d00402144942c801e000e400305503185a00c50078400450801080d41d03e406000000d0304040900100d4200211740d80d040b00642c808895018200c0c20682c0301504100208015407201608842505d6038030059180240ea25110600010b204c0b0705c01c0c00f9020351042c501510745c001c0149034200085201e100302030502c807507034a0b003030140020b00a818000e80464241c0c5800308110001d580d4803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 337161609 1250 337160359 337160363
    0xf0302011d030c0d051b0907171801021b01060602060402150304020102011d0a03110c03120f072019030c151202040303080621030901030504060905060405030904060504020403020d020d 81
    0x850b0143c401800142030316a800e80180e83e03541140703181c8420081803841a20080c8030640e0548074508020702c00522949100d0691185c40c4641d101158142105030f41c42c426081c240d40003907403070b00c50f20311000e451540e241041d4081c5619011001944500100d04544a130340c00a0658101c10140e0a01c002158002041241103540e10180412804820340e22144c101a05d08001e00c5401d420380340141c1034400083e255000c0c0e0f0302800405000395800550610f41d040c1c1c0ba5401c4d5200c81d0b000c902c10401d030150a07801132481a079203a0000d14a504640342441c01c3d0703411030701040400c4001007000c0c142d00344c5d170001400c03440006405001d0448030400d031710082d402c20714100b181c549810380010f0807604160030440000c2d070b42c0814880d140c60505403030b00300c8001d4021680200c12041c922103980e071090515580c1410744950026083c050359a1008026641000c11360340c0603c0c0038a04183c41764000043c05d48a0340c600440172030641401d200351002e0320740c083c1034402c070842640c0800a03114145942 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 337162859 1250 337161609 337161613
    0x1060504090b0619050309010617060c2b09030e0906150306031018060b0102030309030d1805100b090718090209150406030f1d2d0f070f0f0302011d03 66
    0xc420048090584d001d030f130200c11955010740300d080003080c0d80d00390340c0d10f940501007500000440c01101130010a501e81c00c2a482c41010f1380d200f000e101c02d0030039214014002221550200e401e20445a0310390010241c4034402d640c0d415500c84c02d5410414041c90540c0c0c0d044c0c005c1c000c00d0007100c00181420003540c009900400701d0700c00c082c100b40c0300c405803807a01125071002d0024201950420015001ea6044100240040c50031481c014807116503038006e080014414544808441d01c540448007400c5207155002825101c00d8001c55901401400d1b10354500e41c05403031110002103140780b0602c010a1011881140c0c0400e0b40d150001d0800607401552900754080c40101c0004120301c10000140020b0505880100c3c0c0c80c803415940d542118000d81d1003824840700c0140b40d040c20400070500340f12140c1d0820800f0312038220001030090702c0200381d20900e03c0f40b244112007200144009030100880c0c0380d4007140306100c1d49400c0c2d0040300e0b41c0c1d50311000703010070340e045050715030004400c02a01194601030b003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 337164109 1250 337162859 337162867
    0x21c2d0201020c030706060e09070e13020103020d020d05460f140703200910020c0603090a050618070e0a0912080604050a09050d0c0203010b030601030c061701060504090b06 76
    0x303203d07400c5511a0108031481c541d103802c1007052018010403281d20461440c080d121152410b0800f80f41080c00a01103085482d02240c43d20440e0f000394140c0c2c0309030900f440210744403560b000c0719100600701a00c25040c01d4035404042141901c0c200340b13440500801868403034080d84007110042141c005049180c070b03070740d031514a4104c1400f0284910000340300c4043c1c1c4164141003841c4041d046904540008181c07025126480700c0f9959900c0403903041d080b0a64907640b00c07220740c1404074203110303010001990045002003031000000300000e0b00c51542d405802904c8150321002803008650040c0108a40c00d9000341404000304c5101d4035445a0040d80c101c0042a21103295035041c240c91003401c90705000c514190300740086170605103d280d9014048450401c10b00c4856200e0b150b854503001c9072907007000303d5a4401811910290004003030484003408480315541c40e40303000c602e019000c0c0030b60000500303070302ca002200601c28002c0904a0350552913181c549414244180061b01078a0401500180108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 337165359 1250 337164109 337164127
    0xd020d1808070b010807030203030a1103090901080601090605010507020f04090302100c020303220f0b130203070b0903060705070c0e06040207120207180e062410021c2d020102 77
    0x10350601000c0c81480e22960350002440e00541c04034041e048965580d001d80020720041e200041118580000c6043c02150003605000b02441c52103884510b0703801890040000a060400059140c183c3e1810302c400e004144d10340340115941e02400e20040c1d442465aa004642d6051030f41c0001e4204d40240705880c1041445103d8005542c441040280141e00000c2009910030342c844007040703011070701d4200c4a618040307a00c0d1400b0902c006000030304058a000b010032003c0d050384201241503903000d4140c80c040c42c1e8550300e0441d5900101005400307400742400040c5881e00ca4421123000507400000f0f026064100140103585a5000317201a801a86c2000900d001c5003505074000354108155006003406070415010301a02112140d21005403401c2007080e0303004420200765290301000251200011000c40310b810a440752a082e1110b401501103d103103541a03a001c40c20401941900d0800e441c1c03103183d88004c988285800c44c0610b1502d50740c80c03d2a4a044e290045104580000e00c0054140a161 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 337166609 1250 337165359 337165391
    0x30c09010b09030f03190f090303050a08220311011109090f0c070606081e0115060c0501060b0f041d13030305090f0105100e0f0c04060c17030a050a0f0c050d020d 71
    0x402c06c25048250340500d0b00d5182d40e200c461103024540d14a810b8004615542e00034200e40101100c610a01c800a00090103a0134015a138112038221502101d040520710706024040710040d19141d0b4440d404c00803c0d81c04480c4481c2113604980002e000e810044c1d980f4042080484e03005004e40c0c40b100820048200443c500c0c0c06503038058190500682401c1040d002503801e003110115403400280d043c002c5a504590255103454225810340c01c0101c003564152610b00d0040559800640101f00082407142000090b03070090710503152502c40400b2030b1103d59040c2420024101c0e2040400244c2d140017400091207a00055001070b0032034115409120030410307840c29035404036181080700140c10001c00100c008018407580146c140b0b08503030703900d0504242201091045000b20404d000780d00040e0000c1102600c03508049217031a483c403030b0300c1e818602d201001070001600c0c05a9a00e042c40d440018030803181c82401900c1e0724544800c3c8c41c1480100103c0b0203900141130215030150b9030052a43c0040c24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 337167859 1250 337166609 337166617
    0x310507180f02131403060601050a0e0319081b011a010e060702040507030e0111031005090705190305041103010e070e10090501170715020601060c0c120302100605030c09010b09030f03 80
    0x580c0c65064045400c0c500c204e002285a0600d241c440d60104c000e00c9401c4e44c0120031915001118504101c00c41d0540b40424642104001c2c01e540400c0c030361075000300340048003018003111807110210f08080001607401d10f0903140800c2c042e01c0c0300c581e8101344502560051186522455001e442a4101000c5400003400c03608100c942e500403d84070003400500b000d080c4990790060702080519800c0d4200b841da07400011b4040e005481c06140c00340b000c502c0203401501550209010741c1028114441809001006468152000c41e44003944405140152606002e40b011100e490001800d40524004045030854009402c55178440049440416400e4003401420b0107002904044c9402c0c010401060f403030301000340d101242c00c41d40701c02001d840035804602541110490301d440703822001c482c00c14550030a40341e448a003c0c8102082040d04064010900b000c1440c1600b80401c10f965558080c152a441c00c400103981c8062030400602030216640040e203030461019089450040759400d1141c51540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 337169109 1250 337167859 337167877
    0x305190f0b040b01050403081207020a120c0c0911031302040605040606170105040203010e0f060f04060602160602030f07240519050903120a020a0c0209310507180f02 73
    0x18070307115046600e0070203008a43c1c09002c01c0c40e00030319044c1f071742e110b0351001c0c09052450803541841078081030025201300310080120350410780f0024101e151a2000d0500d070610842121900603408000464900f1441200d59400c0340d44000c5145541d00c07032840350003040c501740499005942e0a008240d0391510710a90001d4030340307a114280c0c180c0154021082c1c8242c16440140b0036030042006000341c06032000802d401030380500c0000115110140004c02648007102880d070858900080041d036564001000d407240d008818031322503e01e890300d40481c0c8030f05c84c0b01e602001446040240500180c29418041e9680c5c40d12509440803d0450702c8510035510141d0386116103100c8400303201000781c55842042d811200345002903140402941c1003d0302c10310000c150070880340e4003050502c000303030042c8054001554001d10043e000e107042682c00030b644402e00400301d4140c01483ca640759401e00b44c2568103c15030008020030b092803a040032641118106c02c00c074111541c50782c0d02d00600c2200c1e800a444610 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 337170359 1250 337169109 337169111
    0x70c050706020f28150603081c0506010801060e1212030109060f08060f01090923030333060c16090f0b0405040b0f06060405030a080304052b0305190f 66
    0x5401c04203007038948001801d481d1540013206a2070722641d1082041040b50690080e45002040703c03100004004192962000c1d000380c1000490032410131012142810004208a003045991501c1e80110780c00c0009002e0040824040c42d1100c003546800852818910901421a4022045007a54038907e410a03400300c10f00c03a8459905100300e103040c07065031001d0408000148820b16000d840448241410b200300410159545018024000c5000c003681009071801e142429005540131400d540b90b00c1110400700703043c002480450002c10306480700304503103d81c81415070740782c040c0c404125072a41f01d070700d070540184102c003042d51015560b581d9480c010001008006600500b044240d400c2c1c3e44c100444500c164582000c01c80002c5a11070710360f401c20308114030000d140e90b420b00440e00c14466900404c0c0d05100d8440303100304000001d8000e41c8100e03c52400d030340c070000c15003042ca46146900c00740640080346003118280030724070035032060740e00c01c695034000b0701c500620b0301820085603110418030720383c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 337171609 1250 337170359 337170373
    0x40909020a081605060f12041b08010204080c1005160b0105040f0e1b120729030105010f0c03021507020a0302010c05090a09020706240e160c0b070c05070602 69
    0x50710300140d40344001c065a6018002c8051282c0d000708a5a043d801350b42e106800214000610321840c10554009807007203810719400303041a08055900080c405104c2c0c100d52640303880401c4400c0d042c000d41d000c5030342c1700c0c0080c203d030540c05081040f4003d00348000c004002d428404800c2840d60300c2c81d5942c07110f0007140b0034900c65060105100684042c0d440b8401074904040e204100ba07040020310309900b820000b010000481d83c0341c00500a800d4100e40300bc200e00c80c0110206048080048464100e5941c078011824406c0c223549804d601d000c00d1050a0105500f8015110040c0c0504c0d5044100351007841030b10140c130304504142e03010840644103500144d00c441007060406409200c2c0c09200f400c90300f00706003020074110000750030031003034041d1440450f0045080030030070500d42c1052941f00c0009074803c8504140d6142caa502d00c040d403042ca2a0400e806000c1480c4030002d4802078070003130495031220000c03d0141ca40d483c090801801000401120314403000100e00f080c05400b0251146070b02034058 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 337172859 1250 337171609 337171613
    0x504121401110a0f031407050d09080307020c0307050d080906160f080a0206090c0901050d1403030903072d0204020a0519050408010c0806031b13020a050901030f0b0d11040908040909 80
    0x1c0d0783c0c0181c41107003494a0f181b42007101d140c0d01c91280e82d0240152a115948240201c66800541910721006042504c04014043e010340c010941144422095080b900a90354410402c21101c04c840e4020302000380421076540c0e80d04120f8000d20250329040030410303400009513210000c000340c03102e06035800c4402184135900d041c3d040c00748a80020490000b8007512010a00080000c0c034180f10795441400500881410441c10324164149500030740156174603482d014205a0301c0780e01180048549003420f100108050b07646c07000401144949102c008502c0c600d6038203010083d445014031405000081c0301c40145c8101406444031075048035596992503600d8041d01e10300b581c86c04c02d200000d2040392410030000380c900042c600d403c0d61103500b003a08809255000b24200c0d03001407a13403000180c00060360042c01600b240041070038810030398041181c64000d00442d02168a081442070b031144003030701c0c10130116032141c10502071020010000181b0083c82d9651a103294401d42c024100241c980d044003007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 337174109 1250 337172859 337172867
    0xb070303020a03052d06030a0506040b090f06070504030f03120504140c101202091207060309050705011d0f2709060a021201062f0609100c0504121401110a 68
    0x1800243e5503988032850703070300c0e0203020892a0400000c00c0c5d08211003000140a50740c00c00c007105031990040140c42c00c50404c2d040c850b413904800c07908001a44039411005030007400008189104406591300d240c1098219956403a0050000d82c042d0300700041003000d070162600512440c1d01691044682400e40d019990203030703040c203440301c0c0b89034032409402c1d80152140d42c200380a0b0320044003070400107036100030304400035204114001243c4210f228000d00400c605030076a0002c12014040d50440700c449a0b258011200080319500c184040140ca031000e140608107107060040600e4010900c18208000900e5105444010061982010624000e0115400c401d10487d50045c0e81104150b10707001c40103a0310f900e400c0c410b00c20481080004048030280203008107036844000c44c0055429401c020340000c1d180c0c0e459007039601908600a041f0316044c051264891040c40a0954441600b01f92510410020595002c0c405030303011070780c80c00c440f01c484000780301c0c1500d1408900c030b295485005e0b0b804010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 337175359 1250 337174109 337174111
    0x9060603020d0608010c02070b03190c0c03020c0a05060405010c38010f0605070f050705150301140109052d04021b060f0405030316030912020705010f0302120604020f040b070303020a0305 82
    0x85090303498036500e20225a1f0100e5490256045518943c1ea01d449500c440728103003c5105d441812585006e00484034030341d000300303c42c05440c029403c42d030f0303049142005c00903801c50034800e4a5200364100400c000039405001040c0580340a01180c0c0c21444030000543d03404170100261140040480b1528840404401d600c10301600d81001d0403880c4504105002d0b1036842008005001c01c40400c808908000e000c1152a0240c035014045000d043c601c0c49035a0181d41080c000d40f0381440440ea41002554414200503003141c070014101450b42491302480103644050401d204030f805140d0041c6401c3c0d0700c4500007854460000f000358410000e602e02032904040c400b40548001101880c1030001040c030000039aa000314600961241144400009600908071000c0003492829158100c486940d008921481142e40c284c850b0344442103c5002102240708202c0654080b90140c0c000c10b4043c14194050084101c5402d002e074505070f12040010030b540c01039041100042e8001503188480740e0303d80141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 337176609 1250 337175359 337175369
    0x21f0f0206240625060b04050402010c030e0f0904150e070b04030209072a02030c042906040305060906091b0315060103110a120c02060403020d0e030709060603020d06 73
    0x60031150a04450008400415401c500c95030070300c2c480009059a200c1040300d2035440394101c1d5549052900b0b180300041c0c00d0042c02a1030843c5010604800c40c18140140c1c1c0c4140d0307050f540c0701d5a40515070ba0940c5c80700003801c10305411403080000c0035031585034030174240c0c080c030b005040c0720303000d2100441c1081c150f07100740500074003e41085a0403ca51703a03051081d40e0540b5412101c031041030740c80c0c034011a50803400c141d840501d4120415011051218003621418281c0281c040d10f010781003400074001900d00e4940321a6005403800d604140789441c60b000030621400c0101603c0ca40f956075201c0a01d02401039602a120b50010814404060010000c080b0b440d404980b04401d40205280005e40715a452400007018400d0580098220f0b03110303600c4840910000f0100c0c40e128005014020300c030b15001e80301c406800b03140162500081c0e0000403414400c6905500a0041d41c1003c4801ca490101e070055050300751103480000724900e14140500009070180303a80053b110040d50318104240d64140d402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 337177859 1250 337176609 337176613
    0x309110102010b060403060c050f0301150305150a0b09040b0904050d0e0f01091e0305010c0c03090e130f060b0409060b010e010906081302031005010b0307120c0503061507021f0f02 79
    0x12009042c0c83d6003017502c045a4000d034000500400d880d20640d20752142e551850070601c0008004550b212003400c0c2c501c1101754540d0100810b94070540603004469614480d41d0f40040c40c04010020103042000418821802800c04203409004078003044034880c0580781100c1a42000c0050310010b035115441c44c0016804448414894090100203081043e9900507038010350f00c5a07548140d0f071343d8259851801141d0000003002480501800180480008042100001d030000b5000522079403001c015402800c6011900e400c0b4902a0765401c0c00b60001c60007150183e840c2c00401199603150f2140c14800d42c02080b021aa036000c41000401d0a8425004076040c04102e2a041c000250700007840c552200c907840d04a042c1342ca2600001c1e150441c0001c044451030f00340400821078102d1600510301604107a00c1d03032589401d2608004040d03511440d00340d40001c50074000605289407144420401c0c0d0050b1042c92314060340c0703401040f2514029001001d051400038180000b29601507131101407002c1501c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 337179109 1250 337177859 337177871
    0x40614090a0212040209040f0b010803131e090507090b040b040504060501110d2006040c09060b07050309040b010c14071517041b080d02060106020d0e030c090901020f0703030911010201 81
    0x500349583c460190010740150340ca80005002c11402c126000c103602d41141c4c00081c1c0d9a51030301020b560760301440c2c01d01c1c1110030507200014181030900584210315809812002c07180e003090319403c000d0400030508000c00880050008684c1d04540050025200d803442580c1c0d0369041c030b818842558015880329040000ca402100c41429010507540b0003516603240110481c103e0034520980c80c01c112441011a02401382400108007517070070181300b00c0f03502c4041408481d0359841c0f100c0c0c03a800342c840040c0a540042049100e00d140941c0302445800d81410400d0080303207192a0300042020070207080009900000d424041c0b98002d001d00f2103e4a5140390491180030f030404480e01c070500182000380034041d090350308141d2414140c550b101034240401150030305031210000940d0b403c0f084c0710b001302500a15103c40211071050455903480c400141c02420146e5040d000d01c071602d40c00606868944d58248207200d1140380701c00c0100541c50090b580400c0360305013403d00507003130040100348505680c5050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 337180359 1250 337179109 337179127
    0x6050a030f11280f0b03100905090a140123010503030406031806051003030f0c1101050901021609090b01170703141c11060a2c030702040614090a02 65
    0x65004035240d41d110400440c000268004070302410f0194024030880c414222482c5090400140000c007120aa0301c0c2c01e440d00c964407105907405202c00d0f9074402c10029500d0003401029410703000260041e081c20f044890b038821a850701c11500012403620030740c2d0794650b10741c7d140707108402400002590071f04100d2951035140c08000303562842544920028580c440c00ea1040700d80e0000d041004180d0452001d1001e8905461222903030503c074001100800d4100381510a00b80c40303014141c1119512949e80040c0442e0100155a1500615201230443c420084410410704030303214101c004085100c004541800700b0301c1d03c5c850300181600026005840b1110002c2d60800005850045039000410703000020055041c1340c0c01c000d43e800c104c880c030501c24222801495800300303441580e802c400d400c0e100b0036224100408140e8032a01c00e5640541e40d44400d000c100766800000c01202c0c00401c1c21a8038101840e4081003c1d1307429a4002c50b42050398840013007550400c4a107282e801070001034114a412925 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 337181609 1250 337180359 337180373
    0x106081b0103110d09050f03070c0e18010911100e06031308220e060117070509010207180903090e01150e0f04020d090309060906090e041e0602090406050a03 69
    0x4100200c840410040030696074001c2d44143c00c0c1208410031565030743c4900305580e000c1c1501e0300c03040b5518491075654207030049020056071101c6034005041c440307803860302c44000795402c0054141c3e50025241c2c0c1e014407441000740309602c03400e40302d80400700c2100070300802c000c1041e482030705490500415580c0c1e141e141d51a2000c6075401078445050195807000c504103418180034181504401032012642e07400d000c0c0000004108460f040c0001e20500d60f20703100116020b841480704a03220b1080300010074141402203000d049000340610440d60680d9071118030714568500501040c41242d0b94284d140d0516500c584032102030310682c04070619035450701d0401c80310407e20800074020032103440c0c1296801e0307642220b05010038400601c2903441c0e0103c41101c000920008608034041490340b0000a041802800418100c3d0303403503103460010919202c0319001d1543c004104480c03680550741041c1c41000a19a00c03000306000300c00040e15a9038500602045a0090304000d124641c8220100001844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 337182859 1250 337181609 337181623
    0x50a0b0709081c0c150e010606110c0909010e0d0c050c0108040816030c080304151505030705090405070306091415010e0406090309210c0902070201270806011205010e010608 76
    0x5000d41044450f403000003c5406403010031008081d8000c01d80003050461298100c0a000c1c00464000c000c1f07542c0d41c480c1914070807400014800150005030155486141280481c1e5005440c000041340c540e00782a40740e030900c2c828294282c04103e42c100c000060080411091300100340c203003000111820300d5107a400c40c038001c18140d1920b1208001c840000c261282a021912650015003d88c480c20300b841c240c4c104188104c440c8240e107282ca0350540c1520003402021045032809805040b07514144410300c12134040050003900d8520940e4000800200b00b4880c0e864483e010712561800b0b82100ca16160030500b01242942d00c182281c070061240c02a41c0d826260820780c080e03400107001403907107010b0300d40d0a050b42c4000e1504410f0703c0703076400307220301c2c50000448948940c2084900540381c3c14550100d005075200070b40003072540341c5404079030303a0f8580015050344215018040156568445503250840981101903680c0454100030104a400d002d0621458928002800f80782d0801104a43d00d0f48 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 337184109 1250 337182859 337182883
    0x1209061e1503100203010e0912030604020f0c0d0201051e0108060f0405160603050106030f0603081206060417010f1a0f10030e03040909030215070e0d0602090d050a0b070908 76
    0x9000d9000c101c0c080d091440750800e510001c0c0c00d48080014a1001c20300030340007440703260f6954003804001201d041c4041094a450078100d860242035880e1842400003d404c042e00b03038185e10400f0420500d00260401410f41840c080c2c2d400480c175490444c011644c0b40d88845041e000c501020703401030142e45c0c030118800c2d520021442000c0207699850500500d0010203400a40c0754000207031012820640c550400c0d4183e40c240d480a2107002e241038174070741c211111840060188032051145058500c03000121300c0d0040c800030400b5050a84420910201d4800c1541003100c1760b541307080d0340e03100c0442d50043d043d52100100900c09940384150100d0f42e0100070580300c510075000d04095000e1075010364021905170042c007007145d4030f460f110000f074001801082c0e000d030050302c03810899001d058401c120041c0314644695810849100900c1404204a6540c40441e401502400400d146441d0351616040d1180038000400244040341440302e211230015091104100c0c041800b441aa4000070b40c0031030007030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 337185359 1250 337184109 337184161
    0x17040303020f1c0c02211812060f041104020408030a03241403060f01150c11131b0f050f0306030118030f11011a01030c23120906 57
    0x51800002c0308450f114242d103003280503031901c0c58180364070301d07070750040c154a44550205c40b540a620700b2880c0354603000e0510b90b044a4010082055010a00351442c5100c3c200507140400040c1c041040c24200703c8110703030050602da920f500b040701b072000c81aa280d40f41642a2011854035090804c1c0d581c40e88101c910071800d05440303030340035240b81c08032100352071174000c00034102c03803910340c440031420040c03000344007458447d114171004101c0c1090035030440b0303041f5440030229040d200300100c02035542c040c0d4110144d9100d4075020402d0380ca40c4410340002500c07481418005886a482207074404505200b00000040000901040d014950000c044640d107c08114030f59071641c1d41d410001c1d0140c03540381c003604210102d418030307201015040403500390b00742186e484250003d601d21071920300300c403420003c04d4005800c58144000f694003d07031040068021910340700c01ca5090076030f0300d408114641001d22010440000d82110b04546401949410684080181c500ca042000078010600035140d420b900032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 337186609 1250 337185359 337185367
    0xb010507030c14060c09190509040f06020705061501020f2a13020a0e03071205071824080115050603010e100306050f0402150a0c2d0813061704030302 66
    0x2004046480f1108100c0c680700725109464060084c0c44a9006900194040e0a580c01c1d900115082148801c00ba620082c001010325501c6032918040260510016240c0ca45d08010304400b151043c05014031a074051b1220101990041700021f1503c0c5160700c618206401c01e03c1c03d079684440e9494450b034204104003000480064040c006403d148030b030141140c4c2e2074800075141c00742e10703005689a145c10000300d040d5984c80d5510b020007880300700d004000500c2c1e0781100406200340d00c80526902150350006000144606044030034825003002811400d490454003402000030420034010200c80054454581988518203030206160b4041030040700111901400024900103401005100954101c002840301781403194402c041c00320140c2d401c3e0b024200d0036060002c810044e40c11284c100200b03a0318a45128041c0c5c0740d4201c02e0f1103041036280e40200003400d150302d0720501e0318a1300c007071401107105954480540500c20b41d0b07204158862018048881c1d0080b80c4e02800401c0682d1291301800c016980b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 337187859 1250 337186609 337186613
    0x801090c0b0d02121609080a1a0408090d030c021311090d061104060507020a051f030c020f070603140708010609030602090402040e090109051b030c010e061201031209090b010507030c 80
    0x2a01586054404401a940c10032410501d086142d01c5860324644480c06c049440702d580c60f4454015080c0580300900341005d0700441a50403100ba64030501036a011b500b420100c1d400180300d00390041c0150001480301140d0340030751902040d04855840041d80801c10036a01032510202030042800c114401c201d0090302006000590704401e550546161006644507210400505143c0104c042a0b01500000340089014240201d0945c016440403d4840c042000d1410031009000aa05403401310701400c421120082030400284014240759140810085c0c580c041c0007042e0f4600130811410480200010400b07547c00001c4542035980007840980e4a240c0c1c000400e02074403542d88040b07019458141081390302072065010f49401845002510300320080c65444000c0f2034154140540e064100040100c560740c00b802502d00048405414035092640c0d4400003200c6803c00d900a940d56012410b107500c68580c0807000b80068800d4000402041400b100028a54010302c44000c050020654040007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 337189109 1250 337187859 337187861
    0x240603100e0f0a061e090b0d141005061906081b0304060e1501051309050a0506090309031501080a03030e0309030a1b060c02100530010e010801090c0b0d 67
    0x9040c4208840303085082c918110310b10300b942254105001481c0110118840b0b040c8003a03000d1010703020245821036402c0000f07110081076440c07141c0b503010b40e80428110000392092810b64100c0c110102600313032458903003406025200c0013002d0300e03c80eaa010040707180350301d80c4240410079148c40c1e00e0164182e07541c84c00c04070030107131140c0103a51080c0d801104010410a03150000d5890681c88829aa02c0700322440c2c1590b034000e028094194000c5603001401d152580c1c603841550b00300d0054080f10200c01560711070303508208060b515520213400001e810140c07030800704001d0144c182140d109004540c509820030346c540e6141540141015103829030034031628020002d82d058504010f00791a100d400d0303032811003950604551041060540380f100010414050503190005a8024140154004401c0030488840d0300040404104c010304090071000d4101d151b034800380d03048054000e43c486504102400840c0f44050384101680ea04000c02c00e00094000d401c400101c4082c00283c0ba00c070019030b06208 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 337190359 1250 337189109 337189141
    0xe0706080711070e0103021f020c0f04090f0b0f06010801030f081608030a0c08010906050105040308031314030c060109091e02060c0d03020d110705120d06030206030c0304020405240603 81
    0x40551265500100d013800000007a14101d03482100c2442c40010055154600d0801c0a07440f40c0142c0c00020100030740d81400b03e0141900900104000347c2c030642540c544903000b04080d030940f800240041004032401c100d0007a0f9030071440c2420140b0b100d61460b952030245640e250070040c080a0041036600311114500a620885a40500301e01d44074a031295125004101c0000000c0c00140741c40c0001440103c588540001c0e2903044e56801c2c507107070640d102e92140d6440681030307103180c1034000710910100e1500300344c10081c0c2c110302001e107030f5400c000c0744654500841a002050f0382c1d86405a8140020805040141d28007140340740d521300c80d011030000400c2030052100c1b8a01e00e006042035510080e9040d130040c407a0482001040108a46000c51070b0054050300a0082040d4841c102c0c450058040501402031045c442d000410ba040d103030740c0801c41c170360001d4400020b805004004e0000318601401490f5011903090b030f6100c5059480c0c0f0342c441d06000141c24003802108000041141d50307460301495 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 337191609 1250 337190359 337190387
    0xf020a091107060605011b0f08041512050105011b02090a0b04020319050c04030c060503150d030f020105061206011401020a050604030e210618010f050403120f0e07060807 75
    0x1c0041d00102505181550301c0800112042071a101c0d011411b580151902c03011800300c0d592825100c03540b82c0d250016119080826103103a0410300001030a20740e040d10351041410541e50303031552001d40820312000d540040c1c100c9814405141d0b0001d01d001100716110031642d404450030869500d079241200c0c010003601c404181c01a0000080105009903450000c22158800c0d408000b50343d54100780380001c0c051800010203e2100500401803d03109101468005a01c0c0682000c088a20b00003e525030f070300800203c0218099420b0340303040a4080c4100c9900c4617003038131583c4011801507040750312000d05020b0a8400982c909400905034420041c1100c166440022150503003000c0c100500722000410209101e10002d4600c010003490a5809441000c407100c000c0255885021850450b5801e4090340c80e501e42d640c101c06021141315028150195001ba1900c0e46120000103008082e20520600c0d011454140006c0c2c00481c200054120104d402c10f1624007025107402e001218000060329070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 337192859 1250 337191609 337191611
    0xe010f050d0b1e0f09010e070f1b050a030f020a052107020402130305011b0c0b250e0406060e030a06020703030912030209010f03270206040b04060207081e03070f020a09 74
    0x10300840703165030303002c4203d28036811520200c00c0031100c030030010f030765000b4000c031182c0c0e9910b600443c2c4e215009200006c0c241c0d4480c2000c00010800c00c0e205201c0c1548134405072503681c42240e031081451b8001544100e051203900c041e045104191301d40c44d64812140010030081260300c610390790054000001d584c038013503000780255901d80b0b0f0041d246292998a001c240c5440d441e04500000b403d40707104d002c2110b1400e94484c003540034565200c0b29025440149406440c19581010b4444000303142c90018135410384cd22400d019481c2e2400340002c455164000e40b0520802a80440c81907400007004500d20b940004056680c603181c2c89c08502400403004004c201c0c0410030081d541198141c0c0292410000a0762076001008186008a003581c10400c2c8200070789000c08084c1c902020150b429020740c0d07001909140c6483c1d910502901194410b500c2040141c0041505011092040c050410141d00070b159406000b8a25001c10391a0312402c04010304450400d2244003c6485c2c19030118018551510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 337194109 1250 337192859 337192879
    0xc0a2a1b050a03060b04060602070e0c031e0c07120f0203071106041205070305060a1e0b0333011d06190f0b09090f010e011215061202010207060e010f050d0b 69
    0x50b11034040c0003000003086c4981d06112010820608c00100101200d02d84200e010310380d203800c4e801015580c8042c0001c404c2159141500f40d41e509420f24460045603040c0d0210b948020a0034a030401c120758034a002c04000102e41410b0b44a9800400ea400c2d02e071304454044844080280064800d22407903004141540c1d4004240080c004042005030440f4022003c3d94281c0c2d4502c56403004a0f61107158401e010380d01a81600d0180219500080c00300038050204d811840307584c518a008100c202c0c0710100d26580d003007030702102c1c986c04501103401000400d040c0300e44400c2180f000301228000070b003401d0081c5070308020000c61200058110008200300c10039440980d86940c103000c9140d0190090a000346142000f240302c10001040046c1201c00c0d212000c3d8059091180b060304d0026100c0003591400110420500f08a480344510001091030484507140f405281c80003a040611560140c02807081d0403282d16101d03600000a5805100e071441c000e0364174109031000500400314800029004000c40c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 337195359 1250 337194109 337194113
    0xc1803070512150702061320180714030c0904091a0c120105030d0f0e0402070803130302160e0c0d060312080a06050415030f020a0e0c0a2a1b050a03 65
    0x4038460690100002c1a08070f03542d259142aaa60724055a0603080c1c8000101e6442c085650811451140c07645100c031813808122200019800c584000002d1303284201400503c04402e4100c50303d00b4401802c0030f41c03d4103620740074481d50301901640401074010750b25404044104003200c5810440ca0403941070000345811312911280250b0403980e01d4000080403400046124900080c110901c6d404c2d0b1356840c844400d544c1c0382160802c2c08a058140c000d9001d00c07024000030b0b500c001861042a8040746030196503640e0130020702e4614000010160200802c20074002e10301e0b5070780c07800d90041d580641d030340c1d07034680d11401d030b0000703001d103500180c10005613800d50820158810105402030713031101d03030a00072551190f00f04011242c1e56181090f0380f0302540c00c1000040d035503060239083c59000500f40c1c0400365980d050040308601c00c85009108910000306204c3c4a504492044180c000c8140201d54010f9251045c280422002078090103403865455209413140641d034007440980009403102524507600c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 337196609 1250 337195359 337195363
    0x10051c0902010f080603030d0e12180906040902130c021f05060a0503010c0504120804050907020a0308090304030209070309050703120504330c0606030204060308040510080c1803070512 81
    0x9103104a00041c0b40840380c4100c01d224204040c01604001d015502d003101c6690728000a0403030f8243c2d900349000ea00500316510341d074880580341c08054071102c80200440319041101008c0c009000760b11a41c50002c8420150301e035200580a040c000700d0f00018140440f10702a13203803490b1403440911140d54003140403140444d6810550082009039483c507540317600c1c0c01c00c140c00e07503503c1c000101c0000d00500c0108444607080c8070300b25695001c1c030b00f203601e01a01e6034003144107032504030b0f076a00259100d03502440c101a0700418841d400002e4101440c20b007800c650000d045030030003520900c100341d103503404c00091240c1805072800440e400003854002035001c1b0406489904640b181c000048202a0250468440700e038410200b4100840c84001d12006404240c41042100806035010b5940d4900400113858901c100c2d000f46000c0d664a5488a1420341048008055981410f041106c00c0003400125104403090310000c2c10b82d1100003401c0202c07440070038681403ca6200d250b0240e65104100442000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 337197859 1250 337196609 337196621
    0x503040f1e020103231f0b0706060807170d030f0e01090302011d0c0d0201140c1b0a0909030c0b0604020c0604060b01030c091a18130c02010515060910051c 68
    0x401e88085c011300001d202e03055480301e10f0790340c84541246800d000500c0d12602e0f4122028a1581051000d603ca032034070082a016046a04100c500036a140801c0c0080354003004a1b00042c4943c114881980c00140c080c079499624101c0e1200603d62a000b0f00002c5a12030f81202580c00c2044c0001c11084616060080c080d0221066010700e0340c4880c1c0d15182240c00128601ca604100a02298601c40090340116007054414194031159941801070040a92081c000c0b50141701c00c0c90450000c0e004060204000022985d01130140070303291400220010350030203050396083c1c1d0001418080741e56410041303000313032244a041c80c003640107410403c401c008003a130003400e40b10000e0381c00300050544c8034000ea0b13034024203008070700c072600f80d03080c450702000740d6000203004025280494000d50308840d404510700b01c0c154503d10701c41603105d240c50f4205582c24032400340d1018020564010030740720040030a8243c07040010584c041c032803c0c18000c02a03801403040f500200448a802504403807151021340084c60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 337199109 1250 337197859 337197863
    0xf0c020a060b1207120203030c070303090e0705072f130203040c080c060d0207020a0509070203091e0d03050c0f030319060f051e0a0308130f0e010311010503040f1e 72
    0x2c9002c80329a00d9007400c41004000303240031001441054140240c42e071842d194800101ea0600c0104031007503006000f4407180d00114881d848007881035040c189a202142801410801009024415000480d00310325401001220144003400c000e403640130754406008400031843d0b04800d444041c1a1041c2450b801135204500541c01064003c0d10f8801c100c2e10b504000e6480c0368084000c0c01540d1362000d00c4c1d801460b203148002c0403042c1c1169240049083c0c40d10485030100983c0004c111800da40c01c2a000c20032a070f0014441c040d1540095100042090f1130703842022b01000000704050b44c2e02e6008201107050004070004a07603ca1501a01194581d581c03442424140742c01d00c0000a54111007660714015160014084081646090444101d804005980d01d86c400c0c0a088000041000341004101103402c07260141180c40c10049582c83c040403a600001007049803a00400c045034044031030610003c401d11f46aa074945035414900360002c854000902900610721000c0a101c1a60401020a40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 337200359 1250 337199109 337199111
    0x40f1b0b0a021e011802090a091a0601031d071802040b0c0c010212030103020d020607080706060801020a0f090509070f27090e0d0c1502070f050304050a0e0417030a0f0c020a06 77
    0x80b020010500307031707144190a14041e00c101c0b201c10005241c80780e800780e4000c451000c001001e50240c2c8401404000c0005c8900b0b00c140c810040c407640d943e05001719800017284001d03120400d400102c07000c0d43c4940600c160502c030112081c4401b183c0c100340e01110b008245422486880307024017000180c4401542604902520a800b8402085000201543d04a039001011300d900b8a0701a020307c1030580c011001100c51134000c00c0310400040700707403150b0405409403400041e118030540801800000f40d550004041c0b010301c6c131040205a48000f201680004245883c0c101c0f000c3d01d00d02030f165980b00070900c540d903100050125004d20160028001110349002090042c4a0500d90080d1907000c5001754100007006260410082900b40708041001e081041380146485c4d255240d4040720420201c0403642500001000c01941c0f404850410140080907409107042c21f00c2d075160880004410410301d200300000c80080e0b1105032036404000e096821043c244080303090a90020b454000c01e410440b151 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 337201609 1250 337200359 337200403
    0x90b03061303050409021804051302011b1119050a0b03070f0504050d030311040801020f07150b060307030507030b0a030302060a050a050606090d05100e07080601080105040f1b0b0a02 80
    0x1c6580c01000c0082d015114586402d04020120010350700c0840b09000c01481816800c2c00c1d44c81d207110b4540b00d59440903840204083c240f0004001483c101b10107036240c8084500e801c00310398072001469407203008803101c1082d6210b5400c0c04100244990045610400c0a00e000038162014401507101d20200c0ea252295420609070507580340c01180105034010104110200010b40203034405a0142c400702841030400c0d68800646003643e1007414400c8800c2c5000c54a04c00b042400400c50504c610b000005000a044171008941743d8000141a02d0030180c1b00c0d004a45d9507400b9a01c09520b5280191811109039200d08000e5a1284191901d19035a80b4101c000303282c0183da80702d45406040e00901892600350324108005051140c400d095840380a4988144090521803040060752100340025107012440c2504090800d41d05038400b0b07005904101c1040000358040e04404c3e60140d12442106446100031310042c82c104241d044115082d0000910990554000600c20f04042c4500407078084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 337202859 1250 337201609 337201621
    0x3090c0812030109052a0705011d011a0406050105030c0d140403110d030b01020c010c060e010203040c050102070f03030504050405070e03121b0a0b0c0313050703030302070614040b22020406090b0306 87
    0x1014002003030404188084444001120142d04000c0c80021f001c2c800100c0d8ad0b21aa14404100340c400c0079024200369910f8001450400100381580f0165000f2034080052525200000e006880024200c80311544001090b02e61484298466480741002800600b03841ca894a4054884400d00c41c125046202d1140c10007032281c0b19009611001d40113038040d140c1070304400700550314000c62403001c80f51355440d4655011740300400d10246210b036000c0d00301040ca01d488c0c84006428980d2903081444400d0f1b18040c01d0000c241c01c541140c0484205071000152640c40400403107046040308540e47d80b40c00303209001400810034001500f040400e02c104902442411225603a681980d80d200500c0c0c0344c1c620000601c5c1d80030340c3c80603550101078900040180b4041d540c680c0e041c00034942003200400c1c0e0200c0d0131000c5c0a0144140e810110704201e0301c42c0c0364281a1210500c410008080070114058080c03800480001d41d9401ca01e901c0d80a44141700440d103c200407005818000700079400b0380329040c00102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 337204109 1250 337202859 337202881
    0x2030907150c0f0b0708010b0408030316090506030703060323061305010b06210105010503150f04020409020d0b1002010b0d1b03150507030b0f1003090c081203010905 73
    0x20164164000820049161031034074070306041c1d6841d10100307000c440d810407000300f20504078081030039104809500301868845030181c10b012044c1c003c802c1c00641030006201c44440001243d0700110318004100c40d00391a110100c51001c12500459002040442404581c5e81c240e0005000d4031300c60380ca600c1ea01c201c560b90000b1010100210341925a10289c007054600400c41e00300c8070800c4c0101c00104002a203840451000c1e401600400c225150850001003103d014031411030140c9403d00c5c050385107080c040141504110350700f100c1881464001004162551141c0c100ea0042c025820255110060446540300501c83c075440c403805211000002c0d41c0c114818030503150480c400409408440c4a0b94907080d41301117519202124038042820044089140044000072104010201041c1c6180c404002800c1c0d98a513180f0b41d014005030603668031242c0d1240c041c4000082c00c0c0c80c0c0003840c10f02c0d41c0bc2c5603407940342c50350040e2200d00030b4986040000e10150300960684507016014881600c90280c582 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 337205359 1250 337204109 337204111
    0x619020f120603010615050708070602072103050907030f0305180909010902010806060a23040518040618030f0e0613060801230d060218121b0607120e030a08030f01180203 75
    0x40001d00100420030009d550030000c3d2a6031402110f0042c10b207410b80c2d4030007001da500e80d48800c505c5a110b1034500034056140c040c95901030000f00c0a440d540d40703180d8401c6942c008605000f0103001d0301140d080a00101041410481e080c004d02c4c92125080c1000d8140c000c004500f000e900080507000040c001d4108007003220800849960703001c080c1d0a407101c0300300010340400011104032004200019040da41c1e8640d815541c003501180b07040501f010300e400fa04683c0b60803280d40b40d2a039000310039000701c0d40103032443c60180300074200a40916406000a0300324410350000c4000c4400954000c00c080e5032101e0034905a8502c21101c0301503034054103400d22102c3c0007406142d8450300c1c429081f4006040354016003c1020b0007c004041c1019600c0001e03407084021118182d81d0f8020048d01c86c3c0003c40030f10060000c4800e890852600307081d615400301550b04030300380c2800d1007546c805292040e10204482000240c1080340700d81c80e030520040307a00c181d000030310442240d6690f0001c80500c0070450b10031a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 337206609 1250 337205359 337205399
    0x5060c211302011815092c0604020901020a0f080a141303060f0617060a0605060c0a060b0d05030706020406020c01050c0d030903120c0201021209030307020619020f1206030106 77
    0x1150740346600440d05004500c40852440c403126400140b00c0340c1c210071044080e181500e40e05861030411451204041031100d1b60080a031080c80c51601d030b080204035094120405403070240e980c404410041c0d14084802c0c200070540d01c0100e4826003070298180107006095123540d1042e0704610050860030413801084e50000c5144c000840c104001072080d40265070107400b4420220302e095503402002c0303d0305000e090340d0042c1d070468800c0040d8120302e44540c0025003011140b140c00d02d011190b65541d41c64150200810680c0c1e900f014040350740e07507402c1d40303000c00341c1c0201140e0351001e080c509040690000c3c81007034050f200b000c42c4110950f0050054405040401004086075556000104e014060401c015024850240090080f00b441d074041c002288203a42c0015a4a2050136403801010300020201880c54205105110000360b000c1b99168101c944103082000402e03203568994000e10841d1036030341c04420001403100030002d0b03a240c5031384140c130210b001300110369841d070741c11040b40204521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337207859 1250 337206609 337206631
    0x40503030112060b0a1701060905070c20060c030a0305090d14130506040b220b0406140d050709060e0901030506220506340f0f02030705060c21 63
    0x14002e011a4140004441e400342c07101049440c07050300495013040180d003201084109a080404804c1c000340201001059600e01c01c01c020710300682c00804d0b2454912004103011b602c201d2104044a5100d204000e0b103800070285950f411281440c45e90303d502c0032000e032002c281880005034042d0780c08a1000704100b400e4032082003400c5000880f20003640501d00c030034002011040d000c030707107500c400007d40042c00100714810b07a00c0c1041005241d195441c18884000c1c00418401800042d200c80b06940441d40c0e50300700102c031244e48009010160081c0b9100e084120300d00420840210f5100070002c0c2205d41c0c039116800c2000301d91083c00802042408082c101c3d41c4040f000c10601310742a00305000d40c100c005c03040100074a280c0d583e642401c4c025100228900c0188203040b07442e060305030141d0000d00c084d0038484450405800d02410f8100c007007001d001070000d070b440500c512500038000c0b0f80800b580401070751000e01d07040c240e00b149904220f400d10441103d26103a10094070940382d00f94000c092400d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 337209109 1250 337207859 337207861
    0xc0f0303080406020318060406020a030b04060f15020721020405010602011505150d0e06090c03030715050a0f02030a1a0d021e0d0503030a091e08070624080a060c0804050303 76
    0x203c0c5400703544050022004a4605004460108020700c41d19008e584606005652000346180c010b01740ca58000d0703403520a52420380100030081002041c00c044a801d2104500600c080100503818605545d00c40d0041e043d04241c05c1d119001075281071080c491080741d0401c0607980b5844102d00301e0301c140c2d0001512a84900c1b0a02c03031443e0602c0f10030760215540701690302d0003110001c4101622a08010b41034158480310031b1101c1c1450500424881c03a005400a42c24110117884030320000300100740e2610f01c03a50b9200420061007568100031148000c1306406c4d1b59900780301424000030310403244200c515400c40341e807506a600e0509541c1c000150010402d040780901d005000c2240131441c1c20b8941c3c44070704540c41c400081d105002a512808025200244c1400070b41003402d0500030400c1c00602215a020507500082c0e440b1080c0c403c034980107000015071112a0540011034130100200607a00c0e00d9010002580000011b0803200042c818801070081c8801410203032615002901d0081103500180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 337210359 1250 337209109 337209113
    0x6030c1b020f0a0b2a0c012709020c0607030510080d050313020409030c0c050402040b0d090c0b0c1e0c0603040206070302010b10050904050711030f130506030c03040c0f03030804 78
    0x710352415858020800d9005641c4c1c0c1444001c643d004034140d000c0390380d00446030b480040302c912501101d407413558080c040d6000c01c540002e0a5100b11800c43e00410303003d011401c3c00161f91840704016143c80703031085564044095100360740d4001110580000782c24400003c2081000b00f08200440d901035004003003c1e0450442519582c0000307011148403000c00b070f00200560b40f6802045c111a0080e101e6491001c2c59041c40c44c1300c55081d800441c082c0d40108001c0004a40040407180d0031506150001501f1160b860005514101036001d081c0c0500b02260782c003c1c50788003140c002c540303403501040d81c181c0d105c0e241141a1070300030107070721198032030401e0000034058144030b0000e158240c800c0c800000c0c040888400118020700d5071100e10005000800c0318119814a44505c640104540c18003001c0c4054440388241d0b6032180101011002c00d001c030b60044601d0a2688070303009090001c003251341301d240080d9084000d0300100d80603580700b4100100000c1615103940f800007520307003603901c0001c0c554541d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 337211609 1250 337210359 337210369
    0xe060a0311070204050a02070224160f052e11040e06211e010207020a0302060d020d2a05040803032404020c0604020a170a26070c06030c1b02 62
    0x11000d0501c140c1d10420440005036164403506104c3c0e00350007070050700c8114900501444480120310040c0d407070354500703c8061741407004054504400480c0004c600022071443d06003510708240784020b10700e11502082c44081e008001082c014125501c40c00a1842e0303460004c06d0a940800a85400e001c804110038400c3c1128510555800030f000340c1020a05451000400045840c00d6424500b80d0015041041d030701380d0020811008a0584000390304004c03140e000511451194807000b8440c45000641030501c54440d01038400c4009409010080803150000d85050f1000c50080c2140c609660905400c450340500103a4040e601601c00950a43e40d5420016164508446d0107906000b003038180001503954600050252940030b00140220f07007824410300010801c07540151242c41c0d24003414002d44140018052036040d0403001e08100d00000b22003890801211070004081040f0024540c001d10400081c0042210000e6070f0403c001c0c5e031528000c0305c200c42c0b45009203814181310701c6010091311700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 337212859 1250 337211609 337211621
    0x1e0c01020412030c03020c09010312080a0b0a0608010314030304030815060405120a15020a0e010309022e080705040609330315050a08030319060f090e06070e060a03 72
    0x4014001450261242d840c00301a03070042c0401c03000a01905412020540d05215220950038217503002c0029504540e501c60040e4180000b8004100100c0002150311881c0c3d00310807a04007002c1c10000c145d60320340070001d0038220b09000503900340780c0340e0416040022000045a00c070b030780c16913103221498881703200c518603034107229a80da60f0100042c440400c8a50b160040b4681c5c181122009203403120f00d62405071503080c83e02180540c500d106225009040d41c005080c5202800c00746400522010607100080c03a00800500c400b900b40c14803e81c20f84265031070502459903c11f280c490308039540c0c0307100d400c4480d441540500c000245080404124841405020b00d41d0220360424081c81164031040e082170a941b80e0352001c001a4480c07956103a10480035503294060401030700d190b6486401c14110b2603580c40f0203440340342c02c1d0319082000f80c409486680040b000c2e201404c02012425a02c0101e40d02800e04001042d00501a00c030100740f1032401605089401c2101901040c1004580301040d801010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 337214109 1250 337212859 337212877
    0x40503121003020618040506010c2001030e070603050906150a06260708010f08010e0601060c02031c02031c0c1e0314090703030206011508420f061e 65
    0x70348021005079103510152100242c0d6400a070f0ba00191001000103644000e00301506004000c2010310100e0301c4034800382046544018828074201c0090300403802406445220302d410b002e00b00d8041003450341900664007600d0003104239030036a1140050307160a200d803c903400354030071000441007080318001e41c030346204402489661200c8041082e403a04c105001150f0060008901070018403000d00f400c2d6000001e80341030402081802c0040c122565105018099903090001085d4880e0031540d041100002e04412160a029501c000f80c10281d62a00030041944171003400500d0341c84030800c14030a2048504050343c48030030741009660b082c4840c0e400c2454503000c058661160350401d40045054900030a071040080406e9451410001e06045068101c0c00c01c90690b50021140c140d8003226598001170643c40340603841e078011a002c140c0800d251005040c0001c0740e00e0f2041741d121070300805000300c1da0075144107211460002c02c0021500c2038524940a20629850180c10030301c04001900c41c00d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 337215359 1250 337214109 337214131
    0x6010519141507050105160f020c0f06070f0c05040b0d030519260f090303060607120201180f05010e030f180d0f0f051606090603020706090c14150304050312 69
    0x15003a0203282c80c1544584425562a07441c0e00070b0042840f4240103d8114a84a00c3c00c0d09180d449080025101c40e14100328501c20410102510030558544007202e062692101d282c2c83c0300038540c50904100c03107407031045c1da105520b840701c3d02046003803180341e40000c140e1542d141c5250811640c5100c000001d11002e0004029122006101504100c8104648100e00540d00310043c90a907120741480003000b0451540d0f41c00c24070a102586d25000c081d0b814840d40904e52101e00e0148a604900420708402c1955003501da6100b64010b02019980d0300d100c150040c0004d004020003400019968840c00307414500c0003208011400000880e1203a80c60301c2107005000d540c425500e03403106800c0c6003105500351103a40c0c0000a401c200101080700564405141c260065014a0f1400240850b060f51040b0014140c000030020200402580001d50280e48010010b00d50f58440494002400c061000240142030150504000b03241d0841601c0c4102e90000043d0f1411a40510441000c42d0181c02c8015031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 337216609 1250 337215359 337215379
    0x30030905060301060e090c0415080414010f091b0f05010e060c01020729010b0406142b0608012c03251e05061b0405060408030c0601051914 61
    0x141e5640c80056000700780c59550100c40d80c10543c00c001c107190002c0c08140f02d40004010070442380c941e6500c0745070b4019450504588503500d074100099601a5048140d0070365190801c01e07511111540c1c00800c650b4003403100714a42c650325100c1e101c905041809121405207001d031007002203600c44c010007080d681c0040c01c040c1c24a2501003003030342a070f000305008a0b00520108400b041810030b50b130480a10b01088010703007041d03502d40301400446100380d0152a040000700e9030103101655000d811520034185e00c40b00140076803030300b41c5003412444601e244804428248000003c02d0a41400780c03c182011b11156880b02d02c0c2c0c0c103200d95480803004088107503940802d1100a116903800070fa82d421111488803420100c401c00d141c8442c82c170640300410f412140c400314504010450000742580d0100c0703100c40780204040f60500c20300c910f00503540182e9004100040c042a0044040b004c1c0003c1e000d502d0032512140d80b51020850404a85045c031a500080380c0b50030042410040d0311500503400140a007146 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 337217859 1250 337216609 337216619
    0x6010b180603010f030b0915070c0f1b030204050c0c0613020a08120316051c0f0b0607030314100b070b040f0b010b0921070905250216300309 62
    0x2060b04242e1020315210a003c1d030400500c0f415500903580882140050400542070761000c90741214050001810440e42208460030040c030341c1c2408640ea604961400c62031005101044010862030004900aa00301000b00b5080640c0c10156480c0040d00c00c0501050740c1c0d11104403640c40700d045403c2c2ea0018000a0020752004280640b400b10210485121390301d142103a0301600030326a00700c4000402004024548030741c200495403030007483c503100021410a2001d04100d014055070851143d100d00c00048107010150554000351481304000d0540b40c1a5481040901c2c1d42c11903489210b1108004000340c06c0003405e0703900c089a106102c0c034041080e0012a4807030400c40407098221441d00c05000880d1540b610746504d607030000d021415200408251075290240d2507400c2489040d24032910b840c00b0441c0351805c1c0d680842c3c091080c01c040f0303002858401d030007035540440010398024111140c0c80490707000c449100083c00c110005600798800b00c59040c05003074000c907020301642000035171280810 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 337219109 1250 337217859 337217869
    0x605030a061d0711030f03040204020d0f020d020c060906061c050106150908101509090204060504020706020324010518030f0f0c010f0309050c101404090c140c06010b18 74
    0x402040030184103602c6141806018000309030800303d0301d002e540180305d242ca000e503628045aa00c207606841c0961941000143c1901038103d0a600120f002c1c004180003e841c1307240d0303010349155907a8608a4586803a91880c442e01c1e17807400d942e104d401007c255200c0214112079070f50111082c1c821301c00004c030a0341d00c440c01c41386414450001c0c0005210284104644403082246071201c280d00041041f29804904660800e82070511507440d026844202e29029541d039688000e004190182066503102c040b4901301c0001d500c22140342c810303048541d1171580120b45141d550320a0741c0041c0c45241c540b4000c0d05c484d5054004004180354075104e50b00305c0c1203010000784000301041d81d0980c0108000e4210100240ca0f43e15246202c0f0201440c1003110750105100050000c00c0c507800b070310400e800c02d9002e101100d0b22908140d01c50581b0300009030004403080160f01500841c03a8a68540240c45082401e0840b41d04c20004145029030242005010b0300803207000500c54020118421003060482c240401c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 337220359 1250 337219109 337219139
    0xe151806120108070302040e030a0e2101050a05040b1308091e030d020609010e0c0d0618021c03030b1c11312712051b1c02160605030a06 60
    0x10060700000801c10441c02c0500982100800070230196041803079005c40100a250341100b10b911a408002e10020045007640724500000c406500038052450a800000c002e0541580c04480300303c0c2000000e9070b1502c06410340801590700c8150b6524102c402070410650300c0c4009440014031402c00c03c81f0f400b82c1d0f0100142494416141c0141185251250301d0500f181e8a05411039a55000b91038504103903502e814510921903880300000840c041c1c1084a29030000d4907000c0290800205103041650700441c1044000310b034460fa5050100e04152001e0040440c4165100710120603608a00400508400b040d212441d02c09841c65921448245080499900700b0181e02d140d0407880a6002d1040c081c1e0050703d0808804800d03440041415150b84440214102e2024100c5100818002e40e524410f10480700650881092641c64107802540d1035100e1020f00c115410704030303a4800d4509024008a0041c0380d044012142d07002140c500402918141d00c01031940d1101c50b62680d0126003080400e1800b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 337221609 1250 337220359 337220369
    0x5100807020f0106140103020715020f040e060d02090c090d05190b0c04051f02070801060b030108011a030606040f0b04140f0a060f0501032a02010c0e1518061201 71
    0x40209090030880a0700b480222200920684d05244050160b6031a20303020403058170080c640186c0c3c601150071704844403c2d80c1c141c0184c2840c00041c1c025004103d2002030401e6a030250000507254a0312010410078940500000b0f400a10400c00280301041c880081c00a4207006032142d0300c0c02c0c00c55900d682c200f500300001c503c0c1170880e120295003400200392005034480c2c9101c1e02c1a01c1e043c140130000349400b000d0303a1881b070745021031205440131510a1144500401800000740540e684803044001580c00074041c0b13210a6280030b503158031802c10301042144465010f4003400417030303c500f400d03c1f010380b035a480920701442d01c884d000c0b800781d21103110b0282d83d0a020f50b092069810201f948021003407000d0500c00c4154100402032198a000c0c000c1601111001d00700086c3c007007500c00c10022103c40c1c1000e00902e107081040d24980303058043d045968542080c0c3d070362140c0b19092108114540c10041c0c4280d003a84024400c225071010442d1034082e4110004180905000c0c0d03000303955860300307801d07008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 337222859 1250 337221609 337221617
    0x3011a091909050a15030803040813120303020307031b090306180b04050304050f1806040c0c050102030f1605040b0f1303080403060e0607030e25080717160305120708040510 76
    0x4000d040c803c00d1017203c8804041c0010280e03507501d1502c40c2c0c0003e0001500182c020180090400030f215501d0950f0001042c1c0142c03d80301d94202030402500941007200d00318040ba044c00d10503a01d1034003032a0041e000c40d04d540c517031030941815902c501c070051420443c42d4150701c00441340940801c40c81a550340c41144a0401180c4ea64240313828000c520105a80c800c2c051180103500c0030055550b02480c80e400081901c000652120341401150200d82c5c208001d8070039440041070007224080515618031502580803c411609545076048441e8801c52141c03441b074603010701c00b10a0b0001e06600414203c00d011004d0f914240c0c80b034495260b10340c41a40212030003035560740c14621540302400082e41c010781c07500701009040b01d18000241c49a05541c000000c1c99000b00703408900001e50384410002d800440304560480e9201d042d03003aa00c00c0052030143d0386204100a1a01c4644011a4141603d5000700503104441a851b25004c5940001381c08989011003400302162940b83c0c1d41001030041322682d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 337224109 1250 337222859 337222861
    0x1804061d0102071502040b04151e0216060503060607030806030f0d0504090501060305010308070210170114030601080a0c06050a0c44090f0105160f02011403011a09190905 75
    0x1034040004c50752000c4130718469006100030080c020b0058160b1707045440104100780101180300003182c51001c18003203140e643c044d0914501000d640060500000b09440c082c0007000e03510340c00103403142d0000f181c01070361100c0100f000800080c03040d020300b60803c9002c2d04551054014400c110b0601300c005104100240c408a01003020100c2401910300414450400700103d5045480e0000c25200e1444064040c44450340141a51842010f081c2c078002c403d40e01580742942c403421011070b25410004181c2c800c0c803c51001007030034a4042481c0400c00da03c07410004110785488426200d90700311020351024811082d02e10800300d0307910b0f034540c00c1d000d400036000107800c1c0c0103d4030103003001032a40b424620365140b489444001c0b0010400c660300d85004451800358900410012641c03842070b0942506803d0354411900104505c11906007401c51007600e500c005907a1034038071040b5030b010910410500703d22101c8241803603110034008106e0008041c02c1c013030034140c0110904943e200b041c3e020072070715aa214 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 337225359 1250 337224109 337224113
    0x711060307030c0801092906090a0f0f090509280605040503090103051302090708060f13020901170403230408010527010902030c1e1003020703080a05061804061d010207 74
    0x4131502400d0030605c01c10054800900030210481c1c4080720601007000c007142e0f000c2035036a40003514005500204214202d42c0c50b80c45c81450000603104026040c4038900000c6510140341c01001d1040d03420b20b000301b0440300305c011452085400d40104840280c0740c0a840c0022440f50f000f0144660300410046545000178400102150401020400c500500002a90051352100781c625000012803800000d00d456a000107014900c56000e00b40e44211000c4d0300c03a610002c0e603009002d0044098075040c24020003074038116a01c050889004000840407194030800d0507000003220707500300201001c0c1d401c09817038240e100d003118800d99588140c1600462100c1075030761401c504240d081c0e8080b0080c0565180b5501013940c0c2c00e102c007152480b807428159483c00c2070410040f040780f40080108010307019100010043d00940c0301000940000305150001024400340b0f0203154003408024001d044852449030a8107a4403402038011540e882d225152032000c001000f10204030310445100050b0340d0460340c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 337226609 1250 337225359 337225367
    0x819090f06120c1b11040c03060e0705030c0f040602062a04090e03070f030815030d080a0b010c02040518060f01060903080a0e030318180412050711060307030c 70
    0x580c04425441103825080c00155407000303215002809500010458143c8024291580c442144d2a105140004543c540074010a294001c4041e041602d04020481c0e6100045003510a140035048070b02d02241c01107501c451003400103543c4140c100801c1810056140c490304c050303a01c2540302d000180d200100348180d0282c800b0200501e00070620042c1107000c0800300600441c0540e101c0e20100d241c0d1200c818507002410f00803290b0007540007c011032400b840d8078010708010001e4403541020000050860082c1c04c0020707910b070306800b0075181d00d0100c0e90703188003a0029001c801029410400301d010440f005032214040d460040030190002650702c0c2c1d040d48a0740c42c0c003900030482c1c0800000b520042000f81e8000c040d10303040d00d810104095485410358030640380810005425278041c80001111200e2420310480c2120404040b41d4101c3ca0700004600e4014486041e180502544041660885043c1c060801441510b200d8030b45c500b945a14000082c40e16002211020086610b8049030f0080c4c941c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 337227859 1250 337226609 337226627
    0x1917030c190809060a0b0a0e01060336080306010e09040c050112021303030e010c0503030f100608071403100b0409050405060610211e1d07140910030819 67
    0x210b4500740c5002d00e0042c0c4400e54504c0c014003240c2001307035520883e6400c0c0e142e244040d0060140008108140e503510000100205200c9980d18584225aa0307403850f810840340d1030345130980781c401003150340221540b01c0410703903800a81403c1c103021580c091146940c0310681010f11950152540c01d01c040d161030300241600ca0402c05c5039124a00c1003202e000034102000000302502d4251520b9207038101d01d01d00603903000c0d00c4004080c102c0d1101100300810060091a4030340b064130803440703143c80341d542c0c0c3d00b09450695040e5042d0000c00d0310391281c0380301d404140001d10b42c0004071100481020fa070741c000310071456025400010400352107204200070f1140402c40319030480000c1c0c1e1031440d070b8000c8250050410204804140d040701a2101c1d001103210241c21401641800c0380342081e0824065031480d0040080c0c003a82405009018244104050f01040c0c000449032040342040c03a002c003104c100b1095a000a110190b0012201c3e408000300e07120001070907441c003021000c1014005045409001080c17 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 337229109 1250 337227859 337227907
    0x1b06010602240c0304020409080409202b0b0406030b060a050607080a0f2a150216060216051f20180102120f0406030e0703051917030c 59
    0x101e02c0c2400032900c145520140e900100440301c4541342c1c0c4582c0f0018010708500740001d07102a0001c1380100b038600030381e401100000001d007094003100010a0b42441d207406007042c6590010a404111200340d0020075806562002040d000100d02c0b80b440d0000382141d6007a0015640000c1d1181005a0350500380004409408211411800c00c0500da948461500c2400400c008110740c1da0828000d4074050490350010700321841403070b170561a803c0d0404054843c884001e40700d0034112850520f40c040d852003190400e00c1011034085c402c080580b185006544045a0b03a0700c03403e039110440740400c00501c051030004516240f0406451160200801a80c850201c60302d54515040c00034500b0b51b0302502210103070b501c00d03441d04c55900549001030b81881061400c1ca480c09c000043c0f041c1c4241c83c80001041500c0c202d4408001c01c50460740d941e40c2d60513450100600c16800844103030316814807003544200d140c7c81041c000350b051500c22550011600183c2d20b042d01801e0214a42c2c119004440c01c44505103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 337230215 1106 337229109 337229143
    0xc081303030e01020606040e0c0607050a060e030316020c01020a14010902090103060f180c0e190204060216090b090a0b010512040f05060c030408030a020d021b06010602 74
    0x41c41c40b180e0041c01000d0000741e9524051085012481d8203400500c407a00c402c0c0144805d84d030003540150764500c01d01c0440c00001e000307401025030042d4180b020756124100b0882c0040a01400c0c81503606540042c121310001d80d0f40001c0c0440c40310b4200d0048540050503060b0746005001a12020390042c6900b0300100500c02507800c003508001000004100d14298962401d0140c10070b000010702c0a11000001c000401e01040103c0d002651108031400200c0100f8210003203034040c0e0b2150025030000303a0000c0f0303440d400c00000e400814840d10148140c084003c0018500100245142e400076518440c0396050391140c01542c0c002e520440707040a117410141080c5c2c81048080f00d0449151048000103080b180d0840c0960f4011a4040710441c02d40d202c070706009000e50882a80080401e03802e22000c2c4115a864183c403c920309217201500555050200c001d06010b043d00d1104004 = true := by decide +kernel

theorem cover : BRFrame.Cov 337050359 337230215 := by
  have h0 := BRFrame.cov_init 337050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 337050359 ≤ n) (h2 : n < 337230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
