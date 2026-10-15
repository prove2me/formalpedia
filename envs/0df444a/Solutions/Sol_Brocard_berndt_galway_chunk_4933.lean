-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4933
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:12:17.903736+00:00
-- url     : https://prove2.me/submissions/79a3c37a-861b-4c00-9078-8da4ff7ce7eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 887050359 ≤ n < 887230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 887051609 1250 887050359 887050391
    0x7050f0711090a1508010b13020c030d05040503041d04151806020721050c0c10020a050105130309050a0305060601030504020a03121706060f0f07020a081219030b090415 74
    0xf00d591048280e0390b0780c00060740c259050a20002000110700802c18500581d001c24a06448040002c6101b50001290041c06004008540b1506403004080060b418a03140032610380e03001344155451852203040c109001070340c2ea04da41d802954001118400c02da0300741d0100002c4c018405c0111400070404241c240400c402e80024100c0d01e1244a10a188000d120501c04a141c040d0310f050040181c103114610f000e420020301c0c510f4404044819980200400744224605139182c04010840c0d420f0000f445030544414074583c40062007a258074a0b015140c1c01070051150480c480541507900190100f03c10703501942c000381d040f030700151940025503200e1b12455154140b00300d2100009020f44100385015040f07000362600100100e40c0b41c0c1c605000c01020403424010326011290940002824504560b038544020004000020580d0844000d02d0905109a000b00140e0000c1d02040c00700758020074800d01ca00450328100400303003d0951641c1c1c417054840c40c200150301d4000ca0303071000c40007030408079 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 887052859 1250 887051609 887051611
    0x1302120601090207051504020d02090405011503080d0f0b0307031118040803090610060f03020f1201060915081012170f090a0801060f0302130b0616060b0907050f071109 74
    0x4060001d80e84013080e24003a0300d0b010309040900080300d1503d05200c010303582c550310031200940440342d942c40b40e11982040e42c01030201841c10400d0041800c4000100031942018041c441c0302d41004100104d0004482001d89110001441d0301d50491482440080c0100d2000040650044e240c0e00320240342d54211703c0b0440d8203450541e070051020040101c80c0004000840e400003091041182e614a00300700078000a030550798103418150085078101e9900310503010b60f070008a05501c6070150356507030100034044007098040c0c5407545403204084003d00d40201c0c01c0701c0c02516a00544640c81d450841078220140e04a54105c0b41d01130b04014101a4000d0341d0041c110403000340c0201690303440d1910030000107030807503400400a41d041000420918400c42b80201c00c582c1c041d00e42d000300010f02d52960004000f01a12140d1026000ca09480301404223032120310524800c21003000311049860030000c030510304840c1180010030400500385a509110090101c15128510054640e50440001180d9180c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 887054109 1250 887052859 887052869
    0xd08093f031b010b0d0f0c09090803060603071e0f20030d020a0207090c1206080f0c01111509060603011506050406031109030d090509100e1302120601 66
    0x3000304448410141103001a03415080003005042200840103955128081c14100c0c810030032103182c03600a1420203401c081140d00340109121502c003610b141118070b5201c0c0030320640f82d000705a10049804203140c070846000c1600300708000d055944000800c0301a5100601c1001040682c1611043c49403002481101c2883c041d1100c2c125010443c0c001082440010068007180039150787c00c40506a001c42121604c0c070b840d02c0c015990702094a016403070440c1d103901041c40c603803030280c3c0741905c8c85d40458410b6148805220070b1150720ba9400015584010038159000780f5040001c1c410070b40d60107400080d5154522900ba241a59a543c24101e04600700721001800303508800208240d900c3c00b0712a000c2d008505501a4502908010000301140142d020b8501456524240c0440b03082c503c9042d50f0262500604403021051010b0008055580c0341c810507000b0440d20022440d100d1800a030300c019900c101110450540e6500e64004100e4480042070382c01c04ca00501035402c810007072009070f003e0307d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 887055359 1250 887054109 887054149
    0x801060e091b0a17100b062104080f04080c0a09020c151b04030b04060e0106150f09170c0f0405070f0e040b030d0513090c0806040e100c0f02060903180d0809 69
    0xd40800c0420584040d0207046c0c0c42034008100d203900c01008520800d1001c1e540d84140c450f02d680360320307208809c0d11a5101c0380300480d10101e000100c1800008054268080a07a070b42d1100660701c0d0000c4060340102501083d1a402c48003a00890199110031141c0c4518000001031401c0a20004d11950791300c00e0700240d6850111100f0881070010b00c0c0580e0304a034000d41c008005043c9401c0100c09001091b403c42d1080020550040030613505c5480a18050410000030940005041c1c01460b51080c1101889002d41c0c0e2108a2440318030345441024071490740d540702c01210750024581198a4000d050003e944503175502079010b0b154404000e590410711494949039617904c50000c109401d41c0460f400b980005007058283e00f111a07100303514907007059041c0c030b001c205d888420300d4140c200081d455582d41094074144200280c90307841035044450704011b8003580e1068840c000c02e0347d1684600c0034480301048140d0040398907800c0c01d4000a0381c00d4080c018060034005046c001481d907513095070b040f03101c070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 887056609 1250 887055359 887055373
    0x150b041506030e120c06010e0721060e160e01030e010204030c060503041b0501050f0a0219081c0612080c0f0610030b0c07030f0302032a040801060e091b0a17 69
    0x103e081005050703114100f102e201410218102120b503034039041401120000710100003c81c0c141401071440807146149d0007044d100701182020044002c03da11300c5520820100200414441c0024484090084440b9a5030100304841d640040d0080d0210301101c41ca159800c10000011504e0100004090f00a5680c1d40e5900d08040c100487c11800700e40504200c4480500104001da8100d01100e011a000740d042c40d454138138603001030342021070309180540703410314881040040004a600074085120125103200080005d5058031003118401c0c0900358400c01e242aa4101042d6003002800c95000950110342010090300c20b039504150044d9203140c0303031080303001d030030300c104a1600b0000398803101401a090070028541c400a00c0d00894003422000e160340000440d108450703411b01c101030f43c001c031070f2512510300c6030600440031a8010712540045502c3d001010a425a4842e443d90140401500400814090f44030350100b0400d01c10b00d2a030700c01c1c590032000440240030054100c003c2c0c1c000d00a0001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 887057859 1250 887056609 887056631
    0x501050702070803180d08040905070e09090f190c03080a1107090507080f09070504060b070209060a0b0d020a0201021314030105160c0f14060c0406030b0d150b04150603 74
    0xa0300c525500301e0243e940007405810300840b202c50443c0b006010441d01c030050381516091400c0640300d01e0f04094a901d061a0030040c03c0c41d0402d103260440d50701034a56002907a20502e00780d03150b03031490f80c501c0702503046080d8010710381d4400b07480085281d010b508845141713666a40c403542c0a078810020200440e40c09115401e40070003d114041c0180007010007444075141c003210060140d84000c2491003040104d4020800c041410402040a400003500421650f916005211550740004400700d01c15a85040021440d0400e4001902100d10340504076040008441046019400100d804030456509000e045100c11181c202000280400c030024070155000805150079541c0013000c0c0c545844400440281e81544250b480002c59040034502e02e2201c10351401b444038000005501c036040c49040180009961003000400844896440400094101605120201c01208c05c09041d074160304c0140038001300b86d0340002e50a184010070000f038400310113406010f6103549410490000f0b503140c0402d89 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 887059109 1250 887057859 887057863
    0xd080909180708030316050a021203011e1e051302071e0203100506090106050f070506010e061207030209070c060e100c03060801090f02010e030a06020c0d17100306110c03070501050702 81
    0x3c3e200c2c48000d03601e9071510040103002c80c5202290034080000c0044c04840a0344240301d48074500c500098026a2569218001c0b0030402244001c15103d400d180c0700000e0841c5021240c1182d03000709081004d45514010030030a41440001003c01c83c41c1d0200910360004450740401c2e28080c40d08c503030034004007404d401030500e846600407070b01200600e0301061003031640c0c4280d82581150703054540b45644400610080016006074240107205100e001c2c0081b031404d02c4544594460901596103106030000041c4441d03544101d44806500030f0031480c00310b600c1a2003800001e1029001e2140410000c156045062516580d2400c80000c1c503661380c045003803070760b0500074080100002c0b002482400c406403a12100080b036004020b0503c500c5000d0306500d9103061018608003601310008640700d441909401c2c0c2c980e1894000b01000641c81482411810006101a806038003107581500c4003a08541e65040200107a8466004091062000c01c040035010002000c0e1188900d0004c5644e0034951000380c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 887060359 1250 887059109 887059123
    0x4120609021c0b15042a020a051203090f071a131206050a0b0d03090509101e03060c090b071b080a0f1a0402010f050f0412030c02030c040e03090d08090918 68
    0x15101717500341007000201c541401039a02501401d030813a104d1360480d000080c2c0c030f03214100340018514000c01d0948094115400040c44c802d650300c9003503601100d005002c068a600250107a294214444030464800151410181144d502050081034005444440c0313003250f55130316813049038801d4507002000710042860281550314401500d004880b0b256039680a84803135000e00074a8002c0d901c400004180300350103102280140400084210f0b2441300c00c840c82c200c400a03000a403038043c14820321f600160300c10f24400048613014800076003415440c1d502d0031050400c1443d90385400400c0c2c5804078400905200c80d1031017500c11441118100c41c646441c07440c802901c01700b1600f41c0d142208100150760407205104c0341d040310f0324005644484031809031000740901d0b004102401d041100c0351082603001151241458000c400f103c40031480d660402c01a518445607030344c40d5400c280060480c83c20b200d44501c00321880707000c0b420b06107240c0d0320100305401c0b01114040700c0e64030f84c80c00054403010144010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 887061609 1250 887060359 887060401
    0xa060503060622140709150215041209050a1403060a0b061207020f1518010b2b060f020406170618090c0405070e0f0604120609021c0b 59
    0xd404940392020010340400441c0c280c0a080310300300c0007580000c881e140e01822052040070044221410016402846c6c031820303000e4840c0301d0015a940c15142400081da40440e2441101c0c80d02c2c00382d9590b036a4203200091410440c0a00000b280045095030b07800520703402a00b01080c0d01850b2440c910105072520401a00110185160156a486584800e021036078800c2c0c961807000324640300c061040307140c680c3c0c0e44c0b1000e05034050031907044003501040040a000d01c20707061680c44200d401154031400c0b240741a00345540104c200c4e502d0080000110700d60480283c0c0780c1c10980420409440b054196030841850358840c2c0e070f00040c2400902e0b0802c411605050001398241c42c50303d49803020400c40038500e081c10b0780c440c6607080095845041007200000030724010384180304034202410040c020402e107031060f522036851018400210b08001041c5c0381115050080c40343c82070801d846900080c8050101a40c000c042c806040b103c2045510300001c0a9208070b0768080f01d4503192105654092409082c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 887062859 1250 887061609 887061613
    0x70b01140a06090e1b190f0f021501170106091b110a0c090902120307060b030c030f100f02160308010510030b030a14160305011505010207080d030209060d020f030a060503 75
    0x28070902c1c207685079455110b05d806030100070255500402009034010302d030118030210388040100d01c98075480151580c1c091126104d0102000703c1440903a15209562401c2c4a054407120041040c07100c5007000601040c10140009015901d80e20040141e8140858204006c903910500b0802c442d40a01946140064080500305100a0380c1d51081d01c20030fa4842c00e00c0040e118171100741550740c0c2c62014007294002008803030340d900503881c248014002d080c031064400e000d5104180450708020444111090054020300740005d40351034050000d1543d48190094035909101c200450807540001e0000c441c040c2d140e0340341c1d070762511080281d01b00703a881b201c00801d414031034000c2490705c000403030020a950104c0741c00390455088a415183c09001000e50100400c0c01d80c0001c28080c045d84000700c030765400c9161526203074440c17005a0780c84806210302511940004d0301e805150f0710a0780a0000d01e807004101514210820700c0f18816078000c0084d20200400010501c009441d4034428000203000583c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 887064109 1250 887062859 887062877
    0x5190e03070308070201020c0a090b0a05040c0c08031b1b060703060f0303030903210b010e0303090603011e09050c0307030f09020303030601051315030c0f020705090c0c03070b01140a06 81
    0x80841d031500380381d100040000300e02061000031a8001d000d10700e64940090320041c0c11680d1042682c01400e10303a01e190f80110301444000c20b4909060145003403014868540e81c0c0140d0803070380c405410713501c0203016843d0b2000c9070203440800e802c040f0043c038103520010340e040d500f8198090010f04105025142c04141441d1140401203c1300380d514801c1280c0c4c1508000803030440500701507a1401140d8210682c10000c0b0340c0d8003405140d1a0701c41705000340203030380b2680000c41b458145a80c921035003c560745d000d001840108112011401d0804200210400d41c1840c1a501d0903850300356401a036013580a0b100100130400300980c58413804000684180003444004400d801003034481c480500b03214104a000128022000d0300d010003400100744c0042d0280600d04c560f000100184411480d040015048643c461720040c0b0020710182510740080c001503690702c450103190310360350084481c0d0009000610941021940c1d11310218000d143d40c1581c2140500001308005564005411050034012611 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 887065359 1250 887064109 887064137
    0x23a0b070f0210050106030213090b0a0323010504030207230d200d0c1401090b0a030209150a020714190b0c0c060a0314180a0209250519 60
    0x4106a8200e1000e080410005801240490601d20303400e8900039078070300742000002c84030ba160740140b403c00c1c001d645191002e9140c21680081d1002100d42a030320101d030003401e1000c00c50f0869050414010600300d0901d01642203000750035988210b90640150300710940420000e602401c42502c0b0f208a094050110b60b281c0d0000341a010101e50f020b4003217006c50143e0101c2e4a1141c444030040480280384a84403031040c504210744502d640148042e0300000388086456500850144046d1400307015040d0500e006007904400035005803041941c000000341882c00081c04a03070080c0201000395024004c0b80c0e0030a00144d2550895040d03e0307002c0d241380c99100100d0f00725a14458166284107000c00c0e510a0409105417510f003401140591048001811181041d01607014035000c1101c024108403c2c1c0e18502095946460030004400c150405442100140f80c03560b00e540d8401010b480d5400842e0381a01c0d40e0024108000c0f0410200b17100042941c861032002040060080d12481c0c83c0c0294a564 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 887066609 1250 887065359 887065373
    0x1c20100806061602040b13020304050c04020702011202030a020906040312090605271201060b0d06060e0a0509040c031b030317100b031e24030606030309060702030307023a 75
    0x41c800003041c15030003c0081c003c568441d04604141d00c0b000b08003455103650390b51004002d5106443c1100c2901c07030814101141c0c106402074a000c00d80507110900014101c1c91100041d5100030000400340c0e07800c001c100c14036030f2a4800360000c1d5008076910a009031110388060410b1020350000c1092040500c00801c4d10308200d000051400d060045201e0f03019026070101d0800c0c08000c82c545415420500301194034551140500205120003009000e003d640c1c80c001c1d81c1c820351043c00140c000e20322410030300841c1042081d06070028499a0346070011541d03034444116074900400700b0040181403480400c00c0c50f40c0a183d1004143d401945ca0400303083c1031380100009495882002c550800120001d811481516004030703246035a58244589440e18441c10144400c10360b200c6011768020184104d9103050025005108600240046160512480030845141c024000c102d0f45072104000f21030050311410311010155044d80800303812540c51801c0c0200034801030201c01e1040305410070040c0405c0d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 887067859 1250 887066609 887066617
    0xa030c0e0a0f09110c0d0804290109110702120606030106050612061018060f140316210e0303220308010e1302042a0207141c2010080606 60
    0x105900004c025103041c3e101110b60165800803000b6008218482d00b400c1c2c0c005484910035442000303000c41c000c40e080302d5800404840900140840340900051114000c4da40c442070b0035110b60030030319003090359aa001176265000c020075409250440e009000003410b09004940191000f2a00c55003805e15840c3c50855418008102a2166445c0d80113403070000e000b00305c213441e00b8180c42c56010480b41c071181d001d4420320322140c4141c0002c105a055503056400302003542c0c000e00c40380d855803082c0030140400321444000c0b5100c8120440d010b200365010b03080c02c0e01c039860b040355040d07000e1f540324900700540250a81111100d120031303006a00c25600000d07403114080d81503130326050440e40541c523050649a80355412040094100d460303e14603440900800c0c0c00c0c000c1c0346681120069084414490407a10b8584910034034060078440c2d10041c000d031400707803940c0c2c440746136900d6200383c080b4a03501d0305521100d00c200d8015038a0552240850340d810a102003010500c02824443c1c282c1c00e01c0c10102d095842 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 887069109 1250 887067859 887067869
    0x1020c0f0a0e040c1a0c0c15041e15020c0a090515120307060b0a050a05060c1002032409010f06051614100f050702070b0706110a030c0e0a0f 62
    0x1100000a00da5074800348440d01514644100003240e25080c0b6141c06024214000c000c501002048803c1020b02040d0403503200360141800b401400498805004403103502012101040d4800d0001040c4204021701c0b140d0783c0348030604645d6499140080c10002c0c206600104021504000042074551301c8044260045900c0540006000d644c2c0f2100512100281030a095014503003207a00382c0d803c0b4001003c0d1000c035005170010070030f240003001000709204540c842e5a40007220030008114502d02000509450304110043e0742d481032010040904a9000711548141a80c001c84c845d1050115441070508110042c0c401180c29410410f00444050640c070402d41081400211441e88031503030924180f2075607210742c150b01140380c0190301540310b02c070003800f8024030392030300d0006030f2100361034042d803030160990f03030003070032440e41000312081d060380c8151003d4484c2c548401151b40da001d020801007000c1c9800b6900010344c9200640004c2c41d40c0320007100140724200035802030003c4164403400390201e80c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 887070359 1250 887069109 887069119
    0x906040b0d020f1305010e0405040506070c060e010609061a04080715052701171b0703020717060402090108060f241c12170621030a110c0f01020c 64
    0x809200e0603010780302d2101c1c1003510f4400070a402901180d000402c4081e00c609032120050864900d0520003101d00444001d0034a50121021031000d030300842460a0040c040c04000c44d007191004099803d651881e84020740d03070b617a20740d810000181240252028000814507403441d10386440c417080d98802e81307405100040045080301e442002d0040c800c0b203201c91950b102c002003003c82a880d0740901c06080031080d000c658251242c240702c0d001c444005110716400b5080316507110703800030f490a07203411560007101984141c14001c1800940e03400c00341a01d8030040020310881c50303d8818003e8005040c0c0c040c0d10b82d030f0303c030809211078401c6032021254400c2c1c3c00c48040301060380301003291045050014009070800f82c51034a0042a1902c0d90201500c02d00a07016064200b0a010b011034480340e07020580c180040a80010458615001e14440ca404034010a0018910007c1d0101420755200002c04408201009144941d042090201c081e02440c120740c0441c2c0d944c44140040e403103982004890303106d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 887071609 1250 887070359 887070367
    0xe040b0a0c050408011505090901092103020c070f08120a0215071806350106030509100e03031008120f030408040f03030f08060301020702181b03090d080c0906040b 72
    0x4622410943e80104280002401a15190a0707040752032001c0e801094000c2c5690000243d0300c03103050042d40c40c0c6592100b141514055042606000207a14628031020036400304015541800704104c03400117000b000d0118120b0924080d4120310303100806c4d040078110541400580740c40d0b0b0f0082004074201000c2c009600d9240e07a0071004844000306003001c1c00001c000d0010115030554000484950000b44041228240841c6a60a80c80000034411f4107a40450b103401804528441d800c002d80041c441405c950207180c541440e2020342d403040300c0741d100c42d52001c410001183e01c1800410001e12400380608490340c085100c0c01d5051040f03d5483c91500000004075007001090360403075005094460042844544038a00200804c50306014000001d00610109000e071406100316000c10707034001c0c11001c0f42888680010304e0120b004043d101c00002e110904031849440200840c0700707000081c05049240c01000001e401080058141c0645c0701c0180000107241d11501d0498040e141050b031900c0d15 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 887072859 1250 887071609 887071631
    0xb09040b06091b0a11070b0331060609052e2321070b0f0315060d05280504020f09100b07050709050105011b11010215040c0305070e040b0a 61
    0x150400070065010000c0c0009400000507401107440c01617a000740c0c162441190350308402c104900050325400103044222144c9900e00c041c19002c8400611040900301000c03130f01d42c449404888082d4000c0c11851740758020000b1401c0d101c09400341d43c040e0400b603400d29010301440300110408a000b80c600c1d1031111203c2c10f0b20a409000703100255030009000d9014408050800102c407413200000300301d20b01c200ea0f40031505801c181c041d02c40201d03890303940a0843d0b070384941c030700040803000032015044002003004003608940c0d40203061007140052605034004440d101346a40d0300c6290107001c03182615040600005964013050b0004081d0100c0c0e0340040e0340c030340c4d04541e408010b0513480a0f500d48070004002081000c00700340c080407030700810010040c580e42c1d0300055500341e500d40d52591010480c16142c90000e209492805400c02042c070403552031420852008408010035142941c99800f15001082004001c0010320007800d16400810210b003016501c00039000d0025109070340e0151180100c01e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 887074109 1250 887072859 887072881
    0x504061e120b04090b0114040e030c0c10050c100504260409150f06020114010e01051003110409020c031c11030c09011202031f050130180311010b09040b0609 69
    0x31307955400880403201d9507541e6085d0395a0420420009010b42d00b4912040c4c142c09001c02640d9140b030340003000e80049400041008040c3d030070403260360144032090000c411403403010404002c40d2000303040001801d040c1410300c4c0400d1184060110000ca05510b1444d043e21442c07010b40b000c03500010300218940a40c6054005080c11a4229503410b800c5040000740c656415000360300e02d03100400455903180d8030342c20b07241000ca01c24020190800003007410b000784a0303c41d41c030421942d0400b1307200904244d11004164181e91021807a2181ca41c4041600f01804881001c620300720138000004002d1000990207400d5540402087c40002c2e0001150703810442e400383e2205034040c05144021940d81c030381b1b01d48049080e1604401002e10801c020800725865004400e55584103034020451025551700380ba080890466205080c1096511107890f4480081d41e802c01aa002e440717500c49125101810820314215800b05611511038640c1d2418000440c030850303401508107c080d80e0b509101d43e49c01c2c076004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 887075359 1250 887074109 887074121
    0x20a110415060c2a090506190302090414070f030302010609051003150e1203090c01020d1407020d0506010803030f0a09020612070c1a0106020f1606030b0315070504061e120b04 77
    0x10001000640c07004c180c1c15841e64903542500e0904c0401c00403500e8901c18403074407100c0101c0440909040e200244090319118410b103031300c184614045500c600c0103401c00303801c10000768014541803518100910802da028040c1e50040c2c0700001c2d0410442c54050300d520165001d038400a4082040394410341d14849194100c1900350301440200c0c1e0401113807030002005540f048400e850180078400c00411150310100b0032900b0960a65580001110141070740307001031703011440c100c1e801940700b400d0b000090411f01003680205010409551245402c060b81e090360750000b410f070080b00d0303c1c03d0703e602c00581e580001d54220004a000740c0801c1d64510400761500c91003000c001c1d10316042940b84480030a56260340c14141c2d05654251082c2c4081c00c551143e8841d4105100c080c09900c82d030382072140c503120b603000240c540c1d030040445042c10021908030541c1d0101360b03045d07070004500140c01d002c100c0d0005488003a40c1603003036858a4040480304014800e04101811503100340d10f5114907995542c0381d400c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 887076609 1250 887075359 887075393
    0x1a090c03191a0103061413180b090307060b09010308030a0203100b070507060e0103020405151e0a03020309011104050d030f020f01140604051518061807020a110415060c 74
    0x20004203090040a1844407405072080b40000d00303014012078000c3d801d0003001b00312030300a001e4215401046203580302612501406403842d80003100c00002207281d02c03010710b00401b10003001d581e8400707003410544140e0314450360389801166a0b000400004421204a07503120ba18590010380341e840702c80c01100301c10043ea009007204900840c80106002c0080341d0602215140e0b1140c03140200c03190010340580c0290f00c142c0d030340459032240050304186100700030305e0790641e1954580031300021920b01c55a80c0d0803205031035000a5003c410000000001d01c034944600c2c085400d1682030629100c001800da040203c401000c0000e495440c040c0c0c0c0b4002c02c59800c1e000b241200038007017840c09800c203c44000c4201e4060384100d080c000403440805c020324246c0d49110b4050140c0d004400c14600740e0b881000080c002d660041e814008100e485c0049150f058001c0e00b051340075103030402c06424a840031000a18010740301d01e1511401c544071081c59916a001c883c198140040c000b425801c04142c0c16000b01c4403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 887077859 1250 887076609 887076611
    0x50a020d0311010c0206010807050111030f130e0a1109040b041b2109081209190609061d0309040e0a02030709051f06020c09040f060c02030c011a090c0319 68
    0x5400c04142d00300400d4090810000020403040300c082c0c0d42240d554800788580f900d1504191000d100275441004200a0703800036400301d034035010200340c50500a0740070a18007144407180030014070100320204075640e041514003009100c12038100032603c040384565060540704580d696200c101c0c40d183c1c0d40000516031404600e45c040111210f070086d00c0e5410f0000801c0c200700381e1a000c070307000341d000d40302d4902802d40200b04541000e100e643c0403c04002c018002000d507110304003020300d01c0700038012048800c0740b0071100032814480d546070101c00d450361040600061081c0c410f601c00420000010784e07203410000c0f1408100400044001d6060214204001e13405000c1d08002150350203168100600400f51558503800340d00c0c3d4407081140c41c6000703014000c0181c104a42010701c0e894115409a000f03409290440499455581c409003100d40150018015030070204001c50004428801c02c0c501000141c1c08920792002a0001095008001c10300300c100315012010485401c0030f594460100902c1e440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 887079109 1250 887077859 887077879
    0xb01061d03010e030901170f0c22090b120c01080a050a090209041109011e03060507141603081008071a130314060a02070b06010f050c0a0f0209060301140103030309050a02 75
    0x104113070b1139502100001d40815142011442d0b41203030f42c04103500c104002d82c0e21441c5511178403035083c11039000c40302c00011b0b18180c00040600b14240904080204441d15000844620043c02c2c000703071038101b150388995078000c101021f0b580d98100d01000c0d48a80002000102584da07040d18000070941d442010307410480e440200410450b2150148100883c111a00d180c42d0b80e0310350b00e501444101404001d51103c00b07034010800220b180d0003942e0003407068204083d100545108851039500009900030184182001e45070516400400060f04981001801d0340101c2c1071040140d07031080306104144803021a18841d4481207a0102591320b41d42940108400c065902d060840703021030000300080082c042c41010880a081e64401c4888855002e4010201540c036400151010407504601d0381c24014100a0903182c0c4506001c101080762192429070f2098106005010140d0001003219000741c2c0761180000034859001211030450b64507103000b0480100e14582241030101012009400001d041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 887080359 1250 887079109 887079131
    0xf0303061a180609130506041b050a03060801020c0304170102040504060b030108060603010902011e11120a09050418080a050c03120118060303080105210d021c0201090b01061d0301 79
    0x10000d003001c1d19510520000b07000400e04003e01803242000d11640b02403440714100380c2e0400b640000e680507030000e0000800100c100b0914440628007070703c550019500150301c1c16400d800d8460325020b000000c000b141010140104c0c1a81c82c8500d0003003500c1d2000006030800d02001c00d4045801903d0068010702482c0c0e910090b2a00c40e400038040c048050003480001006402c3c1441401d280c1d40c0c05071366044050110341c88814200311640c3d074000c100910021000e021210400103044000742c1102c080d40e950383e21410080c40318086801040c841c50505203210303003c61010284040068000a8580d42e0381030004054505201c1c000302d5580c140008100d0154840f660204a4102e03102443d040999000110303250007110b01501000700401c000c00014001d80c00d15154500d000005109401c1030198a94516403a00e5540340700440142c1c0810b003800f458444502c0250700f107148030700090280104a0303544881040341401504100600a19004c0040202d068084060344024001304001d209603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 887081609 1250 887080359 887080409
    0x9090516122d0803070e1225080303071421010f060302091f020a051006050f030601150f0c08030a050f1302030316020103091a06031506010c0f030306 66
    0x1a040984400c0140c004a00740e101c582007903050b841c1c2c0e20b924041e2003060903075680211600050f000f0710400a065205180c0780d194a444032002ca12110020207190401055011151085a02000b019a16004100300030314000081d42e03000352181c184074025000100c1d10303028500840d030500031052020011195101a03850540d41600c0030129141103054485030164264418002466000a800c0c07030f034000c41d1410810b03a80307180b20307551040e0f0700d004404c1e03210395240140700c152001200c2d640f07e000f080540380c54220450401d01c2034000c1d01c01e44d8504002006500d283d19055824409110000fa10f194403038030311210026406283c00d42c60b81000302040c0014207040b80c20607103d55044000c0f07100c3d2a2102950b9003a140d00134021442c0100c150302e00b00c0c5c108200d480480c1415101c0503407500040412080c00862407800c940b0030369601d0301e441010702e05066001c49000c90141034080c4296a6803203c0c0d400902900903003000c141118624088004140f2607102100780251512010080424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 887082859 1250 887081609 887081639
    0x30c060504060b0306041b050d02030d0e01030204051509030d210507090b0c06090c030309130f0608060103140d05130509041a01060203040f0b03090c130209060403030309050114060a09090516 84
    0x1050844c03001f0103031100d05100704c09200d910040e50590000e40c070008000c2c82481a000010b4041c0760260816541707401061901e100400c0704081308102050003d5142810001012208514030706044009000b0891855643e4001300e008003d82d01c1d1000950824010f0451100500981d620255220b0b85000c100c0d4450303906541d0003005003d2400c40d03188030b02e0000180d43c03944100400c588401401d01d0820070090458190340c0100684804001030302c8001808031324000c42c003898080700f1516048000e03038142017140d01240244a418002d4084ac8403401d420607003036541c15030b00007000d0f44031810041c0300084140400c0d0282c819400012901503400300290040b00c007049140c41250752228600d9981e80400c4564200c0f83e80400e04070582c0b464504a201d00404035104018500301c0402c012441c2d9521a030800d03008261203161240401400740310780844541c1f02607103440f0034207181c000503804440501c02d40c100b2030344a20320281440780038400c03011810042c4400c01011661004440c0050003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 887084109 1250 887082859 887082893
    0x1020c030f03270303150d05030c0102030709060801030c0b03130606030c05151c05040807050f0606011b030c03050c013e1204150902040c03050901051003030c060504060b030604 78
    0x10f405960030306420020358501080c440f1100c00785040d0341d40d0411100048420010706a440121205d142d400310790284000c05d801c0c65050005030741ca01d4a0742e000751800380194040000c1141ca8001040403a21512602d8195012139207110b5480e15400c1650400c0c520502020342040e1800800208009000340104100d41c020703688030500b001c03c008031003414000c200301c0020309424080c00c9007281d14544d0120b03510a10030350003507082c40880d440d51480e020414018540650104007406159a003000c0c0d0800d10580c000035484610f002a0740060070304886d41d0004090080225051144040c06e40200c88e0b01c04280c40b5408850011441c00c0d54035000c2916001440034540000e030000b074001000321003107408150b510744169100d59480100300485424092074039a5120341c000010313134803805424013004c55590085513505094071060300f140d1300603022a5240100c00c004000003034002d00a1550f0a42141001940d503030760f4104007000c1c0800704000c079850700580d406c000420510041d542080b42c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 887085359 1250 887084109 887084131
    0x2091e0603010c1e021c0504050a051f03110903101407030b1008060d0b2a0423040f09080703090e071b0302150c22030f1401020c030f03 60
    0x203100c25007490300701e41c0038401c03410000b0802180e0700b0943d20b403180410355103102c80c070448460407601c02c0029820190322400300c0001744005420032580c80e02141ca0000b402088411035040d030406400440074440600c000414581c5480100d00c8804005068500144018043e5040f11145c59914070043c511310703103e0311010802801043c1854441d1150486400c0042d02541241081d103c090340c01100003440b02c1e602c5202060391000040d01c010420f80100070b401c01c0400000d00e440303031901c400c01c9103801003500520f083c8001c202628a031034424060441c0c1423451081c211948001c02c014002818402281c01d003000a03410030010701c80c004105a81c002d5440e601d9071500c030702810880100c20303134400c000280c00e054082c202c618a1400010000d20a00480c1d032a8004a41190400381d001c980c103980c1014045480540002640070f070200520307140040b900c005046980b4000400320181d0058507034402c1111121441400b58120b500e0000d507242181d4850180040c4107032242d008840d03200c521 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 887086609 1250 887085359 887085361
    0xa06050c13090f0e24150a030f06111305010f02120406030e1c0e0a08030301050a181d0c01230304030c080f040b030a0627020903070506030f010801060509070e010e040902091e 77
    0x501400c8002606c10000a0001486600c2c585414464011184098031a07540e0341c0100000300508600500390a446000510010343c9414005440d0998043c101c45c15500705881c101240701461045500342d485a0a000070a02841c0ca83e00d480d2021008090303d800082c454400a400d4009420001381c000032500200c1c4940c0365424203440e40000c1c840c02d50059050380c81440100300d0708404081c2c40030b0100c80001e0810340c050709002e501040c9040401c4540020425801c25640500750010844420520022002e00522100842d01c0014001340c1081000c1d0010801c200c0c58000b00c40c11201c051044d581c855440d01051103513540300351407a940040c82c0401c001264500d881c02d1101b105041440340350703107075030300b10000b00654402c1400960500540c2c0c2c0c085060b94070781006d0341c0600e020201c03045e85503040c4640c460840d1020b41282d0300c60001d1204000c060f66200400c2c6a0156080c64080e000c080c041d000310f000303420900002948900100c0400850311901151210344c41c5a030f89040c035007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 887087859 1250 887086609 887086621
    0x2a030c0914010618150c15051b0a1407020114040803281d061314030708010e03041a270103060e070e0607080909090a06050c13090f0e24 60
    0xf90b5009001c8036444d80c6801c0002c1110240410001020b111103041222061000c0c6e615982c117071180b15030201110303a8442c244803042c0c400d000000103404485907494980524950040d0a4000d14040c0c60b202d01000131f254411648241c0d03203428039120702c0c91103507111903c840000f9100e0300716091079a0600c003100204a410401a0088890301c00907803620340814001c1c04104910304841e00c070a42d04800b080200d4616000d030074a0b154003d1458024024012901b40109030501c0358541c440c049a0b0b042510840e40741d44040200c60031182807004000e00060a01c3c1100030070b00401421000d0055107100b04000e12813040c009500b001c5c406d0f0303010881c00f03071a440c622400f51000e542a000207a60000008281e0600e003005103201d07406000168100503a543c00185415400c1b5205200764009001120406c0000d00405800c240038035449401c1000031001c0d1000010948150989251611050480040103520900b69062a02d00ba21606000988484407850b0a6000c000b00049043c00081c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 887089109 1250 887087859 887087867
    0x901061d01051e090f032d0309060f030907081e0d08220809030d051e0c281a070f0518090925050a122a030c09140106 52
    0x248803510f01001c408482d900709000a50f070340240112070340143e010348403101641d070108610000c0600d003000441c410620b0800300300b81e030101c400419407a0350003030148544980d03039002a180352140c1d010741c036512a41c1c0c90080514001e05070740301400c98045e20800e0b40d030200e0000c0d83c030500f0304e01ba14219a5040303500d4004541003c4100c0c0c00154024070b50318812143c4800803074507400e150144110600301280c1000290402080380404404154000386001600100060451075030790708102c401e08100d1b1829881c1e031604c0d801d0007680e4408204d08240300341c0d00008840c08021580041025884c1c3c41e5036454180b01201c01e03600c14001c5440840c000c2c1d2814800c100b124126400341200c80198111030b420300120041c040c10b6550140200002804000108050140c5002180c650030709094680418804244880c0d004200300300403101802c00032900d50840c1c00c101d9480720340c0400c2580c079000000d000361070b10360708001c04649801100142c000c4070f80c0c0029000c01045283c4131500d9270388140940b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 887090359 1250 887089109 887089117
    0xa11120f18030901200f1603060b06070830040b040c081b0409080408242d07141305100206070f050d11040b13090e03071502090901061d0105 62
    0x144c0096001c800e000c01c2e40700000712130f050100c803100850b19003203821424036003011811b03940c005550000c99010001d000313090140d25806802552003505c1c2143c00d880d4007100d0310600c20740d440c010340300c12190340b4648442c0060a503500d944a00703110007400e043c9012652800190750980d540600024003068007400400d04030301c0c44d0300c40340c010498151050700b44009400035050603500280d044c440054109010310011000c0c0c520b00d13204040504a02c410f4030326646020340f124040101c02517612420030f400d05402c80b01ca03110550041066510307594103c40580c80c52610090b007100104035101c040e149135521806a80040f01d89041101901c80102c1c2e440c1000c4594000044049418500f801e00450080c03600701200705011503011198041d0103959842a03102d04110304000a0b40340d0f1950000304c05002030300f82314400703200c105685444075951780102c2502500104514030440048480303581242c0036504083d207065810340e980c01000e40718040c02203100c0002042000d040000f0340c8960112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 887091609 1250 887090359 887090377
    0x91b05040513030c020d0506010803120a050601050d020903120f1308010b1012060e0415050906010303023c0703050714060d0e030d360206030a11120f1803 68
    0x5540d045100d807403c884c80300c41d00340242c0e00403116034228070205409121aa01800103500216554101d44459500606004111400440c500030500c031140c2c0e4001c1c125071412421001c0541c440c00c43c80000790800c4d188959010380c0c2400001d55065410450010309001c0943d60441b602080d0b88454103400d80c1c0c0c20104840d403003002444000c0c5010300070500c0150004100c01c00054035604e4012803c43c160043c0d80c02e8800b0341041591484024842c000c1c26407110906000d0452540340d56030195440301c0c5541c0201e641c1401c90f0740084550310340300c50708e00075403c444200c050005155200b10745420550000769424025114017140554428403801c0e000d48011f000f443c038110071030103070f54020300354411210045d0100700502d510840300c900a180035960300d04c42d0240f019241c2100b51f500d03109040600c282d1500e40f680d404004d41c0c0e80d9070980380c2c408048440401c1000c0c170f424522400b0700c10907140c400c0030412001841a40910300305481d00c207118100741c2811080700e4150740341c0d44e8001d550700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 887092859 1250 887091609 887091631
    0x14090307050d0507151d01020d0816020f100b040605090705120a0b04230112051b030708070803040602010b01030e0a020f03011e050f0c12150a09091b050405 69
    0x100994100180a8240700c0d0043c0141d81800b03840e44580b001d168484601400040c180c9181440301c0129100c0035600400c1c2400181400003c000c805041804010100311b848442c030404110700d81e009004110004020310305541c20455000608002081401002030169140010224690030940d00b414052845511864109002c0004e20150b62200030107200c5800e031207403411200c584607400f0700e000c00d50300c1c907400e100f0a28841c54a1420524140e10003207848100c069403401103000811003004121a41074011021070000010a19110340d40e8805407071351103001000101058040b0140003038802c40e5001b4000e190810004600750f0340541030469194000500360750040c50400701a021202019001140d05000d540c940c500413400d00341c0403d5015110b00411851401d41c03c50640c1c40040c80e960942860001486c600300110010b05107015103004994145066a400c4d04041c000c0c0000c03081403007201050328204a4040c06441c4000303102c50a00008181e42c640f601482d4801d50030149 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 887094109 1250 887092859 887092873
    0x60302030613090305210f0903030118090c0f24090f050103090510110703020f0109051504030203070204050106030b0102010e1522050f0c0909010b0a05010f171501140903 75
    0x611030b401402000021014070004018041540f0801c0701c1e83d042e9492032000e15035461425900d8100700e5040140702c00c80d2030f08100f005004000c00c00080d01450380d10b031400050003e540d40b60001340112285c04c40f00c2c0102203010000759013013020000011840380005880210b50f000c42003580c048450340214550110542818880c55200354011000c45018404480700401072a9612040380d403003011450f01080c00203010401d0503010003000007103200e100001c01a5040f00d480e15034035151003024444100c108800400d040c14400c2080da5030311703134004200f00820750b034407640074004020401410b4055400c000300403400600105000a0079002115460314550380e040c0360040c1805501c02c0d032843c98038804501d10104604204030410341036050002c1601c40e0380c040c100720400c400240f007070f840c40e03040c1619a50b8645681001c03804035513003030038011441d2644130300c02d82e900001c9001020100b103401c1c0c10880011000c91448040240a884691420411412048082c840c108006030182e000c02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 887095359 1250 887094109 887094139
    0x3030d050a0b03101a2b0c140d1e0c1e030b0c0306090f07030608030f030106032405060a032a09050103020a080f040819020d0e04020301140909010f0c05040e010603020306 75
    0x101440303002010b414100b101c2d440c0b0004401b611111055025600c14814500c1800b0783c043c5689052503510080301e0444001c0503d5441020140010266a0003a9001c42c941000c1010800003070700901001000d0060880c0c0640104480d203c0c2c034482034449408900204104981132400c980c000d41015120700074558944050300580d10018020310109691000005424042440a00b44820001c109030341c1e00e5141010003025180701c0800880700c0039100909500040540d8040b00803100c00380c50441e2100d9000900307500401200b90b030304884460841041040c01d100704241e00d80444691110407000751036000460880c0610b0748400040781e02c05000c80c2001d045008215881413003180b24a16109840e20910b041c12040080d031000f60b4464070040012075040341d100510180240e03800c50441d032500e000c10b41030a00d444101c50042000a0204e0f00c409003e40040d00c2c0c142138071005204180351204010940e92203445804156441c103070001ca6280e20900840380554002085184c4504500c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 887096609 1250 887095359 887095369
    0x91407140d0902011b0b0405010b0105190c020a0b0c0c2d0904020d0f120e060a08010b1b0708151f0e1810060501180305070b0903030d050a0b03101a 65
    0xb2005a0501501d102104441000d50742060a40352056400d080541050302c2c089003500c030750400322414050309000e850081000001c00d007012410301e281c00f81010a1b103001048000b2a170380c2214170703450400901c0c2055108001101408080c003139a2088080340440d41c0180442c41d02c10006c0782c100740c0c51b0b1001c6c074140783c0581a07641207800109502d540d20b00d965524400841510000c0301c0e900400400050040c1c0c000209080e4940140d030614034015660000038103414050242c00e01c0700c8008141d582c07444c903442d01d00310113100055003260344241d1a0040e060b40e8540c000707a400514103603100003c40c260429400c0d40030380008207160561150404400d550700704001002004101c840200710050120304022080f4900b41401e000200ca07800e00300010181a0f00703a8010001084d01e0700c0400020307400040780000c4a15a54071542c4800313884000a04522814803100301c040c0c102014405240381507800102c81000840c211014441c05d54025015034903441c0070700c040e013840702c40c00071450b00300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 887097859 1250 887096609 887096621
    0x30903021e0901180612050c09070804051c30060501110a020411130603200c0c10030e0a0809040e120a030f0216030e0909010227060c07091407140d 65
    0x3036040216850b502c499210001b9040c0d403105481e5544903044030106420020480d9801c035400380740c4070900b4907080e202c040d6140080c4c1c004a088c040044180d0010511450340301d51910820018400b83e1505640404c0c20840c584548514070f0340742000000b260741c0500c80500c2c07c95030f040b0140400c020ba41c0c0800c4024024004114440181044141c2020040100b264058140c5480018030f40030a280046500740c0002c101d1850700d4010400b0141d0702d6400a41c05001160032030b5491003000104030128082c0c01d0301b803107101a502c200f05900301000002c00142c010030605503410031210500840450b92152041622007101c5010000c4005562080d0040f006001507484050714245030600d000107600842c40c010b50001e54170000903040c51a010315051f41107039100001303508040449108000a180070b40d1040104841d512419072075440d00003d0b580c00c0c1c841801920266544c4954400c0a4800c0090301e2a105200300f0020b850b06008410703000b410320070800c209041a202c04040401004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 887099109 1250 887097859 887097899
    0xc0219060603140601180b0102100e07080f071e030b010e0a020915030402150310050d0f0b160207060201020403080412020d06050c070309140319060209030a030903021e0901 76
    0x9215200803000c280400445852a80d070f12004001c03035031405045103c800c18508480390114140240103a030381c1c1e80021584524a42d80000040c0041c118000e01c0c5801100d900100940c041c0d41101b00e0703940c0d004154201107074444200c0000901071607881c10718040003400002c05851260005204800784414100d40c4500c0c8040018509031210001500ca00c2c0c08011010014000000b04411404d11a4010f02c0307101c035080c1e40a0550902045180e401260380c06450f000302d0181e40d45100303100038008141c00250f08091010340c1c5084c140c400c038200b4000c001c0071801600c12004005041c51051080380e0031281c100c4c54460500e0b0406c3e07001c0e100d5040c040b01c144c4c0d2250041140502003002481402e01407035142c07407019aa01d00600e400380a0300719a92100c42016805140b40c0c10700d86001c00d621000e1280120080c80f42225403810790001e0203595815505442110b61801c10541c102c0301810035603000301c4035881c010810643c40d824400c100c03013082c0d41003000d0070b0040100150b07000003003111b01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 887100359 1250 887099109 887099111
    0xa0c031107050d06091a04080f07050a060203010f060f051e0a030b04060801021818062101050f01030c0b0913020c070504090803180d1b031b150506040c021906 70
    0x40e0382d500000741c0090306080305139a11699101603000300000920ba1044075822070382d02c44800e1805482c0ca480e5030003001d42050b8034220004d803000170000148a5000803e521003021034a80d40c54414110760a8828001c40011641a080d40000d1901a00694050304400d0990704048a03001d40720041d0f176000000250103068071612891030fa6039441c0200d030041c0c20b24600058484943c111b440041241c4408854012603404801e903480901214510b5886a0240c88059804046155401003c0300301c480040e040d5180c80f0030710000040c0c02d00c61a0480380a104c908030b00988030002c0000610400c4902d0b54032207403501761940800c200350081d02d110b9200d08151202603549a000c942940c005e00c0381228201000000c111b40c0b0401e440c0c142c0c070745c00301d000000c1c02102d280640152140f0654440c100c1884900d1996a0030148038004000302c100d044840100c8102062424000c0f5040a81944d80c20340d003410300041007424284a0120f00107000e134014100340829814039942041715110555010b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 887101609 1250 887100359 887100373
    0x10e1501020312011a09060307031b0306030b0a150518040303140106020a02011223100806060105070848061005092e1502070b0301030605090f0d090512030a0c0311 72
    0x150303610347c0518451401510081600d5a104400d034042c6200c07100c0da1750034103117028014000f044544050700e80c80090204006803d009450130801207610660006a008640100c2c80c015508148501c0d0b000d2840b9460900c035010810300100240c02c800d00468005030310403410300000d5841920058158451890005a94494241e50040c070309030101500c0c9100c10720348244801c8107865101c41e001028900003401c0d035402c104c40002c0c4a0300c21114040d01d0103038042200300550b001c181014850f0154202c918072003a00b01410f0030003410085c034010b0501012103880c05c1900307002203185403282d1001031003a503401d801d0408010740c60002070464a007040320440e4802c1c088140d0301035004d142401070714484203245002410051111808403990854014200030400000e030074003940c0c15a07502c00c50101d0103596041540741392035044410400b10f0b2223035110030201c3d40c1e085580c80058a0003651004005075501040c41d9a901c40c8c80126000620b11592400c0800d22504902200c501410b09640e16 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 887102859 1250 887101609 887101627
    0x17040308030408090d140a034a04090b0a15151b1a090d0908191a010308040906050a08060a2409060e011509030209070e09010e1501020312011a 63
    0x70001b0104201c1110398003100885050580000a296060385c04040200309400e460403d050710721030202d0001c01c060b8030050034250200700c0446d0b59120020143c0200a914040d041821040d8015126016011b00d0168003000a0300b20002100503207000c084445694142d0400884401c881144103402d100c0f411014840001c2d000c0010840700c00f00522020480d00704a0520b81c2404070a0b00803109101c11510204030550010070441c407034205603220703204100342ca41403100704144005032036590345415074008400c0204400140c0244c0e0f01d880e00804c85603032240300b48510651180900380340b9611440004e0b06070b140d1a007203070420800311092100c06c03001000001c01501c0c401e4000c02411910740348140580082710441c01d00601041e0b000905007007417500d010f0030007031450001034061200000020f4400e40a1141e07080c5000010b0100d150560b0740d80c108210300c100540711021000d01d1412007010540c0300100703441b44e018411480160a034a4010b100342103c10540b45000d00c0c02c018051200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 887104109 1250 887102859 887102873
    0x90a0b090606130915051f1b02040e15011802090f1201200a0e0406260f030412020411040e18100507030902040e030a121109120a17040308030408090d 66
    0x451034079248170052514104020011040b0410342800198500011001100b6502403103c80c00007038601b284100303001050021402400c820382041040c1d11503c4060081c050a0004260480301c815141c07a0b034101030084220260711410f00c455512980001d200034842c900900164060704a0100000305040c1482c405480c40d074010500310660030011401c82d0620341c2003a1146a1004101c4007040500e040c0b030a100b45441e100030130700003401520752001d42c00d00c1c02081444032600d0b0fa0011039884981c0c60300340f002c01e004200400c90003113040109440355000c50000359001e0304c0c403c0075842200d5071040c2402c15003c2030f503814080984542040c00442c02550301c80c0c00d010316040d9401043d04099401403200382d490107014038030725500402584084646c803144016000c00399a03000301d0200c2c980e000010741400f403000d000303500003180f61111342c682d100003484030040c40c07285903426000d112508940319180214840901406030810000700011003480040c243e01c80018150040540c0381d0711406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 887105359 1250 887104109 887104121
    0x20071203020303100807060804080904060305010513200105190c06020301182912070f09020406080f0c070f051f0608122a0a051209090a0b0906061309 66
    0x280250b00000140008a0118006034001c2c000b000020001d0500e08000203010301030042010780b03181c50210b103142c03044e500c2d50407100095400c40e00a11460400f1011428540c180c0c50044a00300c1913401204c001c000708019508501c141611041c1c1007800380c0c48641d4a149408007803800700100540404005001072000d1030203400005074810844480e076000c10101c809413020001400d2605441f003040c2c205000c110700b02c0050a6443c1c0c03086541590301c03545003034840c6d04002e11840400101040140350f56000d0802c48800c0d5035111360640307402040c081d03400e03800e072444084c4480400c944004101c0903850000040c2c0701d0011203d2150170641c10807141006444220032503529404201324200d8108400d1240c1017940c0001c07440c0c4100e030410443c4507a05066020204804110041e02d0303d1014070890f001d254000043d98200e00e2110f0849260340c0c030100151344500c004102096a218841c410313528100c1c00a042d1100036100c0300100500d541204c080320740340500c40c1c840130581c200d1600400e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 887106609 1250 887105359 887105363
    0x81807060807090506120403141b010527030306090415090f030e0303040e0609130f111e0102060a050a1e0906060603020708160503070b071e03050106200712 69
    0x124a950620201c003c20203030955004503c115024085444901c00840a081d086a03250400d03017205504803c4904450096200c80c6181d1010070301901d401100c1900070034424048081600800c0c1441c50140010103a40007200c4000c0e8000c0c80080c5490416110654116010361440300024101043d004142c582c01e0704101c424151a0350848101a003100e07001c581c58500328061424107041080014072142c00400041c885c1d004500410340d10a041d8048100054001c1c1e06004c651000b82494621034508860070340c0075480100d01a1a42c04101c482d00c3d0701200141d001c3c040070384078014810060800902020b180c19603c12501d00201d0710702581000d08054007001142e80d01041c28100d00300c42c80c1e54808018940104160070004420740210f41140f220000e020b00a2081814010b203903008802c002091003c5040c140036089421540e0880e20305030302c03103c3c28894400d100d0100c041d100207114074008200b4042c402c9500e0003556100e503091004c4001290348180e40c8400302028080d5041003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 887107859 1250 887106609 887106617
    0x1706010e0c0720100503091216060c09080615010c06150509090a05100203040203071a040e010e04060b030c130b0f04050c090a0602070303120209010c02030f0102040618031208180706 80
    0xd001c02801c090450031a5100c150600d61b045140441446840310804c4a80b1005030000148030038221070000c0a481207160094000c101c6004840030182c0405898082d040c418800c0e58002214030003d10805600d102c0d040c0c1d1f80709405060340e511003024060040d6403001c080c2d1410400300e43e50329031342c00d940e00c43c0b01020003c2c070716103580381041810035182c2170034055481e00400405c80540c800241010031a0315010524034040200c1c0c074000518012500700424030f0041c240002200c4000343d03581d6014500514080103145680001c242c0d807070889001d16900b0441291440c40780c811507502140f100b0b14084c1054981c0050903001034100d500c12039402840c2c12010031030391700a040a0300014040c0895000510030b150554a01500303041d20f0305a22021301c0d4000840d840c05034071801310000c84550260448180101c444d0b003c40c080d400c103002d60400103120f4000e072121500c1500070b20044031f0300203903076401024601604880210004202202d0800020602580701c0c40c2006400010039142d91 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 887109109 1250 887107859 887107913
    0x120203090a0e01140108090708011806111305040b042307020c033d02121504110306102a0209100b09210706020303101706010e0c07 58
    0x200031869107030350071580c0c00c0c030640001840311004408000d4120442400c2c4a01c2e10340c1c07950000ba1a2440a400c10350465013011100ca0b501c9041c1003040134803500c610703810312a607583c0407094181401054000640708600c03003000c006a00b0290310124400340003400205041134031181c040005000100c501050344180000c00c2007059052044220115085001d81410108840340340c030700494121001242609800d07645014400040d00040349242c003c0096440b00448403501c200c42c0c00c119410322040303410240128581c9003a100d108030801c140c1c0c05440c02c0d078840000344203c100350000b4450034045c0801101b001015401da00605000a00000c4001104248141b19001002a12440006050341400e00c1492248001e0301c070f004406482c084002034610740122084125424090703100d029505000c10304c00d50100045115843c0700f14480c542035915890030004903042d028042c042c0d0031800041c00070f09100003500c1d420240703ca50780341c03c1000e591a000c5582c1030840149030408980d031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 887110359 1250 887109109 887109127
    0x20904150f080a030507030509040b0a080a030f051603030e0a0609050a20010504030b1b1c06080a0804030305160501060e15030105060915040f020a030905100501030c0e090a120203 79
    0x240030000940b8008028005101190740d014040340900600281030050100302c4440c0d5481c0c0e6401000100c13801400034a4003544c410381c00340c13030703072072034082580003d808040002e60903026a0844944084810616403802000e49044004011611500c034050084150303400100da064003c1858033070042000d00790104591920141508072039240703d102c5555490343c0010f682e000026a0112034105070182500d903500c8140b0845000380e080000c4030b5040101c2c003241d9a00c548000404696101f1030204021515008025070300d402540e03006010a10030031040c80000d1182d00503003c0310042410b0516500110303501c0d9825074504da0020150314096808100c621110000200131410f025402003105090140204405c0f00008010b2921003c0300030b09900c0d82d03219580080e500c0740c00d0300d5007152075401011000340600b034468003e039003900c01c1641001800c1c0b1948035460480740d00c1404218158a40500011101d0004119910705d00948402d1404038030341004a440c06100303a40650340d200442 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 887111609 1250 887110359 887110379
    0xc0a020d0c031e110a03050409231b0c0703030e01030c110d050306060c0708070e070f1209061107060605090c07080d0b0f1804020a0e0708070c02010302090415 70
    0x103985031004001e604210000826041120740d011056500303409901451140004d0310301c0e1480401c0600944641c0c4400b000b03040c1d0110140003600c00507032003805a41d5140004039109105044004503251200002c161480c90202e8641d44402200b03406604101c1c402d00c40c0c0e405d10080d07074010f9011800c070700320202d041e6074544038468070106141480c40a89619014a030b070b0ba07200b50416070050000010100d072040c0c0e62081034400c0f400000048888141e1201481034565107144501101d00c02400b01040e1242e004840301c0180683c0740d030b581307030110b84064041c43c080c2620340401c0e10880c1d5503801c11950a10749000401c074072401544081030040c948014040f1900c0020903c0000c00c41c20301540000501d0b0a08030b440a02d40c0a03004540c0300101c03000a4401c049120240358800300703000101c64044142140b184c0f0407402140c2140f01e640da02c50752072020020417108040060306c0080051080ca0240303103407130500c90040c50010b061080800118089030b4154940c40310206d10003c00700141040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 887112859 1250 887111609 887111623
    0x180614190c080d06031a01080d120204121407120308070f09030b04060b15180427031d040c14070c030803090a05010e01060e1b091e0906011107052202030c0a02 70
    0x10301b0b4914407096142503100c4c5d84500407500080d04001c010a019600014103805440141103140403420b2100d1041c80c00c03195000c4801441c40042c00b41610001d1001707814041d00c01d420390162100c00517552500d80440d11045041100e1040c46640c1070040007241c0b104c8001c07413050f8803d500c0000c035004038100f00b1855030758040b908088041c3c200a011014032054811100e03d0200f03860200b04202034401c0499034062080d980641041d040d559941410361206407030050304610812401003017109024003040e00c91040300b40010404a4408481c60f900880040000c3d034090194102215145c0d034401c0358030761003a50741c40c6103680030700514800d0020a2003899a00d601c00802000b1107407800c0203074004140028801805c00000c0e040b882001d100810845000c468014a0413083c1e8100030401440c103090403400502507495400091140d5020344040309103030200d08010400c2501e400200500c503550594154021400300012811072101400074500420b030121015440c0e029403080207280102d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 887114109 1250 887112859 887112893
    0x4060e19020405060907120c020102070210020a03080a050103021c062a0e01031506050310030b0a0f0b0906090a0522080901020f15070e0a08060403180614190c080d0603 74
    0xe8401032100c41340e001f08400b010007154003000719a1003080f0348240c1c028041c02d080a5005007414108480e090380c08542101958400d4039070381e9081e154031050100302c03502404000d401650701282460000c00c02c0c01d5800f00588200c402003112a03200410491001c0c00146001d15400f54410b00307030880790000020324181d0f00a00c0d042021a0a4a0449215951030711946084c0000040810148140c5005500c040e640054070b042d59800c1c202051001050304030380710b0042500e0501c0d50a064035042e0301882c01000d00034100c509a03112200244010403001e40944101e007100382c02c00c00e01c0c081d40c101c07043c40d00d03000f90780007601c903c0c0302d03000a41061050b01010000e900003800d08203044941880d6a80c12520314609000b5482040303001c2000d0654507001408a482944208020103500071a00d000c013880188a0311025950f40704152001c28600320007030124103051000074802440703001c40c4000c03c041864444000c00c102c0c7c58115442d4409001010f0181e00e803001801030000e034800b03d8112007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 887115359 1250 887114109 887114119
    0x50a05030d08010306240b0a1209200a170a060e0102071a0a021b030a09080706090603020d09020d0f050606031219090b21060616020904060e1902040506 67
    0x1000220010240b007414080141299a20203100c0c81c3e00510585807504078100c80028280c95071904c41183e016004a00740070005184a14100d071690818010300e244141c0c03000340241411a6040c410f101910303407040e10f64109102400028041c500a21040c1d0100240409000c0480e6a420b00f0f40c142c1d4020710540c12a41c1c010098880068580010300d4582c9110004100041c2c45040800313000c1d10440b5480c6210305006003000c0001031003c001040b501501d51112403006680b2171707065481e0f042502c2443c01080c1e04400800c6a82d000760020300b1001c2090200140c80809903002844400c0e040c00156900709042d01c0c0070341005070030031484d038005804400504101110b06548040d07481551250043c8100c0d21581d06115801307004042e0240c158107185644602075542000340c1c031a0144111507840f0510408500780f814003500f00c07000003040c0c440281d410b040903000c0c4000c004024108850882e5525a00c00e2244824072640d1444980040480d00008642c0100000c5da0000f8100901c00c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 887116609 1250 887115359 887115373
    0x1d060a0302150307051c2a0e0402070203070902070c21050703110315090c10050309030f090a0b0d020d0c08060f3708010e1c030510031407050a0503 65
    0x16035580e0354952000c001c400b035815074030f903909181103649004012103901442c03503003030303546a40000941204500c4002c1d0303145000003c02c40b03183c400000e90907068a002141d6403813000d401d41e0801341c004006c51800a41200d08090f952908002242d124140559400312845003d200b07070440e0603010030480815040c660019010358845c0c90301c030826840014011064190317810520f4400303000095032038295400f40001da03e00085286e80b2a203030034050b5440b03481070f2004000018011004d680c010400c01c80110b0800c01c4503003541d01e403a071140008950200101000142c1c04860100030090410000c40240e220b84c1d00110220a46028913003180500c0402400c000058075540f80040460070f0031901182c5c201611080078462403107450148854a04042050344d2030085044204111030350500204507010113a4902c0b5143e034a811100410f240061200034240703482500b00942000d110328030404130301d6a0740c0e100440c5c6110414074010340c0e0401c80c4100040d241410b501c10080000354007901c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 887117859 1250 887116609 887116613
    0x1050403080a03091403030a0c03050c07110603070c2003100c050304030804171204050c0a0b0a08071701061715060702091012030801091b090306050612071d060a03 72
    0x82c001c40c07841c1d404169a030a201014044440c040351580480403040d81d5a80c00c0500d8002c0240000d0805880424200741c08100d122404504880000d80c100039103041600c05170040140591014201508000600c0751840c0411001c0e8100310360748404200a1000114020030315040281c440744441480345400040c240f86134100b011640c3c8158945001e040c01c0d9290b1038590642d01d00002d01003500310340807540c28948282d0f00180350080380030720201e44c07420088104000007500f19000f0451007840038000802440c0c06500e940d40c111400d800e00e40c0e13285030743c2a20b00d111640700f42c2c8420009101d034050201089a8042415001001da082c0703510038010800c00300f040b40c030803007400074050b1074103600103890084140007003000781061000c0c608011059040041505030300f80a18103400d898811449100c0440d210103c00111451b2034102d8a030b0b242d529840020503004103616088000c0c0e0078002d86d0034505000d0702028214000f801d0f449030080c0c01810403402070050078075004490a20081c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 887119109 1250 887117859 887117873
    0x1509101b0509150f1c1104030213060905280614120c090a15080118080a030e0d050c07060201052a070f050109110409030c1103120d020901080601050403 67
    0xc014900c50402595855241000ca003010b08501000c0c01c0030100450499101012013008003c40c03010103d40074541c00804000000300c801180e01d03886c080d4020001000142040500d030320b40b040b202c0383d002443da60307a035a040c001d07500e017102d62444584450401c1c202c0700e44a600c0b01a074003440c0090820410741400d10098042e5480246c441c40360b060300719007821541041040c41203194016002c1e44131400d0815002000e02944001c0585412020802061003034051007140480c1e09407010f6880000e901e600c03011400d034460701c01e07130301090b13101d56410450b21030401840954444c69903446540b86101ea503c5424041150030000c01c690400c3c0a01c89280c41d1481101c40004d0008041c00b51ba000c8000706111500c50600000d110607800807010b81802010760041e070b0500d0107a12500d820180e1841040300b190613884005001c2403203040c0450200f1811306101000c080050216407174401500030010003500200605003045400203010301d59540e0020160f82c11100a090480c03d050450355029 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 887120359 1250 887119109 887119151
    0x9040f0c3c050f03120c01020414010804080d050a0f02120901060609050a05040c0e12010b1804030816030b0d150c020606031b01050415030905070e010f09021803150910 74
    0x240f150a24840b080400d58051041c520054500240c0540d903010058019010b50842e11a440d442c881080c40181554068212944120307031103806a440c00c03620003104030050074040c140c01c400383d6a49005c2200342d01d8a10080c80301594408041500c1e162800d9803d00f9661660006810000e01400810040d22010541c2094031000c40e004a4000101c07402169402d17481c001459106020500c48180c0d00419401482c100f1001d0b241d0102030ba510304116090340c542a140200056000d5000039401d0030743d0808140d85041d2440c000c075070340f540c4c1c0d00001c0c0c1c3c03190b480c5025511410510541203e4520340e01c40c554100fa00340c000703010f031450b242d4000781d1910b504007020342e000d0f0204103c100f01a07125000721400303030020b1440c4041e040c2103014001c00419a000d411a8244038490b8041903002500305d00354100c45040107025041c90500071500040d40001101500e10900c040b116400d0355400d12139481140240788500a848c640341200c0d61820310080000802c41e450310107050002d5041c7d907421 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 887121609 1250 887120359 887120369
    0x170d03050606070c1716180b0102010b04060603150f0e06060706151d09162304090b0627061e040c03021e0f040509040f0c3c 55
    0x5903075078500000c140c103440380c0326000b0a03450f842e04000c034071045400d000b2090b88101e02d003190050b80b00b1901041d0544c019000e13800300300034981c50340001081070382c100e681080b078188008a01024900085001d80d4950341020001ca074580350840301c80202500311400614030703402640741c82864282000e41811018110354010f940002c0c082d814020396801190003007181201d10800a9500c4a148290052045030211880d465002160241c980081d20910032181d03000d11020b9203180103814510b2040312000c00003200d09084401e1002e030740e80d11940ca04607010f4100e0b410a8a0010b080000c6000c016185201c001d03002000703080c0c0c2034581200c10b90701ca40151103890400024a100b01064001c00308030036803060034440203480d0543c0c075801903c0307580042c0c101c01c04407060320501d074111400ba4500d10380c5007100030b12081100d4900304181d5a0403c0c01410481d020350441e4464103900221500040d18149024140d81042c044540c203410204690751110004185164151031080d845d41c420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 887122859 1250 887121609 887121611
    0xc2705040c0b07050a1406070905180a0e150a0b09010806071d0406080d09060f0509090a05060a03050a030203120604060b120a020c0102042402030307090603050c071406060a170d03 79
    0x188404000302000b138158015042540f01d0780c1241b807000c81035640c2c60300715090710000e42c08a07400030b10385c149014181c01690b5041d175804d0255482d00c07000001001103007101d14061181006003002c1e00c0895aa882c021900d41e400442c45810800c00d100031240706a000c22445e40c01310381080712803a8840c09641408107040b9251280030301010009002c1c00300e5070000203083c0201801400340c16003050b01402202d421f80c0311440c2d0f02c0c2c00d20205803185e01a9400e030680020603900040d034403601d6980081d6001000500720540d40b9101d4407102e2800880780380480240c1e0000801500076505015032590203076048405100b180c0c140503056960f40200300500910082240200348400c14a4041d210750580e260001c645407640d8200020701403040010200c9810b00c007190080c0d5192002c82241d03c41c3c44541c80ba4103215140000c124010b280003030211086c1541403000340001a415000c82c0383c1c80e400c500c000c104605182c002c12504d1354855000f003d02c0140380079603000d4030301c001c506902ea240407810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 887124109 1250 887122859 887122867
    0x2503020705070b0a1806020316260f041d060d0204020306010309081611060325121104051c0512090112020301061e08040201020c090606070c2705040c0b 67
    0x50010719044864009914a03c0301051a50322035900c103000c5a0a448141c45a181c5c03584d071b0b91402e80e04ca119a007a18003941940080a4000c10f01d1a0000b14020202d8180c050301869180b1a0303210035000040c05203085000003d0401040c0c44a002048160340700a005500d182000d400094140da03418500a00070750b008000a40540c2c026803044d000c00340c02944480d1f5801480308002102c100182044071a5104040110201e046c00070549200b070414100c01d1000703604228040314a050190b050300104041c544c0c1d100c848181034003902c0340400e08158296101ca042404100e011440742001b0144a02e48082103404901d0004424181a4248002d6990303007854400407611040c10008029909000000000b40c090303104081c0ea894202840c04111503085980301192140000d0720083e0041c0d000c2032204941d0714002e0803094000400400661808080d17960300500440341e0b50103441170062070a900d07410b102e060040b0030900d244841c420441c51800356182103002100703004030b0051078000300d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 887125359 1250 887124109 887124113
    0x14160f11010b1f030c0206040c05061617091f0f080c1605060403170f010b093006062e02070b040f0609051203070209040c170a050625030207 62
    0x2601400070010701502060701403903a41011003c1d080e0307181d031000000c3d140042c001d50f0184040b4406025551241c4940403040c5850100300c00d9421690502c0340507019420700e90700158a10388075407141f41d40d41c03109a07102c00c4c0020400c030003c804a00c1001e44400c0c0041024006030744036902074008112420100d07031540760f80303e002c0c44900481d4006a0401482084442840400240e10344254460b42e070324205480461aa8205400140c0d0a0341601e41001d005000c80d949010140c18001005024412030600703480100607030420003100020300324103101a451092400703001503644203006071034110b039a038070219050220601500c00d0740c03403881c81074040ca01c01605c03d0052400900312819001d4485890707a40040100c2224412980450b290100c005080d003008640c01086403811000b07541003608903003d0080b0f500d402002101c0c945004240815440000c004582d0701c03401e0390b0001d05281841d440c0c02458114003820102d04020b4940280c51201800203114075518181c1c42c015840341914 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 887126609 1250 887125359 887125361
    0x50a23071803051b0604051f02120f070b01080615040b0a0803041e06020a021021020d09030809010621030203070506151914041a040e0114160f1101 65
    0x26040300000c007038440e00000900100054103400d400014041c1d4042648035010006144a14482d00d508413018502050000880094100540720a401a03d0040c506d10021000320b0780207041c44039040340081754071018000c003104054054180c0b440100002e0901003c46060300000c004070a204546588005444d9200c10714640010a401c2c1c6c116500d80d030311500c81002c031001c008150303c611055588006029440080c0300d144064000d454103141d80c0c3d21020855040e45c0b840b20410440f40c910007003c895040351310042548058901000404810034176008203640030107410780e540c50381071180500072903003100440c04910040324603800785103201e1324050741140034402010381719000d801c04001c0710020114803101c40c50801c88520800903100001080d85199901904189414151001c1502c0c1460b900082e44c40064000002182d17191900017420ba40032050909510303515084d02001100c503d11141c1c1d0050301e0001c0c1100d03440004c410080a20401036410810001480107201c2c0c170381c500f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 887127859 1250 887126609 887126627
    0x1917011a09040c260105101b12030510050409020a060e0114160c051e10020102040806040f0c150509060307110d0e1509061c06081f050a2307 62
    0x94018000e10107801c030b0107000300b4130080b0000854480f04450031038804c1404e05141c180c2d04010860403d8200d400300440f20490911101c5205041031288440801c6c414a001c4101e4220b42c0c1d00031030076180c03180002140542e2640000d000d18102240c200c0166101c0c0b041c0e1060743c401d480e010196554400048803514400800805115400505491403154a080361080c89014140940312140c4c2d440c2804000c81000b03500303503801580041303101c0c0d052502e4101c071819458944009410180c54140d030070b0900000f52807c4880c80401030541d0104010307658403000402030100c00c82c108c0950120040c0c0395100741c900c003510900c4000000740c0b80f1409085240e40840741402201c138510b01703519001d0002c4c1c1c41c20030001d01c0707012401080c11992814404075400e40b07002410aa06101d84004050704201340b0f460300c0305440b9200e000110700c0840802110020384417400f941c0d20101048008002110070150458a5040c10460ba54404035040e8100c2c1049010a004c0015590340302c4208562031a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 887129109 1250 887127859 887127877
    0x10e0c0d06090828260903041508010e1302220228022512080c0102190306080705150c01090803071101062102100311040b1917011a 58
    0x440415130110703065840005a040300f00c220011020800e00f81c400f5580302d9003c2c0c0c1c03854011030300501460300181142401d01d0f00000d9403400c880c00c1c141c0701d15210416002002000b000141200c004020480906010640000b90440c1c1411450003030340108680c40f5000740b2403100c2440b0294100c10303c1d0200d504441c0010100c001b5191116100f00d1a0b01c42d000da40204ac10047c8101c0d10b070350441080d01d5480072102801e0521b0707101014030b45041e0b821040d80746601501c80c60303814007012162701400c0c0002d1042d03d040c5200aa040c89200d0805411181c15411800c03450380480c10070302881e05c030005003450480090a959864104a954060142c040d081c0010000f250102c2444092608608008a0340c2107040081c400d0701d0719448411802c541c840c059181d81c100a104140150500c3c00901800040c1407402007404d91044400c1e0400d40d01c05c1d80039540c3c000300098034804010002a800d41c600341240390131444a204608c400305510b0040c01000c0b84400c44241111103542c0c010121820a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 887130359 1250 887129109 887129123
    0x50c10020406030504110a0803040521030316020708010c080a09080d060e0106140f19180b1c0e07060311130b0327031c0b0d0f030e03010e0c0d0609 65
    0x81c2d11420010050f20003a1800c494940710801c80c40340600d0b1402454044da6140b0703000310705213403901040001e0600d00c0c00001b80b826010036009011410140015849184015003815400e2018100285401083da21800ba241d02d0018030b4542e455110503801c2e081070036400041000c51a5050020782c5105807000454403a01d80300001031347c1e500300b0050078101c8191b9200d0b108a030030b10b01c0300074000b0f101c0d100a01080f40e00822003000281c4030503070b8034015039009113800d141d0403081c0110226800c689030012140c812001ca00701480d940d0003c42d817410a410b202003440160314901410340e4904450150005042c0c41d0444220790b0010102614420003400c0000301000360ba403005c00010368401d65a100740c80c4428400288407026101c0032032341003800c0d04011032519000e0180310b0f11030114030180920741902c8000d060780c103565059100d0038207030249050201864072860b0191048003041a0603001c0e03410611942c440c2100440c810342000025501405002d80901d000d10041c03083e80002481a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 887131609 1250 887130359 887130367
    0x9090213140a050a02040b030c180909061f03050a0f2904021e09040b0a0f090b06010807031a010815060c0307060b010302120105041d011112010b09010f050c1002 71
    0x40d44078541c20350003010348650400c95500c4118000081c0e1041d4022110907060400c0891080780340d44000f010140790520110740001d0941000a055010039241da4880da03000c44140003110780386103012036140401180944c50645507613a8540c65001c502c0e00540700c03120402c000b609010b41821124104000e500c150300148140707900d10912640103860a81c00380b522002c40c3c6090400a4a2040e15050002e0441d0955541e95803141c00e6810300400000640351030711501d80081d4443e0003010300f241e105039018101807900348001080c114009095604050074480010414100000044943c40c1c007840c0c90006940e4100c0d0300c1c40380501501e08507070010400503241001703800200c00760071802e109900500010300d004e0011016405807041d040d4000069a004011500e000d920034101d40440c180349801c40101411038a01b1210301c0022a03c0c80d01c0300003002e9403510301e640301c4a4050030304911a1410060003100080c41c40903a8101607080c008006062500c07458108021b05003088014419556 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 887132859 1250 887131609 887131631
    0x7020a0311121903021e190f020d03030614180a0c0c020d030c231c120c11070b160206030718081614010c11010c0f05030909130c09090213 61
    0x2103c1c82000150010300506100044c182040d000420408003a60300405428000c01c2d801d460014008a0881e502258030b000c02005880303a0140050a41c026200010301c10b00d04203450301881b51440015110b010703c2d1550417655480c41c40c0d20368200010820001c0e000407028400d48040c0340826002c0d6000300b01d940184200340d444602c2c0040305101d035502016041543c410042d0403035042c0306071041504a04400c228801070002200000380d101c2c82c205003045902040d42d0300312090514581c000980070700302e00403080010086c1e10000c00036003003034515011511210440171404250300a11800001003c500841c0c0306540c200104181152500b0900d55150182540c514241000c01d00b1901030b04800100400700003241d14000c01d060710b503031000010940e1240000704000382d84505220020406c00c01041c0c4604e008200740d4442d400940d5560f00401c1000201c100041c0803903151804030311030308001903580c80310078120b485081001c00c811049100040d50b40d20000e10201c003031362503d5404c9031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 887134109 1250 887132859 887132893
    0x20408010906020c0d02150105360604060f03020919020715020c070f0302030c010c0c09020c0f0c0a120b10091b08091930081b07020a031112 62
    0x78442d8040712017040d10f440d400e98944068140b080703a05015100100414102160f00c1800c03240d00f040200c00d401c0c962071900303500e40407941c0c038a8850243e5404104460810303100c2c01014203c02c05035800410310316400282d24150081c070b503612055030b034114081002a00d07010740f0411070780460892208c0308802441802500440301c80501849400c200252505500503020241d0303802a0107050301e40b0421006441541e11190708071030780d8880700c00000710742801e0320241549140b5980645109801c0c3c05d42c15140000b5203401f070340724182c0e11030100043d50f41305031139100d002d5008038190b00d25030342c201c49900c950350a1350101008030f0501a200700f4600e80421282c2d005039054841c800709403602d43e031701c41d5110500282e40305000701548680b001300381d10003040220710540f0304240b1001400401000c0a00191a900c00086a0044280a44004604c00d0008082c4844003040e092402603000200040308920019143e506a85d0f60001252500450211060414001c541d0140440c080a01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 887135359 1250 887134109 887134117
    0x20715050a0b09070e030c0312040f0905090a02012a08040302030607030b060f090a0f0e0f090c0102100b0301180b0712140402120a06150e070c02180a02040801090602 73
    0x50841498000010703229100380c41104260500905400c3c0c0666030680c040d1040010302c0c1032940d26100303007040e950182d5010840e1900b00491010040c0c2c841c5d02c0c0550f000800b1203d5000146114280010070500783c10008640f45000e4091a01a00c1102400b50400c84c0d0354500c0d0701006968135144d000002c3c046918003c0c01100d100340c0444034160b40d1003004400b114807000216900040400c00b000102210002600c1102c80c01407150391241c1c0e0b02c44108400304410351003204000a810300302700f4402da02d0003e207640499014003603d44041d9020000b03441c1c08200f0300034424a656108441e0386a00d0941c0406201e080d101038818002000b03040c642110700007259000300090030900750100d2484e40380151086510704100e03155040c0c6603036080000440b0842801d11452242d0b01240c0c3c046042e90207040410203513031040d82d200b1414001507040101004110009000d5030203010300041c1c075040100d031425029007907804555200c000c1100040d00ca10f5104850380e40c20007044030b080c4001c80e4010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 887136609 1250 887135359 887135393
    0x140a0f0905010509091b0903010504050a03030c020f03040506030414061005040507180b0c0f060f0f010e060102060415200909071b0303091a0717062202070203100207 73
    0x20241507a603400c0111014803901c68115001030441021403107102200c44203c140c41e0312032181a0801404001090031508225000e9482d0b42c81001500309068046c400c0701402c19031803002d4101d0380200f80354696030780b156118160051200000080600080f103003d4040038a19100b42c0340302d410301c2c1c00c0040802009000d000d10417441e000c042001203014001e0040303103801c600035102050785007160003841a005144a00d0301d9000340c4162000e010005d01c0000c0c4a4030355810f0300003903402c1c0346c2000384800c04142c008034000c101010a000d0160380004500e07030701503400b541300d05d003141d408030b0b50744003900740c080840c40340500b00c1d6100117408070100701906118500750f400c80e145076160141142c1c01503d001040c0f03c14010b002e420b01c0846d03c0398001400d9a80510002142d00b40117280a8440200c200d4002000a181d507409400c2c900c081c14403542c001800f2988050425a01844108041d0042f00c00404250380018401c086460a2100e00d5228007a9003045441742940d06000079010040e4400e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 887137859 1250 887136609 887136617
    0x60103022704050a02161b0f0608100e010308030f07170c1c05060f060d060302220f0504033504050f060106020102190503071701080c12070503060402060703140a0f 72
    0x3103548110b4400e03240c00400d911b126000b01406512007010f40c600040c0e440d80202c00e0600d0120b000c852404070417004200035550600346280c021800d540207803444d000081c2c1c1c49001001080403da1500c10f49402001003484174056855103242a0340390704c406001c0c01c00c0280c8a00800c1302c2e046260000c1c2c00441c22401c206441c2c0c9940401c01c4084600803600b5541c84244001d990f00c0508020015003040e01c1d0020380040c3c0d117500d0b600010500042020100040728400740c401e4108450f41c007465030240d0030803105000da803d155030040c010031080c4180c801920500c0400b150070807210b00c414000031490700358500c0c450400d030400d50345541591200500724804e0500000d1014414401c83c1d00f21810f6102d92252001c9040c001c81701c076800684188100320314541181080c041c8406103074000c00864009000c81c00662061116030008540b48081540107514200700c9500c000c11400d9000fa81110341e60f036900c1d501d14003030301c80c440321201d50006802c010423001e40c901e0300802e0102000c022511 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 887139109 1250 887137859 887137861
    0xf070314011404021305041b0b07020a150903140106050d052b02030301330206091908070f02150412020906040903120e030c0a0c030b01170a0b06010302270405 70
    0x282102c1c0c4580151802900014100403170740721500381d035000b01d0300a441070708480e0a001403503003001501c08a541043c000c9100000e000c208510741701110381c0003804010145000c1105041014119000910010702500740c3c100f40141070390020f40c400f034042c0000a20031b03c4a64464281030780e4411050064402031088110741c3c05103140ea0700c03030455160a05034000c0d891a0b0030a00900e400036003219820203103003806c803945205034005001050304810540c4c0180b400b842c090105c249011003040840042c0740020501e04086400c1c481160400d03a007080200c2180c00035840030926010250384804030700000030074041464034102c11200c07120b074000c40301c4c0d42d40c0c0d444082c10002203030f49074800180400d0340c035403400c041f103030107074025030340c482c0c845e600750380c2012455042e5608100107881d044907000c100800c14010000300c2203030140500142c0000600050741c00584566402d44458003804130f00700356000407040c0e0b100740c04807413100000b4010f40740e2554120080070442c2c01d10923181ea1040703041c20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 887140359 1250 887139109 887139131
    0xf020915070611030c070602071112150a020a0906031116080d0e011107060b0f03070602070501020f0106080a172208100506011b02010210061202180c18030f07031401 73
    0x3c00e803406620000490f0f4a4100141e4500b0700035131060104440d45448540a44183d1784c94003603d8031100010b00141090899410a20101c94001000950458414040c2104160303002643d20141d8045050019080e42064942662409007000c0081d001d10103043c030504104542d8046d0006581c007443c00e100360461001e5003401d88500380702096200d00c050100102080c00c85e003280c1d142060291206441628140100c1e0414415400980c05640300b407a08025a580c1007003212120f00000001700306140c2810640d070b0311422008400380101d03408010704566802d081c3c00300c68044117000001804200c0c03200340c4066001180c40340040502400c4c11081a01e247c9000e55031080005945d8030001c00d0141d80301c0701c03c250030142d00342d0441c86010a1061070700401c0c81560b02a200388401003030180c0440c81048041c2040b04a4101d00c00502410711400c0c405c0903041d078645214003941440c0c0309103a200441e150442040a421562049641c00020b11031400c819006484403840203205544101c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 887141609 1250 887140359 887140391
    0xc061005010f02011e0504151a0307050a0506030a020a180806010f120f0b09010902090117070f0303090e0a1103040c32060f1308061f080d030f0209150706 68
    0x702c028042c105e00320303040da00030440e1075501c901d901505c50f442a10301d0081c00b0700354804403400603c180782c1072034900420b0b50311403404001c400020b01045a00c00c1d200c508081c040b950b035000107460807010070b0700854091000341c0211039080a01c0e590894043c0344503030701c81440f0b907129000c0c410010540900c10380852140300e070780302d15038590f500012046840031103a0341e140034107500100311841a550368420780006035071322030b1818000c06180c2020035000d50840c03010f5082010b60b600c5022006411402000000d130041e900c3e00442e07200800115113941c6591542d030181403d10100800d0203000802c01c010043c240c0d031300f04103540c021004811403c0b040c000702c0c0c2584440360300780301d20601c680d840c41030145030110041c240002e040050713600305100c81e001c1d03801041c0a0b4001249071380014040000c00c00c042d52206003201218441800c0c00c44c5045102503c0d10000c205090070141c40e04c140a04544a0340c04540c86140050301440a0b07821030f000b01c0340390390070464080364068109030340c2507505490 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 887142859 1250 887141609 887141621
    0x2190f140f131118040605120d111006030501152315070c0b07170313030c02220f0b03010b01020c2b12030b04060806010b0a050c061005010f0201 64
    0x2001d8580000c1c40145410040211008500104003a407502c40304420709100602800b040c51591642c030606508141c2080f06071551034201c24055002e4820543c1c0341c1e0030004209040c56101d061603c000041403150780c2c02c1031800d00751401c03900d04100c2d000041090560200c11800040380c0c2c0e05030080c3c0c803000483d40048129010013015164007481e0240d40c0346c00095900510311442541c0c1c13500c6150381d50b11660820541c010003d44401150401c01d004a10a038401030710a5030a00501e18585625000344030048048050100680e51010104544460f08544ca840c1c50200b0071561070000841e000001e020018402003c04d0704205000c0303101c0c01c050250130981d0905801601810410805201c1c0780210004d00c01d6450f0b60803001d06100d0720020524400c003900400d0304200072202a13101034243d8483c1c50a46014034617180d02009848808588103042d14105c9a0080e40c807030000c0030803511800307005085c0c0183e001c1c0d00240f1203440c4000c6000d0045400030307200d0640440011f901a4201c4213 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 887144109 1250 887142859 887142899
    0x60e240a0e06071e0f020d0f0903051b0108011406161b0f0f0905190b030a06020a0e040506060702030a142d012019140304030801050405010b180907090302190f 70
    0x4000c21f402d034003590107030909500710700d141d107041c03c0b0040e0b40340c666a01d456003000000410f4101144c000e100c550344002098050040301d45c9105d15819201d021410303078031604c5802e5100120307011381107081003030011581d00c802000010341400107031580345902c2c000b4100e01c60018000c4080301c0018030300c0c016008441c85410104603c2c014143e4494201024212402c0c130307140d140c020243c0000010f1101c0c40a0324030902e8960327801c0c0e4800e03a0502884111503018007400d20421040c880040141d400240156a099104c401006140d004031800741c40c0c04110550490002c04a980070a22003900d03010520321003030b840000740280c4200c4240710320311420454003000c0300d80f410441845820401521410345c03054503d800d84101d50303140c5080c01c00e60030941d030840000e107030b50004000c00e141500450b8017400c003143c0c3c0c140c9000340b031003c018001194007103494041e07443c181c00245d00d03e0145903404d00640d000380091003180394404c480c2600c0c051074081c00b14a440e0442c80418550745802d40110f0f030314 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 887145359 1250 887144109 887144113
    0x3100b010e0f15040816051f0e04021e07020f010e030a1b17100e0706091707031208040c0807030f061e020a0507060e240a0e06071e0f02 60
    0x1015101c18402d01624181c581d80e08401c052207120110018480140700520590001c0c0c02c2d111160986103078050003036441644101171004004120507014909900100d03a24249200c200b8031202c007150180c050201c1131803098403141e02d5000c0900b0401c0040070f0461003140e4001030003075140015542e08005810440e0103501038130001d40014110005209408a0144040700c02d541e03801d00b04c0c1c217164900c00040e005400c07802d580100c03083c3c0c0e4003a01800800b184090f000c100d00b41800241032002c83e120b021803442044900c0b16040d802446020003654200c141000f03200c54154019050440641d01103c0d5075020410024900b032010614100342c0b07130300a01c005001100c3d510380c500034002420055000681e5000d0a2103860316a10003000d64030791980700c1907210744807401c00c18203c4010031341c2c40a894000c0f2407889241d095180100102010800440f100c6803520500c644c020569200044014800e60042c0410359400c46458000c110301568411000001540300320b87d005401c6041c0009a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 887146609 1250 887145359 887145377
    0x708010e01050109021201050d0f02100c03120515040209010e04050a060e0c030709030809030f0105010f090f020301120f1704061e1d0405090c030601150e1c0b0604020f0309070503100b01 82
    0x161270800b2245a00034002c0c0c0c00301d030081c2e881e500003540303403580251042c001c50840b480c1c1d00201a040384080701d1907400000100060b1500c18034045550328541ca0b510b1285a0006689555a00804012009040c060410421132400a8002c00240914010071109904041c00200e03100c400c0b8003180e21500240d90743d0102c1c4c62450307613610900d030008294203605000e40c00d4200c00d01c1000740300c0c26000b40408505403410a1030031001400b10703183c044a0340011401000184218000b40100b110341d2a44338220600144060400101c0184025140d004803400050000344469100b16541d03065a540b0300b448080218401c0c050b02c3d4000305444402444035072046900c02403406a0006a010310f42c401a600302c0c10003000001d00303210b000d0b00113412814840f181b48405a5005a01803080502529201c25180b00e4402084041c1c0d40c0040c001c000f04860000105242ca03541c040e200c1110007a10680d4590416280c03040e120041401543e01901c1280201039407001c282c0a852003c00040c4c48034804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 887147859 1250 887146609 887146619
    0x30904020703030e030705070e06060c12130e1303030f0c0f110309031002070b0f010305031605070902030a0f200d0b060c0d0f0f0e060301170703050708010e01050109021201 76
    0x80e400011040e003e1640e00d151815040100f40020407015106801900b092410b0038440c01d5070320809084c10340140b40c00c0c811400f481c04000341080ea05206100500c0c3c562129440d16403e5000c29089014003618000c10310408420807500888124401c1c0c40510068070550443e60480d0180000000090623940118540318003c8000c0f680d000700e50803d40c2e20700390000e40400d103400fa1307058041c0001540021400140110301c20804d81007080015a50303640d51454540355130303d028200301c00000c00002e500000c1004820000b520051141840564680c81c0617490600145400800b15480c0f600300910a20b900410340c0400d1060905e9500c41402c01001d0541c002c014500400d40d40d0b0440010454140462410844050401d0702d91b075842c1160040f101d001091042201d042c8400c3c0301f1550b1180c052070342c8000a40303042d03c401e5002c0c101245007200c0543c2c075000f101c0e070001e042405010404643c040741034200099608049000348003507684c03140b112040340700d00080d15440c00c1140006000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 887149109 1250 887147859 887147861
    0x14092203020609061e18070308030c0d0609020f091002070909030e1003151401090e180d170708043018050303090603040201023f090d2d0c06020c030f030904 69
    0x1c6c001501004603004141c0300d42c0c1ea034080c0d60068410100e0000c0c04140d140100040340101005844030940c01c0d400e1075501146d500d400e000341d41d5007074442d0003035032609008a4400c000e190018006800248410700c10ba01300502544002d4502500513240e54000c240100d0080c000c000020041690300d0605600c0d210521a54020010795a0304014203c400002c20303c03c869620750040e90481054100300c02c0707040d0742c1443e00fa6121207040600c520071301c0d5804020760f00304103140c0c01810360030581140d684601c3c002810007000021719581c194400b03c4202004100c203200c00c1541c285803550600001c0074052840a071500e480388030741c19441040501c070141000009150400c0c41030044a80d10312000d07a44c540c0e00c071051144030030014158802c80c1c8101c5402c3d46e860703502030109441603140c00c1c00310f07001c1000c25440110103409000c440c00b0303000b40761552061110102c004604143d00c800740d64a012a80ca4035140302e50001849050700404051501040d01d180403016000290725044000301840 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 887150359 1250 887149109 887149141
    0x605030714030901151a161103010f0b01200715030213290703080a1a03030a0909060815160c02060c0307061514092203020609061e 58
    0x1500704050314110703007510368506000d580981c40000000c10f00126201c03c8060440d803a60012010b04040940324200200c1c800131111041d22041c03c04100e2580c50410300030591041c82e100d5015880c004855182c008c10742c1c84280035003003d907140096140c1040c043e111701c954501156540342c010640800144007040c005200d0040301e410007509140d451b004a5144104135800884903c002c546008004c003408508113800d1088100c00c0c0c4e0030009107460080021900400d444003952383d46000d03500054030780c25a207054040080889688100f038000082c54900140304400b001360800002156001000c61401c901925442c4040310a648410210486110601d001401d1049645002015842d8100107208003841600110b5540c0c00030b01e01841140c0c0c944001c0b800b40e912241c0140000a64000c0b044400002266207200c1d90300c94100004014801c036030420116041d0108040c00c160b000304080d03200f21811025600030740d443c024a13050340c03010103036001c80c2c800e40c010025036000c100b20007039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 887151609 1250 887150359 887150371
    0x60b0108090606181e010b0a230a0c0c0503010c0c0506060a211103030d090b06030a080d24091407020d02030d05040503160501020301050f0621070c050d0f0807030213060503 76
    0x14064110700242d002201982a0040c2c612418005610f59a40d908a515940400500008140c0449c01d54281c115213000c1e4a00010401c26040c01031414041c40400d6903010300701c020700800170262502c40c00b801c0035120800403245c3d40a420005000c0b480c020480b00129070461880d50004102d10108411341e07601d600e005c980f6030320001c0343c8000ba52010000f0300250700300c20400060801440c1002ca102030401401c2c284070342e0010010300000b0b002501901e00c410200c560105d4000454130880c8407507040200324040e407e214400004600c0c005400c5248c2c1d07c1102d00c4000115128040102d8071f0b0210385680b00c015070710400c081606845207501c100c0d4018000c5044d241001c1d0b01c0c501d0790021035956601640c15179004801400140f0701568840c0d031544049860510f8009011141940c1441c0300c00c05800492000002400703a81c0100c2ca590956a4007034140c81d2040e035034000c00703080c7d051003501103c0010013407000100d4150203403007101c5904074115003060341c17903103081000c60b2560300040c60 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 887152859 1250 887151609 887151631
    0xd1d070611151627062a1b0f0303051806071a04050c01181806120804080c040216060507020f0706091508010e011719060b010809060618 60
    0x20380141d0154102034a03025081e45010003680245101001340521801003e1660402441480e584041c3c0343d4982d100446149040548440724030302d4449241658401c002c1070050340c0302000904000e9425116240d4031103503040c8a40d0725403206010500c0a81900004001c40c60421158500052800080c0740040d0f0040090b0320701036807641c44100e40040d00d000100641c24200034001000810f010041c5100020b02c0c1141d032224207802000b00c509050710800caa4040103000c124503120075600001c0261480761459146c660103450109080d0340a88241401409982d004070399034502070080340c080322540910b07001000200d071600c10003400060800d5055100b03c100060f0b80480c2407000c034004141648480301c00502d0074401d0031640107850400740411407200c006100700580074810605540c0c0303000a0b80038030720144078400d06c0d2840240203000910541065030080218640205007544403c1c2e03a83e1149403200204680d40b0001542c4030f40d40550450004035074442c0f0f480c1304a43c0302d144400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 887154109 1250 887152859 887152873
    0xb0c0102040b0a030905100e100b031203071205060607020a0506031302090a060e090c0a17030c15060f0307030312090204020909040506071e170402031c03020d1d070611 74
    0x10b80c0815507210f08038070800310740c45808040a201080c410024840000340061102c3c0c10400d0302c0301d450701d130819080c0c01c02c95515080d01f9510344013009849200b00030410607944d2810504000b9000d10003180c1c10301141418440010010b09060042c4c07a41103a010b4181114281406d0802c4070640008144083c0038020403041e0f005680c031440c0c414028019614009080d071704000040c0e20503900100400c1c03003a8426552100325440c2c01c12443c2c110358503001d64007107020b51011154214802c90483e00d980f441034145850011114014845c029001164400c244076621000d15407224614072018010400a015004c42002c0315084916098402000145003407a030303034000303000c404084e10f040d100307984644100014a0b800401c00c408410500d000381000003200e0600522038005640341e00d151a01d014041011910100203c41d4650414900706220180807030004000f90484207880054504081500c2c2600031200e002540307403204d01014040c03541c20000240e0700c1c995440c000100d540f003070304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 887155359 1250 887154109 887154119
    0x30e060f070e0409030e0a1a0f0708041d010504060608040b0c031003020a080a0618050c0f010c050f0d0e040207050309270c030a05100506030f060a0812090901090509070b0c010204 79
    0x807003082d42c62417003500c440d5246c256080500c0307000041d035000001c038034030542c3c0190215a0250103555440c142a5800e40d036901c882c0ca003540b180c0c0100d610441403030146001c0c180b01e1030381c40740690b03041e0b9400341c0b0700b00700560380c6203800c03240700c10f040e00c010f000440d841c1c021400b841c001d1402164840d806040219525550f80c3c04199804070940c442101f54010718910020010b0600a28030300103510107041403041101e0702c1d070326100c07003086100302d1040303000f03416003202e990103004107081c42c51308401035910352000382800070703240c44030713504410b00155080b010002903191520a9440a036002402581082c8000040c04540c0d1064400041c8840c102d482300c01500001c403c10520035414526031503105d040a21000003611405801c031b8281480c0740b40180000c1c0c40d03090071350b544101d4200101c0d900e6102c5002098005000d40c1151905001d81858175600c20600c0008102c006030564002030a0780e82c0e04a411b00300e40e8181c034401007940214400b0082e074800c49020301002030415000500d055030320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 887156609 1250 887155359 887155361
    0x9010f03060b0c0114011203141c1a10031112060a0e100e0a0612060f15120b090607020a080318070905011e030b0a27060219030e060f070e04 62
    0x140e070010303456a4517900250150340320640c0031401040411168960004a42e9000d481c1080307060301030b0302c07000000c2850b00714140c81c4103c0c00800181d29804120013001c441040c480251182c22840c001d008025031002014400d00c0b0709400220454081403d014110001c110140d10140209030300c06c00300e40021480418608501d40600761502c4840d0b07d5030319010405031208001040e50711a180743c000c08104406407070b4001c131400d0381c0c01000043c51202030215070000b040100020f62190103440c1c1c000c11061150f2044070201030003020050583e03a40c0507200d6071b07228012940c0d8030040e0411061000018a100c001c1e41e04258254000754400ca011603143d894840701c3c0d0b220001098941c00100803441480940c0d5100a442d00c420b042210f04645803000c1850000c1c00e91406643c3e29409582c0140283e502d1010094110034425001c0c034060805001a4111042803060141d50782c1403510701034081e102c1c1250300d20001d0090b000c0c90f079822825200c1c050340105444184121001c1c001d91710707915 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 887157859 1250 887156609 887156617
    0x370501050705070c0807030803010611031e0c070b1905031b1314041a0114070f0b060108010f030309030807030e10021c050c0c061b100e10090809010f03060b 69
    0x166545642d103c01490410b44042c441a9000c3c1e005604804c3d000e00201700c1c078030100e0341941c4103410144c030240d560b840820f01d0f40c490103445030384012002c40c0b807407044114174004090400605040711249a21540903020341d204400600c6003001d6100d085240c581e000724041c42c2c4c0f100c2401c01d501040082c3c2403801400d54026800c001c075041007884284400951410084403202d000d4038100b001440c00380c07440c04591a2480c003035040c010301084880300712150000311101c40da400301a521505c0081c0c6096810300d04240c901c40e0200d03040c80004990b4441c01d2900e0070841c1d07010703924440c0d02855903d4203000359028010540400c00c82c2c0e0032020b5262184058800d005005900408160348000b1241c0d40c800701c0550400100a42042080d24002d400244841440c1045500698072030010f900341c0048182c41c0b10801c04d42c010030f150180c01c480d0700d07032003442807515201c1901c0400341228800c00480300c10410080100c0003d000000265101e40e005041c50010b0381030004000e07844000034829508 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 887159109 1250 887157859 887157871
    0x3040507060306063605060403241e051f080606010e01032f0403051203040c0503012003060d080f090112090b0403180504020a031a0337050105 63
    0x1020103001c001e034503410f1107104010500b43c0780200100080600d0424601c9021000f0741140c400d44460701032240140001c80020080144010741c0c03503580386008802d80711292003403e103003a000a8401501c0c40c0038025090b980a1100761107904410f00b440030030007030030060040c50b24204060030007103220324003a40c440302038642d19004044c10310700840010107902c101180700d030416050440200035181039003001c0b100c207010740e100850451030301440c00b1003d010316800944180301d40c3d00c06500000c0004004c500371806421a02d04094a400500d802d0303d46c202c010680c1c3e000344041400075038001c0303005103801c030701d000f82510444406911804030070f4011050004110701c00040c0b4001750340c1c000b4485d01701c1d24100ca1040c00030740e00c162180d5088800c01032020382480760010b0030021450b99030100001078100240110344076492090300034000c1c00c2c5440b48401d500e0900d0304070b074103d00d00000c00301d42600340210b03118801803c406111801e40040341c91448114118500400040c0f0203000f5580701d20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 887160359 1250 887159109 887159113
    0x1302100804061505150a03110d14011703030f06061207050301050f0a05182a030708013302010207050601030b0f0609070c0b1b0a181502070909020a0b030405 69
    0x4201801c284084907524030140720a080d0f601e80070481921440e200020b04603000d03603583c0d11200d00c03080650147c0f00da00002e8455890008030110200e11a0f480000750000e016501603e983c0c07a6244000c002e0408030000e0056403043c00002c075004810030020394060701c094080d50410f2044620164810002e43d041404500040f00510060a105d030200440c21002c80d031101c2400e19080c04511a5030840185809040e001d000040c0c0310880c84c02d540d60106c07040c3d08180c2161500103c594103c1d0411703175200e8000340b800f100000c0c800075038803212403e0340b0b054036030401c0711103807c2c00c1c078442c65940840000c1555020f10110700451000d129081c0207600850b894035042c90b1001c0111044000100b01704e11440c0e0100c14040c600d540000841c8201e03031300c524404d119403030350009201240100280361201c42d500050203540c1540c80b460407031125650050000c030503a02e90b26466a030301242c1d242e201c0140d02290081001c58540e81025480340d002038220300301c1d0340d01d5071940086544200c505603266 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 887161609 1250 887160359 887160361
    0x121103030a020f010c090308120402010c050d09180b030c1002251e150503090102090a090905060603011802190f06110d0c02011407050705041d01150303021513021008 73
    0x54002070103000e08243c0f451071b01e5a0a5400c6a54240c075900840e412100c140d952480082d08690040b084400201e82040407290418400d4800800c02003190041002f018202c82145c55840d00501513007105600040240416080e1721091100c10207000031004210311400c5a6000180b00c0043c0060360280040c50044406003401340c0460040700441400d01c0c00424050100074807076500c1a0b40d921040186403d943d41c1d15101c2c00c0c00d02a0080c120a254006500e07400002c0182d855880582e03498410802d540a1395031388010103080303c200c02c0020510101c99881240140b900c1350b0042498800c403038580705015100c49400030390755600d410020101c1d00441801110b05802c10854202c904d1034500598401019070000300907108184000234000e40c0825850f0801100b03002132005058090000c2190202942c1c81c0081031882401d503c0c9194a043e400d102d030400d100303244900b6690550002c0803648038400d0b080e800c03401e000700f00441c0c2003425040f02c07006a0300c0002c1c00c10721070400e90303440200d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 887162859 1250 887161609 887161633
    0xc0e0306100e010509070c020a0b0409051303021e010f050117070b040b0d0902010c0203120318060c030601051e040807030b090105040317060411030a0204061413121103030a02 77
    0x18140303000d48254085015081d007003011104001039281503e00030745402c5895100c800c1d05075584e1002e941c009500c45003042020038070007034110240040f12038026051045444c1e10180e001c0c0402d000308094016003082507407003840c0d85801e8244034001115000061a107044c0305010701156000e070051290100c00e9810030302c40d50800c105100140010681217840c01d440c046000b50f140c400d00351142107c0f031b280d144c000c05680c00780d2840300e405900a0181c0f005c8501c0c140800d6400d030710844010040703030b6809040004101d0009800f9100d00c0c407009016295840389001590780f900003e50303001d001c80f107041c89035a01d0704c5000007410040c040400181802400c5207001c1e03120110084c070320700490b85803400b0800800c4d84070b80342400001050348030f818607403140c00100c2c01911401020015010000040c0003c12041d540181b00321586e503643c40780e003a03c861a24805901c501302d144060a0f000b000140605110744206201d06481000b0049800341ca0201003411500080605c2c40980c2005d952058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 887164109 1250 887162859 887162863
    0xb060405070809071206020c030a09053a080405120303090123042a030309180b210304121407080d02030f0d150f140906061801120c0e03 60
    0x1070030400504088080e440c2000e0303000e5603150988500da21802240e80000144840c43d07045801d80c10258081e80d550303480d8070b00060850341c80d45c0304150092083d0841da04228003815005000500042d1050f441c2c92200e400188803460b41c02e509135440c40c8100b0000405a544a4000741c030152188017860b00e0b89444040e0720300311640c020200a01081f400d07400c003c600c008100c00342d44950f002c0d00a59102c000e240309030600d230403000039846210204020100a26400484032003c0301c00d013020f41020032184025a81c1500c01e001145030b0080c178504140c2e10070320801c0100302501c42c03009007101e0031306559000c90405599191816550746600c0030340783c0000f50b000d015480141c800c1100521104030f0307030580290790384070742c1c8001116a10081031800e03a000c8260401c0c9407141000791048040c5490356010302c0744806620541c0c501c05221030100d000d6041c904101c0303105542c000d100609000000a2003848682d8681c800340c1000b01d444442803009556100e0030141d41884e41c0d03040b15014000c1e0600d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 887165359 1250 887164109 887164111
    0x504110603100617070806060c07051c21050306010f050f16060f0b0f011805060703023d180b011707170604140f0a03030f0606030c1413090203040b060405 68
    0x1138100316402003040a0280c02100c550780111080c1c0f00d690740c445c4405401c500300032560308116400060f50505001c4120221981803030640141e0034038146110300481c840c00e044e40c4440354404141d0500c005410356001c0c3d8080710035140c441c03e055190428000350b03130a031079121800000340d410318012907100303101123840fa400e0700e00f2200400b04441000d500c00580010032110000f0304004d255440c0c0400d416403000110010103001e400151680b01d60318019450342c400300640b030b000c1c81c1c07102241452000c41d10a0030000407044c642c500da00380507045250b009402c05007131a015802200b07026070005440c0c1c220f00741c024600c01280041340341c8121031460801417254001103403242e010b409080540d1000c1252500103a015000c2002c0818440203607041c5200410398107510301480044d642415013640005031514903002c2c0c02c100302500d0741c90075030449880d90740030000101c00f96114800755254200410394482d80681456610365501c0b1070f5402c4c2c0e84100c8084441021207802e20500e810540925 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 887166609 1250 887165359 887165387
    0xd0b160e180a0209061201030609050c0d0305030a1d0d020d0f02030f09090402030a0f080a030b010903081812030c07090b04060b0a08220b040c2705041106031006 71
    0x345108101107481e410103008007a1401220a9000851021a03075403001210402da580d00241d011a42e0b4900340f0724028240741034141d400c1d00034280700080300d240248100040c0c1e640740c0c44440c1140c4030900f59030010300905040780031040042045201186080040c44500d05031503004204420b4900360080c10050f0b200790a030255170003401a07019080c102419292180310540d510f107626901c60001070300e0b03c18051005000000d103420640f05004140d402003a262002c0d4038140316801c604801195102c00600c005444c2c0700060204c0b030040034403c40001764044008080e0340c00300e01d211000a0542c1e03c60305001000303a001c1803041003400303080d005511695a00b15000c01c4001e2600000200074850390560a04000070b07440016840c0c2c100400401d000300650011a202c03441a1502508666096400303441410520070300040355060790304220062041d000e4184940c010308214a80680ba000d407003100e01088481044582c0d440d4030f001780d4403c111483e00e408185180440c0a4a030900440f50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 887167859 1250 887166609 887166619
    0xc0e190c0e0609060d1d0c010816050c010b1309031101060b07080c07030c030b070e030609070510050c010c0302090918070311040f050a0f11040302031b0d0b160e 71
    0x100d61019000000c0c0c0034007290a990a030382d1081d0510000d1628800c1c107444a8030f8038a011040c40070701340740192020070901c120088689680d6088010740704007004595402d43c0c0b07001d520640b94420311940c0503104d083c1c4840008602003075809d000803040050503c0312030001c0d5548010809041e407190551a101348402c0080080368100b010400091050307588c00b400392500014007941c0e0751030810002d0000c40e0031003000c0b1a81c9840c3e18009403400300c19950040000e0a02c10703000100d29000c0360282c01040c002001f800c00764604420b101c8041d4201140400b44481030107841200b00080c043d0a8a640444d40c0050303035284104100401d5107000f0307008a240303040002c1200c642c075500140c1002903d4019000c160100c0855001502500d198152a001d41d81080c00707002c01030030150060529900d070f60205120090544130406420b01807440302035450381c800088901c075001002210780e681500a0000c01802c2c4a9803141703075501a050b1511904054000d940066540d40186515400d4078200c503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 887169109 1250 887167859 887167871
    0x90209222a1208120403050d020c160905070c15020c0118030206090d230702031f110909010312110f0c1f05031609080a030c0209060607050601030807020103090c0e19 73
    0xa4003007550003402c44d800e104500a002045c00d1600030001d50b107840f030710200c0a42d80c42141c1c0050b07603110308114a440c4160901c0386400300c1c2041d4580a00c602c6106143d031407101c24556900c92031a2500403515503a03102d5400c001ca8100700d0001c0c062402d0200030710092240d03072119450024034000b402070810300150400c5040c0744031158030049231103c4c442c03040c60020301c000e0025034800300e40c869008001d61620403802e000520920668407485000301000701000052030500c4d00480f42e10503a00c080d584080b4420040c000201000a10380b5841042d290500d42c10800c0060316103070510300300c0070f00038580c0500404240e9252022402c007442034404214816540340d14406001804060403950309207038034407000205907200e070710648010320010b01107403840c00503401e015106584100040e40291108400910a41000001c492500350310070001d080aa00e1754a9a4040e03400c014030880c10581c48101001c00320305204250b0015048042c141161810041e449036800c3c525402c203451300a040003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 887170359 1250 887169109 887169113
    0x703110409090b15030a0f06051024020d0806010905090a0f2a0c03090509090f060a021c1a100e0a030303050a05060405061f0c08040906030203070603090209222a12 72
    0x10040c2c1303a00588c04103001c50180c80da00d010032626429038000d440c1100c08040340900200c1c441424007604106502034591415000f042140c0160049031810b0115100100810007414910012a4003407003407680001c0200041c500342040d1001821134060003ca0801e559614101c01510120400b8450070428885160703680c002c0c00595052068602c6a01244001801c812047c000020041d507a501076864a14040c90303117a0081d00050ba00b0007294604110f51041482248291101c42001011201c07d4100710020450141520300031a0200420f0030b082a0705512018180300140d842500d021540c0c0c0703048011002254401082541b01d6800c002c01d0040e50344405510b01c040300c912081910002550381c600780d40c0804c589200805070f00d4000303000034000c580c40e40312900b92442101540c80440d5035000c104c5c150340b414000a94007020350320100d01c4a0500180d0306506071081c4c10411143d08950300c07034191a0304082042040100c80907104501160325a489101800391081d020040b41c2c21a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 887171609 1250 887170359 887170373
    0x2d030411040b06120c0c010c05041d061507060504031b121d09040b01050901052b03030e150403141e130302030604051c050c060703110409090b15030a 66
    0x440c18000c0d55100601c1481d601c44504480c0700300c0714000e0054850800030210b40f515401103140281c6c55103413402c0b10044510450441c1c0071140b60351940404100d040d001402c210001418441d0b010321400250b80c0340808110103012100e00450b8005018901400c0203085003225000605071f840c1c1c860091030008284c407000d0034040c0410b1400302c1c040711640540800048902c20920b9103c3c18507000c2100700801c010904e41603e10030b88600341c142e40d0307130390500034003030101c0800c0c0710300703449200d0000c6036010b00c0a40c45403241c0c002d02d0040b500c070034107440d0582001c41c98000415500e4004040006040d0000100840c1d80200003405d45420030004101003000001d80b24182c0000002840808040110a40c0703405103800034182c2d44a41001e02e061039840910b402c005035180c40d100e000c04206401002035401c140040310252615a5038007500709e00511001c10801c00460007072101160080e0f0345d1081c000498410310011845082400941c052002d004810a100b03921980c5200001008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 887172859 1250 887171609 887171633
    0x39050405060a080a0213030b0a0e010c3906021b0c06160c09110a020c01050a080f0a0e010c03020403050c09130305160602190e0f210c062d0304 63
    0xd0f85005005900c8114003c0003034810383da8010416a40410080140220b12001c5070190748150001c100c000b1205161500b60b9102d072100b030010030403030503000d12085545d040051005030415444240814071040f941c00080d00c5500595141e5404030780101a00602111503020010b00c1009040d10322820340040e12038814000c1844020701c0e00700b401c0e010408100c9a90020b021801c0050020400403c2c5d00358030b0303800c40280340380140700782c3ca0518655401801100d03c40030403075550340c00a542c0c00111201100001d4921001e141d81c0b40c144810904080c4121246000b5607030b0f0242c1d845182d0b05180d45031400402c0b0f41440340580c00140b2002d1130345170f9100500325500d030800c0703910b514014011200c0c4038100302c00580103d00000d8010706500010740400c401c08150313112903070308061140500068000070541d2a41001200c02c0040d08032000c1c949601481c90958211024001c0400214000d81c1003005800701c007600d45070300c1040304000c2c1368001d00d1030100c400e101c03411487c0640365902c2500b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 887174109 1250 887172859 887172877
    0x5060c0a1115070516230d0509030703030e0117071e03051501140418050105040f021318060f0b0d05090615010c030c02180f0c0403243905040506 64
    0x60b0014140040c03601c15034190b441181c000110700d0803000514031080001d9906c280740c9215000d081c4041e422070f80500c040c1c072035101024005023116810343c3c0d4160340040c418040e0724140918460520407450710140d6440c810b03c0181c0e509150403480640c4842d81c070390303a0032483c014036040004205020354030f6900c0c03880c850424a80880d101003078403149601031140350003000081d0101085041c00e14001e4007c64100e070b40c150380410544881c25072007000c82c000d0103203203010b50440c070404003c0c106100e5400c125840c2d002d007000030340035610389020701d0003041c562103540751110214440e0f06540c0244110707a88201102d001d03000500d00018101c0e0449080750000f0705101c1c160010006240c894012000700c19800b50411800f00d20216035407168803800c07945800e00301280342c00125480018410303241146d91040022045d54100903800c0055903450301148649550f50344981354042e00d040802c4400d0020502110141c82740c884041c02200241c0303020018484208020861074548204503807243c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 887175359 1250 887174109 887174117
    0x18040606111b011806030c02060c0703050d2a080402031c020715170a09121806080406090c031202060901140a0507120c0f031808190c05060c0a111507 66
    0x10b440e5005850002550404044d1024000300c0810a903070582c0c0205400d00480d0201c400c0c84da40e1003010340c218454484014001841402b50300b41b6a6000c0d00614031410541980c6001c800c00155076650781c011140c0c4410000e10000248020750405110701c16030303040854040e5464058508000e0354402d2184a0781e1000d010128105550724440c00450340700c070107503565420359414a61038030806461408402e50360307800d0356080c100031031380100e21418011102c60b841e11001803601d1001d84603494010030640b0001d4650382c0c2200007981c04858100070314070501c0f0240c801c5c600c00000034508070005000c1030b850783c034105145c00300e446a030840307540c01921103d01280c1030740c8035042124507030084000c82c03011354140100300e400b2035008400d4502151041c0d80400003901c210300c1000000783c040d40081d000800402503810089040b2114070750500e01b0741810f0000d0b94a640d13400f4503100003111001f0407910702040285c44075a100c4000c20180410ba4000c1c00421003481044081800107040d0000748 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 887176609 1250 887175359 887175403
    0xd03150506070b0a09060203040c140d0b06040905070503010204260102120a0507031409060105100503010f030305070807050601120c08150a050a0605060f04080c06190c020103020f1804060611 84
    0x1440c0c41d400405c0b400764403410540d2a070829282005002d08a402103070703000d0744c2e0800c424207103091031700d84602e005410441c1201103403115400d0200400903020309442c1400741610100302c0761400d000820040800100c1840040000700d014a544804510100b40e143d004100c0d80f44519140d00c40740d50405442400001c0320f0b01c4030f94041d0018011000a140304014540400a0101000c50710904031041500e94412031800c001d400c58084c8800d008064080000f10428004648228041c0c500f040c4240102460040740f44c0306d407864600d09030b22a058841030721a20708104000c00c0c00040050a0550041000130100000a01e117544010190305680781c2d00c03000a1941810342e000180249405820a55030790359441a0f059030340d10501a014071841000f00a0005052040860ba0440b100f10307a061503a4034240411601104268401d03030400d5000d101400c1e410481b8802070680741903480c00c1ca50361920703c10501c01550000d900c49030500a0111404140e4000030601750700200b41c440f425094 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 887177859 1250 887176609 887176621
    0x605030109050c0712030b09090a050604350301180b0603060f130212040506090d02030304080f0906030702010b09070f090512100507080a060e100b1c020a020d03150506070b 76
    0x990058540251207172803000900e200712600340e4000c244030101510084500ea8408401d25030f95180e1610061043d40424009408960741c3c41014106040d6800381c81461034003650302da03405074100002541c241d071000004104103a841d0940100b50b1900090500591040d40b00050160000400280c096840000381010343e40d034030022290481c1c82c0000031500c03483c0b80d5100b0a10720100b29400c03180c5104400109070303035400005580411002982c001c6241d41da030f03541d52102c260000710900980e40030a00103141136680703c402941c4901000d600008540f2040c2040144000c405088031741031084000c01c00c1420ba42c401e1250056030340070b032110440c9018082000d8501603605030350340d05651410b400e101d065070f8082c82090284108460a100d144e0300c900d130348520207900340c80c1030b0600b09040c0d01c100b1020f4502c2c0d02400c0d0040c1203641c2204500c0302e9413003410076603000b15420b8005801030f101141d00d00b50184a0112844102e80f0385101440c105404604140704214014200c1820b050020301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 887179109 1250 887177859 887177881
    0x1a150a030827040e010902210613030e030613060f0e030f0f0708040914100b0d0504051903180816030201111204080303011409150415080f0705030c0109060503010905 73
    0x1900c2c00038008100c04001c080d8100d0003000081e074124810b00b450035410010543e070103d921051020344010340855162104003c00584102400301c0600c44c144001a9056400740000e03071094150381040011600140752000071100e83c1c03078161036203900c0c008403c0100140001034665110421503000c0d9219080c401c4103034240112540101034010024010500c0095a08110117000c403a440542007915003400c414245121400740620320101809010074041d01c1703410032034100d40140203a0781c030031004101036000181081c2040d400328401e41c00e00c00495102d00f42000c0204090806000c84010091401e41f06400310312020f41008403007081c0d20541c02d0144080514000e801c00029900e940c3d0340e00703ca881350000d01c42c5c18981c3c00210902403480c10540c050318854200c49201c14044001081000001d0198a5201c503050043c1980800ca4840400c0500780ac0282d0710000c1c10094680710030545840b04140b002030420000d03080800209811170305807415030300d060034081004d5698100c211 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 887180359 1250 887179109 887179177
    0x90a0b04110d08030c0a030b1012090c0b0705160609050919020c06091f06050609040c09050d06150807050307031401091505070e010e0d03080408071a150a0308 70
    0xa048070100006101c0080000c174010103810f42641c41c244004006e02c0100081c03044031480c03403c00724110405d20142034200d54001c00b4400d00c41d0048044060700c1d4444500a03410514027102e86a002d08010300148440220240040c9401d2600c416131030704010120704110b1000d8100822400e2804100c804104a90180c89003076401c2022100a032409001055072148210f11590302d012000d06801c01e11031070f034040d04042e508041c0055140903003440500000748400354000040081c85a030126541e9904003000c032509005200104054000d07440841420340164040d100039070280604000517100411120304032604104c800400c8804000024050040003c0c0107040c07c10000040104402a030320941c000c1d0b4203503407403a02401c0c441c5c3c01943c880002d10342843c0d00c0721448c82e413040002d00c55003800394403911030882c83c0d003002c1003907890b140312050000159802c7d1500d541003000b61050701d807c0035030200d03007141e81039070031465a200d60312540f15410341c000d01c0048210f1034050442504c1032003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 887181609 1250 887180359 887180363
    0x30c090628080103060c1b0f030c0506191d060f10050904032708030415092102030d020d0e040b060909011811040e06060307171905090a0b04110d 64
    0x501d045030700c0d4100200044800d010899103a0700e000c041c0380401e1320641a070f401030449215103807200d00240c0c03200300940c00172040407010014400c0811002540030302c40c5a0144030100c000c0321418010400301e20946207410f09204005040e1212072644a800080064001035080c40b40d506648890400f400c0010103500403d412011000510041551141c8450701c0140f24030441011072243c1d6080001c100011711910146034414441401319110345101090410121f090000c003440c1e4406441242000c0441c400402d4081403001c1d105504003070140b002c2c8060b044c401740c01140da20701d0016007082c02c0a40480d0145940780c1010801e80c403480c08440300c440c4001c104209940e581c04019645e000c0125a80b00098108900e0f00b0000310f0300420303503050b43d001c0d02500c6596135441c41407003e26007000300540100200f5224000205038150030b054041d03005103401c404020580c94500c0107445016000c04410303445038414030046101d6040300d42e04240c1c010a41c100c01000c07103000070b1000c0618500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 887182859 1250 887181609 887181667
    0x7020111130e06121c0923040e071e0303080c280c0b0411040612080409050c040b12091b0f0f040f0612020a080a0c140102011401030b07090902030c0906 67
    0x100c1c006121101024600340d200700d540e00201e0581f41c80c45c41c8211000351541840c05900040409102c0c43e00350001271038800444201e46c2041d80e60780362500d41ca01000103206801c902d0304000d006065010101c658072403000c010300d03854503203641005214041d03480c0242c101500102601c0c841d075841036034401c00305a0889440500d505042c11300c0202c101181d02694410351411100040060700c1c400b001c50080e421035041c1741050300e028214800f0308002802c0c1c0c401200c00700808209850140007614800c1c0f0803103212401c03803901c03070202468809982c1254880040d0b6200c032801542d6604118008400191811451003d48001142c00350009201c01319049041c2140810001c3d4582801d0800a00881c1da81c00000d59500381c503030300d0f491a5440541a441c0f06801405100c02140d55403181e076030180300008408a10500e0003280340303000e03001126803190710810703c04203950044a01000d0200c150045140d403c100702c000c03440f485008961401010085003407010030f51841035159400c1c4000b04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 887184109 1250 887182859 887182873
    0x6030c02071a03160f0f0e0d050703080a080603060420040b130c02010605040e06060108071106010b280813080d050901020a12090b0103030507080d0e0607020111130e0612 75
    0xb401d80c0150012615050345900358012003001034843d2514100d00e212a8562400303003106410300f1901c01e40880b00a50300103a13107800c03840c0018000c000355002103000b030045075202e0b00250402170154002501c003a2095120100b8480070840343c200440c03900781c00704811040c0c0d07140540444c019010b100e42c1181d115800d607105400c41c030825040302c4042e81e03c0c1d82c020829142c46100304000c40c2d0f42e1501c20300302c65201c040020225400341714400d03001842c80c20051441204001a00e25004098203c040e0411011034074910b00101795080ca903030300d9851010b01c042e081506070003c002c00340041030302c04601407c5800e0810b02a0341d0045139a002c1c0c001206210601d000340c0d106000c2d500105441c000515107801d084581d180900c43d403400c551303109600822592030340d10b040301d0302d4200f158151002c4000b04034000301d20b1513510440507131485800c0a00f0303040c5000748019003196000c1800b050113040401c0f1806400e00248410310a0b264005280c4240da2161004510503606107019419180709503e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 887185359 1250 887184109 887184149
    0x807031401090b0315010b0708090a03170904060803120f060d020a03050a02101b03081b07060605030c0307030809060f04080601090203041b0e16021c08091203070906030c0207 77
    0x500001c41c3c0b002e06400f103d191402000140c14152000d10a203481800144800b0001034540ba0003400041c4001b002d080c00582c6946401c2000c034001540d0540d892400180c2503c2030a15001e010018074101d00618100380300868112a02c41c801043c42c2a00c1900c10001141aa5100e004140d40c940150100d5000b503200d107446980c0d042d5205080e4440c4041402c0d03100140e116000041807003e04001c021501030090b035041e00d810f0000390910070526010201c14000d5501000a890981d0160201090003071a00d005e00d42052280001907002e0380003000309101103132549040341c00348002510708a50341c0090914080c0c041c0180e4109048602172800001005159030300914044c0d4006c800d0305520001c490302c00e41002c2d013580329490307001c4140340004135000098505402d50f01402e0060b80e061150f001b10342003906034804841c17004101160144451448200304c40610b21400101c61455814440c4001c1d19000c081c0c03043e0010162140c0c039412401e4400d00094006080c052001894040380c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 887186609 1250 887185359 887185361
    0x1914150103060506030106051f09121a010e160c050a050105010305030406020c040216291306270b190f0902040b010206040c05130605060a0f080106020a050706080703140109 76
    0xa10069580b54107182c007080181c83c040c0304080131698010456818030291030595081c008a14500c4410302c08480d0340007415030429205001c2c0c03030303124a9841c940400042489441d00b0b40680007602c203409541c0801c88119004001d071407a414850074080c2145003540340c05407812016560080040d400c200002040060000140c002d54460f03400740c1e0380c2d90403c5820301080b401340c1410302c081103210b42000408201d00a212070304940c3c9408204d034418072003903d00041350005070f0712000ea60184085000912000b40704851780f007c4448038039282c0300c46003155840c144041d118060b29035007081000c9280109401d900f10140c40203203c0510110800041842c001e004900701a4000e070700301786000d111580b000c21400d10031a0300a820f201401e040806210400c03603031084400303055907140e202040540e0b0b444040c0c0f00889c1aa942d070300340300110150090000c64181d00900641d8861822400007800109001c81511081e00d0300d5a513598402504401800c4001c0f108000d0800c140c002140d84001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 887187859 1250 887186609 887186611
    0x9060d26031b0307051c0902100e0418020f1c05010c080f070206040515060d020910050f0a0602070b310302030105090c09040f030e0319020406090e191415 68
    0x11110300e400780100c000000041c60f2000b2103600300001d10400c03035000440c03030008201d0103a41810800203107560a95010655040c502c1382d41346c000c9141c445860680c2d240500940260910300101890b50741025400b1403182051711400520030380c12010201321010550329015111500708009102210a80101410095090380c507d00410700d0000062619400041d200740030329400300040039003100d0702846030f90602d00501480d50100d44c1c1c1e101e01001d079031a0a2000c0c0995030a04107000f9039031508041081414402044a01400c00c941e400c0120540114440049401020b02d06548010070300420025040d007000b8036064940300d1790714010944040c840f40c07094a100b500204101d03181c10618583d11103400d00d02c0d6a2203110080040c0000f501600c841c08414443d081c43c01210681e0b20020f03041c40826a1803005000c043c0e6440d109519184c001e4000814800c402000304969695603592503d00100c039198512a0f01d400c100200925008520307014040c00040c0d8101c020182d40d0441c010360 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 887189109 1250 887187859 887187871
    0x1d0d11061303060605011b0b0c0c0d050301090b04060b0409050c0904061205010c020304080a020d1a0f04051209100c1703010b090102101a0111011103130b07090509060d2603 76
    0x220f0502c4c00315455000307a15010786020400c83e00b0055449a59540d0580c0c10020100302490700140300b01102e1307001c00c0000707240300f61413511007603103039030601c0c0e100c02c00c490191402c244554100001000031200f690100c0c2c007514445074000c1a1a0381e1034800300068460003031056001840e00d03800080c01144001c801390542e100b00001e01000e09001012030703607070040e4007520340140c00c0001a83c006140549665282e80e2181380301d0280c006a0030b1090400d01c1e01250031400c51040031082104021051003440304001e40940720030300f4035103010f0114010500c0e0740d9440c000c0c414641c061500344418001c020040300100c64070666a0740e1143c10b842440d81200006501600c29200c618030784200d0340c00380c80d0368402c0104180c0f280c1c508400044400244455144415550f200c602006c1c50808100544c41005c0d1034001206268603031400c03000441c001041c0d0001c20003426800d00c025036074660100c0e00300400326007250980700c45003012032422560042000d01d285e401180105090715040c041c500c961 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 887190359 1250 887189109 887189111
    0x1503070311040507181206141e01062a0618050102041d0f0f1e1303120b031c02010b031905060903070809100c1b030b0105011d0d1106130306 62
    0x14590071000c4d02e0021014900f14408103401d80e007440b44807198481c240d6002c7c0208408181c0500d10700d021003a84000b80c13856882d5181c0d01000ca010015014103440c010030345882d040c554a000c0c00140900c81c002046030400904038003d07031205000c0e954018800e5014214003442075100c4900d0881c1c002c0d4001d1050300303a074254042016050407a1500c0d403c0c464540d4104403016a071710720b0242070180c40020003400115074456032006006407451100c501c11402c14009031250650b5080150901403110f000600300360030034200c001241c0b03012504910b152001040e00d180c03107030b0441080e0701502d01e014901350144901c803070304c001c410f80744c1ca61078260754014130549040e5110400116106d2050b03080281459004009801803802d10300c41040c8044a14541102d00390201d980c3c40d00d059202105440c09103262050134001c1c4070403502c03114010182402c101c940d40b038603050400303031000990700030610071a400380300d135001d000711114154424400280f030241d4850711502d60030750140d001c0c00240d98107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 887191609 1250 887190359 887190361
    0x170c0901082b050f040b03091b011d01051b0102030a0f02071205071a01080a060b0906010e19090923010209010509061c1d0f0309150315030703110405 66
    0x2040020a1881c91803103464101020700b2041c80484181031031400980d02049010032004405081010280016000c901d040a0741c0c3d04281c51544d1030040204080c880b01001e00403062801c0c0e070020001c0d0020040313803190420203101d00c0d0060300c00307000e84a81092007051800e092111100194011031140c44989801c200700c1c0c103d444120124002c03950000d109000d0401c80c100381031b01800140540354070803500100d100100c15442200c400c030070b030f2258813650300c2038060100b0031166010b0340001120a5488511900c3e11500091400c115210700c540a040c03e0a0912078101e4241c9160015001c0180140101070091030285003114010020310992060311941070440001802101c18144050b910741e41803565501c10401c00d03030300200c15009080003d20400c0c1014800d400b4010340c0c02c1402519000850010700340504150398854510000c1e04200030114032591000d031184540d02d421410715449548400301c4513032034400300c8000c0c0d5041c41940000001c110310705032061410b0317409031002c0c000c5e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 887192859 1250 887191609 887191619
    0x14030f0702102301120c0b030c0c010f05010603230109020a12050106090602060c03070507081b070306060f0807180c02150c0a17160e0d0c080d020601050d0c1e170c0901 74
    0xd80325082c40f00034803000e070f0302e442000b07e0000e80e000b03140c1140c00100003600d01544416006c0c21135000e4140d00c88265180c0c0010080540c0503c107940d00480c8400d01a5400041d03071003031031450401402041c1c403455000ca000e054552045507400880b0083d000104a2135071101c06c0644124800d105840042c8617410004030150100401d880c061081c82d142c10b410309a6540d40c5000c0751b0014059202440500f6242c60389424042154000640c010b2100050040c1440161620f250140d00f14240580c0b1155003000840c60100c80c4185004d10740b41d00050b15001c10200301c3c1002942000403100301140001e01c05080510401000d1400540c2c6801704c00340e01c82c14001d84c420703104580c1800c10030302131800318001500400c01000200380040070011140c48559410240d1140c2d6001152141d006c80002c40a4036010041907025200c101d0350000c0000060342c850701104460b000d09040705860000000c00d203401c1101c0c413000307080f080c0c84181a40c80102038256803103045211561095500d4000020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 887194109 1250 887192859 887192879
    0x50604050f031603140d15032307051c02100f180e06122a030706080c03151807020c0a0609080d1103070c080703030f14030f0702102301 60
    0x4145803952024003058800313078409590201c04200b401400d1001013040d1401703410203100d031640000c0022102900c0c9800c0d41401c01c45030f03007460b1950090f403400641210610500207441401c03200304a5003008440074501100c40150b0020100a4100780100032201060790040314108200080e41e4a0140d1364040d85c4800441030070520074602e161880c01c01144e090700b020420000d4641c2ba1400b200c4c440702c240f150a00180700d95909014104c501848030340304610b03051049100405861074000402e04040d101c11003640710190807150703034007105100c282c1c880d12005081401504102121002483e020300c003c1d40752038201c44601d20402e010346e00864003038028141314003514003041c02403641c3c000c242415607240e1407001ca440310611042c00030f03100082f03000c0c0c544006001241c001c2c00c6032524615010f000d550a6450100038022032554040150009a0031b403503104410000712140c90302c407001c0503410b0084400301d8090850508590f40c20b81040350b90b070f5000c052000e0000c5e061980c0c0e5162111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 887195359 1250 887194109 887194117
    0x409050c0a0c0803071106070203040f0f06080112050106050d08070519030f030f090b0106020d14040b070305090120060601120213050405100906082b0806041104030c03050604050f03 80
    0x60104100302405800304903e00d02456000015060070044082c401403075a1611408031071190060340300090510803082d405801c80000c0040350203000c0461b04200000c1d004180c14000d24140740504d800c59000d1003000d4211000904000d0500c0d5881007003030524400c20380c0700319000ea5003403003005034840d80820106122403026030140d5403840c01a110f250114050a0b68084068101ea29203442c240480c400105280c000c10a54004000c011083d0708040d02c8142d46a004004d07088040c8420024004104c0456410365418500241e50320540c80060b582d1136045034045418008030403400100e44400240c2a001c0c042c00d80b502c5200c000c0e490202026841000000c1d001c1c2c0c0340d000c100308840c3c185a084640c01c50390010340c0b08180da895200e90011521030f5885400c0e240c0c84030202c030300740840f550000141e0440c50028045042c101280203812108080c0080c0d028681e1000480703141d0100001b510f02440c0d010f01c0c00c5000f144d0b02d05050b0f9841c0c0043e901a1380c50300461501e400070102c004212 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 887196609 1250 887195359 887195377
    0x2c15090d1103160b0615190e090403020d0c0c09090507030219052124040b101d1801020705030d0b220b0f04060312140c120d0207080f0409050c 63
    0x2100803c60a99a010040307500500aa5044651046040750701d0281d079024000e100851401085001d400c80801420714041c07500d0755004007010b030b0510020070b90200e1480d000440034280720003041282d25000b03810300c0c2180d020040b5a0326182c3c00c2801c2000201d82c40302101c5c000c6400c00d209510491102c04404054410282e0103906203050745140d640d04040f1040c981440c40964840b0200f030140001440112030740d4210a9035500204010403401241c2903030041c201e042c02d003489900f0b0030102c030740004000782d035607504428903400280c100900ca508101c501098000030742d00d071010b520b011a03481c0c001405442000742403ca103c9441e00700421964007040b0a85205011102c0c07200c03030b8000811264414640100b4410b0014290b61101c1c01000000c610403540142d290859510050441c031034803c034040141c404000c2040e030b500d00011400d85000f1100f80140d035034075074000042e009208101f4020405000815003482d039148400240007203d0090005200302c2c1c0d9a4400c24801748030340764038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 887197859 1250 887196609 887196637
    0xc1203080c030c0415020a1208221104090b010312020a0f02060706060515040306110309070b0708070c12050609010c3c17010902190e0d02030a06021c2c15090d1103 72
    0x82d0001072048650ac40b6105c40c0103800d401c00700684500454141e5804101c20386940a00100400030014030040005541c0d000b880a003840f4040b994452864624000000e88104008103501c3c041c8107440e0b0081c001404010300c0100b20130003080e24200c06420620040d41d4841c40c100003242901056003ca900c2003441700058120a0304200b0b42d10855001180141d0350b0b44c00510440c0000f400d041c22100243c28aa011540c0ca01094070b0301c2807a0540007004600c03240d0410340103100082d00a000c0080c0b5850750001182e1101410b01021a2101c0f000d002c14202d142c1161004683e03034000e030300010740c1e031355107280ca00c1240e0701e440d01e090607881107231084086209103034402150b10340f24006080b441040100007410420054002030f02c3c1c5241c2110944030780e94000307602e40000c5590b0f001488604203101d014454418455075242d041e060301c880945407440b1000c240d0000c201d00313100308503003842030704006900c9040c110480c990302c007842c00b01e80c404198282119484078000006481c01e03211022a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 887199109 1250 887197859 887197891
    0x6090d120e1002072105130b090108011503200c160f0303080606040801092d021309021f020c09250c021309030c0c1203080c030c0415020a1208 63
    0x7801500130341c442d0800b034030503c2c2c480f503003025030100001806400d03041c2640d07465140c103542c42d081d0340d05010300c4c2c0c02120004001c100c0e034a41640c00481d028111b40300ca0360a00003d159010007075000c1d01913804020440d8040c219501c0905984001a22445120078111101a40f421245c1452158180600400f802502c441007000910544415a0044005d003006080070354401c005401d40e406c1c1c43c8101c030036000b1030058100802e60303807038892035840e8101c0441080a41c90f801040c150014400d401364007507150800c0d0010340d01d40c20480e0000007002e9100004421400c80029101c0c00320390306080c40340784800049460040254402c031410216040103030021850800141c983c20600034040780c0101d450310f01c0d004581d1040c403030085054025124007a0f4003100c0e240280c0111500c0e0400050f500c5111301c2500440c2e4440c00a030f0303000c1c41c1e00164031350700d0b16041403800310b9010741d500c82038905808038029100145d02044401d0510b101c0c90000040483c00e0200341e4100c4000c4800312103042c6041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 887200359 1250 887199109 887199133
    0x11060601081b0706111c0f0519020304260c0607030504030f0e0a0f080c04180b010302100e03010606030e010510030210050a0c0c0b040305070602010903050a08041406090d120e 77
    0x4001c080c0c1078030442c0005180384040c3c14004042d0400d48046c1c03200180c010303494010342814003074000768003080b41040245141c540400025402d9002e030b816806a030210004040068807841c903d80b54803882040c12055444e600c000d82598442c90b032400c2d81d8001e00340803418282c001e00845006940c1078903864509224080b04071507007640c10054a0f4400d001d91400122940d00d990b851001d490524003402001030044140000d8400181003655501c44082c07140001c6240c925009055990490345010008142001100d0390125003d8660703241d4a09240090225050343c050004003180c00024443c0390790300b6840c1000c10060784000380d0007500e01451031074103520603402001080c40ba070408091003985a21a40e01c003185a8000b00d00d840300000d424401d008080006000603d440c1c4000d100d4201e85590003010350041c1c1001100b8009584080f4003005030301e45511b80350070149000c40d0382a24103040040e90300c4107070044202c04100d007403005a5480a0301d00070710300020303040c5008024540f40c2c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 887201609 1250 887200359 887200411
    0x110a0f0e090115030b1e0a12150509030c011415010804110402090613090c080f040818010306030629030109020d120203041e0503010f02030906071d040c1106060108 72
    0xd00d03a100406a40700a10705c865039808084500011200404000e00c1040a00f840b41905d880d8000b400c544006d0f0045034002038142d0761050001241060105050303c0310a001c5185000d900c2d580c403034650030000d22501c0300c4d0070041003600c81e42c4c3c610b4403007480d00340c200b0041d100c480e4143c90185c200440d2440c400303201e0503d50010f22800101600c45480d080300300040f81c0071300e1a04c6d004180602e031a00c0da007615003981b110b401c40d0480c0e01102c80702440e06141e07941c0d4003144628212010b00700101a2480c03116802580003500440d0803070310501c82244224040c4e44000c030190210580891030fa00d41c0469802c0520071424000d034003411114160f00103440381d55420312240c80440851004010104040c0000d2607030044408a00c100e02da046410301041509454182e01d051200c50f10520811400c01c50004005401c5035950522851070021840e11034981c2d200880c10301d8026080c07a150202d41a0301025000454070307248150796050310781e40011500b5a0080d1181000700b01d201540c0002c2c004a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 887202859 1250 887201609 887201639
    0x3070f02061309020c0d0e0a031b0b1b0f0313061404030f08180f010903020904020109032f06070302070501051c0501092306220e01110a0f0e0901 64
    0x340381030304200b060b15070861021440d4101d91841034012800c0c0703124250400c5154002606400c240300c4248041c00410b2030304223184409001441c401e50041d009240030030003c00035200c100142541c03610100340ca10b40411003a0711103003070791068262003507078040044155001c2413104002c000342145042c0302140e02e2100c00b01800f18880c0100400800503500500e010302d004e02c6071140686030000d41c280c200854861900707141c041c072000c0c051004240c0c0e02013021800c0c3d0f541212008659207803800122140c02072500018103200c1007035241100d07090080501000803003202c1c8a082e0400016003400000d004000c001000740c0d001036018003c0b0b6014101510798030f0b00c09812001e007800001c01907001d4910a0344900540b940e00e0740036032800710417001e001c517070040c1d15004500d040c1000c902244d0601003100400d50160561300221031849000c0c0c1051214284c500001d1005881e900380021881c0d004003044000b04000300b8240120b03d000381510410780d00000d2a0b2442c0d41e10300214400d151003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 887204109 1250 887202859 887202863
    0x1b051b0708060721020c010b1005030c030117150403020f0c040207080301090c021c050a1101200c150114010207170703030c111e0306090114040809030c062d0c03070f 73
    0xa130403c50285015070600c09004c1031240c240002c01c001e48428144049045148500410001c0400400882404a01c1100e046424126140d01d660175821640e03410329007440c0065600c41301034420701081c1940001d00200f000702081c1900c41040718402080300303d11981c0802002e602c1c0902c010020200d9030740c000601c0b00718a0050390005462104202860340c000881503001c01e4021440c00340b1213920103100d88101c00254000c101682c05c03003600074007800d031140501360843e40008881c0115541404400c540f554a102c1d212003550315615088144159100400e00611519000280003a0400c1c1c0d054501011071010b00040c50568800b180c0c0b50b02050000c5c0c4181c92201e4000038a0b4581d241410342800040240d2a00c1c0003100040509005010305200d01680c1418003001c030b0744500c07001050700301d9032040780180e690780c2520103c2d060040700345c00c49074441d0000ca003a19204d842a40c0700740802105044003078230480b0012070010a8042c18601c8403a680c030031b00989002810340b1541500c0301d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 887205359 1250 887204109 887204147
    0x1d0a0f0f020f0907051206102c040603060b0f0303040f0b210c07060c09050105120612150406050604060b03012d0b0d0e06040f0b0a1b051b07080607 65
    0x160b141c40214150150075a540f8000800001ea0b01400307200400b000c941085c1c0488a0903186082c40d1300007410048804685001240070071070103a00f044110a00c10b0044a0103042072184550740d00f081001803060315895401410407400001e90352a01108860580c1d007104440d840450074200c000486812402101c01040030401101c030060410242052050010b03880450f0f44417010b160410a0b1800303559814180b041e03c81084c0080c1c1e0300801500c0700c001a41600c00940e40d00c410000c0c04c100d4400d585403040b402500c2b07010360900148000b4134822070094078248126240c400c00d1100f02d681c28480c40e81044000d200602152209100e610704900d501c1c004101d03a501210b101c50108034413980700c0501d8500020f01f101d02622180145a00f040100011b4005880d0940707030445541c20b5500c0c01400d111080c1c0000707246a95940c06190b03171888464450202e002c01910141465000140e264801030000c401c101c14801c001501906940c1c0400191020b611801f4061310010007a8145500407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 887206609 1250 887205359 887205379
    0x5010b250606030605160c0b06011805090906071403040f02040b060d050c0901020d110a0204110c03040303200109030e090a140901021207080411061305060d1d0a0f0f02 74
    0x890340e070780200006140543c1340001c0d01c0c1010f00d5060454141e100aa00c20300518506150110b04040740a9074040d00a0030181221034045290702c0e0700070496080302d903100110200b8040003010000d8014413881c0d2035150000c81300d0100000600d5800112001814407a11056107001405c040e0020780c045007000c1d281900700021130014205458003110380c000444004a1661040d41c1d04010250803610b460400c04880708010b5011a11462003000203409251200e100407250002803084030220420391042c2e0340c40b43c1e16807800070f10f040c000c0080040d002c1c24940135107030110700600c034000440742d050f1200d44045080009202c8076040041072415590750f6040c0da014031181c0300408a10a41d106000181c0d02e0a9144100c01050b00c040d0180003040014002c00002540340034040f450080c0031503a0300d85600000401000120040d0000c0360800d0020840b0355094220343c01c144034124401d0340b80391800c00c1c0a5010740e80c40400e0032010f000d54010741e8040300456420042110764600142000d894 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 887207859 1250 887206609 887206613
    0x90c0c110114070816061a09150604030c0f051009050913050c0604061707030b09040f08130312020c060f0d1a040216030f020d081611010c12060905010b25 68
    0x107800c200b17041140001c0700001041007100c2c0b44914038000d1041020040d01a66484c041640810014802411510b4055184142e5542c580a94000315448183d03011019203c40c0d94089001061141d5800b50081038030b91010b840c0112444010341d02c01602d400d000d6a20440344541207644058240e41c103000c1c61200d00d00c0b5032207200040001d00302e982c44031681d0a111030b02030003c080005002c0002c051408201400702e80e602d41c00d9075000354006005000b0455203041c107041920845d069414807100034100002008081c00d080421841a80c0070382d20707a55841c1040c04050311580f404e00c003072420104140c10071614039070702041c0304041542d40500f900d07021401090880c1c0c09407032030450715003a84c0c10b200300301a88441d2004101502c0e10183c8200d1907081000380c8078184c0681403400d030f5280c0210070030082c0e2190040d4140c00420600030703c104a103034a4007500904000c0b01d1311144500b0801d02261030655801064101c8a60040041c9402e041068865004514115170340c2044410141480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 887209109 1250 887207859 887207873
    0x30f1302040f021c050c090904060f0612051e03191103030709051306030201050a080a230919110d1a090304050406090c0801090b0d020301020c07090c0c11011407 71
    0x80b4500c1c981400680d161007480c00000b020b0008044e00001c21306003401c0011a200c0c1c082540c441c00300540b1108003a444900d8008007820450301011101458240000390b54201901104a55801041034461040c419549950140b4480644142c0c0740d004100c100c96854503000240c141c88601c0c900070f102400414021815548280c0d001400190b41d45014401454014560305074000403003030030414245940d002802c14050700c00c0754414082c4070f00015500e081d0b55000f458801e50750124100408103080741344903a4980640b815070152080d10900c110807004003003009402e6420034000d01401581d00100030002030028070885a90300183c40000309400000d00440c002d41c00d00d809140ca4909080510040301d0443e030103101003a00b0440400c44050b003004106065407840180850401d850308045a0b0900700700f44000d4056100281001120360b021400005132854403074280980700c0f0b0078a00300c54a844203000580020056400c0c0b160540c01902e046481a1000d000f040c01c00b00346440e602 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 887210359 1250 887209109 887209121
    0x3071709010506010311040e04060504060209040c02060405281b0f060201060503010b04050c1e090d0606030c0609080d030507021e0303090d1d0402030c0705072309010b030f130204 79
    0x200c016074540c070501401d5a0903008038810308801c07111490400d494148017003182440039101404159440c0701040074080150101c400380c00b0040e01c24007042e41c241c48001d50755a03080710180c410340200100e41d00310012100c80c181d06201d0300101f040c4c00ca0030302d803142519218032801200c00c051f01210700048035900c88010314010b0003503400000341c8924200501d800d445092508074411441c100801410101c110141c03120100305030030400d4144448003802c4954460106010781c00188134400004200701504140141da00c41c00310a0000b613030700e1005558040b180d0048403490340088100c0000544250300c00ca501500c81c0c0b04481c0c0c180f01000c40820115401c210854503500000100600c0301b00401541c00301c040d6518041504c1e88840b00c01090313a9002751600c5110719000408950700c5c44152082c1c82d001034104043c4c66030075a40e0b580000402402c26010701d801c2d0b2a100c25010946032444802e8100e5180f5554245180d840300304088403018000c6c000c8030804107d04040004d40c80c2ea01c10a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 887211609 1250 887210359 887210371
    0x70b0d0e01061a030901060f21150f1508030301150f0e09011503201e1308060702060106030902060a3501061b08070f15050a0203061f090605030717 65
    0x1055803424501740306030940c1d4141e003000003804200d9800b0403040750803540108188284a8061400c00704038540b02500602c04102600c00d2801c10b04c071101c14103015401040f065030760301c02c515512640c07603062607100e010911495000007064001c4102a5024a030f907500510f016180952040f0381c50800140c0107102038000c8840c5c0c268880711014103035014443d804041c00c15000451a046034200380720014840c5051103081c407080d200c2d55900005040b010f03a0624500c41c000c64602c0d40d1501001d950340c920890342000184684000040c24500a204400c10160080c0450b85445803101007a41c14510000c1c6085c00e0b40280c00c03444540300a88035500045401640c0400420f515004c4000d190300c540c46242400589422100d4000590354400c840005521041d403c107800080c0c10482604d42c81960610201810581040b451040c0f82d4000c62040c40d04445480f510040700100f400d035810200e04a10105001d0302082c40b683e40a800650341c8064a450503125480d030821540c10401015206 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 887212859 1250 887211609 887211659
    0x3040e0a02180906030705011d06071a0c0f070b040311030327030903030409050a110d06090c091d250903021816050c07170a02010e03070b0d0e0106 65
    0x20500c00d00d40b407120301d201001e00b01e803001c0303907070401c240003d40b41d08580c0704e82c2e8184402c0b006090f41040610418004462000341500c4d2501d8090501c2d050185a00c0c0c2450040c5688100040f4004400b00a842401c080011402d0038222103a40c1c1c0c141d01d2002400680901892a001c24aa10001c000440c460f41042c080100400141c2c803019002403005a42050b80350020306c4074a6072914002700751000c0700c800d480c01080036216104240c1c003c0051645180f00040009040030803054244c00420440701010010000180c00c01c0b070484000320903014249450b10040408542d04084400f030f00d4210b40102042010b142c0c0c514210f60b0700e0813294000f000420403001080055161a000c001056014914800301c40d00c0e1042d0b00708403c200c90130300719045c0701002c00c03034142c4034604014060107014000d80034402c02d54403961580d514a41014100c0c00100210000c40b401d05010940301e04540440c80380b641000f000904c480c001d040803452585170b035940c941c0005807100c00300a40000d440e1034410307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 887214109 1250 887212859 887212867
    0x11401090902090f090c060306150a0f170c0a0f030f1e0e0105040b06010f0c0f0c090b0a080d0c020d080a052a0c010f03021309151212050c03040e0a02 66
    0x105111401ca40103111115011130f0104102c0c401c04e000c2400c100324582119002c0e580ea0718040024405c41200c06080701d040c0c2d021610b040c19580007243c203a15900c858880d0050040c8070100303002c044100312540341010505105442c5402d004d10b0125811001905001c2820151845003000300e070b0744240c0c41c64a180301e006100680203041c5c85007040001d9004024003030340c5000d841e2514881c10142401341040902c98403070104070310920300c5600d00c03980f115203049460200d003004503c05030280201c01c5950300d032000080a0b4a06004a0021181d840f4050f11604950010581e1004180d08040c0c3e00030b8960b100324000501500000c01102d841504c2c0c0030340340c1d048203d10241c1401c40428141e10b0501c64000701e506c00380005036000000c030007440e19686111847c00110064020442c90820444a504011400c5501504010076403075070416010000c1e9900d2541d9107030400c5900d001340421850b00d000b1700441d8801d0300100f44a4080d80d04480c0390660340c110030001da003811503c400c00300f64007003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 887215359 1250 887214109 887214113
    0x2a030c05101a0a050103020f0301170307050313410a1a04260a080a0c0209070e030d141905040503070305010b130c0f03090302160e0a060905070903140114010909 71
    0x2ca243e0b4050682840e0450520b032410345440400d20040c043e14991000c82c06030404101020821900d001e540f1405403034550075040c400150402d2503000f41904900d2041328842400ca6042c803520841c1a508040d030a820f26003803042c947d050b800039440d600071001600210304600d0b500bc20205e124110881c00f40c2d11480d00b800a03042c890030404010b9060420b012241d803401c80000c00648540c0c10a100607920710125005817038884400a009400041d210100504035070403003248444003509405584407101064011075010f813054450764180481400200880e9041000f5040034030910b0400c40e1909071aa40083e180031800c1e4012103481e034480703000d01014108040c40007020217a0520078800d001d80c0d180f0140c800b076414400c410815650311000760030f05100704541080f40000240c03240e0300c0c1d070329840c01545002088440c6402d07035041100020f4040e000b4800da501c60000c560ba07210318242540c0c0c4041800710480340c000304d00d648a01070810b07010303440d00b42c1c14000c1c102014001130411442c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 887216609 1250 887215359 887215369
    0x106170616020105010812160b090a0501060e060a0611072607060e060423040e0109020f0603132402030c180a050616060905120306012a030c05101a 65
    0x3101d01004690409004000450b000034524864180c0c2c02003113a190b025040000380e0f10703a07041c82c02a20004441050140713141d40401e4240500c1e000794021700120392600d810300184001070752440e41101c1c000030100b0445120708420305030034003880c06490481d030fa90802405020460064122810300114560041000810141004009900700010000c01c0040024440e010318429503a20716682280c48901ca400e080703440100500c0100304001c01c03280104114020100b5100072400303000d110481181c18584441a28418420424051f06940e11941c40300c14501c10070651842d11100d00c52004142d00c410300186100f503030b04c1c0d046544c90743c03156060040e050404c441e0080c004c911590040c440780e140c0c83c0c04c494400030b404001520205c080d1402000900707a07004017a120b03000c2c000c4862030000d84030008601601d4240d9444007545030015002803a070350340c54a00110300c2c0214419400280c021450a040d55005009403816a55144031910903642c60810000b007042c4032820010710381ca04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 887217859 1250 887216609 887216641
    0xd0f05061e01180f020d0209011706030d0305060103021c060f06090312050a020a0506090d08061807080c0f042c0106080420092502030c03160c0519030204180201021506010201061706 80
    0x11715203c0480ae4108400401d8583c09225109000c26458000140499000b601215044880e8000f807040c00490b1000c03140050031240240341114007200f80000d1220301c203401390800c1e0f9401006c81451029070603030a84256100c041c5040c194040c0508000c08104144502c511603110740014200420170000b0083c20b04c40b00400c400d01c07400c0c055139160110103090b049540c0c042040d04000043da1500d54200d42c45001c1e0790382d030b08aa8440010041200d00404428a08085501c1d0844080c610040c49a0054480900903003000070301900c00200070a00140c480340e00b490101d4101603031448060b0200e161400201e0300c0c0203a295004818004600d06840301d0f00b510030041c8090344c1405098031103680c4038480c0556039001521b01c80c0300c1c10300740920300c07140034010540104039185208050300102c201d0340882c80164451744c5090504c04442c1501c00710450410383c140c0c0034061010010070749014070503014101d58115035942401140b000c26004038080b0130783c0b0000040c0346500e8911800059465 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 887219109 1250 887217859 887217887
    0x3f030210020f03070e0f040f140c07051c0306170a030f0503010510080901060815070f051e0d1e02090f0312031b090d0f05061e01180f020d020901 64
    0x8410000d05a01d090400c00f560742100007860141843d503160000076819030803004003a58044d1038840e4000201920f0340c4521088076141c8038291240e503455900c00040c8c003610310090940c0d0061442c0044002821350b08081c000000d00340062070680300c0141c4041044200c65050107a409070660b182499046017204d05101c000385400d40c5550304000105401c01c85090b10002070061207404a9061082074100d0300151000c0c0080b030b4506004010302034101c0d83c003070380e01401017011144851112072080c0200c440d038440d400c406000c0c260107a040d40c00345a1160100000c895070f249004241614000460300070807901a070f025885110090400c400d000e0780343d85080c0300b07500c0200100ea00c40c42c1401030340e81c030a0100c1c8117541102241d0001d40f10310b1240d181a9980072a10000c5030080200301400c2182c00360144045550303a40e40c5da030601d8401e1389070140303d005028000e00100051044420501c1907a215010b01041000c030b240c81d07074001e98008a50095940d50007017200b201a5074041e024220b0704c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 887220359 1250 887219109 887219111
    0x15030f1d07090209120d080103020a1502060f1503370506060607150603050d080a0b0306010302101412150105041208031e04060e0708010603020a3f030210 68
    0x424186610341e80c08141c400d544449801182c40152a5200400d0b020380301d0b001d00a4440020070a04003c0c180e2030240402c80c4241c680710004140107104010b100d1003000c21b60000e001c0e0b515403a400d40c005100081c800c1170105510320030b440399506d0038424044481e48951030048804200c0d44200080551a40c20f0503e140b07003104680c2c040b8500142c441e0700418142d0304a0303545c42c40d40c2403100c0e5508074413002c140c4c1142016000010020300140000c17041c0070956880101d44c075140090f0317080c0c0b2900c0c0c84403940355105c1030050000d45001c0010340c0c0c0c2c9080c60b0400c4000b228021781016140e812030490720040c4040383c2c040004008003040d40c0b00550200b4a04180740c6801c240c22828000301400300504480c1000c80094540c01e11038440b1501c046442c1e40f12585840c1c03501c0d00c8006080308010382401713801020b40014140c00c0c14081e81095079070007403450038000d007414200440d01014089980c0d150440230440800d0070000d1106c081c2c04d0a00000740c00c2000d24609029250160b00e050ba80b40c22 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 887221609 1250 887220359 887220401
    0xf0c010b0906060a0207150306120804030215071128060c0203011401120b0402030102130b0a09050a0b2d0f0d050903040315050601110f010c180b031b0415030f 70
    0x455012551801fa0b90f607040b488500c52a200c1e00c03c03001010703c0d40103c03000d82c900650102c02d2008810203082160b1084030461004034961800d61418040c5d054000c056510041c2c400c0c61074a04208002c503000c0c15400056100c0b469403500c1000fa1007242d01c00004070705410341c0348041d420280948440010368240c21031442d40740841901001107202c0000e0000c4004030041011540d082d0120340d40c441613444000a01511821020401e1303010605071004540c25410016203800d01240d240d04441d0303c1078503c0d0405e145640b00100b01c080301080c1d0f1240079031401c0101c85550f49840a04864a0004107140c0c50310700403849681110406880152683d205010400c0091040d01d80c5100d5000c0c01c002c085982d864503801610510b090740e051110138090044802754820301544101006a140c0da140f241809010300038804400c92030280c1112038508000040c2e040380c1541d043c0c41c48042900010380303000d03030f102e03403400d000c0c000c00040000003621041100c120100030b00540c0c20707002241c024041c03d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 887222859 1250 887221609 887221627
    0x1e0503011b1d04150504150302220e012c0f07050105071109190c03060b07030c0c03080c0d0e01031e05150910030b0714120c0f0c010b090606 62
    0x618040e4000740300401c164050030841d61959140c60350700b0914007403c00d020486140301212108412401203030301035864000c00300c10f2440c141903501c0071203402900244411b201f2202464401103101c2c0e03585c0d0203d80f64004900307101002d200d502101c0b50307c2010a0002142c4101804040111030014001c1d03074040c1c0460400c0001c0400c2c1281103480908000c2c0d9243d856140081d0341c0958a0551688200110200002403114946001003203010704010000019500d8040d000c8039214020320030b5010307003803040303100190103008460380d9140100c03c200d160a0740c9035680da81039404005a01f0458100041c99481290007408841e01c0b2002402d0601c400c41d01179810005a0100c40c4074184d40c0c41c0c84402192000010500440c02c081c0c01902102052604508401c40503810344002c443c5043d04800080005210b5000d9200d9004044502c5282c500400710720550b076000900b0458108408012a00b002d8103260700400d43c0f1840e650020401151000402889010003800540604000c02075118 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 887224109 1250 887222859 887222891
    0x1603060510030246140a030803090c030705010c0f08030c040b072406060507061109030d02150708100e040501020922060f08072328140a120317011e050301 68
    0x2045d15600d503540f040c11040e07a0002000043d060b880030b440c0f104000144180008041081c0e00310403400c1c0d086484055440004541190201c10090104103400e81c401c0e0000b41a50003c54000300031010482c10240c84401d40310507640f0454080b158610601407402500300b00e1541c0c4811650107481c1006aa0b24007040030b015445981c00040046664048148a074008442a80c21160700038040343c082d12000d0758045d54a0264210760740034444103400242d0700f980f15030500c43c132a840003000c20388140e2500e040102c042002500403500c0d55000e10162030303561203140c014070400041c2c1d4041c54032289281c809008444040d000840e0716404c0070360600c1a00ca0005820003103803c008509103505141d880b4100e0b050003c54038880d440388564220000c0c1049200317814401101540418015960390b1403000340000380e000341e584d00265050000c00c2400b802541626805003e8204011000d010480480300e10030241c01c00c1c591515103a424955504101da00100500301c1607000300802c006004600d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 887225359 1250 887224109 887224249
    0x100509150a1d07120501060801050c1c0f020d020301050f01020a0503161410021b060106120507022e0e010203060616020102071a041716030605100302 66
    0xc401500e40c81c8191041c40004082c000b051540b01c140ca4400340c48408202c01c92051082c142c80319070034100c02040b0b4030720602c9414020010000d0719441d0010b54039002040d04e042400500300305945030304603074203e05613000500260010705001a80c0e50304100030003c170189001250f50456129006c00000224000200d4544006025001d043c0008900e81111050002c10742100c9500803a903022100391095000340c102130071036040c8281c00e40c04040015680f000c0900c0380c0c00c00501150603a0401d00000c0c0d0000d60007602c5881519002c0c0084068000311014034041104984081f0b06040c2d4400354a205031010806003000a43c0707035040507400140c036401206021250581c07507540d020116802004400300900078105e0340600242c19a0300d00d40307a03800c10300c2100144004d01222150308040460040c00311515100498081425620360a00609004008100c490804003003c000340c6d4800a614a0100707405000c41d4014051408c0001807600b048500301d580111142108a58076000e1540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 887226609 1250 887225359 887225371
    0x216230601150f020d08190204030503041211011404050105070606050405150307080a02241209070e060603040305031f05150c010b0402030103020934230f0901030906060b03070210050915 82
    0x405401f1403a05100d00901c40c542c0001c140c0d00c00003c0000e01240303e2803101031254001e6400820401900005403881c103402803103250101e0040106204546c002c2010b00600c81c043d500000d074903170b1107801240481d0001daa040054800010300c01004c2d240410000b405403409101524480c0750560100c0c00c15041440c0307030b107580700248941c5407150b034400041e24503001002e62903d0290600c000c2c5580c84802900603607c0407040400002c482d03081c10070840303000741c0d03256482900d113a4a0000900e180803003492542c00e070b04060000043c1c5595003001c0080082c00200d0015a2842c2c2032403800e00b1107601c0b00c0618003550052004102513034400100503400324040f86400368020041c50b034407449400c02c146005000b01c014981c0a01103a00019040c1c02752228a2a1204485a07006030300080c024440041040c61040100c0c807500c0d4803a0300b140203024410840400c07480d448400122642e0021a121070042e806210b903586031f00214000c0c0f41e04200b0850260401001c1a00030101800c402004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 887227859 1250 887226609 887226631
    0xc0d0509060c010603080d150e04110301110415030e19020909030d020304060603020907140d0b190311030615030a02150d050a06090c030216230601150f020d08 70
    0xd0244a03107601044541055034000204820390302e92a0598154100e60b401100840c9031403855a4401d94444030002540c5004406110382c1c0d5075691954505080c514005406540b10018120210b114901a1001c0d142184003035001001e4504010704481c00c00404540c20f0b848010404a18020390b014014540d8041da1600c2055540b03498035499841000c8003641990710010420046c41007a034008010303288210740c141300359117a42e101142e40c84c0f03c0405079408400c2c01c011040402c1c003203a01480c26510302900c0a121040d020340c00c01e400300f040b40d000759041c00c0d9808030300045180031f000259201003c4c444400e01d070200c010110b59100b070440c50003401403284c0291584222160000e907a00301e44001001c1c0140e140c54820030000d0301041c03048501d40c5082510101401e8040d0003911040c1003070310081c040c3c00c031046d00e488150024410301003020a00d503522100d4111014001d407070207480e00d02d440e559000c402060003072200c180e116010085400c6010b802c200180c3c85405260801401c1c01c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 887229109 1250 887227859 887227867
    0x3f0f17041505040c0b0c01142d09010902031e0105070f1d04020708070c0302030c0d170d15030609030215040308160201020910080105270c1c0c0c0b010b0c0d05 70
    0x1d405940404e0a400564880001261026004005401030b80c1488049024040c3c1034580c0da280800f070000103400e508001c0c08510710303000c1d1502d0f8814403070303400b000360400420032001c3e0b81c0219080500800d1301c1100c8039800802182016800d00540d50400712034503003c0c02c15040840700901840a41c8520a191a100d0010601e140d60301e805840c1d8081c0c015a04a075030b40c8003403614200204003480100e001c2c8c040d03409008281d20300881224203041e08030810103d46001e44000c01090703401041d0554800e075070b40300b8003081240001142c0c00030314411074001410441e5400c0c007078500019140b0003040090103000f00800a0ba20900303154200204000e4100e650a982505030f0180c010401126002142c00c2c00700d9211661084945040715000d90703452480c50391541040060482c11954002c0d0f522100c0081615503035401e004020b803400808442801c900604680010b40f591200010006513160850b2414814001c2c225401030086004217407409590450321900c502c45082080d0901c030004c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 887230215 1106 887229109 887229113
    0x309100b0d150908070b090c090709091508030c0709060801021204031b170301030308090d14280309031b3f0f1704150504 54
    0x1400c9a10846a10346420b0100440203418004141c0d40d84212404549102e029008052140103041400d051404c100c1f4680740103411a03070310030790009081c0300c05260007020400c00c03501c03a041c004c40e14565403000c070081081264008030a90000164a84e6100c401141602c10740d002c2c0441003081640703410545080340141d0102d0370302c00070300780042808280100b40580084102103108c0c02400c0040d912a664020f0782c030212241d21001000500400d50000e0100f07030b0021500e00100000903541e0320003401c94005035556480801c0000d09010618104106403c043c2ca107a0307810491140801c03802801050507000903000035181201011364001c25010301250503030002c100014109000320050143c40341e050070245a00804070354016021054041421942550f86a10b680000000c1c0040c080d500324144052a00700200104000510f0052052030703021a010000500c50b0364074 = true := by decide +kernel

theorem cover : BRFrame.Cov 887050359 887230215 := by
  have h0 := BRFrame.cov_init 887050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 887050359 ≤ n) (h2 : n < 887230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
