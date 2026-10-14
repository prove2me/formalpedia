-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2709
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:30:48.343564+00:00
-- url     : https://prove2.me/submissions/a66aa948-b913-465d-879a-e25a4f4b4b2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 487050359 ≤ n < 487230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 487051609 1250 487050359 487050367
    0x9161d060a0807080715050306100806040e0a062a020d08070314070e010e060c07030b070e10050405011202091c050115030804030c080604150b0f1f0906020303010602070902070602 79
    0xa490030f0101002070700404006020711441c10780c000a6030141c8020040801c5014018032085544440c4503241302552031030300c40000c1c0c55070740004008013074003128400700c1e105810842007004080e4228005003040c1480a4801d03003215a001d03060007a0f0f0f81d85000060b001044a0520309004000702a0007036040d14001510b000c042c145055a01020707500c0a0210341034880484030340d0fa01003020000c010040d2a03281c10801d105017295034800d214000181104080c10004030028800c40c07189070100002085a001d2071103010010f055035201c0d00495000503041408581c403100c441c001c48009143c05010079110b126110201a0323044d01142080340e0321b54803003181031500000a41e40380c01950045189035502c610b58a020040e4110039404902c807500309070308210114401d10305050a0a403003c2c00803900349280c50003e03910910044010351300581205240780f80083c20301d0704070b9980402ea10350303a09550301d4640681e502c0c00248198001a0b202d04d4040c0310001c21034001d49141e901c182409414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 487052859 1250 487051609 487051619
    0x1203190c05030f0408031b07084c0f020a090e092a12060c090105030415181115090618060412030206010603090b0103023609161d060a 59
    0x81030303000d50302070b00072948003140c40c071210070ba818503500c1860403070b07c000c1000ba49062211600c641d000843d002040d902442c0006054041020740380350032440742001014007803100c2241040b08c201c0030303030380c4c0700700d85030a0304050000340910850715214081d80700d0107506450191007142e0703a8402081005c1c2c5000303107500d0302d0b86114030301180102c1d00003107203461940030140c0061142c9050a02d1070744030b407503012506014601310710ac421100b00003c00e18001d5075035a0b650074643d40c06a00000303a030b070905160003081042d1302c209400b103031416032180a1030040201b2080412084a00c904400000c12008010300ca82600e000c000400c030340007078410b5804441b19004001171807038100b50f0151520b003840140200c2003507814041c19001d4411801c003046500210b4035030424820301400024000c01400680c800c190580e03e600c2c1c04182911050200390f08000d000c01d4001003400d44807152103108040e0001d084240000034281542c444204c070348490203005104a84c10f10000d0685a0000039880d40422 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 487054109 1250 487052859 487052887
    0xa1e020a050d090c171f02071403160b0c090310051504110301030515010b07030302160204051e0105030d05030c0a180305060f070509010507020f040b13050103021203190c0503 77
    0x100030b070180041029091600410401102c1c40d88034174401504810741d203000004c00807443d2000305000c0d450041e20f1341510310f408656000c180094402078030020030b880503009018a481992548102101c010588412003451007030b010f1032485540c15006240000541d00d40c030760083d68400110310303a44018460600104040303410031000045079640020060003402403c10a0210f151110150f450b020b602d4684803909501814200500701074000501c151114104c0d080081c1c0700d41c000b4800c0100341410000ca4404019248031001040700d0240001100d11b8045a15004c107252902c86a11399a50fa4142c50b10302d90000d0300c160180240015100c1c101c1c8815030180d000765215800030107117400c0c00030009240000007020001040005c0242902c56607000d020b890200368103403451058000164001000b03010101c1d042078100028600c04084d040f203030340205048a0003a56601000c81a041e8a540c6a128075411403800c0b505020344109154402c80e580e009c00760082041d42c0c180950150200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 487055359 1250 487054109 487054121
    0x1306060503010e100503060f100315020706141e04060e03071506090506010c021306150e0f0901050114070f0203030d050a0e06040201091a070f08070b0a1e020a050d 72
    0x1000040000c4010301c0407035042c3c604580c00090854403400076601d42400242d403454001c2c0510b0b0700014100c041000c03924410681c0b006140d010800000c1071820725861002908603a405641c80c60a20381122855100c000e100c900ce40001e0103400002012035079011103501c401b6008032451566440c01c104400020702c09885064071405500f81204900c58038802034039600d40056103c145090184042a81c01c032484d00c400c207505803035107104100c1c0403000300002e001550044050700700c42002d000e03240e98015204030090104031103121844185400b4080034000174040c4501140f01025411540c070f007e08040d0103420b1003030800b8540401158003190940d04110340280901d500d60060081006440c028601d507a03140c900142007a1030660002450000d181c407400c0c040803920302400c01343c6034205013119480c44d00301c020302c0344981c600e1370000141c1e84241d00984a142c50100420008050f0b0b00480000240310a120011403825111030305c02544101001c605000b410000b01603501c006000381 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 487056609 1250 487055359 487055369
    0x70f21020406110601050102100903030b0d151a0f060714100902120a030c02060c010b0d050a1103070b191215150c081e07080301171209030c010e1306 66
    0x158440780b0744140501866107100741c001d0103400c040d0040c02941d80c0026208207201007070704046050812400c080d0000c0448402107038001040000150a00484502c00b60486202620800c07a01c3c40c100355540d4040000c80106500803441074440a5900d0400b001d071081c54003589141a039074680b292140d02d481c210b113003481402511202581d06502d080b000c0048101d0400001c0c0104240607038008044424803907000384520303004942c15000700425404140d8000c405860824a0300080c10070340d6a5440d500411200d2991612003074099040c003262180031254101d4005041400d40207892441c110380d05203480400c1a2043c00c01009200c81c0540700c40d021112840905240c04c199020f040c0e01102d1a60201b4000244e140ca00000c0d10307041240c03196100400044600b201d0440c1c1029648a010005040d41e00e0120012503c52080c002d8845100300510480d08104140240050240181918a581038201d400c000c4d10f9075004440a6400300c1000b81800403a00c1000c40c0941114105c3e080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 487057859 1250 487056609 487056611
    0x2061603022a072120031f060906030b01030303020f2a0d090518040503070204090312050708010b03011503270209010b030f0c1b0a121e08070f21 64
    0x5104002c60050000a0140c420300d1240c0c0000f141c0141110010010050000c04504205450032000141110003141140c0014103882540c0b04d40752a084408002810038a6181d2424100094070086807064004513984018031081c1d42c0c1ca191025002504042c01a002e400c104005070b003541e41e84c0780e542c00e200e224800c402c9100548410140c9180110b01c412000500901da84248600c0d0390f09403648003101a21741f03202e40142c1d41d5180190a500500704025009410042e030f03003040640008607601d0455286104020b903070368030001103481402c01e1213900d001c3e403030030001884000d01c421420741e452541070801050031142d0f074192154510300d01d1205d5a09100e044034a030118a000c140075401440d200010b6801c6051081f000e01c09048081e0160204030070024846203908803a090103a05640b2280546112080300d003008400e88030202c44c00320018000000c420340001d01d4448a1114240d181e540041b141d0303c081094a02d410400310720414000c641d050701d03142700c00c0b506a44120039000070b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 487059109 1250 487057859 487057927
    0x80706060303050301081c0203180a030b040609021008060607062a0504090b010c050304050d330606031505010807020f0322051503041e0b10031103030a0206160302 72
    0x246d2401c04200d0783d0030031180c1c80420a100481d560000913034084400d0141c019500036040000602c0b15403550380002d05441c032100421042c07040301d51100514034002e407441215120050000c8404010880c1d1943d031014080c042c45000c13410390b601983c164801c048203030303605103103a0f641c00718075001c150101f01c002100000d007445480c0080c004d890704130f4020300f002d604c0102e5135600c0030b0f00c03401180909401080d445c54100240509064911600642403204031105c07170259400c4010a141390324189041c0341004000640180b081c803802d4a91040c80412401003810000111050fa90242150003144688400395881e10b9041c00241500014a20303072035824481e280103180c1050290340003a225101011a1141d030384840421694040e600080403415410b10300501030325003141000242c040306145041049402c0c11103044001d9a0140a07002c0341c1c01001c400b01641c1f0f10800403600700680000011420403c0c0d4080511000b0b046401c02600b40650b10340d00d03000b2100f5a0701101c1c1e0340b5200c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 487060359 1250 487059109 487059119
    0x120606030705040e03030a1a0a090605031501050d06200a020a141c080a090606060c15060510140702030d090e07050711221b030506091303050304080706060303050301 73
    0x10500e00101010f0302c05020903110703c81c4a07900c90000614001110341c8800c000307660030300c1c07802040b060a4002480c95251903101d51801c40184542d000d81c038068400c5101020020303000825190485d81c00a241a10380c403400d40e00c082c0500202448030603c1c10040081004040611000d051034148641c001c2001c20020b0030000c8001800319648503041c2c0022208201050a4104100c1900c2550a0808180e107900003000000c00c94072401030103052038801c011800c036030301240c1084068080d4110384c2d640c1422512201c01c550503440b41c2d07a40540315405a042c1070340114480742c04280640e01103428901e00741c011900f050b40d40190b81001032a60441030120780c02c60303505641c0084030303841d205040c80a26030f14030781000100e60082e4410350f114400700000082c218071852407070250842c1072105e84c280000d03e801e81c64201c0340c0c01700440e08010000b12182804d06101e8850105074088a484125070b48007602c11707074006007064503c8442040801c0105402d03016000095201c1ea0343c00382c3c0c4e58508 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 487061609 1250 487060359 487060363
    0x11010507232a0c180f1005011d130501140909011103150303070203011b0906020c0609010309080c01020a0207031208131707060e07140303030f040305030c040512060603 74
    0x2030780d8440c0c0d200e05002204a0440041a003101e201004101c0d903100d80d82048483e182c00e24584085074444401614542d07a43c48400005000c3c941c0c004c245030154a6909084003100194003c5500142c211900c428400c800c00c07110182c0340c04043c1002d038510a18440b00b0f4140c0b0426080808041103d010b101024140941c2c040d44c002c541c40003c220402e9249030b07103401484050462507501c10681105a455038050088511850f8010300030890704003440b4102c15002c0c5118004000f04222070800600d8500204031003e4450b0000c100c1e6141c803007040c0065000300980c602c2550030340414050034400d9882403009040b4480d01d6001011818558540340d0400c004684095080040e00014404c4000c0e5803a0445640e41d0301c2142c20740400340490510005010303540b40903200da424422404030340880400ca14099407a905046180c44010401341540d920050703031444098140440040d010a1140340559040010007401c603290980e07810010700c100040c0e40c1007403015003000040c0310742880e003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 487062859 1250 487061609 487061657
    0xa0c090b060f04062001180b0709093e070204090602040b03070801050a0b0406140f040b12062707080402040b04021803060c03160f020a060509010f06170a15060510050309010c05032511010507 84
    0x8075894481d206900c1d1050cd60750390152040007400b681d240d41c000c0d010030410b6010780b0044c168061045840b45414840109246428403800d40030311418840400c0c0416030f40116010341e58142c651802403140e403000410307150f004941c5555500818400411074202e00001042000855070302444a0305108013000403c00350701841e840081a40241e40104007004176145500c07800c1810890216a541d00101e80902034072102160300c90310029054070360b11340802c44500f150a058080b202181da40c090300c00c2c0d0510041c1c0384400c448400081070032550784500b13421410740708244141c501c1c042c042da4640054650070340c2c0d11040c5944446070f10510303118610810008007040d8821a03074504036030040c2a2105158103000e404a83d503116500b9403002d080d00280001c082c0900308101d9015070910007840d82c2c000b0341e2000c826500780402011464454800e880c000c000c3c480d120361000c1c941202c3c214101d25125554400e028000210074030f07058081c0300d81071190442c0c1c0c940800440c02e400381280423540b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 487064109 1250 487062859 487062941
    0x902030f0a05070906230406050a080708061602060105120307050d0306150f050414011b0302070611070303020c120f10050106110a0c090b060f04062001180b070909 72
    0x201c2d068082200103001003440414203068014502986c0c0e030703000400d018102c1ca400554000c0c845000005156800041c0c000484801030301352802d40d16411618070400c1101149100180e001c0310050007036141040e0034070701e0310035090f089900d0000c03141d40e45402d01d07008005a40201c3c0d52080700304071400707445801a0100c0c00614010f03040400c50030026196026038040c0072401074101d501c01d00d8503400340b1107079101c2c1c000840d819001d440d01d0b4035000307641d54a907004500014101c0c4045240c01200002d040e0f007661340c0740e0040c00b5000c40340c8007809800e1001d09850380d03030b5202e84038105200c03180a103c0010000104040403444d0b604185002d0300c0c1c3c50000e42440156400b001c207034000706e200500007006070390340040e0110b8600c2481b40064414000c0d13554001c1c03c03050001d8009803c5400150f0070b2900c8066800b0310b4000b80100170440c7c00c8802000c0c0002c1e0003603640a410001946c002d0341181c0c009030780c1c02e00740309040c2c030303800c0c000120ba05410079250141a034080c242e401d10010083d44100742 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 487065359 1250 487064109 487064111
    0x1917010b0f012102090109120609030e0618010305270f060105010c03120b0d0b0108010209090c0a212004090e0c01211b0507020909030f070201120902030f0a050709 72
    0x200d401c860f40c1480d60449004407481c1580410600d0441c2e20401d40d003802402643c484160000d05410607000600c0c0050b81200821a911801180ba090130800e485c4101c0c00888500e14040703881005401503c4010541c0000c031109601e42280c4200c00d0903e00e507000c0743c180003030501d020300300b0107103140c03180c1030304141c1c180140d0804403400254410b801c0515600400f41c04250110307110b020680f144040b41000701000c81306000814403001c15405840c0600302120441c2d110340350f101c9003101e903202c0c00350345038000f0f4403c140e0046040710700361203050701070311101c80020b513001220804c0d5a800784494420b000650005030403c41c041041c0a0200044170400252908506400001e029030b80000c00d0791550311111040140483c1c1990700c404901100446203c2d040c4644410060041d809044200d204001490102c0c0d0b20940020948080c1d4a2002040f858441550010f54001c009400c081c800345858a101c070f40103031003c0c000d030340000340311400406060b0b8951520341c0c200501c9401c201c0031340f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 487066609 1250 487065359 487065377
    0x5030409241a07020d08091503070f030b0f01081302091008120909040318080d0507210206061908030a050c1510050d081207050c0114010b0403021917010b0f01 70
    0x20070300403012903c480e81c0c120342041d040700b024600a2030502440c40185d92144484500200c98000f82e80114842d8040c4e5482c29420f4a5074801682164400308205070010075507600c40b403480d4080c00c52150004121429641000308030303400a0140002203c509280c4204000e0800001070100400070303150720303044043c5d410408420040f500c0e0080c010030190420100c8121240e01c5480ca00c1260b018207e11400d6400c2c5e24080c01c1c001e06507604c0300204490005146104103503d13002d060304205001142e5000c2c003181c0c1c440e0401c100764120300207604c1e076000410b00000114010100000c4c2078207901d94075401d8544150882c05802d00042013410b081004803407080042d000000e5a4440940d03000300c405441075820380c10448401d0282501a00304041000184141e1940190103840d49120102c000d0242040c003008090320700d0420b205280d07450070113200c18801031511561038803e004180800030012030f910142000d5009806104045030f954031102c0b041103007082516107403060f00070300b003412031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 487067859 1250 487066609 487066649
    0x21b210c03090d0f080310030b0705130b090f0d260a050412080d0504140717030403080705160f050a052e0e030d030f0b040b0a03030c0503040924 64
    0xc1e8800c03034a02e98410400340c40c02c6401c000d80c500d10380d201d040d04480c0494a9150210042c0320084050100f0743c2e080220300d0005610138402c804450b560f45110800005451519140701065000f2031655580300644100c00041525060121b54225024480c480c901d54070b075140340358010801c03400c0d03c506100200590305500d034102080300c088503001c51308004443c00a0801ca18540164a100d1801d2070415060100b03011024083d100528403400603201c415039900d5040b06400c0344030860b42070780c1e001480708101250740307500508601801001503c170351110444803540390b221240c0101d03034102901041800203040407140705010f40340907a018040b92007c2c20b9028020704015003034200203085072070143c480c10311a9010b1050f10601400321903082101081c00b80c05040e80e4124030b400280381806038525803405004240746000c018144c00301c482e013942c4048484004415081c0c68912003000001440c51f8148201c00640b0500c419080d550444075203241c818035903642c005602842c00d10340c4014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 487069109 1250 487067859 487067863
    0xc0503041211090132180a02030906072a1a01230103020a09120f0c06050a030e060105100507050c0a0308190e1e0a170106030b07090608070e04021b210c 67
    0x18403440000080340c9454045c1c0f000461503d00302c03044201040066050101860780c0360091401459079009a90017540c030aa0226034000c6240300001e810640a0805082e445025543c2000319001c2c070b0903400b200001a0480d5a00d00c42a4403070210656000c2c0c1401508260358110f043e884001d01c0c007549011f4021a0081a0f81100e0050240c5c00c002801c00e00100055004001003041d0311240440c0703640c1c1e4850019105400030746018012900b4035202815929010980e941a0782c8001c100311000100d5100440303150304451800c0340d40b0310904010409540e2284a031400440c030075144560348400d11020240418803200040e800c2c01031a07090b80b2840c2c0ea40b81d41c481001c420030480e500900c640d0b400080d443c0e0030168007810142c11540044034003254103420050a5a0041186a22a07100c801c411220802d00b4418400040c030500003040c071b41c0f0f116180c25958803030020009403e00034030842c00f08000711100841103590303101c1c00d04001441c21340c0318900742054080819506140c8414015070b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 487070359 1250 487069109 487069169
    0xf0109032a1a0106090e0f07050a0219320705060c030d02040b040314030a050f0327010c0f090821040b040e0402040612030509010c05030412110901 65
    0x40d01d1035014021100720740c0c8050200c1c0c40d805412540d0b0409103200480c40c0d40c0c10302d00c01e014080c001100f0101c08142800001401800b074240410a4640d030f95640d18121040e4000e810b25800314012448070694400d03400300c3c901160741c05608411906117038005000031000341c4100346000d910b00708140400e030b0500410700d00101c40b000d82c3c403140d0f501c030182c440906501c5901d0010185a20210340803c1b40300031000074105680c807460320521342000210100b503590290b035003c400003500820541804958050180d500314178842605491101040d00b906401e800710300001d41169507032110319000f03030342c00103003042c03483c2c00340c2000c544640c2422142c90f1507004030307500403031a40507458802004c0d00490040324024510300031255220394403207480e520b0340f203404c2d00c0603407085051000100d41c2c140042e060100160b8580c50301441c000003200107582004011b001551540802c2c00005100070317400e104803105502ca0110a40700f0201c000030007081560617000054159840b01c20b602c0340341011001c2c9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 487071609 1250 487070359 487070387
    0x10b040b1f030e0114160e030307060b0a03080307021b0a0803071b050303030709030c0816090b01020114070509150307091716060c0302190203120a032c0f010903 71
    0x4071003159107801041d0040d060740104024070b0342c80c1030384052160341c1600b103060051200c03000c0a1500040d0490031503591500307130810755154104010060000381c1960000181041c0940030200e0659207840e5040c940d001180c81e1030258008600c81c0000f80c0c4640452450311404643c039218090801340c0103a0b6034054000002c1200e40a065503840c40b42070000074000070100241101d94030300d0700350380c020b1500c86184011034420300c0d405404079031044041381c400580b03808a612003049074540280d5401034200303440c5150555683e548600c51182c1107403070b01d034441e100b42c2c0c5540740c1c1c3d0b4a43c9814803100146002883c4031149060040c05250b1354800008011140210006100c0840100c0102e00b094084941030003a580c200b800000c1c0950003180038030255000e03409403201d011324020489920150714000070340c1a0041286900c02c0d040340790140c2840051440d0000700c80700c1c141a5211035500080c2c0f020380f603c01c0359124601082c0308000384240c0f545020300074070030340e480341d03030701030b00c0304c5027420700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 487072859 1250 487071609 487071649
    0xf0a0b0f07050a0606061e031103041e0f1b0f03020306060402070c0e0f01060f050c0705040e151906120f02010804020d0812060a0501090b04140f1908010b040b 70
    0x7110301485000c00c03090a01c0b54100f03008100c5139599039006400244031948843d40b401c0d10b0248400c01500901c01c806108001540c101d1540d5244e942d1001e000d000960580761700d89080d0715100c081451210b51b509040d2240b102a07007000340181e201454a00d050f40800404c01d001c440c140700507100402e400350428025140940c03030701c2140c9040601205150007550746030892074108582e2900810b9198100c07149512002e03a006282130b811550740c49107944404503071f03003e050b0812881c1040d50003d82101c40b81d0f800c3e90740000fa00c02c2da040002c01c06440d04004602000c1c41120304212500c1408000c00d00200460207500155481c071100c083d501c003000e8140021000000c1c103540b45c0c003403584641039021758880d50b03c000b1003000f07002000007900c0b40c038010411210081002d5005999280580c2c03521b0b0030340c40c10185880429002c5051400380160058555048031303526403200a54180c500c8407615455040c503040c01e05450860343c651251611079400e00700b11410a0721148035034038140450f461 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 487074109 1250 487072859 487072867
    0xc030a03022a03030a0f080109050f070c03050c0109080409050708070c110a05040519110918060d06020c031206061207110a150b09011508060105070303060b0310050f0a0b0f 76
    0xc0700c0d100c148600d542c0e2030341500000880103845a07004e01408000b5540f5203580c05280d0f01c07200c1c1102161400c403880d11000c03404c28007282185009a02c50210503110b85011480d0a150010650035074408070000c813242e800100301030224010030300074182c2c00090b82c41c125000e403415060013000840da000018020201c0107014040c16181c505c8000080c3c180a4418406030400101c11800741d08101d10b081c441610300b914070104100a4400c498499000800c036525001c141c000c09103407501e015021580c041050034210002480b540080c0888850305406583c0750034541a0302d0320050002005244980e1080040305e0310560461600342d0003595a01c1c1c01440d07400300d82140e034035181e09030202500d02901000b25503440c0c11070b40c101700b00da40c0c030688290b14241d984120690712581c4506424004c58040d60008078079500c06d2010f070010030b010345004101d4554071210b00207290300039103040c22038051000040c001c0f81440b640c40c03421940c082c1c80420f9410f140184241c06402213000742880000005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 487075359 1250 487074109 487074163
    0x60509030f030123030118050f060103150b03010618050912090a0303050307170c040923041106040f08100b030d08040b0612010615140a0c150e030d0506030c030a0302 73
    0x40544c501c2200140081024407001c0004002254201d0001c0f1010300c1544509000c0c200041130041c12a540300c02144000d02c07106407450007500c5121004d43e0199620304000448805101002038101c0c0402030000b52401d000d5030445c20000c2c40045c44613112400c00ca01c000c141c451440c080110794051804076142e842d901d808a6a880c0d4041d105540100311000340003a6514040092048885000d03041204841c01410f0150844000c12080e400820020014022401560b89420540d80040100d85890b032164042c6401c5085904580c21a51107056260002d00581c4198160941300320f0091042815a8000a0030044000c200a0100101901103010303520ac18a0030a071150045009104154650662030092010200c1c000f00184070700c010601d444007100e048405400080e03441940b45d90103030f101c1300d04418203c00c0c2e51841659415034a1002c890510240c402402007002c081100e080c0391040610f02041c2c407068501c60307005904003c00003500003400102140405000041d019580 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 487076609 1250 487075359 487075409
    0x609020a05101e0e121b01031a130b030d0206070219231c020c0906040b060d020304150203181218011d062113170309100e0703060509030f0301 63
    0x80482660071a6600c001070741d080c1801b080d41c5500c001d00039403841c18a40e002c001102502c001d90000c99841005980d80001410a08440039070030003030002c0801e188000c0e801203481c1c000e81c4624200140c0204040c0300701e8a905105441c01090072141c01d410040141e10340c28038000e420070b001d41c102c0c00108640400501e007030100500c10741e0a010045151401413030080c0d140c0c003e881c5103601c00d00a18001503803d1625104041c03049401400442c108140e440c0307464000c0d40058030a480d2146841c0c200706101d846400110310485120a00074131012503c07108500e02024160b003a079002c1001d00080854084143d11074958850918182400101c1000700900300451020302d03e420440000301c00b0b00864040c1c03000302c070f2000c00321440740070b580d1003240d105015072024034001c000d407023811a1001904a00b0020350b401c1401c060540d0192001d18218204468080b401c88515070442ca1040080c05050302c039961344085480c0140d454524441c1c0001010f1105000d8003034604002ca2032141e01604c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 487077859 1250 487076609 487076627
    0x1050f10090b040b280903021311070c030b0a050f220206040b09030f070609090207140706030c021603021513030c060206060a080a0302120c190609020a05101e 70
    0x705400c90b641d1151070b5002e0046507440b4001d0043d0440301041c00b8402e10446001203a520301517550394540e100d040d40d0801c100d248000340c440044503110b40501b42c50108990082000c0341c0325298040020780342d40307044400811700a040c007484e00d00e01380410080e40891801158460f034541d004901c610000081c8001851071107002070f40004011402050041c1c4800092400380e070200c0c01ca50941c2101540103581d061180a1003001402509040040c07552540103000040d100e0f51000c1201c00050150074985016680319900194503107130012441d90b014021180d03403060801c502002c1c60305540100e9a0b0719090034603000b522800242880029120040c0840516808440d000b440d1f43d440c41c009545d404161350070761240e1140b000c002149000020000c000650540203400e0b1982e03c02200029500992000302d001d01139185040403d1243c0601c12003094410000094401141d0040c0845981d4030f4109501411000004032385e002d81051580c545024088072092525080c40c00c11100c1c801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 487079109 1250 487077859 487077869
    0x1a0f06090a080a0602220b0403110a090c030501060e0a0f0e040524090c04020c061303090504090305043f030207030f0f1205090a1707050a0e041a01050f1009 69
    0x1074142c1c290400804d40c0017452100118030032501002142030303002112848501c06ca0401c1034080104000042804400c80c01c034420040043c003a0a580d00a0740e400e42d000d50369802c00083d9030304d00500c05c2c0f40e0440c0b032800c0d54a10507600d452200d428014000c840940c0b902403141003100f41c000140810004000b465501c06804454075450301c00c202403114100300c103840d180e100340550390003105039007014402d0b01c80e20004400100225100c402c102c42d603c900d500030035000c03c03000b8100401c9549a600401424034440c0d91181e5580b86003a20303840410044019841801e10038110001902c01c0c0740381c010b50b54519141c0d40c4601d1300d25510b016440c041c52036200a09035003140045505002c1941d0380d00741d07030034001c01c80e5080c0d0f0042002d00300c910384030f0386208076442550120103012081805003840f560145a50459045030740303400c00030f03510b80c00703950002c007000188000300030030001150242e00240a120701403260a504100002d4002e001ea4804280901c0400094064143c1300b0040000140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 487080359 1250 487079109 487079113
    0x302040509032109070801090b01060e031608030c0118050c060d18030306060323010b1309050c0c07080102040b04030809040906050405011d06010f062304181a0f06090a08 75
    0x254182140980c946004c0700c040f4000d000306000081c40381018012440100e40c0511043d180fa0f0810506991016034401c41030340500c84c8500343d42000070840d40e040b000d40441801103440e02e545000b054291072a04c07410300c9040710008040e10010708001520103100b0001c5a03041d44600c0213409040080601e5459072a600f144220380b4030905403d54841001d031340b440c0d5800e005080080d584a40e880080411241030f035201d00004100c6e1026000180917072091313804100d064540e68091b40401d4038410b690386000c444d00010712022032102007000c20300504111009600b050310700480c07110b8500891201600360400094003210039a956400182c00c9503101400308591700305828441d000708441e12252242c00341440e6146004400051240e04840c12075009125660400900b1900300604001031107440c6000d41d00707051212507840c0a0005400e0407202c07032490302c3c1d400600c0c01c20350308142010180e6450200784608640c44680c0da4200d1641c0c2540c807541da40641c40042080303048154070141c5030f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 487081609 1250 487080359 487080397
    0xb1002010b2e2a0b010603050705090a03030f02010f05010e010f0807150806060904140a0e0307020a17070f031212020a050304030c081c0603110102070503030a080603150106181e030204050903 84
    0x132001c02070605907501039408012a0740c40300000d81e01881149800ea0340a50b0f07071801080046c1c8140940b0f90012224070005c02c42d00840311500c800e844080e002140074666040041c040e07020b02e00c0c1c03e00300800500008019040c0b80440382900c030304d145200c00c0c0411904500003034540d20740074103c2e5140c100144c020025890f000008503810b58054651003030700d909040342e0241d8120008150380c451500140102c18040c5040c981c14051503c8030030000d41800341c03000014112500c003030305100550103040030038031044406c0c80c001e0540020708546450680b050240d00741480c1d0101c15654441d40c0360400c08002c1455007050065400382c55000c02c403600d0b1090100c200c00c00d40d0340100d17044a1141e81da0002002030311b001079031034450602406805034802d101c1c0701c6d900d52048810f0390f0414801b4040d5103440d41501048003a0310005d8118901180d0310b46085011244000402e1004214401c04001c80c0101c41030381507012007040c48040c0c0300b55280d01c0801c1d0340c840188220b5214000301c180d03449036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 487082859 1250 487081609 487081613
    0x6061210320a050f06130b0408030a1103030f0c070c170d021006030f031407080a0804050d0c0b070548011401031202010b1002010b2e2a 60
    0x20795402440c040840007800c1640005905125100205440d0000c128200e008400d200380a80341e00419030303010010300101800540f40300d0100007040a4084a00951b50341c2d43d00420251000c4004440c4054942c0308108010b250500e0058407170300066a42c0009640784518200800014410f4100c1c036001c1c800c440d804218041c0000344507044900d10b409440141000c95210b5040b40c10341d20001d05108442101400084d120b040480007070b41480d10725608040c201d44420a90b81c0040118001050001e030500090100810042c000243d2502e811203a031500d41e030380c204c00584050700c0031090140103e10654140d10115540c81e03c0380302c80200101f40174644ca03120441c0000070b0b00050300b40310b04c5151800f1611040c0618a1107454000c1c507000701d41d1030366503103559080c2c60418400c01c556860310441c017569501d035141042c01c01d21794004203080442404002a100b403180000d42c480800e20720641520301c01c40081400c41800342040010143c0344004810100210072985075100b907a0383d00201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 487084109 1250 487082859 487082909
    0xe040615080c030d02011b0305090a060f020403030e1903080a110a050604020a06050a0c02010e06040b03100905161e0207050913030315051c06060b0408100f020306061210 75
    0x80324504504a418000c904e1006074201c921060030150194400780b106150356000c4c3c3c01054001010900300e5540c00900e813100c2d001c4a00c4c0c01802000d05800040400a2503070103414014018421114682d402c500181c08a03066100e0380f100804242008c580b4500700350299070448508003500003600c0e00c2d0f40103403070410b0b180c0d44119402c80c8100441c07034002ca0b04074400c600b9a1540440d9444200c02e114007600107403084810a0f061590050082201141c1461480c2c0914003803400300602e07840042c1410751120907900c0003000303500b11b201280b03030f480d0740c003a80701c4c245142c200110f2271955845800c102c400c030304060040d0403d0fa00001503405001c0c0d1181030680c01c0700302c64000d40d000c01484444080322151010144189a400b0b0f050843c0c2072042585140440d01d00f503c00c1400258183e50303076002089641007640a160540c002205150b0170305c2d070f10b0084e101e5130321204c24114a9403400c0d10008070716015085450006a00301c0b0001615030418680c1d0b5030251000100100c01c131006e0361141c036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 487085359 1250 487084109 487084123
    0x3021b0c042a140403060c0c02041a0616020406080703140d020703030804140c090112020f0d0c0e131707060b15250f0b04020319020603010e04061508 66
    0x41d0145240c01c5018a0305041440000306000400d410302c00404040d080c00c0b6110340e01071034180c0ea062420000000003409900c28401200d8940e01c520030341012500400c42243c01d240710942c40c10b5a4410902c1d1242e98060441e040403481d15041d11000e40d280c00410010003164001600a10a01c4030100602003e403141000c140740d16001c0b110b8003048090220788900440c403006001c26400f5012500240001010390410741208080710206c64101c0300041c000318080e4020141203000340300395070a40c207210079032042c0c011080d40c4c000400503d80c0d440300f260352440d1244980d072500d4240401c88058944d0313600c0e80c4039900840072940812141e80e0000013903000510840c0c10713074a005014200d038103160b16800c100d07590582001d82425030341c180c2c006e07028955856241043d40302a1546001070202c01c40125514000e108080031890a841410300e0038021042541104554802000040e510343e412617040d42c0c0705100c140300684917864444054502c425082e840b03420714040100b1020f0000941d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 487086609 1250 487085359 487085383
    0x3150108060c0a030e0a0c050a15170903070f0c091413020609060d0f2c0d0e012307030e0613051e0904050a06050c0c06150f090c090103050a140f0703021b 68
    0xa0700c1429070700d607001d01d101e2b1061100400410b41100c04031080500c3d4005441d84200e5000507245000f00a0340c41e40c0c040d401d080d000712143c0300f0040040c002701607a881000c81c0b502034044441614200000302465180d0302d110024400d1b0000248a005e9885400c150307030b065201e1007814000820110b81c580d02070710030169150b07141c03810000513001e001842003034680d03c550044060400e442d61108200c41c00d005a0858905100311034072401d002c94000c5401303440c0e0f02c0700d21540c65201c114a1400510802c44603c00b14800c88061080943c088040c1e46c5560132644125071094016a104d03001c44c1c4210b0600b5117469004511000300400d1280c0400c8452401348280c60801c030664401100704902c0c000e100c00d420300c41c3e03c00800100701141c070711010020113074010000c03070007a2003480020b04034200845403080a4038010442d0812960580181d07a04241407100034420325011202c0e2030b0303e0b8100100304440c44139200002c114524002d80c11221717200319002810181614411525944000700014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 487087859 1250 487086609 487086619
    0x12160201150308070b040222050604050604091a2203030b0108091b040e030f130914060d06051f0b2d030c1810080603150108060c0a030e0a0c05 63
    0x9415440402844015680c0c40020f00b070810f080340d10fa0200610005100700d802483d0030388a402c0403065108820381080780c508010900346840b6080c80700382d50020700b284e40202c1c201100c1300c00148110790482c480801d00f00082d80943d4864102d00f081c5140303542001e0071111048551818164183c0080d41400e5080e02e95480c82d44a9a046030364465a4075800e064080c0c000303a03210407615141d0080030124541c541228144825140940c0c01c543c08107072610030050420300100b1000840380105c03840000426100301d21840d009020030049614240d005004036a5440003c2c0041100d003411080c20903005040c200c0aa11a0f28030461a8001413000c2c69542c40d000584030807400e5040d1041c0301505501040c0c0c00c5441e40341d40b0300900c3c0c100044800c040701009140c42c01d00d840c3d902011a28203920f999500c6241010b01c145402e000000340410340032204c94005102400740002ea880c2c10500c2485030b01e50750084450110001d00c01801007510f6809440100c1082c0584d02d0b0391a001d88408a071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 487089109 1250 487087859 487087871
    0x120503090d080904141b0705030f04120209010e0705031306180c08100b030a29040501020306120d020d14090d08030703060b07110d15020a080708130512030c12160201 73
    0x60503001080c04c4441d1240c4200c2d65101c21b00c540d100d8405400e00030300c00e00850782403014034800c40c18547c00603004180c0718030314800c0c41e03010751501c0c1c01c05e1401003071003000c51001801c1c4950003d0091000402c411002c1e29522030340010803105900030420701c440c08003204041415490f121200344081d2013110014801c540425406100e20710403907060050003401031031882090790390205600c0c07404042d001148031501850351210060404148628032400005940745040c00030450500d8511482e80020b500c00c40b010701441da00098440b241c001d45041ca101d0b403440300340e15040380780b08012095401c800d100d080d400030492060b0241d8010001d5813001c0c40502d0f25141d2042a5024003030002d095100c1c0b00080d0007282c10000700b00b030009070140c0d80c0f07505251012140201641d0052100a00298150041000550340000741a070098200034029640340450f0700c030595521840006200c0304900000401c0d0b41881010843e00c02040000202e001454075901550142c1e03000302d0800c0140d400e2134 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 487090359 1250 487089109 487089131
    0x10e060a05090d0c0210030b030d05040f060309082b0908040504061d04110a090612060c111b06091017090604150b01020708101d0c0604120503090d080904 68
    0x200340b4039248103ca03511004903100d113400f004181841a18800c003407582d20606000a0b40b810300c142c1c041d0388005c0c1c0701e040da0340e03241901d1034400b46000d0384034400701480c0a00c464005031003182251940e55048452140340d000400c0120f2100060848582c80d07686003100b0442005501c10192003111800c5808100050350380e01c0b15050320a41d40580c903281c240144c002000500610244840070300c0280464000c0c1e82c4610101017219502d401074603041d000b4419a0042001c01e000b04851451546083d20100014100070365940810324502100452101c4c0c241c186c40d00c0701001d40b80745100c000c1c8200c202054818001c0c025001e6400254046a400300004580c80400104a070180d41d010030380b091483d905004080c0203008400c035140c1107000302100040c0f44c503802c1014a2100d4600f003400105407030810701001c1c0c0c50500c42d000412941001c1504000e5079141030640c0d0498000e8465415401924504142148170b0400201d51010134074007070200f8400c610000e0100318001b40c0b01040384da0000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 487091609 1250 487090359 487090363
    0x2206180506060c030a0f0c0209010306060801050a0e030d09050307080d020406020706020f100c0c050109051c020c0603010e1b030c030402090c1219021b0606150a082205010e060a0509 80
    0x702c0c100c0c940d240d00170800c8840030f51040c0200c00d01c04030f21b4500301e42e00c8140b642c0020810b54081c0d1040c1c4520f501c0c1c3c181803000b41e0081c403810f500090500d5003000383e41c0700111095100d014071203845d082560b940504105105086c021210704960001407030303644041d6048540000e400c1402004014454501e02141c0a800040c00c0407840743c101c001055000c01c0b442b10040540b00c865807071400c001280a0b1040003031800d002d400411032080000d0a2406803003100b98074400641c80c84c003c1194460180034880d500d03003204481c151a80b200c081400e503500e1041d00c030000103141482e010108000800c020001c4075030005580290700c00c645d074205075101e0000d01c56045c084d4001500d55070303012601151011703c1000000c1002c0300b01080c054100b4018150894400807541504c4002c0c1d0058401c000e80b0745444030112068002c007000c0181481100c2038000c202201c01401105c0300c0c8621010040324076510f100d00105140d0040003888038042400c9020344481065511a440a06200100c1c1c688440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 487092859 1250 487091609 487091617
    0xc0303090b180d0c08010e0a0302160b07140a141b010815091b040e040209010f0f060e011e050d060e07120906020d0603080a080c040b0405220618050606 67
    0x8201000c4400020041001007841c01030f501280c0001d0041e01c0080d00713040c280185150520500003a0120402a080283c141060300c1001103088120910510200383d0143c1a44d0030540c22403510710a05003450549441e0036103030a000380c02086103100f48294103400042144104140e1900490b0311030340e5500644000500f40c602003800100c0c0d80550340d40b418a001c14640c401c02ca188048910307014001c03800544d030301030782000c1c02c02140481008190304062502e0f80c014110099682c010a02d800c800350542140e5000780810403202c0440301c100d036803056001000d1101102440302401c50f0240024103140d000716000d4040c0750405000242400d0300c8141c031803040d40507444010484800c098100c00400590303030121005582403042400303518103886a1005075101e035400c81d079111140040500404001841055558406c200a0210780b011005032411a50140c980301203280d200e80740000314200300304090104071718250340010343d212849202510b1a0b045101081142c0750070742401240d110b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 487094109 1250 487092859 487092877
    0x9010b031306180f122a320c0405090c060921060703060810090b010909080c0d08010806090316020d0f140705010306091506110708010608030310060f120f0605030a0c0303090b 77
    0x4207006e010f40201e520000e02c0c10301d10300c1100105001c032a60303040080701e07000d05185440080d40502c40a10b42800c00d8412160080a404014445541c400001480911940d040c2c5406000c214911b02650503224540c0000003034250301344d0f10b05180c00c100040040800344a1050103104210002d9210b01c0c20340315101003aa0046c6a407881603090240420184c2040d500844c1c0134881001030f111110428002a80c0c080f40390342d0303807000340c1d494200450300d0b01401070b058007007030b402c06c100441c00700c1d01c540400c1d2202581640c2d0f03801488403070704108a00d28415440076040701c1407001e10500031000070075035001340c075402d8908004543d100c5480c1d904540080012a00003105810300b07210041c042e1060311005090a03003210380191721f40c04400c1c207554065210348423941c0301106110031f9a020b4902c0d40e000e01114603080095441300c1400030903013034804101128181e03407a07828007580c0d0b52a401200c00f41802508680d80c100031440c10850303265140c07100741c0000d032005802113100a52036040b60543c1c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 487095359 1250 487094109 487094177
    0xf15070b1e28050c0405030f060406140f061c0605090d0f0f0503010b0c19030201020405010806060a1d040e1501080d0206250507020a0b0909010b031306180f12 70
    0x82211219600512000d0b00c130024845042c000001c0d00da5082009a85440028001c1c2030b460900340351890a483d12890b10400086820081241c00610200c50642c03200c4100c0c2c05028072070441c00c0743c40001442c080c0c00340c41e4a09010400801d1400028018400c0e1074660b01e5901c03002c01100211a41c940314902000020760820040101c14a00c00107400103007001c200382c0702c00303101c24104816a0020090b08601503500030504009075a04900211b500001c1034505501c0c1541d03e1310000d003202d903440c1044d4212080c2c1c100307550046d21154070582a0003c40411070740d5001d49440b502c40d20020900c91804544030701c803440d9840600c080340c11405080900300c072641184d03032210002c050310b004001c07032002c0040c14800322016030707220a696002004110039040d511024541030001074038058006c112003000800034050301c203408188075121141c0240b000035100d6031900c9280c1100e420b1034000b40040940c0310829050100c9040158441d20207500c90b02c0150491811812008030300c41410400a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 487096609 1250 487095359 487095421
    0xd020a09051c03080c12070819150b0a0905060d1e02090d170f18030d0c0302060a18080a03020a020609071208071b06050d0b0603060f15070b1e 63
    0x1c4c1c010515550840010041a41041c51001a8001c080011103e07600012001707414400f00d170551900704005050740368800c2c02498000e5507804c1c0d00f5440ca1266140d80c16002402c03001591084044a01500c0000d000035030325003101c0608406082c0c5071099003004401411905000a0140b00f261004500070f0b1414200c00d40b2600c81d088084200b0380b41401c000307000c00c209071110141400a0540c400741c519011030b02c100d91400c0c1454150180c6219080c040c1650b43c0c40c020a4000a4007a8030850004010442e4815a402301c0000c00e0080c4005052480c0807841c0c0d02120303010340191030a00c5090b42110070341c2d91074051842e620300307407840340003100f070000148040440c2c4180d0090014501a000d60840c0708120003288a101d0015030088000810100d00b50040b07a41900aa01801c541110303594110b003080c02c001b443d1900061080c0e4440c01c41c2d0004501000c01c0241924199074205914002501d044228007401026000301c2c462481c40c42070000d01c103503014070b030780340e009404d000410707145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 487097859 1250 487096609 487096613
    0x81005090415020f0c030301090c09082406040b0d0b0a0e0d090515070b150a08010e060606071a0708091501120201080601140f1206060c0d12090204020d020a09051c 72
    0x290b005a42c1d40890600801100c2c20702c0e5006c00c01035009103005400090018290a0000d0a590140c0c0042c0042c1d0020408002d0103000c612103040c1c2465100c840c1c07201500c6101c00038000308540c1081c0c9070440020f041503000d225807118010301c20010000c0074095180301b05100c64a23281c0421114001c50141c480900407030408000c0034040401204600d89400c0207501c80c940c0e0300400b00c40080500d00e0b1a8a2804941050b20400008040240080c001c030100150f0260301c030f0a005003032901506010600105104c4e81e040105020050034440c1c10b00d0341014500244030183c1114010079a110b0b00d0079039416440410300b428102d85007400980b40c02600c3da801141c8a144c0a07000c907042003082150502403002c0180180120300b4034074805540c4c3c04503240083e0460078014031052081c5024003441d41c0a600201d609981c200040c40d28442d80c4540c01401c05c000c0040c800041c0d0444d20104405080550507030080c1542c24194071401c0e1116600c0741000312580e011034004080c81460300c01000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 487099109 1250 487097859 487097861
    0x140105030a02010f1b06060803030717060f36010305010b0105070c06030b0d140c0301050f0903030606130b0a090503010506100e0f060705010f02040e010609081203070e10081005090415 81
    0x2021141c00241600c83c0b01031b4854400743c1d0303220b030012801c07a0000014440d1090f0803071000d880114040f007240e040c40c500500000c00070070302d0700710300380c00b5490b407198505c01200346422181c40c840f028000ca0101042031440300c00c40b22024041190032f5071811848151660050b025a000070b640034485020700d41c14240100c0c0034000e60b0740c079650050001c0352144005034900c21441140d0b21a0030003480b600507070804150a445003d000c999551050f0803d0001400c0040116907000e030741590032642c6d601040c01413003c11121170f801600d0b80d403004a01e80a91f2580858800100c80d4210000c2c01551140c00410031400c410785c403210003041501c40200c02d1400c041c0b902d00084940140424100881a00d400c0d00f9602235070740200c451540001c044c0a0b40030310a6940e409010580741903800c05040000169075885069a421400e081c04030014650700c0c0700700c14013a410034010b41040c41c1100d14580207801e203082503601c034100000f4043c020510703081280c02a40b0942d00160140311801c801d0704190 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 487100359 1250 487099109 487099127
    0x12030e1009050115090c0e120a0308090a141f0b0f0f2b05010c090e0f13080706091202010c0e040b040b0612010303020d080603030720040e01140105030a02010f 70
    0x4445540f184c1c5525400c51080e01504014404c00402091524912400a1030a20b004034800d00c111030700b814a6940740c2d000140c5100080d41070810741d02c40d480310102e003494000d60803401442c006055a032605014804210880c00340443d041c15000b1201e01411751040c0c1e6280b82195030005803d0640c0034079460191700300b00e88054040c14070762030628200c00c42e1181d211a608020300c1d4581c07080320082001824800c0c83c10b45a12071800c0c9281c603007400b0401e103c080300a00800c18101c2150b0102d500000000e10b0854000e82c890070304c0743c1c0e41d5007514000c0c01a100e50303070781560480b9031407a401c440140103000b41e03030180d51281c2e03070300f2440b244010401000707001c175140c1250007507a0740c2ca00d400b980e01c41c08002d000d00c1410011200c2e0700e40c074616000f4507000c4400344c42e504001201c410301890b5140081030307a001690150b401002c900842141202c51a20b0201c02c650060400d0081880b495040d48107800070100784036109240d80e01e800a15903180e110020007070000320100804a4101e02c65180c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 487101609 1250 487100359 487100363
    0xe0d200a08070902030420150c0718050f090f1504060f050106020307060f060e010509040201030905060c250203120c030d0903120c0801180902062512030e1009 70
    0x3118419107818200c0c0c07a150164000b9103015500205000900c201603003000d04180d000d000403039104180501040c5100c0f11440314200341600030070007060b900d40c203108403000740046030411503180305e0000706040640026260307460114110702c0070030700398000411103588030286c050040120041008510007400e1000f007041c1c1d0b0003680c0301070010740c0c0455401402c1c02010968011a100c00d1a4106401100c8942c6000080302d4a0310a04100306014058020b044071400c5459440c203581780d00060300a01314000004055000c2c0340e08001000c082e001c0030b0b0065194660001d441c690224005856104a5a00195169002940c109002c44004004140e80403490050302d042000b14800702c8191803030910202d000c03d0400c43c005801c02540d00c19842002c20900d4116006d51400182040d9104140451502c480d00d80b0154405d540310a4219103201c0c58400d441444084005010b40102c0c6581004444c0071000c4018204124868002c0b1440b602080019000440724810000000c150421003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 487102859 1250 487101609 487101619
    0x13111606230601090b030106092606190e0a0f060e0708031314030105130204230412021c092106020c0c01080606040b040b090a240e0d20 60
    0x41c08031040a600740040d480d09844090304030a09040b00050106035098115101c0d4480c10303c0100308455000035288100c036030103c4c500c14000300a64031000c42940c00300402040b44549414414180c0b40800d100740c480f1600d800401800a4800085456103aa8100940000818504007000c1030083d07100d021301c001c1101c2199446650b4605e16811a004501090461117560100300b00c9040314174121070a41c10114003c21551030301c010828280d81c0c180344083e0007180d4032248604021031502d480b030703c100c000c0d001e11502842c040c903100c052400d50b0510f850043c0121005490b55030000d00e0015003e401035102d0038080703423f0410b003881580c035880c94010881e0385014040042501c42c4020946a14124050008490381600250503134401070b081e41e004010400080040b010030000303a9080d2880c46800c546e8030161800094501e00041d0403002d240c45000c00c0c41d25040e00318030001c2d03400010b1f946510091061520410070a01c911000c0908600701400107000a804070b00c486114046000b40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 487104109 1250 487102859 487102871
    0xd08070b090309120c1003060303021011040f092310180207022709190308090c030d0c051b100309030c050d17010806040302070b1c0f02040513111606 66
    0x3030380440219844e0b0115041340d0702c81805800e081c0c828401190060801784201d91079582c00030b69401022450b048210b40d00c03100c603885655500101c6000340300a03410700c0000384c0c42e1200e440c010034043c1442410009150703180361204208009440c807070b038003602c0350881103841c0204c202d031f000d03e640e050303c98650b50801c4a44010ba44075901c061000110340714805941c071150805100504015180100070760018541c3e260f800705151860410303d90600d010b4000340c0740c80844a1900207600800b0754103002da89026485107601c0b50910131020f000c1c6080300e0327500140e07564000d19840d10807810340c0c10458020b41c1c20840382c0a030708140002886480c0030550303540b190f11058208507030012004d00081c3c0d11008590800d60500180c7c0c0508079820151046051981d800384d1364000911611a15a4021070290161201aa041707000880b0012051003094207041d03002c002076105004180c8102c1d000c1000031324540051090081129200080c00e103040e0001221140c40c0c40314004c110380c25501e0354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 487105359 1250 487104109 487104127
    0x60a020120041403010b03031830060109090812091608010e0f1501120215030403030f05162a02040e030301090c050c060f042a05010306050d08070b0903 67
    0x6000c0e010800d0800701c0c0d407681d0810b500c40c2c0ca0035411850311403090b030402d100000349541c040110b03500c14050201000d4a0109400441c508448103e4940c6118240640c0e08026880c682c03000b1000140040640d08a0b070380321907a0204440c0290ba000e8a502000d0140a42e154031103001c040c0c00c0604c03541211755181c0000700301c498030321035a0003140e4965160051400e03008420080799235610080e102518001c0b860104243d0146070500c00d0504400d0f00d841c0110654540054028541808034039096403403505050180c0a0050248a81c2e0309a00d860300003140c4600450034504521050f954010017502e10704500c10645c40e007020b0b0380c002036184210010050391340707200301540101d060340070755140c0d0302d001124012101c440a141040c01010000c0c80b011402c0424510350148031862001455180c90804110764095a5048405040b2400e1f51408a11442d910703682100c5c82640c05108207500c590500540320010500203011100130f00184000401e82049958884d031000120707130600b4050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 487106609 1250 487105359 487105391
    0x5041505070e0f0406050105070609030516030f1803020d120201110d0905010b0a1203050a021f051b0c030a0e12060c071103060403050405060d06030b1e01080c090105060a0201 77
    0x20345a010208504640d0b4040a041001e2924194502120100300691920002803e584601d0000902e0181d5a408403c2010b001d8000d503900708815132102800c40403e40b0b4050044500c85801001281c030388011408032400a108201c240c0b42d014040c0c02c503c0020b692034104070721610050f1400d554075140030100146101000e00005008080b01003951003850a111303013120000142e150081d01044d5040c4007450500c4c40802c02294545441c641d80e41c0c15100482c107003074200941b0403a80c0a0f4002c2d981c612100d503001180a1320f011b410750208540010806855842540c2c451451a0414088900218000d0340502c158040260842c281002e1104600c1c0c10280110380400d21014081140c0d000c0c0254000c4a0300c0840c2c041c0c0050000b405c1c1518090158000d81c482c45100e03400000703810f11417a070990051801103622150700301c0282482d00050115415600c5245910000140000b85c912000164096212005403030100d41d80d0800c1c00344032003588414850780a641d03c804640c0e03011100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 487107859 1250 487106609 487106611
    0xd15030b0910140103030e01050a0912210206040c091a060429040506070f140a03020706030c180e0c0c0706030c030c05090109140d0203060a05040b01061e0305041505 73
    0x201c0c00141480081c00c00c0604110380601024601e41c002c0c61005000007600b1000710882d61100742080c0c2e4a0340c0b42c0d1002100d54100b20742008646030b02c10481e920800081101001111302120f07010a01482518001c07a0340d0502142d01901041a04030304100c422001d85c03100140d4942510901030304201e81e0702003105603001d5403014036510f5424100000b0804050410880565582c003a40d107400d06d84000104140560000038154404c20f081c030f4030421007420441400b629810007550204070300340c240652602042d20482010a081c000c07100300070343c800d115603680c6c120b04100304c02080e41000003114401d10014040703c150101000041001c03842044600c0081440317643c0481d00e10218480141034802d43c80c43c050600c00240084945603805c00e00c0d94095030a128001121514284009540300408860194150090405014040006401240c451350040c0054040d69994101c125882a50b040c1c00c200860100945410658440e80100b42c005000d001c1d50190300c5040701d0303081d0803110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 487109109 1250 487107859 487107871
    0x302120a0201020c01090f0317070614040b0a0b090a0e1204140a05120c09070e040204080601051905030303160c0c061e03020301081009020d050105240a0b0d15030b 72
    0x100800d0548110740e030400c0303180030f81c19081c0b13452012249001010a03101c4858000201000950171102c0c0351800c4142c02d0f2145d0b9a08110184607200411503003654240083d01c0948030000c0000000301c501803113014001c4908406850030120340e590015000080800d001021603c0c021800e01546506454000d440904003117000301084204160421a1b480c089a1016001d01854545d000303400601080440f0b1000b41640c0b800c60681d82c64204984603101e10014542c45480401c020510190000c2c2c0e050584505031118112914042c1103502c4500ca50311441e030b815801000003424480c0604e151b0b2265850b01d0030515141c1c419640c0d00d41c1c0049298104000181140c06d030340c01401d000e600311031103011050504500c4c1d541030032506501d41126091036010152100060030854594468041d00203800c000208642c1c1048075030100700c2141c500040c4620300321101d094080d8900600d096003240c000d80042417609080c007510794050300784407654025103080c110000021a8000e480948038134 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 487110359 1250 487109109 487109113
    0x5010801060909183c0f02010c0f02091503011d07060f0e03010c0323010609060e06120c0307020f0102030f07031a030f01020307030e0f06010306020f1b0703140a0c0b13030212 77
    0x3d200d051400000407100d9442c0044461118501800b09a90072040001b0b04c0d020301c2d05214071805410100e41d080c10450300250030070500c0080102103410703d000c900040b03c0032002070264040c1e9510024080003c000c3c1c0d140d030742d0041c00080240381e000e0800314541d02c1050904030000155440024212000b00c40f50304e011a890b04078403028403148503601e900e004d00e81002c140c65541004d4006064110364011907003800a00c41000941d59203403403d40e00300c0d502e401d20100880c917108103001140d0300f050f90084058412a110401c0c45101070083c0da10620170480030101d5990b50700c034202c001c1d005001e840800800054190541510207100d0403032101d030488000740c0d881c1005a00113049552200e520110368000454000c03901c5008030b10319045a4000e1405a1241320340151000c4c280f150242c1e41c800c0d000f01c07407080c1e03801001c0071511504490145e03201010400752a00c0e100c0c2c440b6080c207001042201891418442c0903200e20287c42c00c1400c090f519006543c4990102e0303032445110320b41e00ea2a07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 487111609 1250 487110359 487110413
    0x220306090809041415040c030212090a0b1e0a020d0609020d06030b06100507020d140706020607141c0e010b151e070b040f1b120308010501080106090918 67
    0x107420f042c066203210300750702402c01c01c503490704806403100f41e801050500d103d25103c4140248040c840d40689158038450044d00300b8034100300a43c15030780c0740306060440710b003840030000860b800c0c5035100c540242084c0c2c400444c0720b40c2c0c0d9584030000a500c1211200790040d0b5078000811411194030103000d81d1060701ca000690907085003400d801c11b1000801551044072002103410a03d94000151100107606840d4009440352074540449180a500492401c910410b1000590075a002a020740509807036115088c2c0000082c1d80350704940f190b10041d84d008124200380a038582000e030300c400611180400006246100040000d08203401c00c2078141c019034002c250320490b034404840d0251a03156140c4868545800c9a9800c20f400704024405403900d05000c1303420701444115100302041d01c1c8061188982280c81e0444a00710080d45442600011400800484c5035400341d8643d40c140d400036254001d080d0302d8103072600041c00f400100146011707094420500041d0804143d001050364002c440320700c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 487112859 1250 487111609 487111627
    0x5240d171b0f0a03050904090f0f1506050915040f06061d0907020d200303040f060b0a08031903020409050a270201080f1302090f09070b07082203060908 67
    0x40e003900e0100c0d00301c1074202ca180c0c0140508001880d811159040c20003a8a480e9100d001400800d08058003a2608102d41c920400300450603050521251090307240403242d1070303405103180c210340300345c06460742140303004001c0364000d0048034407403000707100003000492088050200f5109881c03003540802c0118944000c200e003070380110b845082c0b2280702a0740c00a840d10380303000d0084d507401c4201d10310b9060010402000c0c508841d801c640200003542101201c0c1e4909140c5020307401c0c3c0201c1042900c01d645800c900e81514500003401108880b2040c005505200c50450070139129a004503024043c50b500f0400000e1041480c092284913003000c80000a200b6840403241c4496410109250103c645881e2100c0c0180e030850581a000b0402c250b09101c0c503560424810300b10144c20b00c01030752054803902008100161003114610541201d820740310309c61b030b40340010302d850b0040000003070060909104210b00c51541e9842014481c04d0094111840d5550ba240d88044941001c0c0c01e0726407210014403054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 487114109 1250 487112859 487112887
    0xc02070801020f0f030c07050d080f0c0304030e0f01032405090916180608102903060a0216020a080a05070b0405101103130b090f0405240d17 62
    0xc1011500030740c5020038030007045a0520803006440101500071002c0307103000440e81c080d19401c40d4440126203102e465150b02504030001200c04240c400000c6001440c0c400f808420b4a010310b078180c944401c501840c00410407690529030032103042507a501030124003a08130f0403003000048826507138a084c550070030341130003515040107204403116030084460b18070021640294038111800f80ca0007400c01400c100c2110050b01d0a40c1c03180c0d0507803081c22482d01d607000241d40041c19421003029400400d10040c00245502130721500805c1d07240d0000c0f40010013000c000e4000b060207034414864410f00d520300c1d50001d8050b4240d500803207002d50000d41500100042080944060300c0d0581030b1b42d042a10f85030008003000ca0f04400c003000c200220315900c1c9203c50800c25103030b0100381d4000c51030b1403980301c2060802d182c114840492103030868030200303075441c01c00c0d00c00c250103505014a0700150303500a41c06641c0701a0007807841500480090808408103000300c03425600d075440719001c1c645d55440710fa400b00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 487115359 1250 487114109 487114123
    0x15081f1d0a02030402090c07030c080a031b09080304060305090309120d0905041b0c03020f030d09020f0d020d0f140d0504060816020303160c0602180312070519061503060c02 76
    0x20740d582d10410502c80581e8481418035800302d01105429070f504d80301d01e411030b02607809003002802600041001c01c506901034224a604503149403c00ca02e580e020392044890360407610a1803290b40080000784402407280c0c100542c04601401181e01e0001c68001003040d03252405200001c642000418207000d0f80e02040b11401040101c5040c0720243e5641180c250301510010010248801d000300c42c41094001c0c8413807020a056001a2510362004c505014050950f072041248101c421f9113003100207140100410f003041e0b401030401615074205a5444550400600007030307503261600d02d01403100000810406503655119603855484504d0318602504540d006412181d01c0130390b0700417042507158000142c070f51112443d80703020301c400c0822000340e401c40401e10010740381d14000a401a000307182450884034401060b8100c6111180b200304000940c06054001402e54011282c0100300035083d01149121501644000031024415041080c1c0b420f01940200c6030184c442c5080d010036030f010b02001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 487116609 1250 487115359 487115371
    0xc0c01091703090d050f0a03051e0408122503031a04090b06190e090109050f0a17070201051b060609072607050403080d0501051915081f1d 61
    0x4040c0745041503505035203900030014441d0113009400c03500014000d0800400300c460104001b51100e1110364200104950b00144500d06040030b1b042c90440c0c41940340080b035080368042400391100000403205030b1035a80c89403101000440d80016101540c805410500c801544039441c00140200380d00305100f60ba001441034944607628101d080c9010130f0500320364680c041021502120a05403562030841704d500b441d080418000d00d40020401039400c15072103510b07014016412503030400c001d08c402c40e95802042d000180300c280c01c0710101100701d10500281c038401d48141003003420701c20300c0c241e01104280050800c0d25107900ca030301806024285000180d40107410f0740362200031500403c44000220505040ba90000c2d8065800511520321407020380b8003450b404441150344105820304039015100c20f008540c03007070242c10100c0078103001200950088401c41d03000000207121400c0141c81025008295904549180c0204104002000c0b0301714003400d100c10b00b81010a01c80079054038100002050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 487117859 1250 487116609 487116629
    0x703140f100506181512010f06121a2a0909041a09012d0b03032116090b091f02030706060b1201050907050d05180c03010510090f0902060c0c0109 64
    0x24005104035840140210344001e640c0c06c1b45815401c80000e0040003460100c66100d03107410300100d807086400b86002d078402d015420700010225030340911107074454280d0b40c480c543d03000043d25262225085100b62024422500e1031414800600b0100300031860849003144c0d011402a120032611541c02034aa4000e0340580007084003110328000e082e200c00b82039100058403209544d07031020310301080d0031028101a025090700d0300c4010b801c500030001240280940504031803580011079608003140e0003402203203156680c2c0039080c80c1107140d07210f980c412505d03950050703005076003510402403c440b04151150664000c0d035507090b0030b0400f9002c803002500500c5084004200c46902003480b4207806055440498a1171555100e0b25801e851030b1080d10403a1000344c0c01c003401c0188100100d4003400803c50024103803070b0040010b00402d422240704072945032100c004450140481d15066100080300110004d000442c101550002001d80d0002c0d00707000c000b42e21100c8500d203107583c4004a20001e00014003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 487119109 1250 487117859 487117861
    0x30f110607020d05072108060a080606090a0507031b02060a060e010317032a07111c11030a20010912030206060105070602120a0e0f0705030703140f10050618 69
    0x4030003503c5200d80f50740d15082050100d800b40c280100c030a20007882103054408806150603a0401400340c5d00200d55a520440040c3c000242c94030002c0b500301d00c01d000080c0004031070b82d01c1010340c100912015040074201641e601c0c8180d601c2e201c0d01c04403003000301079800070845890582c850400f50340d810341001084807071440042000801021341c05010071440755106461340e503402c6507101c403001c840c6221000900385441e80c0c0c45038641c0708011b1402d640100c414205c1d0384036130b2040c404001f007585280207030035121800c403101144061025000b00032005040e240300340e1454643c8802e0003090550040041b030661048011503030041c020f0380007000c41c0d110421000c132244d200607444402c010040c6062150004000c420091550b04030798400d461481c074900c103030406030040401046d0460f00c1b2800740c07045450f0030404240005a4404480000f0003c180d018250b1b80c4003400705151f51650b49a91040032030320402940c040c07101d0303005145141d40004042c541031040040045203c90b400800c2d410200c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 487120359 1250 487119109 487119121
    0x140705011814240a1b0c0203070905010e15031c02010209090702070614030901110409020c160b07030509040e0601030b16031b030e0a060c021f0507050306090901020c0a030f1106 78
    0xc18008480c1180340000c40443c0e503911405005000080701c17410041002191000110740c00400c0e00211500070713400c5680c03840e15000e20341c0c2200d0080c0141c0030303007854440015140e50032200c000c0c140c0c000e025050394441481b100030500d80c070300b00c0c4074203c000d40d4011030000118201055405c1c4e00070043e10080c401e943c1351401c0640203510301070001003412400400540a0b2200f500f2007001c0d141d0400e845682ca039076138039045009402c50401048a03006005402c0803400c600c020b604155200700b5210341c9400010382e41550964803040030b05030803a460f01c07030100d00d80344203002d014025030041c1c5441400c2e1910308002c2104c526685000020b06103000c0d21040c114079501724070400d035000350800040f110720403801346280c0700311220020000e41c10007004401807030340481d51152001042850307900313800000045905032402190700c24001001070000030450303d4500340031034004003c8800103203020300121006042030034007002075002c0b401039210741c012035034040864002e10110754040d007405d041c46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 487121609 1250 487120359 487120393
    0x5180409081606060308070f150605030c06090301090f0c060906021c0309030215090c01020d021c080402130f0b1e0a050f0a0801020c0106150c05070303140705011814 73
    0x8024402d94014001e00c80c5020442141c0c41180910781081030079072900410714106021050124003110203150104c4e82c4105410940500c7c41940d2005000c0c1a1010302502401040d8009582880c5d140d9210300c002e8022443c071511341440240910b00c003036a89030030804040c040185680c840011503104103441c8028450303a0411845001a502d800b10b80349250b82003c03450305070380004800d440100c039806c0c455410340002d105a10300c0002e8096400b200503d00040c0d8072a402484030400c8030101403003a048251154003941d91051004200452101d2041c2c00c07a0100c2d071711040071402c3ea0f942c0d0800c3e00900d10b81084025000d0005c855001c1890118001041e01143e0510402e07006080303417080702240d40d841c851200017506119008548a0102c11000c60203024584181101240b10045c05981c04d03108000c00c110051b04000180300c40e03844c503501200c109408070710002e01000d00b4092031000901c00e0040740200700185140c4442e44086040480d214008001000032550001039410400803030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 487122859 1250 487121609 487121617
    0x706020403050d0503250e06030f010603150602030301170a0c06021005010e0402132d0510060221070c0e0f1b0a020a0b0c070507033504290a0518040908 67
    0xb80c2118141b190303144500544011b07841144245d03100c01d001c000c1184100030340c21018100d41c121395013032010090900c0e150021000ca8054140141c1003040140305500c8030307041069051394603500304c40200801d41c44041c0c01d9035007a00810010707040401c80c0301030350045000d618098080c00303080c0c0e034403070a241d8001604e110343d5031510b40c040e81e2101941d0004000201800d80b03640101008614903000303210359000240350454009041001c13070075003c00d880f0b10000b4108052014048000ca00344221240c48519410142080354040c24407100480c0c0303071865000e40c43c002c0d41c60014035822410005007d00003405c0c5416450a007010500a540300c0c075a0000b10259402c2c1c12030a500100e44814000e00300c00d208403180039080e4803070702c5000800c112000340b003030052800d030941c0e091045000000c180c6030100b062004c0326945000780002e20003030440e489000c0c0c080b001c100502000803001c400b40449a0041102d49022030710105030f0100400315045402000d0100320b5041001001503564212a402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 487124109 1250 487122859 487122901
    0x90f12030c1502030108030a35090705060f04080d02010e0d0e0604080d090e0a05090a020f060d0f1a030304120305130e01080a030e01020a030c02010f02030f0706020403050d0503 78
    0x900000600050300c0c00840d010341c45090a554030746c0c5502d01555280c1c8420009400101c078040c001003540c00c0c0c00060040303220b07006000c6480f41c24440f80380000d0000900000c03d50b0285d010002210355604008082079480360702101d454030703d004600360820f843c0300100c50641e414004000c442060200d150110340000d800d025801c45d8041011a0342c5003d290000c510521400c0c0382d2450755034003d41b01904540c0640c820306403983d210200481038030402d0301c0341001980410100001490b180c40c8444c10868084c0095040102c592810070503201021002c141c000e0390b0f6003544d814010f00140a81c11080d054000b5468140740480b409148591080080d040040120b20b001c07200c0c003d60755500c01410a00d224100c6941c64080e6244c46044010f070440214090b040011850b50010031a00c080c0c5806807a0a0490075003600150350405c9100091000c6000c100581820307821404040d080190003108010388443c103504d000361502d503440a0311010300c0003c1c010481d02c400c4014008211078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 487125359 1250 487124109 487124117
    0xe01150207061d060d090b06061c09111e01020c0d0b010504020703030603020306010816050a0e04110a05120a051e03041403190303090213020c03090108090f0307080703090f1203 78
    0x3c41220302c045980668910100c0d40040c001441844c04041134100c844824020007000745a501c446040202034415034282c01ca4601060301a076009044a40c8442d1006000c0d00f42c0a6000d81c100c40081c2045e401034090408483c0c0c02c0e0b1085942d560b0401240307001000a0f10903c1d81d030290384d1180702603000c0500c501441180c0010301d14007094843d0700a4801075034081c084079aa03584070040da0303458406035082c2d514002e0344044001801c0c5011103041c0e044812204100c0d920f0b807550340312242c4528a00c800079401a4a4131000103103610b8120f00e003100018410003504100c070440c6806e0703040c2103103842020b008596046589484480c084105c3d0102c40c074200074084d00845a0300424240041c9868000700c0c810450080020b05270160080c00300c4c103108403070740700320a030081c0c0e0104228042e8414580581e40140044c003180d50140c02c0c119002100c0f9411a02c1100710101d03201c1c55a0320299040355985000301c1c0300010550000b014034050410207117200d4007242031407084030940807a610054104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 487126609 1250 487125359 487125377
    0x228210e120a050a03050d1104030305030105041d030f0409050f10060c03020115090203060102010b0103201b0a0609140601030b190e0a21030221041e0c0e0115020706 73
    0x144808010b41c0100992010a135604010b15003400303802d6800c05074844001c40e081a084c801c14601c4e20003114160781d4191100e0381180d00380020b10000380400c1d030741240031b021400b180c4203803240c01700094880084000049a81d460400e17100005170760010f0040185408100306204011040a00d00c0b42034400924200807108180d08040b405022040c50381c7c1d4014401c00400301d4a88070503001035100b000280c0080c03141c0040c0c580110100d0b0004094a40a24001c0c840c100c5d241100c080241101820340840d014450103d8a00b50300303000011b20202c1e0b1242e80c0707030b042000f000382ca0000c1c010701c1c1c43d8000207400d07190b240d07440b006d8201100404801400410500440700b16145600848501d444402164400da507249070056070a0300341c240c190114101042c104104501c01d001300c0300c840c8010728000030001c00c2d4200e052031201005d0011036400103c00e100810061040f0004040386000b6000d10440e9403030a05080140da5040e00401003494900c80e004080c0c90300080c00c14210780d0503242090720 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 487127859 1250 487126609 487126639
    0xb0904080906070218040303060314060f0609070507020a120b0115090e062b0b28021815071209121b0b041712090307030809010228210e 60
    0x11742c581d690305098000c0c02c5d030400d100605078568007590030359114034000011b5803840030b80c0c1517a0300c20456180c0c00c1c1c40d103c0400070700c4038141001301c0ea81218150428034106542c681c00515284d95a400002e5070030300001c9801d0600650500301e50043c20b80303640000d1000a0b000000309510101e0242840c00312496010030b10580b101d040b000300080c3e983c07081c08580d00440c11210a03400c0c540300d00b07680d13810b0010082540400c03031082204000d480c041800f4150406404281c02a4000300f16010101c017500500d166281c403491152052000c0341031000d0342c0c0303642c00e1800040c000003107144042041000f0600b0b101560703240940f5505280c1100501e0071220301601c590f813402071560408206c2440108002600174540c45014203070a07922004c0c1d0b4001e80b148041400c040c0100842598140e0001c5410000305001000a21854206105940000105580b20300c40603030300e019207000e25060707030008c20248800390b058928012482c0d101c09520019020008003803030340290030507114401455505803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 487129109 1250 487127859 487127869
    0x1101141f06230d1404120302031311041b2c1e03010b100c0303180803040201120b030109030507020f0901050a090f09050f01141e07030507020a061407030b09040809060702 75
    0x40d148442400a000000703240410b000d14100944003180c40c15680c0307a41410587c00390080d06e01c28021050140114030b059294880e4038040790440c141c11907070351308841070008056212256413040c541c44141a0410744a81036220b8203040340c00742d0040310f00521911a03035541c90700c200d00060351035500035442d5600e00b0000e0b00400541d01007550040804141180f440c1d001408802414001c0e01d0400c03841000c00c00701089210b03c914014102c0e070007080081c00540c025241c003228000d03074440001d2884010340210703086580382c000c2603010990125000381185041c18010a40000550700d9107c1545080c002c00c2d42540c890003003c00164481648019401c4160b110000451700401120815101d110540380204a15480503092100d04170000c0c14480140e14401c07541c0c41d03041003c0740b01780d0707030400c00310010800a0420360441c0200a80c80010410a0003280d02611081480d080e0302d05019a0190441e405c40e0811b50203105010200000f0071230309000c0e18100c00003905e03695030780c0d5003901c0003138 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 487130359 1250 487129109 487129117
    0x4091a060a0e0411030f2208031b13060f090e0609040209040507030605010609030c1d0106051b150f0112050c0f041107030210060501020c030705040b040207080c03130e0606191101141f0623 83
    0xa503243d0002d04006600c650dc59035521120b0b025440d10030f10103807a06440c00c006d803001c85140d5000030791100443e0044c00c11005081d070141c0110140d4078603d07181d903038000995600781d00000004003280018414064054214002410b000804d442ca00090701301c090302c1b4a50510030030301032101c08102041c84000e5201c1e5286000d00c3c0c1c200383c6401811450100725900000e03030703080b0b000c400e40340c2c004104207083c545034140080d0018004d10580d01c0b0101004082d103030021030b03503420648480c1410300311603d880107003031414403036005003041144401600c02211000c3d48164115406004155400d44000c21010240c3e0016640420402400000701c2c019205410b4010040700d00024200201480880034089078546c405200d841b640c4d0321000c0d170100140941d01c55600880810000ca00a007441c01021001034503410082c24200420b007515084444040390070251100301c0b41040102d020b2081c01050312001441884103076410b10100030b25450554a201420300c041035200c40c03d41c440c090903a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 487131609 1250 487130359 487130377
    0x15022d1510350c0a170106090c030b01020129042c03040e151309030905100207080c1005121305100204091a060a0e0411030f2208031b 59
    0x34000400d81c0c000c10010140d20b0904118a05001031001c40040c020414810502c0000d280480b4541007107242c030000c90240342c1c072030307215941c2e540c001071603003074501404002c00f1240e100003c00f82c06050019003500d20700603c00e05d82c0220203c1c00843c201001c0481c860500c8199000a1000115810a0003010148007000c18090314500a40700a00c0c0020040040c7d82c0788651f00840b41c0c803200d840c00030302010419001d84c400384000c40b20300e4880c048d600000c8440d0083c5400340e810740c3d41700d000c038105681400040740140c03c0b0351420311050300704112002004100340c5070b20302072150b01c190041990042c040030549190800c008aa51218254003140d5210781000c291415940d20031800b600a41c45403242c0154a420203210036454426030480c0340e41d880c00a01014500642c0303040440f000030030408e070030394440c0d07856590600c130074120170146114803101c0d003800780c40b4181100c0213144d003c02145118400404404400005400d40c8292034100c10725420149024120f580c2c00e0711140900b0042c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 487132859 1250 487131609 487131629
    0x501060e06010909020c03031b090405010b0405041109060714120a0903060c021903030f02070803090d032009100c080307120506040b01020a081315022d1510 69
    0x808110420442032403806580c003601d81e000300f80e40da003001d581a4000d1280c00e03000c070b4000748005130410031040c006e4410b184072041011700d840071030400901128800c0c1c10110340620040350501c024109407203144403000c02d0800041c01d010700000007400a116442c0014214031840c8203072145207004012500900d103d000b080c9403a1443c91303030014613442e40e40c44180c5034039041c008074010203400402d081d6045800b03689044c64110079920300342c010340001001e010960b2390800c03020010803071110207180145c500502401b5001c92489008090f1303444201e006a8240150442200d90b01e0200200c03010140162001100c410501005491f031028540c0e0191695100104200c0041d9200180310b04204803030204000d941c481c10180000c481d46010200d0159208040c0c100202d000390340178004c0c0400e01c0403a262200c0e2903040b890500c80c00d05800c40c0161744154070b44292040413a03204e0b5681c410b6101c0c00450205038003240d07079031503400c00030080d8050030902c04101e01604080c0d540c0c2c094111f01070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 487134109 1250 487132859 487132871
    0x1f081506041a210f1005010924020f1911040b0a180609020c010f05370b0436080304032106080a0308010f08031e07021c020111010603031b050102070501 67
    0x500004100040321940180c0000401c085070540c0140449030959070480001c0c080090141414a080089d002c400000e51003199901041c80c281005468000000d04100c204500072600c0c0000150860b450f002e44205d04216103828940c0f15000c005c82142d411159400e000040550040001c00d442d4200c022200d00025040c88581015000484a00c8619004011903501c0e440320b003d8000807112000c1351403070f4001c603070704026032a003540103040d01c881000041c0542c0d030400041c2c1240e1140088608031240d003500684541203900104403c46000040e46038201901c0d07860001a1100a0005040c0040000310f040503900d216a076185c2001040001c0259036250b03482c80380d0365420f4080840003d1250f038004100780c2404403040040300d40c003800547c01c10340810120100c42c0c030800104403440a017840001e0240e902d1505204c20101c5084007100340b00c0e024000180030400d8000d1141e00c5070305010341000007a5100c1e01418550400b001181d07107140d0076140c00c41c0644103110001c0d01541c2000c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 487135359 1250 487134109 487134121
    0x7120c0b0106320d150b030709030507060c082b110405040e0f06010303033804050a021303031202041a0909070206070212091f081506041a21 62
    0x450154402504008503011014445510baa440d00a000a0b9402c020050115000b003503241d420881e05ca0360041001902161a5030300b140c0310340c0048900f10300080404000b0024804144002c01c0504014a00001d840010340c84118441c03003000c08078010391182c0b500900c1000460100c140c05072030850f800b130204000c8007003e82e07641d8001e03026081c41985482d18507a50078000242c56045141420050002607203184c500394010300d01d107114038610032041c480c52099408810b210342d000d180c14460b0b04030308440200900040b81c200078900c075005481008134946140030b44080c60f04076581403400e55030170b07001030418101a006591101048140081203003480c0810000540225042541e4038443d40e0b8601400301d940795000e890040258114282003550350004200902c00300782c0280500030380b000d40f04180c00070350220b029807400140e401024065200c02d96025041d20703030022940c042c10f1070300303121130141380d00d09000034507911000002e440704142c145070307030307a04c85010a004000b8401c1c5841 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 487136609 1250 487135359 487135367
    0x130609091101020c060a1b030c05031201030605060609011211092e17010612090c090903020d031b0e040f0207030c1401020403081c091211060c0301060507120c0b0106 73
    0x51101c50241c0245580c143c400d040600c166405c0c5000d0703660f0780c0740500190728100d0111840040603010403000c10201000f01d5400c00041c2540c06081d1101c90441d0300d0750412604484000c1c207110322640c0c0400c241e90381c0340c2e0f00c034444840c2d091841100040c4501c1070001c102007842802c503811340040583c5502c50070000b210b00241c805a810154190125400d4001114007002c1c401c03450983c8000f0800510410b48189400004500c94450004410703500c0d0700d981152101661244140a4840c1096420180d040c402c0109500c210b082c1401f903110b19400b04140d58150030710440c01c0007801d8955001e16a1281c000701c208c02d0251100319a00e444508004010101c0d00c1401da400818000c02c00004000501c2180d00322a08000c1c0141480c0740f11440c010304035460344100b81d403141c840492002145048840b5205c0f1000b907101c15214a240c060514200f100c000c0c400c80c01001c00f480104640c94110003120001644481030000103c00d6080c10303182d441211401400c1c0b403221800110300c007900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 487137859 1250 487136609 487136633
    0x30a0209010b180306040f08070809060316030c0f09270203070f08070f0c080f07020306010803090f0a051503100906140114070f02010e0d02040504080a200c13060909 73
    0x8542078501280f00c3c030418103a50300300c00c0d03400402028900c19024041056000a880305e584901754541c98116082c5c0001c1c0d96030015520048114113140c0010f2003640c00d03101d440103150160800f1000881f00b0000500341c00d025100b4030382040c0c03240144221243c119540b1080c0711030510800c40d224106400b00030f0902d040d48200d80085945ca4000c5038482d030007080100e88811440da60790301d980480e81d4a080140d0040f01602a40074820310070400166000e1007031074068500e0900843c0ca4260752402c00003200740a100031800b81c0403085040c8003035290780d10303181d41c18003000600c2981c9855140343d05800800551021501502e0600045022242109410800f02e802d80e110003410b5410044609035214600c401401c40d03084c4030000f00103500900608007140e000921004100348150007180503038008540445404c540050440c1840380c100003e08010703a49845407001c04071183e80000da4607803850066510400f02070941014101d01c80d0804030107001c0404090011008500d040102c0781c1c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 487139109 1250 487137859 487137877
    0xa0c02120d0f090b07080a11100b030d031103010b091c2402040605090d051c0c06050c1c0203092d0f010c0c080705030708040e010312030c050d0b030a0209010b 70
    0x250b0700c100440c960f4440c0105800340d49441c00304a140c40401d69440c021644112011000d11130741d04c04080035178806005552031600f45140c00309014015400701400c2c000340110800501d45824520b10342c00200780709503410748030383c103000341d030b659100200041e44034402c40004144003911301c5042e0708004035a07aa4100410301c0e040311498070b40c0210403180a81c01680035103400598240326581031490112803030f906081c01541698400104070251070b111088140403a4080f0f022a06103204002c0f4074803505c1d9208143d00070190404200351074502c1020a07007620303240000e070040049034071500284007240f420701c25021900c444990040300d40055041c10444521207016100544c400e5a5040c050f1901d46890740d42c44030903004150b82e031141c207500488402d85a610040c864100060701300d0004001400c80801140c030700758918a402255031a4400c00d140800d420102088644d50f000400d0780c1180000070404101d82c240a00442d14080d65450040e50000e0b114000059180c0031a0052102d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 487140359 1250 487139109 487139117
    0x20403080d0501050402091315080f01061a0c060c07080d140103060b090603063709170c06060f06070b1f050a180e1c020c0414040b04080a0c02120d 65
    0xf80e80d031000c000482c01112546508125441d005664210342688503140401800b044031f05035a454403415440c213001a00d1150303207a95109028440460745030ba0031000011120940d914040079009810b841302400383c08403080a0012a0480030030190000740c52000d11519020841504503884200c02c2c3c010071301c0180ca0152820000718208d04100c4c000303520640000c0e00404142e140c1000d80c2c02042c900661595203141c40c00e201d81c20b00020101030810100380e00002080340c0500e800c2c130081c049010500c2142e48a02000b0346150308001291859000300100c03501c2d82c0d41e0103c03d02280c0e0501c01c0c1d80340103000700b003404100442c46000c40c4402c55604010300040c1c81c1c0d5030702c450622482c071400d40641c0e880c564030303151440c1d181c0449400002010701c007042a540b0301ca40103a070303d02c0c202041c401c401d00540c100c02030045007801c00c0e10400703401c10240c560600302e9085c5500c6904046034040c01c0542400f10008002034440c3c02082040640355000d405100313180b0585002d1174441e805526000001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 487141609 1250 487140359 487140361
    0x4050601050c070522090605010501021603050601090b0a091e0b0a030308190228180e0601030902150703030b031005090d030203041b080f07090c0906080613020403080d05 75
    0x5540320310151058114030b0401054103a060000b0004800001c1d109402c0180c19080c5200c551034207030041030324561040070081001d5040100190810044280310742da440c18a10040012910015126046a16801c0b000070020b4002e8042040c101c45500504021030628200c0c4152003082c041e5041d0f072001000d41040742da481da1040100210f8a80b0010300003400450102c0e000e203001003039025a800b01420010b2420700e10302e204031056041108a8144543c14125841150340c0044610150410310072079501e9a0341040d4800410410244c03803d810580e03076003405421503c940d90f03241c61300c1700303400c2045440d5062494010050210080328900034098029298a01c404500455000d109a1000381c41101c43c0e00710100c0c029000100f042e0b90030751100410070328007440c01540901801c8240080d0243c1c042d29903103240f40c644154082040f040c60310b000c020701150710078818010f840451a003070706a91507030b000040d8130b4826000350b84401ca10008002041005900050041c3c5413900014411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 487142859 1250 487141609 487141621
    0x31211010605040e0c010810090c050c0c091e0702011d071a0c0a0b0c1306050a0810060e04020c03040503030409020717031003081b160f0b0418270c050405 68
    0x1a02c3e81440c1581150b80300c009104401d41c041c440385644551010451050540e541c1c96009c2500c00003441040807804c0050f20400040d02030001602952007038407808181e040c8408103a01100c811015100c03201c0c5100040b60b001c603c02e41100100c0c0e00840c0c1404004040070401d1f685540452240030b10b5940800040724130007401d01f0a5943c00f1aa0f800609121f08107901c13106d00c0320341d005254200c0c2d03030410424050180c021a035924040c084683d169502c0e45080c4c07134003900580d000b400b004500c11585a04200c1607a105103001d40d40301041e41d000d0b0301c0306c2c1040340103480c47c01550855541400041000300f80100300341e0190050a010b105146178441203400f00414901c0185c40b03110041000c000b007880400c07000340c001d00c024580c0204904130001340006007400c10703d204040490110020608104a01200d00300d00060060b0045407441c3c1444c11807008215003031140070080e000c0c0c42d17402c00310441c0302002c400e003c0b40c8419035181d030818000e454070303426000050181901c500d00e00030226031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 487144109 1250 487142859 487142861
    0xd0b10061103041401140a03023402130204050a08061e070801052103030f06130b031c020106030b010f031a070c02190504021b0d0c0804031101020703121101060504 72
    0x2007000804025500d001d0030814528001d0100e20b0030340d03060140d000d124444074444c1c1c0004201600d419603005803103071005d094565948490400001c10607809190100e1f0311031482d660301408680c101e07101010304101c0d074420b40c0a40500d038003182c2e002e19030070300004007040003148a0348182c0c0200c0500e4645840501c00030f11910050382c01c0f100080800f0f0040c4818203150b9041c0200030301d244400c500c5000d50304411440e580c0101e40c210580070010060000c10708124002e01c0300a91540024021490303880302183c1e03035140001000103044560003072401114002e6100c2805160886140e0910b5a101c13400f1350711598403440f00300c8840c102c504000f8a85240c0390f425a015521075500d505000c02c01ea02000725921112200060641c1170740e00c001002d41d154030007019540156504200c40c0c40c1b0071490300b810549002520420320207152044000550b110040310207a0740d1040c070801c110116040100d19000c0f81d90001070040140c80104519140c1208402800412010090010710b8a46040c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 487145359 1250 487144109 487144127
    0xe01060608040b0703020d0608030d0608010e030a0323040812151008040c0e010603060e06040207020609060309010f1802190f060e0112060b22050307030206180d0b1006 74
    0x50009108000030500268034059401c4d000000c07854050f0a25508048200c210365599001c4421640002444e01480c0c2242c080c200003801e0080c0200026001d0400d055160b2041c194003504159540070301d041d1080401c8038090701d00c901c80e03050070218589031400b01c40d035034450900c03010003801d1040003a40c68480c0c0c00200001030b8014020320070980711000c081d078007500050310485402242001c0410b62150520303485001b4000c9680114943e8501000c0420b40c04026045602650040010310050388810080761285041980d1042d13603513403000c02d82d5004140c1c07168010706003030804482800080c444a078032150940226040403c1d135000d08601d11461165104896144400810030405a4001c1e40f50403000c44041c10f00588204a80c6581411078100d508441c0d0200000314824156079446000031448113617219100d8030b0b190405000a684440b0391000034400e00d80010620121308200300d6505000f400500b88240c0c00706285407500c0003280071a04004d0050b506200080c1041c4140404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 487146609 1250 487145359 487145369
    0xc0a053403080405090414010516091d010b0f1c0b090114030d05030601171620030d150302191802070c1e05090106030e010c051c1d01020a020601090e0106 68
    0x1c80c83c052800c0144803054000900503925a40390750308020800c0d07028003480f885042026408200b201500c0d00c00742c01c8503601d401c442400b0411209802000300c0410100b4103558146044e90340392440b01d500b02e4907034441c0300540c08041c5a411421140c8248907044000c0072a001c48072041960381300e0003034a01c0e1f100140c10040e850350196a0252105005900035900980b061514140310000d442d04008451015212b503841c00b440a61540c2e62036900280a1486145c40000610000003c5009964030f0260502640c959940c94803040302d41c102c00070f218801940d024007500d9100f0f050903e01401051144280e4240e00c80790b07540c18003192194401c441d0190740c015022040c00d800e20101101c1804074550346034030022462000308159950a500c0f6008100a9401182600510b03500c50f013540c00c004980f06c10710905001000d024142e881cac03140c80000e80030350005880c00140010a80d0fa10100c91810300d50352001030300c01c600541c04115941660707040c02c028080380f001001494200c1d1031703921903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 487147859 1250 487146609 487146623
    0x3010b2209050c06071a01060207031232070c0e0712050a06030209040b090c01391209060306140306041203020d051015030c0210020c0a053403 63
    0x240210030360141d0004040c540200c084880000994000c40c07241d40c050041a5080e4810003100130545544511b014003404052024103002c61456842c3c030260900c0304100c1080c4006520540490460080084800054950980c200740d0f40c500108816174808102981c140b0a040400b24001c40d03003043c458010074044d550543e000d01c001c14801c00414001c2c240700340603074640301c000025030b44180ca01401a805180081498103007202182e24041c01020f54505010126080d100400b001c280c017103041c3c3c013a035407a40940802d00d0341d81c0d610000994030020701010190484002999204c4000b00683c1d1064404004044e15452208180e03c1180d942d568154064070010b80098a80c0d1400e445000c1241005418401d005030301d407058410841d20401c8401c0e00740c10800020202104e014201c0d00c01d401c0402000340140710003910b450041c00140f172190780026035518045020086441c1130760b0014180c5400445030b10503020010840701d0340c000306020300300b1405030312458035409008481c0c1c0490 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 487149109 1250 487147859 487147909
    0xe0703150f1403010b0301140f010801050103150b1903050d02160b091207030605010b09010813030207050405060303130308120105030319030c031d0706020d020714060d02040b040603050603010b 85
    0x80690303001d8144102c0d0541554903007a43e040e0340d44003402031083d540900683c2c01040c3c070f07028200f207030403c505900c40c51803a030425004002080c1c404400e001c060400b410007051135020603010403c504c445006040120400160000501c940828084400440d40d400d07100709810071610301c0d5042c452402054001d850404c0b010190740717402e031003802203081450b050392071540c1d6031307120340044a800f644000d41003140080c000700e607507038170105959025104440c04643c2c0038250310b00954850a601485010741c1e86c56010407400da41c104190340340c02c842121881c0c1c140d9200d00d041c64268121011f4500072540080002c9000c1c6800b00079100340110303400004030303902131060084010b400340301d54800900d66160501e20840d82d500640890740c0f09174800616001d40b914070028901120258190115000043c0600010300072844d03012518030129803240e191001350f84200700911444d804003201d4900028009034175034240d040310f0711500040b0020070000f84124140b0070340f901d2078441c086074820902 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 487150359 1250 487149109 487149119
    0xe0a0c050622090212010e0403080f070302160c030209010602030403050d050f040f0305010207020109050f13090618140c010206070e1011102702030a020108040303020909010e0703150f 81
    0x4409000030b808003410340300b80482801110740e20000d064010502442e0001440c1c4100c6203045407150040162662000903403a20391401010700002508126024090301c000c05c2d400c9200c5e406480ca211402810f41000c1d01c031501c0c3c0400c00003140e00c4200d000312400e03400099210300110903101107a40203030203024906e00801040381c40d50300c0807550a040342c100b070001266440e40800c103400510f10079400160794441c540009800758005900207842140c02042d61404c6450b00e20b200c17400c590300701c0350220348290603103000c0010b0050600d00d0404214080480d1061121a8501e025166003100541c0c0c509402c41004a0300c1e844211904000300b44039402c202070904040d600c0011580a61a1605919802e464114140f00c019030400f403c81da180d807490010b084c036004120f1504c0c000070003599410459a400b090301d071103010348003034140503044000409260003601105d040280040080d5459a1a05220004640706450260001e841e10f804d0300d03040103e8400c1e0b00140c40c004801001c0c064900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 487151609 1250 487150359 487150369
    0x50a1712070c080d0c0b06240c070504020c010c0809010b060316180303020610120f0b06011404060302190305101e03081b0d05040b030c0702121903030e0a0c05 70
    0x3484202d0b45444180000038180c441400000520111982c52100000c181d00300740707000e05405804140711311420141188086140c607400c001c802a10051207458000c020405802c14803140d002c01d401c0b5000107109054454103601c141d000311242e44414540d900e03030244590890311200344c401c0e003145081010504000030981e404003140d456240c02c4034a290528805c4030070700d04039032080300568071600620480500004140c0040c0107841d014035045e44058660800b034190101c006040305483e03030301003041a4801c4038005241041046200e6481ea91444000e0080d44001051191100c406840b25040da1085c06041d00441050580c09407450601c00340380e40c132600d510aa49880030b03c0002c00400109070201600c00442100d45805d907d00c04079140034180802d00c041603040110800041c011680c1481c1500d800250640c410745e281c01081c400300d151010204d26000861141e0410100d40c060304a21b10724150b4429035052111001c0081c0007581c13280405001400c000c0110400e114a00303113 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 487152859 1250 487151609 487151617
    0x10608061911270906010f12020313050304080a0501060b09060a0f052709010806010315090c0e040f031d0604030f02180f0907060e0f0105090a030c060306050a1712 72
    0x61082d10a10785031200041107080250951040421008000210014030b003a82e40564480001e080840303640f06c40e900014042080c2ca01842c8130aa8080003040d04071840c010200c040310390110480381d40342c0d115100541d903408011811115503007440004142c2e0003010b4165050b0342c401030200760401206110603039040311400100810440284a501c9841e03240d85080b60031303081c4880005002c170300c4a8040c1300011005811160340d41d40001e00400001c0c40a84aa501a519507400050150418035044c4400d100690000411a50280500007484503000700701d0540e0b03200342c58221f81080d141c2c40b484140700b0700c00d40c4158008030600007000420340c0c00b044214001c0c401080300003801001c45000030b0b40c003026076402032040e07403240805c01004070030007080c0c0c00f4080c0790400720440c42c041e10000e80403085008006040020200c0d0b91070745a25041c1d072500296078090398820440740c8416004005051034400c0600c95009841c0c000f852a071420000078002d0000c101030308803407008100710b05140d48 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 487154109 1250 487152859 487152881
    0xe090c18040314040909060e0c0303041502030705031c0e010905070915180203071d0906010f030905011e110f040b09030a051507091409070f11010f0e0106080619 71
    0x800c90343c0c030803941090350000384090f001d40040014441098140b039012500460306003d40c0f0b0b40a1540c42005540010a03101201c1130400c080d00c924050040032825030041900040182c8030201d103040c50b54454407003541c8445d401d05c504120356a03e00030011300380d5541c02000317000ba800403042803040045070f400000a0790a440b10390070340b440d0f6800304581203101418848415640c044280544d20342c1c010300540c032801e54a20100096214503000406070a0041c0c006410b000c9007007081030100d40a9046003d0058000c002081402100d0340b01c01c0350b00411520158180380b50501e0320081e545410195110440354440c61420141844c02c5102107070310012240d54180310f041102c400069040001440001e4000c5c2010341c942002d8a016240c0805c60b00115400d900b580002c55040e200e507400190b0010361031074010050100300320242c0745482e20b10800c11442d420103031400005026500484620a0600e0080005503a00c032101ca0321341c541a5800c0c42000d410b0702006000c60b4040c0c00c0014480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 487155359 1250 487154109 487154117
    0x20d030509060c0316030f11030a0e01030e0604052d03041503090c08030418020f09130f09050f100c021c180e041a330a0b040e090c180403 61
    0x1280302003d035807a40d001500600c0800c1c200e90309007420540e210318801010320f05402c4ca40840c910354000c039500c038018201048101700340884c015810b44e103e0340040c489000001c0070b590f02c500300350a025455207040d001d96015911442e0440403d9540c0c0c034003800681d800140070350b003000d0400c0c0401c561882e800e5280004c00d91105c0804010840d482030040061025400641d981d600c1c000034030000022402082d1802803050040705990303612a011a030200c04200c40004810407040180401441c03400609000b042c0b9061040d000c00c5070002d110001c0c80368041c1210481c1c142d01b8200000c1c3c44140768803000503000321a01d03105003e02c0190100d0502403604084003101c41c00c0c5481e207810040307540002e100240c00c400307110900640249003040920039074030302407880c6040350101503511202ca243d140310301114010100e09001d0030201000190004201c86c5046a580000180b55006400b610742400160781c041500c4407000200f6818501026284a5030355041c1e03900390104800c024001d0b0140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 487156609 1250 487155359 487155367
    0x21b060c030f1b030a0c020906241209060603070302010507030c05032b0b061806070c12021002011b0503041a01060f0e030313050f13050a050a0e0a020d03050906 71
    0x50308041c80948404600074400c952900d0240303c191041003414a0080c045410421604d20441c0d070000e40306154a4060710031021540f80c0d8004152032024814009c41070071b004a145400c6120313100c0042403003035005034907a90107807542c2c0c07503ca0f1946d905a401643c0355115800400042d40640d000d4865240282040448100c1d1600e80f141942d105007240044d50b1060016096003031400a00b40c24010080304003005055034010100713005101e2310010b107148900f0308403044030720341d94041190821a40a0480200d05030354208480391440380c007508034452090060000c050f1071052043d030001d155142c1200d219903009079000e5605600207442503c00301c006806200c82907080002040c000e000c2a034689220040c0c1c5100108401c80324a0300b14800d401c1044680c2c039100c440c1912006032402120b81c41407040707004001404402d0018a0b54480d1410001003000050ba6076100c07611440020b1010b10280603203941e855103c03400740c0e400a40c0b003101000340c1d00c04244140d002d44a0130b01c001e44041c0c68 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 487157859 1250 487156609 487156627
    0xb0105070221012433020706080112050c01030f020906041e0503060c0301060e0409050f0f070605040b04180603350c0d0c110d06020d1b0c060e07030b09010c0e010e01021b06 76
    0x1828100103c1711000da48100350800c4503a500190290040c40b2a00f408020b449150341d40750b0b1135800f00000c05041541f504804070040030258121765520320024a01643c40d651900314504484030f010041d407030010040c40c0001d40342004103800b8442d00800301c1c9945568202841510381006000115802c1381d03680300b0001c0000c208000d0780c03024201c03140040105000b9900b0440c0342181540066041105c2804104540d41011003a141903d00421100b803640420f104914014031955001411007031f00a03078911002045449081e0b0041c0b40400541820a070880c2413500603c1280142d01140c1d2042181002d014464402101024410301c070490319000348038002044280250015200f169000401502029891190315115800d803204080006403260340070b041e0820055001d40880d417103c01c820300101050005402031580502803202e1400c2010540d4001d0a851007801c01040c01d03881c1d0311440358054245803080c0d4030164006c014040f242500341d040d4041c0c01a072142c21180500c00c2e624 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 487159109 1250 487157859 487157939
    0x10c020a0b2d0a1b1e050d2c0705041404081e0d0209031501060f050a050f040f05090a060b0405120c100203090109060f080a0b01050702210124 63
    0x3010f5500b01c0c0c0d0220f00c80780300d0b505003403030300a44c03810400600201c0200b40c650040044d40090100c80e26081c2191910013801c07000000c0d010320203950006002210b4001e8811010081c0d038007000e00b546048442c159202c1d4140700c122840b94151160100b5000c00203000180098018650744015000442c6614605d15100f80290881200c007408207030045084c0009080800160500c8198070480c01015490028090b1a00540d076206508000c0002540032000e4021004c6866810a0b42d5815a40e00d98842ea0038404551134012a8400c264030030100700014528002c2c14142c904201e4120b14003440e03c2c0801c004d800032071200b040540a90240c0c00310550398000e040300007400a4028540d1072940d80001401c1810980013441444507084601107040d902200482d404581d0400006400b0810f0b00180c405005010000b5800a40302c002c5c841c5c1801c070382014402000c41d001c0203012040c1d84040340c070a002c107407826104044904c41c4040080c0c40c601d0b03003007404292000c4c240018540681e58100d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 487160359 1250 487159109 487159111
    0x60d0c080106090f090b0103141c0915051c020c0f0304090f14010e07030b0d1203060609050d1106030604150b0702030705010507050d140d0c03050108010c020a0b2d 72
    0xd800c1e55039110401901d003d50152140070050510300300480156940e580301a40c006020140010040c0180c41501810070864007070f0303000302d004c140008218070703420051468070704c0c0c0941315040f08482907004200e13001f141500e103484000402c0d03174240803540300700d800250443c180044513881507031000c61032040103200600150210311000310f4026805910b840580d404d00b070380301d03a07118145001040310b0b03100301003040d801072181d14000c241c010021001401207168010b014002c101441d081000268140c2c0c0600101e40913500d4030030300300f95034000b044440700403280d02820f5240020007005942c9004c900031035001c580184000b4200c022150b401d54903103087c0c1c101c4096000000344807001d51608000800c014102441c10301c3c90405184d0b6500d4448050680c0030051144410240081d2500030080c2da50480c29074404002c02c00c400d00c0e0007009040207102c0e0507095440d159511038414404a5007000f41600b0117040041070700d50003c07c0203800303240341d079140100721070440a880c1c054a200f011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 487161609 1250 487160359 487160369
    0x606020309040608150c0f25020103140915100b190801081b041817070b09030405010c030f1b030807022505010c05250e0a0606080a05060d0c 62
    0x55403941900402c0c4001c0724110781154030740fa070048251070852001e148140d540525021401c0b5114107020b41c2d40d40340b60158030300c240c0b40041c07040721200701d44045402d00324105000740e03801c1c003c0d01c845914902c2c1001003900c00d4070740b80c0c21541c503040701f07031405031039050b00441402c262591145c2d6450203416180c014910840c03d0014a04071a0700b000d9110380114003400c4124040c00c0c1c40c04003c0c1b920f01c451440e69242c140103d8880b4054105c85460004185040e0b410001c0c00c03840504040c40442c0540c0819000c4039031107415804642d400b1000003e803800d9460603103ca041145060301e055400c80300300d800e01d10400c1083c0c0080c0100c00c0f260140175071443e10940b40d400300b07800c085a01078106a80140746184035541c00a65241840340040d4030021680c00b0300700009901c0846c02c101c3e052419241100601000d96141c030b140055990700c4141c222940000b00407187d80361802c60b4420b540381c80c820600080d10074004640440300e140d01540d00090020004502d1072100d5903400c120004a500c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 487162859 1250 487161609 487161613
    0x3030903030f050f04050d0f02180a1107150209030a05030f040311010f02070506030601180305060609070507030801061b12090f090b0a1202010c02090c0a021b0f130609060602 77
    0x104109504100084400d02c00c80c103119040044200168041d0700545c4620391149141c14a888148200000400725a540191100020315012001445841c40541e00f4181c07142c84c003410303691400a0b4a0035500c4041e0b01520141c003400700310341003201a400c110710690b854005d50310400001007040004040d40881c43d4003454032103156091070b0310b19408401d10035052111407648440d61b5903010500c4000d840d401c880319522a11042c0c012100007440458000321545119004001c1c0480011010310030041111040000d580c0c010044807140903d03600140421801c20040c0302c0140282d9003410625985019080407942030f480b00420f0342000003010022030a040d03014400c1a4900322400701400d80003078180702d001e22800c00f040c1c004030180704680c610510240c5003006c580c4075100d442c404e00d0300140760080c10700b80030030340b01090341c06904404007603c95000210301c0941118981d40021800804080c600503081083c040c043c407c81d10b6000e1155603070100421055440d1184101810b29940 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 487164109 1250 487162859 487162877
    0x90903040f060e0f0f09040b0a1d0a0501050112080f0a030b0d0b0403090f1a090301020f0403050f0c0a0f030201120f02030a060e060a24021c0302030703050618060411070c0303 77
    0x34000d091807071030390413030085004a00032081c40d00d41c1c1c3c046c55002644001301c19081e40d41c01010700020f00f59802c1d10042420340800c01400c0c80d20000740066010301900c0200b21599039040200c48507200490000e03c109014059030022100c0b20019015040050030081030310b4440d10001040c0c13401c1414226428002d41c2d06000c14154010700f61070140c0195044041e503a410180790201040940c2041c00c0d07148030020f002c800703680302901502c407201500203c040e1140c0d101e14000d82c95240001032127079980f195150360b503280c1c54841013920031203c45a0110340c1460540d001124010103003085040940e44408490f449500a440250300c02c00d02000006880c03400c02101006449006d401c1314445d86080c07801380041c1610140348010401c0011240d0400c400c03000080c0d0900b01400d0680e284000e51411004400c1d0705070300190b100e414107a03010821a90394004020543d20a000c3c000920f00c101c000280c0c641c2015408010480c0c02c148005040c52a5030b515a40b592819030400c4000641d00c4c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 487165359 1250 487164109 487164137
    0x60a110304092c0303160c0503030a06080d031b0f0215040b0a0b0f0f0409030c050708030a0909090b040303020904151502010c0906170a09140618031602090903040f06 73
    0x5401c0f0468103030340c2c1c0c0001208a40503950310b990380c08040c0a640c110b02c2004004201103014590010005522000b0b43c0c0d12454074000410051009225028241c0220682c072244030f0305c60b11a07460051000007485901060307110048071801c0035044540305520984045141101030343c42810304c141e21640c2892514544910090b05a406c4000f281c3d0180800081e8039036555194144400c110406030f80000e5003280d036040864251985150103011030150403c04100682e022001700407445864841610030b0b9134070440b00045400b008405071034000244082000240b09400801018000a2011401c0c660006404071205000c0c0c0c408044c00d440c43e260440003a4081c012502000c400c0d0800c01005403804102403d24414499544003040d1501d000070f0002c1201e42c0000d08098218540c110307030014981d603079992090243d603121002c0c0320200c002c14403440004101c440007411040520707001c1c1c007a94248521311401030001c1c14240400e0201041340d40305512084000e1007035582d4a04010656 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 487166609 1250 487165359 487165391
    0x191214030739030b07020a170304031707080f060a0b040611011109030d110313090c02061807060c02130908072906060703170c09041407080105060a11030409 69
    0x82540e9070782034608400d140320410902d0800400700c940129a00350581da41140884c02d04041c117100910b00b0000c2501024424006000785100314481d84885071040c0a002203846800400c40f00309001500d0040000e540c076901c405525003015001e807242081a865240c0c45c0c2142d00250030640020306840c1840c1c004417424050555002485042240780441e5a0003094490a41009036802c1c403c0000192104040404c1120303001d1070080750401c1510740b9101368101420001c000d450040c4030301c00100311005102c0001d5800c044030300c0b0003010b1031403411600780c55140101009a078401d1902c2450080807080e8000c18082511881d075003a60392485251459003504048100050319130507982c02c10f08075035500c0d034150b04100111106511032180780340c11503000004c10341e030190091212061040d40d0040d40c020b005000c008540074000090a900000041001203c140c00016181001004a401c069000b401140c641e4a030421900448003410751440c0c0c000c1c0e100d520710356940c1c80032034450620 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 487167859 1250 487166609 487166663
    0xc1106091513021c0309050406031202150906130c080304061e03020702031209120a2006070215030903040803030903130b070f020103020f0705060c09010e1912140307 73
    0x11400a0b601c1040954012600800104503501131503071000c0c08140a02d4020ba9581001b020f0060003030200d0340d00d86c581100c21501c270640040240c40303109050000c1c0300c071400c01140320b00c4610004002e25620b2201070710303484060010540340c01981040c0810000d00c18002400900b48030307151300901402c1e404080140e00c4c2c80108203800c16105010500060340e000c940080b00c0320741105081e4655001c90001210b561800c00e500105102d03040075102041301042d503110303450b089074006548102d000004e21005110b1010001e500406021240107405194800ba44d00f10610008507414161600d100c1c500e5544107846501d126440031851140c10420600b6140c0908507c400079800c2c402d0b142d40707803031070411030603402030502d5004a00d0469000c54036094514868000b42207984a0912180c100c000341d0004010794006204200071401074280f406d1804030400500381181c0425203003641c0c40c0c4400380031120440e80703188038140b000724031502040a84034040c021813182000c0507100d20444a0124 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 487169109 1250 487167859 487167871
    0x806070504081b01200c030c01140708031f030b2203050a08041103030a17010806010506120405240613060501020a140a051e06010f050f040c11060915 66
    0x80105000c50302c0301243d00c3d400503a00072207050000503100c00503195a4030f4a540e0802481d0600d0710303504451000a080100003200380d0658071086502d6004540c40320107000850605401080703808000f88002004543c014400d00307160380441440d1032100c020381c14a51003a2181d000180500c2416800004580044484144a6101006d040d580581140074407000705090000c120000340610101010382c0900d01c00003015690344a615550103800d0040305140350381c80d03402c041e0010079460030000c0c01c0d9040c0e030b00003080281030038003154184004036402842222039000b000511110103d100c401500d104048801003091450200306100700c41c0d1544481d600410f0520340d00300301a0340c01080d4900d15a400100505e4003a0000344514a0601c1601006007948900c000c0d05000c1c00c01c0901780c40301e086046041d1001f030303641c0e04503450309507e4a003d0b1503070002801e00701c003016280650014244010500300448440305803140c40c3d0070142c0440c0c04c054070303400240034201240c2e04802410390040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 487170359 1250 487169109 487169117
    0x30c0801020307120e34080109032c10082212110304030804080a020a0b13050609030118030e1c0f03030507180303030f050703090b0f061201020304080301080607 71
    0x89003a1500800030300c40d0390300581c5000d51341c000559001c2c0050028070080c40c4007510a0000101d504c0300e10100c1c0c420041d202c1d090750b20381c4001068487c810700491117903c2e05592030b640d005940789201c001c517988e4400d42d0404488200c00079009a11098560b181918480c1c0310700340c0f00c0c038001d038042504c04040300f02c1e5401d07803c842460000159403517888030800441c0b4605448214003080d582b03451841540c0010f0010240464005103c000006a04840d18800c3d614220455645c1c0001021030240081100b01c490303072584240150b003070910190400c07140090010030184648506602401100c8105070001100403401e0b0501d0309003581d5401c418502100700e40584551610307800d9402540000050070140c4541c040340d00c603031049004d107142c44100c000030100765036a498050010459074025000ea035040030002207080f0300900c2050400ca40010b42a0295500c20408840b0010010212076000044481001d415082440618801c030300c1a040d49599504041c0c8091901c00000c0c0194108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 487171609 1250 487170359 487170361
    0x70905010b03130b06010509061602032a010806010507080c0703031d030a110d02100206010f0e0c031609080a060504060605150a0c02180a020a09050105270d0807080301030c08010203 80
    0x400083c6108240503a007154041103d61904401243c9a1045854080d03201d03402050304100d00b40b903c01c044160500c200d0440764913171820820310003210101c10391480810510071030850a540200c0d0010381c0080c051400e285009641c0da1100a29001800307084000c1e03000e4001402015000200790881c07110f605007001c400700e80000025502c0140290042c401d4a0b000c00280d4030b62281d03000a240c19078018103a541e1240c0851009665140034414011580e1400b44c0011710480c4404116028200c0745001d6480d40e90b030005031030b03c18500f08488500300185070000080320b41d0180720718107106100b0360740482c00d4145810030400340d4409070015032060403511a1041076144060440304000c00c00e04140421001600020351000341c5400c10368540f9050303c00b00a400c0b08144c0c01400c0b10385040c0ca8081da0316407640e0045805000d68a444003200d13151990200200e501040d40c0e0481c3c48000380713400c2200749035650300c44042e080b20104070f82580000c4014010403554110160260080344021030035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 487172859 1250 487171609 487171621
    0x2010f061a040515040801062409030b220506011503060e0709052205040605061309020616050102130602030c0f0c060f0306040b04050f0106030c08040215090604090e070905010b03 79
    0x61003140f0503d403040102401100c9005a56800d480c000d0684900801c929039852207640b100990001e03400c0e0072145040c065132104d0340135035001800d0baa00885442c010356249140c2c004180c0d000105900c15440103641070001800420499000c3c000b2000d046003840d040c041c000e000c0c2d5500ba0442c2c0c1e0300310035000c104008285c0c4000b0b68401c81360215104450b10141519045042072442c8a83d1120341c01c03c0200001c0c01091313040a802900140c2c2c06070310044026100c041158118507009602000400c845030a008081c1410038400303000e00001454428080380c500c0d90b8041c3c55101c04056000400c00d50718214090040403c840e00000c080d000707403544d02001400381d00c102e10350040e140402002041640e240c6070b00100d81c40a02030070400c005e091560750710300100c90034401c01c4006401e2020101e803040c0700e40d01c540d000c0d5030301811681e48900b010042c00710a8101c0030420350090030500001840c18110b00840540b030758800045d003441c6080c003000100f40c4005070864800c192003001400b41d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 487174109 1250 487172859 487172909
    0x4150602210418020304030513140f0f01080106110708070f0509250507151a09070c020919140412031b170901061205031315080f0c09040c02010f06 65
    0xd8902c400e0b100180d07240e1b1986410703505401340321030f8034401c20442000840c110150341e01048203510115071111380c8428003410450a0215140311a0000d440c20004010b2176001d01c40d60402001040242d8410b25200c12003517151109552014860103c440d004100360308000c5082ca4108903814410441c9400b00103c0000903402c031440842002800034041c0b00b13000c01c800c0c14840315026440140582c5030a0105500300034568000d540c42128a90b0200700514052109a07800541c0642030034502d40c0c3d074003201c4406902c440d45860380180c507038007240070b009828900311b031059108101151810030780340002402c03207401c0b40c0049014005170b0101c4030030316085055082c0c01c03400c801c0d03c41c081f40d45e42801d03580540043c0d403101c0000c1c090101408100031011010780746400d00c0c0012001116138a640b00c00c695a02806a20045440300c400b0441401060741d4182d48205005016461b002d800c1d4042011960a00d06135001030350340b1480c3c0000c03804136000e00070040040c86124100341c1c440580301d0f0313 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 487175359 1250 487174109 487174139
    0x50102072d030e18070f0f0216030204051801110a080f0c09120c09090a03030b030304060c08030a06080303070c060c0806060f09041b0c12030603080414041506022104 73
    0x10b000d000a080c12401143e403070400c049a8149411840142414240800340c200e05480780074a002c29919001b003083e440c400960102000c2e5006283c4403800e1564081c031004040c041c1072144180703e00c2150300a424824010084003030100f20300c543d039a101144009146c0b03030f03024090000520414050115540340c0300250b840c50b200c110303009504075100c101c8417843c15000b40c00442c2c210082800300030b900c1c6070100300d0000c282d019031024040c4840c8207081589138459405581c0104a200300c1c03600208004001540d0f0000c101c4600184070342c4c48500d154615001240e4071f030000307183d101510081002601400c40d0508650400001909001001805038095449010304160010039400c0059403035400030601c0c0c900350500400c0401d02c030f4000400e140e00104d0306603142c800c08000040e401e4402d100e2401280e0f0070003005800d0a043c00d079044c00302c003407918800341c0c07107612040300c2c8469400d00f1214800410303030340d00100390004541c0001090030128100704802240c09000130045401a49810707 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 487176609 1250 487175359 487175363
    0x19080a021509030a080c0d030e030a1b050102071121300d0f060602030c0304030f0f08030901090501060801090209060d082b0501150219140307050102072d 68
    0x80100300041d81007410503406468150341d0f151042c2e00704038043c041101c009000d0b00c00c0c00d0307051303405074043c51206a0555400d42400c1000741d0041140515480c0704008030340d08001030342e59a031a00400b40c0c9916080e41c01402065405240c10341505019191036a0140e0003103016242c0d14402070065866182c43e1401500c070000e840c08020180028100807883c00b4050740604c0442c2c0e0784540c0c1a85801c3c00410010040b840014a0308902103602400001078a025010320b0005601e003d08582d0f43d03903104a010b1100302e540f204602c54810005589601444c4515a500e0000510030f80798104182542c0040d0300109503070349094103900150b260f451070958851030658a0a00003c0a40703484e480c54410341c01001c102502c002401c10394004e5840318040300320721600303080c0002d98031848201d030302c90707010070007035015911110124100450a460010340c2900603410f09030100007810030b80c1d085600c6100c0444d04c507540081c0718802c1001e1405606c07001c0308503c80072040038041e26a4000510100f40300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 487177859 1250 487176609 487176619
    0x10c031808010204060c020a050901080a0303020a05130b0c010b0f0604030602070228080609060709090e07090e03120a020c060705180a0e04050c04140106030e0715080619080a02 78
    0x19000510391821803034001865014002c44d512a6a118014500e403c2c0c3d400c200d01c5845ca003040080c4070700d803030703440300e0305070b44046000e0601140c140d80c041d0000c3d40f00c4014602449418020f01110340c031840c42400c02040010303030280c0e40f030400c400d40c2421030f0440d400c9244210118540401541c450700d06071000e60754001740041c0e40782c55900000304101000074042060580160700c42c4840b0f2041e40e6040100c55001d4101c54890320740d070466031303102c401c00c854120001d00805410802a06180c02421081c54000203982ca09034649410b0010383d04000c040c01c4180d0700015040001080d100d05856003d41c508c2811402d1010301c0700c0c820784641002c2c6c142c4003007100104500002e0b1405030217004800000820300700741c013507a600d0f20404080c400c803001d944138000e000c0b00686506060069101a860b1042d903c585607007401070540041010f045042c103c1c0c40303508800305141d0075140d4910540221a01ca079503440c5401010000c811010f2180010700d1602c0100c2001072500009640111300d1341290 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 487179109 1250 487177859 487177877
    0xf1602060c0a03090507080106030c032906010c030e13060f05040501140f03070b0c0606041406090a230133080a0207031b0c24080f100308030106050315090105010c03 73
    0x4001c0d00d40306e43c0d60415a50380d440c0010010800c80d2030007144049034856000b2490306030031250b8169150100b00090b55040f595800004d94541c4100381d80c0c0703901846030401000c1000c440001c240c045040c03040e240c2c2410b44d16001441203030010f2034040c00409040b507080c08598100140401c40d0304502031410b000b1024020000724030303541030007010701508140012a8a9642801213a80d07250420b881c5c02d80524500a90704e45040d250310b090783d200d1500501841402e44500d1542c400801000b540340c03407618100b2a4201c3e0417010480c00c14024811104122400d540c0d2240c06403a1046010078001c00c4014010b0103440d294200302d1081d130107a20300c80b00503101d40c420305064942c120413035504200c0000806140c42001000c004000c03e030788280740e0b42c80390801030509840b134201e004480c1c140882e400f50002504075861070b0b0100d038068500700c1c84a488950380d9a403442660800e801081c08a4000300c2046200314a01507904000b440c1264503020b1175240100180501300c0d1107e0141c10005081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 487180359 1250 487179109 487179113
    0xf090203100522030906080106080f06091b07050102090f0d050a0615150f021e0a08091309052107032106170718020414010f020c04050f1602060c0a0309 67
    0x100c2c141c0c96a60203c20b01418282450000c003030300003078025040811800710000c6012845100c0341441070380110344880031616100100f0448442c01040c80c00c25403413240d42c60b0030401c00000927202440c8600000360f12002420104104005803205e010b0142c043c0040b0080890400900005441c0c3c00a900150400c41030044460101041d0000000c0714580c00d010716030950300c52500045d140c41642503890300c2c000b454014541c2140001c12298a510070a561004140c02900600074036030014180d6240a111a4610003a6000c80c941030741d60f40c00100d45040340c81c1d419584550080000620390f0b01d00101543e02401002c0015a090b00001145c0c42c200d00307007591a40a00b001d806262810441c5c00300700742c945543d40b05140504006401407811086101e0b40304c0c000c0d00c0549015842107503c0360640401100e40140704140c4604502c10320346800b40944441c41030f6030180c0030180581c0050f207003500d9283c004400b020004021035200c0d80401004c51000c405540d6803034407a00c2c01041881440c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 487181609 1250 487180359 487180381
    0x50301140a21020a12033203130b0601020d020c010e0f0904060207050d020c01020703110310060f06032012040f0f110f090403140a120e060402120f06040618140c040f0902031005 78
    0x41c5051f207800f21000040c04102d05407210030007030b4144180f550700a40e40d5a4401203850310003c02245002d0b9004100a40d03013507002d460403000010025140e8103000d20090006103106005a90594103180e000940c41c0520405010901e05090507000422182c025000001d50301d681510029000e006110300c404190350302841904814004801c090000e02c0e108d03c5c03145001c407044d21614010071314210450005003070006404083c4554840d81ca403c21040b10b04100040348018011101e0750a08001000012008680c0040141c01241d01070034200108003030100c1c40b030ac0c01200c1842411940100b00000c2e620022281841c0354440146484509003441652800c00d01041c8180c42401c110606209036400101944958000c0365a003510001c9400c049840c5d071040c1810a1840e008000020040f8500b608481d0440d0404200f101281c83d1645801e42401d00802240c0183d0300300e6101280305103080d024015106050540811560009038002959400d040040308e04154581303001804480312 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 487182859 1250 487181609 487181687
    0x12030a1e02030411031605150c0c060f03040c0501050c03070204090813060c11011106010e0c090d0302060703050f13030c060207060603080403060f0b01050301140a21020a1203 77
    0x2040c00564403803c0c945070102085100c0c6060b9130080c0700d21002115190680000301084a00c040c1450050042801c1080d0350380d800720700c0d10441071007044160311668554400904041000c0850940c880c1000d00d000034521a407a4070645c10844144481418800f002c001ca4402da94103c0d0000f500b0703c024504040203004039081d41c11070001b86803000849903004010003100341d103d510310003500c90703690005403000369003c0f0219007240c0c4003400601652031550641c0741c11000818100b424803014000180009152030800c600503000349041c0304240c0e405004803071300303c28011038081c00e80c83c201d07004000440d10342a0140c10070940300618400e200c4560304a482d05c642000342441280d07100c3c07c102519510030310080f19618540700e4816170b145540d208400810750140d644034a182d10341454406104002c50240364408003010000035821b44400e031900c280d0032900381494074000340d070040100c040c0f541e500000101411704800ca001a60006c100f441803101c0781ca4000d2803056840c0340b8091106 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 487184109 1250 487182859 487182911
    0x60f0905150d1e0c030b120304030b1306060603140603070b180d080a0903051903020705010f020f06100515031519120b0f06030c0f04021c1b020f12030a 67
    0x1000790f201110105540004405505a80382840301050240030700051a41403406040940c009100600001c1c00b101000f03900113422200d82083c450041e124242120101e0b440f1201203642c450ba04910b03601d101e001641e001104034042e1130968981109040e00c2c1c0304034401d40c603142c54010407000642c0d440c1c164200c1c03e2500444619140d041d1410080d0075040c8500040d5458410600c0000c00380c11203000755410103174180c1c0548052482c0c00d006640600341448100c0941c000d416030390100311002c100e140c2c490f003110440c05444a02d0a01400842c0c810100008180c01d0104200086201d00004000e250041030700d4010b24040c402d022400d104400d500006000040d2225010501c030141c102e01e405a0381080d013071010742c2ca0704020903903140805984981c000101c2030084203c0c2c9095801792266000c0e503c444401034106886020803103c0c02c582501e040d640910702011415070400c18100c404500c01c00a0a540056181c01d035002c0c0401081610780e0344e104c2d800f40c5001500e00322100d4441e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 487185359 1250 487184109 487184141
    0x60c090f030b0402090f1b070611070b040b0106110c0d030302120708070806180703050702190803041a0c030417040b0d020705060f1e062107060f0905150d 68
    0x907807a40b420055060040d90309a210301c000c0c002103030340281520025400342013609070810700c00130f040c00c002e03038170340c101030300903a1070941d07030f0100c4152062414020072000344600e0456030036103003514000100d41d1040c0c2000040001c0b200d600071210340ccc00203a03002d1141c0f00b12550740700030600e403604030702074415801c1c50110545c040b4140210144c0140c15180115915181c9c0e80003680c0e0369041c0301c0040d900042d10b00600c0004408264a14040d80c00990015010320660700c1d03050113000d4603058007000e08411130301000004200300c144280103108415280c4015280a607604007a95081458000504041c0481e80d580c41000c038440985ca0468004240c0b14888584810480010b04000c2d00501d909681c0c9020b0940015070740e4040030074880c40b13250308903500d01010740c40741c40b40819444001c2549400008a0820b25080d074443d510721041c2e0ba50100080061604141005180c2c0c000411170b5000d00181c1c0b01d09000c50b580310240e035540750000c140b249480318410b864582c007908181e10a50140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 487186609 1250 487185359 487185389
    0x7021c050a150b0d020604060c0c030b0c070201120e1c030207061b260c0c010605030334020a17031204030203040618051e12100f0605010e0904060c09 66
    0x19181e601020b200c41144820000c4000710340904c0401041040002c2d03000000700702c180040d5000f100103582103402803507410109602d1b660380801081d006d9615403c144c001082440c219070740440c1d01940340c50b8000e01845682c241d07403285680e80b800d2820699510f0000041400101c0c4254191086250405410b1000341800c40c0c2030181034250311100000520f81d04c8109051503465900400d00203400307191140140e1381c01c0445402c5805c0403004100075500c40320000340a98003000074240c0703080d040c000c00c00420f01c000900d26010390031390b0300e25a5840305010101e015a5585401c0d00c02c44001080840051036000300d038034210300c252106c0001b40c0c08160280b01c1416400000343c401e5910784d45407120340c606441c4050500700c1d098810745a103c0102c00204411807608101a0301200b00500842c00c0e400c60400c100e420040d90303d2066100d141c0e1248422100111030203040020102802c120310406e680c1c3c0c003c910510401400a0b05c070035210441c0007030041c85409800000d202e044150100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 487187859 1250 487186609 487186613
    0xb040510050720340308030c0405090921090a03062a140403140316060504110f030a030c03090f0b280512041b0305010b03010c03050c07021c050a 64
    0x1d01c210b50704010421006080d1003015504002020340501d2130800182204051140803076141c94000d61201c51010b440c104000005503402000d540129000d0088503107031420320050056185004083c920981e21002c4250005822103685c00307031442d021107045641d1030000c0b02040101015034401802a8a00346880790000d00d40042100e03900c44d402004085440607070310072a041c1851640c15603201104200400c0007951801ca01c4071281c1f814400c2d03d0800352604030000d03010340c000000742c40080e210803c000030002d4207025522600d504584c84d01401291307401080e640c40041000806210107140b2400526000d4000300d4020b0029917001441e258840c1c42c040340a80008007500d407849180b1402482c0608254010350400c01103541c0e6604014100200211503040a00155002c010300d05003600d059408440c02000380d03000d0400801c10849180901d400c42d038101e40a9002c15103002e092201c00441c48048946668044510140701024003840400e80800c40000400c0e6200e50303400801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 487189109 1250 487187859 487187867
    0x1403010902090909070812091206010602100e1204030209130506070e0102070e0601022d2407080403091811160317010b0a031d0706021f06120b0405100507 68
    0x103401000c0e116504961076980010b0b550390b00c07a000e820314581012282d2001a407a450183c44c1d500001000c41c042761414107600f609186081c1c1001c001030304a90b0206100b001c141c02041c00444d18040148041100800742a115000350f0000a104174420408140c0d03074089401000e8816030040145d9181b4100524058001000610114054001e00000192180d05079031800c0c03086030107030083e2204a07952004482160801130a00c03d0139000140c074098030314420000024800c0c58240d04803407001c44401e803641c2c1d00100030115003c10000c0340c00c0000013a80103401004407148600000c14082d081c0351100b003d41560207171f4101c0b0140115140204400e1600c4001da168081e4550210303105101d084103451040c00d01030760f04010740401484406910903031014054000702d8600b82060202c440c4058107040c10b503484900140c0c025840000a4550501c1d45500804c80540410000d841c19081a10b01d000480c5c0242844110710000707000d02405012540c41500c004001300103610b00114007030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 487190359 1250 487189109 487189117
    0x313061419090503030a05071206080c01110d020d0f020f01090b1503070b0708090d080c01060e010b04180c21020408060604020a1b24020913060b040311011403010902 73
    0x181056480d81030610609a481074401260b00303c00550300d184c1e07030302c800705000c0e0030b026101c1c3c0c0800001d501440740e030503454030883c4041e10302c810240101c4045500010321007103680e500a5000d4021030074091203680c00090f01c880d40209820319420340e03440307440b00340d08281c91040703000360742d5080038084c40811000c98006403103007032000005900380b083c440505940740d9403030213141d0b01000c3c00c01c6098042024580984400440104021541070055a4429154103d401d440d0302d20380d100c45060114440100089000d010000d16560501c3c1c60600905000041001496040c6541d80066888144071303041441007030760020152801c1c550380720f284000a5105100d100000d02501d008101c5515190013103400700f104aa0f20030441c851010010000d00394041003c40c1c180041c1051340c898480003940001c444600b1503801070701c52a0076003c0c000500807100c1c40103051854100c00b80715404440d02035800740c0c0d8024004000380480f800040e1081003520001990781d00e0003100000300160340760014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 487191609 1250 487190359 487190371
    0x906060d02040e0a0c031506110a060e100e0c01171f0f06030e03090901030204150e0702030c0f0604020901060810050307090207052109220c2f03030c03130614 70
    0x40118501c07548086044502ca1091f05441600103601000524031446610070840700041c2980e8a5007115a10368080326100a0059046c0c2c10907041645202028480c80f0b501e91704250141c080000d0343c01c0020000c40d1031185c107940c000b40c01404904000c00022000035144107414548030855205c5510f1000c90312103109240009092480e144514a030200580e0b5901c84c1c0500f10380c0941e425542000043c0c16084006600c1013868140003a2480048070442d000382c0031500511b5490101341601420203140d603401c0403a990141080c040140c5410b48524110340c2d103442d03c0e02c1e2076200c81ca20524080c10640c003995240c41400c2c004107a480c2d85600600790715102e402151081d43c40c1e000140141040300c41160b1200c001800130705902d080000f503490584045035250f414416010160608a82601000324005083d4035040c1d451210505904610180101c041a107020b0b008104241d49200042070304446a00200210300130140403040c00c0d0485034000002c0c049011101034000000c58100e8030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 487192859 1250 487191609 487191611
    0x1802030f06040c0609120809031c09170f2508061f0501020604150b03240103170c0705040c0905030d0e0406052205041406011419060c020906060d02040e0a 68
    0x40044c2050207000301034220365202e400000d184040d03480e000c1c0c032034110045080d094007400c540f00d420403040c4150380e40d81c02903d4456070b00703550038001c0e2140720000078004200c65501200080c58108000968035264419000ca0050604011000481282c1003507000c40510300c10041401f120000f5150002900310b05003034540d800321790b14401242d40d1b5400f603c0280c20420580040c4d9982800c5411030795907400041c0845070078415000c42203901500d1410500d02d582d4401006000700103005001c0d03000000180c01d01c40c2002e401090040d21410984100c503c500d07618074014072a5801540d10900a04005041c1d0700340d0200128082d2401b01040e0700c0302c0c81146011004070b65840c054490f40205800b00f2007a40703c0484e03103407041c001004068415120131180a6848285c003500b0068980a000010068900f501c041c0c42803200101c00c48000c90f80c0640c0e6468148041688400882c0a09804584408180c0c440c00003150312880b505000043c503c1c00008c002c10744d00001340301103006002d1a14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 487194109 1250 487192859 487192883
    0x307030f0315060c020904050115090b12031c051009090b040203160b0406050c12040b070605240906121c0801090510150207090609090615030c0501031802030f0604 72
    0x40c100800b2105008440c08908811100405401c12901e4a54000d20803400003a500c40442c0804c1c49071101030380301c0c608003500c41200c86c81d642032004400003d218114015402d150000145110b426081c1c3c14021075555190006008440f00280d0080280140750b420091400b0341d00b040108584200c0303040c0c0c01ba2050600c404c0c05c0b081140501800c0f00e0841c1c500b28103150910b1800c4030395511a510301c0d0b40c41c2c801c910750801020480d1000b0700041c148030036051750f543c16501d401c90548000812640c00d00c034890084440c030340d401c102d00c0f00084400b00c41140e0b8541d2400000340e0881c42301402450248100691140c221215004c0c52a02111030349a0056981c0d0300d0b00750740142c80080300c041490075155070302004000703100e5400c41d20000340342c01501d0215131600400400c885a80e44600e13426621803904030f0034801c0380c0c4202c20950080c0130036103c1e014155240d16a400325a0320600d8101a625440004104100c103142d0141c240d00070156800284140c03051a40c50f04251415648400030325 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 487195359 1250 487194109 487194131
    0x807210602070b04230c010f052a07180203070c030f0203070c08010e0f03031501080c04120803010513020c06010509100b0d0903020c0901080d050304080d020a0903061a0306010e0a0204080307030f03 87
    0x6d6000f403a07050503075807203001d5042c0b10005c80701908a80c60000f4010803103060902d01c809a500413140071f00700e160044c4075040c0342803140c4400740d5001d00b1a05941c0d00c10800d01240076072001e84c4085140e0141003071403003048180703001c1340f07180300e07000740548410041040441c120310190001c0c1441d044c5c41040f01d0310140d480c510f4541b40d210a032511014500406d4101c02d0b107500070b520b881d6101c05000b401505156940034024001609a801142d0100d4000014003451401d503444258402d001d010450400c14072518450f6141818090340c0d1040e0004c10014904603540043c0c0005000303661103058880b450300841c1005420809011805070140d646c0075152400c190310614100c440a800408849007501b200b61001d0744054010340700c0000c100f1010400345801e0009040e0020641d885109440c51410404100c4051580b01944203100c014200346680d0002140c41c1503652000821140e41c0303070440750100038403565000170042d000100d503a0080c503810584100e806002070302d0901290b9011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 487196609 1250 487195359 487195363
    0xa09050607091d04141f06060e030a03111207150506011103040b07050c0a080a0c08031318060e0106080106081302060a0c0302012d060807210602070b0423 68
    0x180c0684564020154000004096a00c803d0358105000b541146190041104203d0070482c0101c01c00500da22020002c69102d202c1c3d00c200c100810303042c5400e07100429501d000035112008510080d0410150341c01c101413441c014014230078114000c5101c3e41d0745000e40d02e0100d00101c004c444d401c1803640b500000030f00075401650410210b030300720b00107585068104480c0d681d20350070042043c1c4040c0301d80142c4100a40303c01c01e21034083c0121000a021003405e5107041d0600f4900d0f5000305103070342c0042c41079006800303414104074140e8500b04550b42d41703841042d00c032a00511840e40a030038012480000000c040703420401c01c070b06031030b056551200960b89500b0f6600850012140003500010304000c900c2103180305203c0945500d01c01d100210301c1e0b02102c00340b901c0d2080d00c48a02c1c0140c8144801c15902480300b80310300401001301001030450701e803600d400268090300c0c01c07240301001c414040b407407820003000341d0458907020350094182926007041c1c02d01c481c02c5121240c40c28242ca07041d0603420000000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 487197859 1250 487196609 487196627
    0x60b0a170c03040525030606030b09060a0b1e010e13020903071d041112061501030c0e030607211103010302010905011e050d060e040b0f01270903050904050a09050607 73
    0x4400204032985030b03241c89803900309045c20880f070420131502d004800030781c0c3d600403a0000d5004028101884c200036004909100000c0c180c11145031a10700c0d140c00303603141e82032141c41c0e00210080c950400c458010050b94218044100b0710390007803201070303454282d030000ea0141840c070310107078100c5070b10319100c800348040182600a2170745815408000a00001c1c40c2129960005002808403004a0702d8182d20624004013070350401454903041c2440321a0356030602c82e0f00b0080959241250380241242c000c65207440001d070024007000700c0020303035511200050000400081c21401c0410a40c070800b850310959800a0008a000408010700040e4941c460b103070442c20ce01c060034010074155480d0341c06440650000f448a210315031a084001103105000741f1492096008101020a038940180c9100548005030054000750804000e07180c1901c0c02c03400040c001c441000302c002520400ca00302605d107070003040303e1070380c1c0142482c04128951100340c00c0107160f02e1040044514585800105a5070200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 487199109 1250 487197859 487197863
    0x60c0f0504030302070b030705070f0b011e0308040b09040b1009031a09060a0b030f0109061a10051606020d09080a0201050106020f030711040e0109080316020703120c0204060b0a170c0304 82
    0x5c0b0840e8103200c0340517200000c41e08403501d82000380c91f080d450781e52b110701c0521441090391328402140042041c28094005c0304034014203251701c1c0c4606410b6a9804285000702d0142c002d0b0084041011100d40d141d0350b00030040c0a000400000d00c12040700001092841d140c00100d8030304083da01c2507540c8044142160703010f00c855001624a95555000d070500074120503600f240e01d48580c9000c4500d020742841004003107401b402c0041201c00186080401c00140c411200b4040c2940d054228030443e130107010b0b00c9000322448200103c402e224280b04010340102903003200c903c1c1c9407120031820010900c0c0102141c0416800034041e980c0e071113500b03a803103110103501d000700b507007040011500140010f812065080e50003000010010001d9041c1ea08603140e0381c1e01150000800014001d1003224401e079140e030881340e403008141a0f03003165240540c0034031801012041c00b20304240b100031541e8607044040a00400c56a2a131102040d40008001985c001c440845c034000e00700c0131600d000c042e0030490780310b55 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 487200359 1250 487199109 487199113
    0x51002270f0d0609050a06290d0c05010804060b100518030106030507140103020f030907050a08010c0f0302030c072010110a0b07051303150e0607121104080604060c0f0504030302 78
    0xe44070f9251140584413807030044605010308501d0400140803841105003980d5984006200030251051b240d07460103c0240592144a590554600062142500000707484003032034818020744840c0303030040151422011440e4004410f020300359040d94010050503082c81c144070a0070100c0041d0060508136401800040c2954014041c1800405502c1072070303561424041c90010710340ba940c5e0480c60b81700c0e0810f4501c01440d40040c641045149005034800002c1c1805200030003409032514005002c14402421113024550040300003644c420308241030710200d50700503a80f0300d4410031105049800c0c602e1040107078415603004034035285052092041c24608080800100364080f126100c09c507a040f0000c20340c0007040790401003480071203107401e0040e00461040c1d6400399910b10003600c1d0300685145440c0c0041640c44441044091366200c18140c00822075a003000800a00005c0226141d1040741c01c0904a8032036203007480200541c59010b50a01c100b00d07641c4d4888866401c101715014172803840701400507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 487201609 1250 487200359 487200379
    0xe150c0102181207171603050715050c060f0403051603090603060f08070311042c100e030d0b1c032703021003180c031b0e010b1204051002270f 63
    0x2218004201e090017800011140641141c860500c036284540d00200e54580000d00100b00c40310245100d00c908510f54100385050450100035107584807001001c0301980c0c5181c0c0041001e1601030012214140940c80054a80101500f40906400364030311445e00000d140000003e002c56610301103800362210a4003a04406282d0381b506143c1c00b1210003582d40c0103684100d0f9591340004c0000041080b02070501b00444281040141070603c4800c1c1e0140c10b0160400d215101c8055001c01200c40f040e42441000031000001c0c0d0124120039440700c001ca46041340f000d1134005140d0460304414641d400b521604418000d00d03000c0a5060703406200080d007040c1500b0304501101d0080e04128a810b060034821514040d00342c840034440c00f400e90099072030768060001581107100405010001e0105d100c081603865140030403c031064883c0d030b0300c0514540741180c04601080410b0150403d5100403880c20754840742014107280800c25610801850b41030700100c0c80142d800d06d0b403205400014010914007030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 487202859 1250 487201609 487201619
    0xe0a03020d110d0f05010b0901061b14010c030b030c0d0308010b0c0a0618060506011107051e04090311280803091510060f0c02030d0e150c0102181207 66
    0x200300701d09804448102d0811090051601c1c0c0380300a9145500600800780680840d0800908580d070318002d46004e015010010700a150708400c031910300e10100303224207138440074508040d00035440c81d0800780c406500344880e00c40000d070f041c1c00c1021680e0007141600c0c1151411030421040350402080103010482c0440100034401e207c00140094541750300c145c48295200d41c1c0c4507401c560010800e42c0102c1c000ca2088014055148502c513809282828100700d2144010340c800c0d50741c6907038400d66125801c40303074202e501143c91003128909040084d20a000c220000d01e405040b10a01c40e200300207074488e1401d07010f103620310402c050604030280180d48041c59020703203e82409500040c081d52a0b40b0070000321070151304500040500c00d03101c40621010b6107040c558024070003502c1c03041030410030040380e0038003000d6a40481e00e070642c20300c0c504242000346e0312200400c02541070011155040400419045190603042d0020721298441540a10303000c0b0204040241007a22060310f28070a52140d40140a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 487204109 1250 487202859 487202869
    0x100602010207262203030e19090e0a02090c04060315121203020403021003060f060203121f08070305150115121113140907210b010e04050a05070f0e0a0302 68
    0x75001c1c043e941e08514140c07604a0b44101c2c81c0c1029480c00c001d412001d82082455840f41c103c51034210121031042d10000149803c100741c0003940921012030780d81c0c2117449251181001502d12050780034000c54458900b0b64040e0710103402038803401010905101c0d04d80c0c0184500c0d4400d40568a1082440c000410301d40c40382c101a55400c45104103240c0c0c200408005640c0300e00e80007000c038000341c0d800300b001800d252400c1c901c0c440c40d034441c4081d54018000030360681031900000f5848202c5060844100d00c00c1008100410340b04d5000301c000c0c3c002e0035404000e101000c500e02a0201e00b14405407683c0e6030310004800d02c00c80c6002c00000003407041010640455440d04842c1c0c8401900442600b011120300328100158010b6216010b071703007043d0700103000f107041072030300140d100141d4140250b884003908a05a41c0c4643c80804850496039601c2e00f80e01a8003c211040307900c02c029000b005030b032424407015002410140c5040c0c002c1002400001c420a114034000c080c1e4040141040c03080d2403035903003407107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 487205359 1250 487204109 487204163
    0x11060612070e100905091c080112060e10060b280906110c09011806080304030314160501020a03020c0c1207090f0b030d03020703120203042d0209040b100602010207 72
    0x954801400300f400924000380c0c0c01040e00404464024007000300c1d840e40e0303203840d02c030602da0030505004403000104000b4428030004400c41d600800c003c0307031885220100c0c60801c0d55813280000183d181c102c0c08100122158003030708441940341021b1000d081c203c1c2500c00c4051894041500003500500140b201500c5002c405c0d00076110f4208580b01c0c011104c0c0003803404c3c4001d801442c012100e030078218080d405640940710060000c14042e610300703401c58600608058203080c040360301c050009806e401482c2d20080c000c14164010000315210180d60100070040c0d4080f0104120714810800c03011801d281810304042d01030b0600d0002c101e441e1401d44002c0c06400303a007000c0c901c0346070384050205036500c086c001c1048522083d0350040e56003d01c0c1c600600000103103851054070070b206104106c0086c18040b1010400d01c0100110002030242180410b6261200351001b50402c1040c1c040c40200214825054001e5140c00c0b001079810b43c403a1822400c0317020700301001c1c3c12040b010101c080349402c0f0600740 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 487206609 1250 487205359 487205371
    0xc02120c0328020d03080915090d050a09080303010b090a05010809101a0a0b0a115503140a020601030b060d05060f0118020906030615130611060612070e 67
    0x540c0c4011110f8002038003500c0500815004150140c0410081d00000e000c68442a00304100050036410728021059480301d283e08204248080014801c1c0c01c94000c002200080040c60120b0340d40790b848211b01d000c00d40120111354014407140f000890250f00400c00d89106084130001400032000482d028005814a038191004502c19200c0c03001e01c54492a41a601500f081441c80e5501c0495540042c642d01100c01740404540011000d42c04088018049a10402c582d610b00f0101c46015054034084150300c000d80c82542c0d902031100481400804090306100c0c0c002d0320b41144201c03040301603014903c11b511010340142c000c40c0c01400041d400d10022504406d0203800c90680700555903619203442c6c3c0c04d44168542c0344c2c910004002d26480034194020540f00c5032025820000c011000c07031543d00003c2d00e23181c444c240d0404208014402e04040e02c01a00e81000c1614034103a459074090941c0d0f03040b004140342402070400050f4142004142461011a050000e142c15850804c016406450107015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 487207859 1250 487206609 487206673
    0x6060409081b032116080c131202010801080d052b020307020a060b03030a0c030e01030f150513020909010509040f0b27060c180301090f030c02120c03 66
    0x80000503401d01e284982100b9040c8009680d541c84040d142d064005100c2c03110800c0f0420f036000c00484006a100c000444c81e180d05016055440e1807003d1300250003031901b5952206200d0f03400040c6070a50001d251500da001303803a2041c1030707600c07004804d48070160b180014010502c10014500e540310800740106c00e40703000000c483c0c0c00220501c2c00d0400e0349d0087c0d13040030041e48468045014003540e48201c1c40303451000c170700540c03821003000c80117000c001c2000d101405122010000c18003a0740a508035807c11400f1400c2008411000c001c480024102070140034043d030b030307040360391500080f06100300c0d491800c00a00e580b2080e86481d08000d80301c03500410480c0c1c42c2c120703112484001400c0c091814003441c021f4001440702c07030080241e440d0004c030900100000c0c0d0f000300c00340841650518201e4020b502c001101d84d46001c00c400219000d040d01503001445860020584018141d01c52000c4d08103d20884008248030902c464540c2d41e03844d0340c82c0c034913810b80142040150034800f40c42c0d9840a000d030606 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 487209109 1250 487207859 487207867
    0x30804022d132012070903031403181e0705040b1507020112090b040218040b061216080106050405130302030a0f0e0409200d031e110d020106090c08090606040908 71
    0x50740d4420703603005800e00c14141010503040c0440e0004142130b0303032040316032511080031407135914001c01c1c0c00c01016480c08107103030020106106a1561a20f0340030082c4078011101e144110100070792140f041d0514021642c003400101058070b260602400c09104030003803000c159114991214849540203100c01c0303040c40403c241c600700034982805580c01c00c90003400074940d123161074010f002e854030304004600b80c20a00300d0104400201000c103c0c80e00080b0942d06102104100c1c1d002c14909000d03510021200e482c1204005111141500044252181990180019210018032602c00e041c00d0400a0158109000c4100c40510800400b40000b030b561401d4880300d030a44011504a940000c4247e0380705482080c240d901882e80c039030254801105803001558070456860082250038015070311180141110400c078040d43c4503880c84014184183c083d40c1a0300c65009020307008180034070030000b0503814205444c0c074517400340301c03054428bc1c000c0003d0700040e80c6507001c20004104003282280c40e02030502c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 487210359 1250 487209109 487209131
    0x507080f0c06090f070501170f041707210801120303050c160b04030801050a0f03060b0d1a010f05091b09120106060203090a1703270904030804022d13 66
    0x800d1038042c8001101030b004240003004c40904141c05070700118140441e03011801c04020015070309950002d00a1007544558580340351403542d140b40040b20310100d90011507000240410b64400c4a12540c100b603080c0c0300e0807050b06050301c0070042403045001040c106a00c500c042802030b00055403000c040d51589180c41074201c1c5040e0000c074a0344080d161030380c58208010416400028150141c0300440b80502e8003840d1151850350754840d4040102210317280e50700e106036500d0305c0c080c0c041842da00c181d004940000c040820301c560302c000d100704650040b0303050b00000c1505003210100d0140c541c0c0c0030315441c604141d030540c400135406800316580092410a000400d24400e2041102074149035000d03591300c26030074080141d00301c5c1c5074000900000b044003010381e00d000300008407010141c410222042c002209545844071140d030343d100365042003103170041008159210070680e206500c00c54510078044030781c0c580c0e800781000d001c00c1c281c2c10b03620801d501a0f05182c482c1c402000c640d509800411010001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 487211609 1250 487210359 487210363
    0xa080a090e040b04060b011d0112060f0308070b0705070305070308130605040b15040e0c0f120f0601150503060a061101020715061d0f07051605010c020a020108160507080f0c 76
    0x110360030307510f0440c501d0602042103c24041c1240304802480c004101000800c3d2041c144000203ca290601400d060403402d100e25036040710008246044031504c050b9903078141031000e80d1000ca13044465010901c0000c040e030b8082e1007598205038150351500d09060042c0d40948211700c0290903a403080c01e04000d82400074015004040c4078170320038426000b8600741801d511080d402c0410a143c070443c20401c60f81010507000490005071241121a42d000d042c2c2240820320340340c12940c1140300d6004401c00d400340000c001030321718100d40458150120070100b080381210340740426194141e11204a0702c0030499103200341784040350010a000011300d0512140d59000a00507800303c00e21a003070320b81a00b000300a1640d4501f0000001d007100f111424034110002035034504d0010010340611401044c02414035000e17400308210541d010300204421407a211000e591340b8040e40c0200e0010700703900d0019949a000c1120700000d1781030b40e10b074281003075080d41e41d01c1500c0d00300a0b840c64000d803003440b40b60308155003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 487212859 1250 487211609 487211611
    0x80c060406090506160203101d070324021b0d02060a060b0a080a0e0a1a0a0c08010e0703022104060506040605030a020904050319110d3605040518010605040b030a080a090e 75
    0x500c410028181240d07074031601444d440740c1140c0700c094004030740800c08074cd0a00310b1300e41009001c000c40f04807440582c00400080c06100020150011000b1000c43e211800040c5480f01c0c80594086403a5595059103000c00e41c1c3c564022140c41450078011074000714029030906400c43c00805010400400813205a840c00015940030b8a03c180d004540064240c0c170049569000704401c0700911108501200140102c2c40611549038400040c50000385001d12990568a10803d40250040e2100f80600c500c2020502a01c0c107030740caa07180030040b54076440c191003020308407038026020b86014030340342d0208030000400401c240d807140400c1084480060300200c0380c151802c0651140b01142199103013480c078014041e101c810510007040c0280c0e445041501030318200030840e000d04003c0c8d00c00340c0d1060720030b06001e0f406150000c1c01c00e0140a0b202c0d031b00a0302900ca003c1101d008100d555034a50422060b108240c2400750180c11400c1c0c0c03680030801e000001c000305030982c1041d4000c00d64420403c400800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 487214109 1250 487212859 487212883
    0x170325022d01080a02032203050702030a110102010b010c0b07030c05120a0905060a05090c210f0706171608040f1a070305010e0601080612070b07050106080c060406090506160203 78
    0x10110100601e59a003110380e85410070203112046040d0f1030041102e0020300c81a0100c414101c3d1110b06200405104034100c410349030f8040c082d14071410392442c0091811030000411070255080403c040d403a0b502c200c14144c08103400c81d42e10f031065110385205800405681c00e06104101c401c1086072403542412020034021141c1040c00500d0f0002c85c10b019080140c082c1c81c40c8140e6007481c003400900c00c400180b02142c048101d410000184103031030f418541040e013150304441c2e800340e1101c03504c58050225204046a0f11522225003012000c0084907003510101c42010308222920451450548540401d40d801031207403950402d00115074580001110341d0b4002d030086643c1c60750030031003155414003542e4014070035164441070f942401c50019080c40c2c0024000d600501041c084140c41b000104500300003400c0700840306030741314260705245010f4071013070080c415148a00700d240d4806007441000c4034102c0760241d9480441905090030003003554001682c400441310701e0950340c80940d5003070020351301d0f100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 487215359 1250 487214109 487214179
    0x1b0f060408061f030c1a0c1005160f02070b031509040503071e0807030c0c1e1d010506030412030917180108090a231617032502 56
    0x881c0600c4a10403000035a240800f14140a500400004140800fa60140e5250001c840c180c1503000700304860354000d80c01c0d03401c068450030285003410800323940024040c0050b040700300300c500d08159050b03c410524044140040c1d0008600f00705000e01e40c0050740d0044507072541d46052034170802c005008104140c1e42510a40c01c0043c881c2c080007030130100b010083c0b602e005a200e82000903281c10380180209200503003800310b611680d4040080d89074842001e4244229150b1031403085d80b480028050560007001d41e08a42c02e40000602040003001d18100c0d1001802c0e10710710394543e0b0f41c0c0032500d000e5142d184181a1240c4c0707a4000922102c403807910041c200d01d069500c0300e22505151032100030300302107907050140940c144140890086484030150350403800b035100c81c2054056000010540a0640e4901e004410414000318800307090300049a1300a52039001c0003064a501581340d1041e8003544841c1d101030111300400c1d16500088118140c002008140d591101400c10707014074500140400f144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 487216609 1250 487215359 487215361
    0x617060105031b012001150501020c06090d033203042307061b120809100b0a1a0c0105090304050310090f0b06030709020d0c03050106111b0f06040806 66
    0x4454108001801003004400070b01d0b0308001c50051265400062000302e040021601d000c9a0f030444028420100101c2d61008010111081e504401814600e0043e40d0050160032030801e100d2401c41c0a0b03914100000382000f070303001d07103035601500e22541da004090044c1000c01c200600a040c0500c0d20700e82d0143e469051030362441c003440e02600040748e42a100170043d1040746600c10000000600d8000d072459814032840544051f103100e880f0b0940c4c01c50040200c01416a10761009070311401042c000c41c07600b4112240b4411203003010b010744220049040c1c0000800302c1c100050a5600303044c10905c0715954440c0c0c60b003842e8040c21800d4400845a41500c1c1d4400101044103003810842d203c078003404020100103002056039042168400e14801520615400020400a54092080c10000c0c101114115a1550b40480c10409089842c1c400c00c0444c0c6000000255030740260310080100a60b1009021486101da005030100c015201c0015040941c10600b40426218500248081c0507080b0082030781e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 487217859 1250 487216609 487216649
    0x4092117010611070e10030506150a1a070609020a081603031d030a0609060b09040b011d0408121803130306060609030507090b040b131d0105062107050406 68
    0xd0a081a4825010800b050104200d92100030810406807041904000300544401e01088486500c40c2c201909034003d14062000f130048100304600404030941c1c07118411640c4d107040b07041d10940b141d03c8001e141010002d1100261456000780c95052006101d03560075612110502c0c03426290305c070410215031214200b0300c1815040103640c401060a2101381c5600d6070700c240440c0c2c4411102d43c0080643c0d8481800c4420800f80e50000d69404601030003803c607a103424248800311030028480e001440c07045c00803d80e05030328040603042c4610f402501240c50602050045002080300a101e00c1460710007007221410700134140000c0c40740300c08400c41c4d0148282141814021908142c2c403100c11310020329002c000195000c5820700c11940304102c00103e1000c1080070402030524406450b52041b8030a4107607a055010354040c40c071210001030b5809204d0a090303696400c0f00e400390f594682c00b00010302c100459101e9400051058800d0000f502d0300c4941c2d0f800800c0585810b40c008000301c04020086c0d100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 487219109 1250 487217859 487217897
    0x706020304150e030315010507052e0c08100b09190902092106060603070201060905041a07170c0a050d090b181f0c030207021005030109180b0105040921 67
    0x241400010f0069443e6003081c64040c0c8080b406500c280d8180140440c19006001050042c83d1039002d842e400084040800c40042c5c040600038449040320038504003031075403024803e424441c03090b00300c8688001003070b040ca4561005500f0241800d42d006480c40d2032008103a4424480300c006001400b400b50315407001600300040090923000c0e49103e089607a2000741c4030748000803039540140d0180c0e000c56581d200c03800224058007440e0050b411700390038071007070004015440304456052001020b412009442d101011140481d1000400c0c00410300070021420340e02001c0000c04a40c080e40c00c010b860f1000810645003664041503059032140055001c2100c1c03449121310a0b450551032101030242101c1010107084403a401051a208131640c4091440c0b01d81d0103981200d25058004140d0700c1d50700305241c00208030741d00c00d000e8000c0f00b6003821001c0c0d01c842211405441c1060f0f02601d1103071030741e0030b14081c88000d0100340b2055030a505491401480f04040f001310b0f9580c0700550ba1582c02900031101004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 487220359 1250 487219109 487219121
    0x90a0c062102030c07110d0614040b07051608180d06142a07061d0d120c020c131d03091c0503160507050301020d0204050301110408030f0a0302070602030415 69
    0x91890b8010420000701070520000c55008035030103c1c0450081e4401c0d40400c1c0b00c203d214038002d10742d038038000a907e07000310740341c1e44144500d11503446045540d03a90706044904d0301450341c44020030fa00780303a0380d10000351a280140004050188041c0d203200586000031340144802c00d0141c455955508191000342d030802c2d60260b2010400313701e061003654040002c43c22580382000e04910510214540040098030b07002000b6444140c1e400044001c0512251603c03400b00c644031074041000c00c10901040032550180907888009030700034109500c50300c000c2c4000802114404140305941d918050314280c4031101d46130342104000c0003142c60790b17040e8040c044010600d0b280f00c0700040c550b006120000d00c0c00401c440103820001e01d15000802d162030050326091b280d80080340e241d400807521092440c420790140c8200c440c214020310ac00600000c4148143c41180605102900100031145002c000d42d001004a00c035185401071501d0b09685500c0202d800a49080365046100501c14844403070500a903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 487221609 1250 487220359 487220417
    0x8070c080f1b15040b0106030921030c090905060609040906020405030715080a020906030a0902150c0a020f0d211112090102010b011418040e010c021c0507030e040203090a0c06 77
    0x14a0682016102d880340c0d210140701c0c40c0304041c0c444803080102b0030341d00d07540f802c05081c4d035000e08400300090300d015014040d841030600004062035000146001d1600403039001d25400b038241d42c50f00e0700c60070600002d80707418101541e80e41d80070080001d0f01d480411500c0c0c004c0200c81c1002d070641d01200c00060005601420181059006004483c0aa543e0f2400c59400005039500018102c082e1302c0800c04021600c0f444544071000454440c103d0a4046942d410841c400c4070543c50100c104020081040a030800141038482c5010218801c0230718000c041801401c142080d42c00040107800d00341c40c28120001c0018000000718807600075503024041d0000410003400d0148001d040582400c01c0390040c403412300c80c0c480f0910b51984140c4c649038815200c4458000c001e00482500d81c1010399038010071840c40c141c1425524400204034803a005032140c040e03256844c51018100d00c010030020b900301a00c03811050003013007a80d400040c0c1d2145040f0040c02d854580f40031740301b48044000f059440c01240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 487222859 1250 487221609 487221643
    0x2215152c010f0c020f090408040f1a0304030507051207080a090603020c0a0809060d05090304060215191a030321010f030b0c0f090604030b0a0506040c08070c080f1b 72
    0x85841c0c0c0c10030350701d9080425520740614052038a00028540e483c0301d205080e0402d008900303110610222800034030944004090f43c2202a903644000c0342440c29110440003c02428804500003921500040034040c1c0280d0483d40105010004600254000c88044030420b07000201e0001c46900942088002d042c00c1c1021414010203007882e58840f074000c0d40c000d05c85200006d4a500703c0d62403005035800d004071000c0800040c5010109260350b0f511078003900c40544a4101c1031304a468072844658403406221000981260507650704d00e0207094000600d08510420320340c41707070582d10204098001e0081ca411450740d00550301c6402d109407441038020f8640d01590384010710200d60b103403e00c4c60304104070b880301940c0d400c1180c0c1c85102c80d001d95034000b03904c0a40054000103204004940600807000d080e020030403034403007504100440314410414004200c040d0000b4065601800102076454003401c060791503c1629000c3d16484d51103d00724150800128081c2d49001000b0840180b5640c441c00f4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 487224109 1250 487222859 487222937
    0x305010509132618031005130803090a1203021902060112110a030c0602060114090411120a060608070f050d03140d090b070c020f221515 60
    0x10444101003041803002d010490065104499040038012081480f0402141683c40e040c1c031074aa180c0140d489040d682c400d1042c440302c010214007600c07500780111800b110645031070300642c0d503119140c1c00041c0700d003035540101a01d68010a140d50013807134103a0752540e00103035120b5807a40003410311a1a0320b403c0046620030b00040c86000c4401040240c803e070085c03070b01c0072800403050004402c81d1080e00000d000381d4084100140454001920a050f524403500b402840000c901c140444c400c4100c502500e201c203c011481186d050071001108440315190588540c2001c80d03e450040e01c0d010b41c032440003644600004c200840000321403c1c0a8002140c07145501070f045d0300c0080ca142d02214000a07040c00000300380d620032103240d005551407a804010306806140c00e0a02070411451220103074011040c8003598000c6203031006030740e00003e20039001d500950250301241030051603140c140c0f84650205100c046004008040700e40002141039403501c03043c681c1e40820041c118002c141c07410104007145 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 487225359 1250 487224109 487224121
    0x405071e031a10031506020c011b06020909040b07020106050102010b0303040e0702070f1508150d081605060a0608190507051302121503010b030a11040b220b010305010509 75
    0x240321444a490928000c1074010700400c0c2002d0300a0341c142d4140d4040f4554003c1036040e078054200321705d89200e00241820031aa90b44007640c036003495000213400030304500910b0050710140d00e21a40c00600071031006003440c9024010403c501c00503181034072580c408008000401340c1c240a2000640801e00c0240460040381c40840d58070b000b640903211000c00c44000080758148200104002018098424404996281c0c02c2081d18000c54a2203000a900030340042c0c3c90340310300100c0f00c000740005410f13410001116166588940c114000072460b40d501c10420a012810400c28540500c260b140001907e518000e400b80c07400381003001100c00ca1594450a00203e24041000c00480d00244c40380500c500281004170001d10840b100c2007100340b0080c1c10b0000040c23280e0042c0e00c1d800c1c0d080d00200b00565038074040541e0768440100c001d0010341d04403141c070840d0800d034002d00705609019015104092084a85071a0701400c0d100c0e50150503514510400d8941c0c1c54010700e07005006c00d0300c4062442c10b180c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 487226609 1250 487225359 487225397
    0x12070b040302040b0f06030a050f06010908030a03110d15050301050a09020303070b090c0a06030b1306080c0609040b040c08071d06040605130305011d011506021f110d0b040507 77
    0x1848041c3c407039951141111116200c840000c2d2000c080180601e41d68030701541c40c04002c0c070041d121010300e10028400224154091602d04081e110310000031810481c24200881c00340a8000415806c01010b108000080f2864000e82c08941100707480b2a0b002800c0105040c00c541d4014241c0d210541041e43c40f1025131000700c01c40e4812780d0030061085859136200e0f90741c2d1508021440454010703089510004140d6030683c40384900c2c0b0340841e01764605201401c80003040d00d5183c02451200c0d00030041c660300a1600030020803072140007800c080743c2d07031f4141c50010701214003100b5241c01081840341001075940d405590610b06e2001a1008044100150045600d41c062400b482d001d1150000701050304420403088240156804402804407000100e4106c5080b114007000001c00d41c20710702c42030b00101601038035009441180d4000c101c0400d1581c0e2440d0300741814840340300b449035074030000303407122403000001c003507001e0b0b20700003c998207510b0014030003258801403100080003912030312043c1512407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 487227859 1250 487226609 487226617
    0x111e03100f0e06060f0d05070b0d0204030204050f042102240609010f0f03030c030e2e05030411010f050c16150309030210053d050111070605031017010b12070b 70
    0x800e9445020072010f500d80079140820325004011038840c00304ac0c40c81681b9240d002081a00c0c0b082e5818000380c0c88980302110002c0c0191802414800c00c41c0f003104100b054107032071502d080d000744110381154041c0810400721403083c03400c0d02801b40445003002101d0400758091401861980403410341c140c0307000d44000a501c201d000040400c0040080b443c180740c4501140103809400400c0c00403411000c0740c601a828031040300252a030391003100c229000070b0042c400e403840b454001c440c00560180c0f0030011a42c0032103900350101444400d00c02614500710800042c0c441d0001c000e81414100e04080b00c124510041c00a107208240c144002100000d50200c0c4240007c2808100804c1310b80f100c0001803503401440c424500340b82c8084106d144444a2403040e069911001c610000c036a60b12240115100310002802c0c400c3c41d80602401c00506100d40b0045500480003030781c1d051581c0d02c43c0ae21900130801c1c0d42c50412269100d0320140d903c0c0c644100e100c420007401000400080e031500540e4009402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 487229109 1250 487227859 487227889
    0xb070b0c16020612071b08030112020607050d03090b06100e0f0411070309052704150603060612050706110a140307021804060b01030207111e03100f0e0606 68
    0x600864110308056400c1042080c059000b00200e860301c030084c00c014441a011581c900024091001c0d403a81006114a40341b021508840418690f070308102d01c4601c0790b41002400c9801440800840b408a001441102d5044d401ca0380c003c240c4116904091a02d4100604154411440c3d001950702a640041444040c030f030741038800504042811000078001c0c00c002c111038078501000030f511410103600074004c4003500d50454403039402d01540b41d001d05482c0035000144c04940b5000010501046819000c80400c864070030000c035000303481c0c0e518441a14002c1e4441508030500788045000c0000501807440a4116803401ca0300c1000000c58040e91001c00c944068041240d4440d19501c541d003d01c129000f194006d04441070940009000380140d04c01100c0540380740d8030f8800c0c001e00c2076101c0d0003129109900500309140b03110140080041003032904442a2070041c21407041c0303007213441c1031002006041060707000260b80c1ca561050f40d81601e000b6141281950441d000b00b000036980e007480c0c0ba0700a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 487230215 1106 487229109 487229131
    0xa090501120b1503041b090e01140f01140103020f0406180602121b16030602180910120311010203090307030914130f0204031403030f010b070b 63
    0x40d0b01c074000070340c1c0f1200040c9030710700d09101d1802031a0000d0142280004c40f10f200b400003040181070b035010f2805252507802c5e80c61071310401c0c8240244811031500d6403140d0b262030000c1040004050107046540b030852221101e4592180e4140d039400c0c0c10181403240e59944981016101001c4107550780349920039180c011801c00c0c404101d0120616500301c0d010704042e41760012805400d0a0807190701d4a1154288a200021114a58200440c09440e005941d00c0149045807200800b18001501641c000380a018900800c0f03000381c01159244000d40300c8204291508480c0c0c0200015070290960021041c80750100c030110003045010f02c251a035104a0342c0e071f135509514007070807459001d5000c00304092038045859031f078025450f400c1c4140001407901d500c984c0c524803a8840007958040365070000c8208039114840c2c3d400a805031941c004e920b4205880e59440d011201d10052841c42c1d14 = true := by decide +kernel

theorem cover : BRFrame.Cov 487050359 487230215 := by
  have h0 := BRFrame.cov_init 487050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 487050359 ≤ n) (h2 : n < 487230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
