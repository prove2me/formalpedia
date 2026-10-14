-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0999
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:44:22.348036+00:00
-- url     : https://prove2.me/submissions/49fa7989-4c1f-4396-8643-408c694fad9c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 179496402 ≤ n < 179676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 179497652 1250 179496402 179496407
    0x10050108060604020a1b060e0a240b010e0f040b030a0302250e07050f0d0c0c0b0f061c0c0807030305130f0b04030204091a010902070b0a0e0c2202030f0604051006 71
    0xc44169a0083c1d01c00c062507803003489069004108100c0c8c2c01026640c10102c2d0380303403410560b80866180100c8851000001d00c00003018030404414100503150000500c00590400c419400042d45d85504142c6403071402d90b158608102d5064468401c1d0082c2c101409138158082c80007020384507144860340c801070b0411414070720b180e04a402c10100c0c03400669605102d000240310380300d00d0220b19141864107501c60b0100d54010b80e0000c03000c1c07107208141c0241c3c540c2d040c00c0b1803640017580c1240c0d10420700503030703602900200c0c500510703040e00c01e4000f020000e65500440d41401e145034019008140f00040c00d04840040f200000c002e44100082c0540070b504003003e1104a0090707000080c0501d6070381d40300d0360902554244c202c03010102d6100d40c00040d030f11402c651019400440c4200d8480c03000c0310214040b080240a460590741148004044005c540310400155044c5003690025480700795a20742c0304c150b00e03800214071402406240b1b07443e60a0000a000071114014403480301c1e0030141d1030a010055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 179498902 1250 179497652 179497667
    0xa110a021528051b0109050316021302031e0f010b040504020d0b03010c0f030b0105070f020405100321090e04050616050c01020c0d0201060b0c06010b07031110050108060604020a 78
    0x185038455202c01121141c40c010071003010112601d0141c45402d007401d2540f01d002002080051540840c519808882007401d81d212104014485e8000340503245800c20b9041ea020309003400205542c80307602117540c1c204100d134070588030344401c0701d501205410b1810032003803025013040380c01380c0c0d06115614290381034a10380103a0090511480c1c001a02a681c40300380d42004c004503000a00802407815004005820085d0031b01074440428201040f45c1d840d0342c0608152005a6080700c103410401d1072503400c01009002c020400d90718005e4400700400841d5401404041d04034513084c15410032802c020300500104100c1e844824039207440b40c20000098004501a9040101c0400c500103410341c05506032800c0c00703100c8000401d076102081d09111a00005051307000701000ba0000c0043c56101e0094521f54451030000c1c10596000c2c40041100110800041220234003924214021a5184e04040c0c10440a18001590b035612040140000f403004e004031070b0064400c039011440d15100200103802c4a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 179500152 1250 179498902 179498929
    0x1814030a0f120b18040201140412060f090c0b030f01050a0b07060911060c0718020a05040608040305160809090c03150d0f050f0f010f1404061a04060603020a110a02 72
    0xb107070140d421100d441c81c82d080b400300210020940d581030b8440c0340d4046481c200440b403d0340020078459a40218006440840701500c8100c100b45480180a031070700c200ae0142c14001c624056075502021010440704c000324005481400811603503030070220303070390031541c003060304510b00c56450b0000070412080420129041e0729802134020070702031480c0c18003100c0310420101103a000f15000400805116010640005030f80302c29601d280720f1808900c00e502280940d11000e00421020041803205900410409038401e129103025490b007203108116085840552500315a13030380c0041030450403490020f032490303407144001d52018150b20300041100140b10351000329a00401c0080261002c1c015850200300c0302e280c00070304651071100001c0410380d4038500d20120b03100325441c1071544a103400c15402890004442d00030300d51055144d545418000740360507048a04011400111214981c0320b500568000700802c0c0c81c010788412300d0b03082c0070f4820a99810344203440e0b00325032102e5005070b40321420b03018030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 179501402 1250 179500152 179500157
    0x1260706050423030318090a05040c0b0c0705030a061407020a15020a17040b0f0f0405070303031a04090c05010e04050609011511010e0105160201050f0708090705041814030a0f 77
    0x32003854007800700030700e0b00f09521034144c0800030303052046081554400307808600940e0026242d40d10080080201c5e201510010102d07001040100b2850350303d8406031224019030800e0328100c5540f080040d140215520f0201c580944507003130741030310342108904140d101401e400034103440c080c80e074cc41c00b58405450243e078650700d03800324403040c506109450500e00d1800180e24021582000d040030740c1085012101148c4a2000d0000650131401c1130a0140c01540d0000c01890362609551f82540a4100480d850f500340550045401c6695540d01840220798081e604895105007480001414001c0864100f030195041000b40840380e2164822141100d01c506003400310041e030900100d40041000c003170354041e90308160811541ca079040d40002e0140550b060100701078904404141d090b40d40c1241c00800f46001c010000700c0d0b0600480340c1310307032082403441580c107842e48501c00134048403154542e03040f20080d50044a0200002c107a07a5400b000c1c940030040d820103000c104020400c0e840d00507003408 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 179502652 1250 179501402 179501429
    0x50a081f080102030f01030210093506041203050601210203040303060b0706020310060e0618060d0f0e0c03011104150309020d03030b280605030402030a0803012607060504 75
    0x128211582141001c1c00052009556030308046544024580f000e0100b82c3c4034044416200c030310700d4028034820040302d10308184c4c80d200801c1c0040d80e00c4a50f07141c3d072198070301c42c0d08210f03208030b180818011588501d101300d031304d02e090880b480030080072244000c2c0014140814030407040855007490421030a4151510b17400b47e0745c1d40e40e03881c00b00c0141580794000b00c85484046002800c01c00d064025520441070203441204076a0384040172a040f140e0311202c41c1d040300d420072240c840d00c1e07030041e040c1110702c80c060000b5240c4034200c035003030007250440c118810360283d840a5230b15441200b44400c040e100401c0f0002e2002006508441540348100c2c0f040d010110014481201014040c2d000404010380050940b241210682401307070251160120181c0302e030803819981d1054101800d452800513051503040c0c44440d04003681503889900140c001e81e07061040c0c8005400182840c0c0046010345180d941d2510325400600402c618040c540b100ca0005d6007021405101c1c140d0b011081e1011a6107503810800e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 179503902 1250 179502652 179502691
    0x60503071206020c0304080a082205280b13060225060f1806080105090f09071a131d0a06030b0a020d02090a0603050709170c010507030210140f07050a08 67
    0x3032a46c404c80c0d100c28464004c44807014280320440e0081c00c04080044945030840001c12181030450380c0318014a07a1100184220354200d002c007030312120201c40d9101d070b00b4202648034840500e003900040900007100c175008805000031581405005101841d9003203400c240700c0014a981190b01403030080504101c1040c0400d03000e01d02c038024804644182209603e901038844e88020010750007406081c0c01904a840802c9000e035048184512900d0000f025040c12400c0c0807464800b410030550703d01e8040c00c240104005d01c0100b40492000740006500140c0403820755070819038140d4020648600b45180c6541040440c680d03800240d4040040980140c2c0c0701d41600081e0000c1c09518410ba400400340d10003c641039801d40e000724003405594a5841c0d00300d036100013a403031190480c414030100b600562405940c550040e4050318480d4030a0040c6c904600c807800c580c43c1120481804002ea800b811000c1c4080f00b421500403d4010609140c506d181c2596a803000d003240300c0103000744680945041500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 179505152 1250 179503902 179503927
    0x40906051804030e0a1206090303050108031c0509070b0c0604020f1207061808061602010b030c010e060f0c1f05370e151902120106140d09060e0106050307120602 71
    0x1020305035014071303800c04540341d062150003802231034800c0300800d00c0c0100224409000100b80c4504003d01e911040742070048408450281c1030107005550117120310007010400e109920060400c09034940c00401d950300e45801040382011a07003070024020380742c6040e100b41c0031130041003400c1502d60604040340e03192400c0950813840004c903445071080b400782d00c00b40000d600c04a03880c441804060750080c010285003204054560b000c0c0c51f0b00300e000c0303140301e0010070850410744043c08008a0612229040140640546041c824103014442c102c0401c018071440100307051203059048000100324103080040e40c120300442080c96034400707a84c800c0c655154105207605030000040d01c4060802e85400403001102c03101c0221007520418030701100c44201e850502003d20999103d05070108038107290303906c0d0070700a80e0014001c6804d070348006000c200507040990a8002c84007254425040000c0c8110301c1607001d03003120340c20340045201ea004040d0400010704010000c0800a0b04070700300580d18445420030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 179506402 1250 179505152 179505169
    0x11390102120a0e040b09130b06040f0e06041a040206161704060c030e04050c0906070f0f1109100b031f090c020304060810050105041403030c0a0602040906051804030e 73
    0x1224045000003800d10b4a09910803000041520107850501100303940408100c1101812140b0b45c1a81040d0070042000c44c000032103891304040c01030300c0003801d55031445080e13080d24220356900340c1030350182c4280810850003a550043c1800e00c040d8240140c107141c1e0000e0b800d84104021510904d010265035020300000c41c20400803000cac48a40c042d030b42c0341d41d80d00c0604001c2c40000c1c00e0300818000b0751034400d642020b0055034030031031402e44c02c646082b108904203d01500400390640d201c0048080c60b40010b01c3e058540c04981d8050740101034410090710410403001001018048400c10344103042140c0c00325001a44d070080d103a04422070359041150801d40d5145500c3e40310301c5903181030104030810181c0101c0100b0540350180e880401d507a89040034000d2603501d40c4109400500b040204101250000b2114960074000400356490b02005d40c5080349805440c41c1c00745c0301c8030341c000f40c2042400c06901c21440144402da42540040250810a0f4140c507802040076092000c040c0c148100d9030707500441c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 179507652 1250 179506402 179506423
    0x10f0b0d181b050607080d050c1606060905130b060103230f060f120604080d0f1407110a0f020402090301060302060304051005060922030201020405030d11390102 71
    0x38403071001c500e0501c542d15141c0b501c00c1c40c0c142a40400046181d00300300e821a0305558200068500d8880071010760002010000c0c44248424018420502ca04802c0481c240c2454000c2c4408107400307041c0b0401204540000e03107140d0f034110052004400180b40d0b40490b550010007401c0c00a00704514000750050107079a040c001224004500420020440e1243c68030301034030b03050390f910394506401c01c14003d0001c924041e0119540c002800100040d507100002d1500000d46500459003084203809002030712515100c01c01d039442080d0401c50056032200c0396011003904d82d402401001101c1e180c02c04403201003180030f03000307a80004604410382c6094008000440d40a000590350389094180315884101a0302036150700380c2404046803091400e40f0041e401042481c940003c0b04800d8405040da4150a0b03804900b555020b002c0010303282e5081c049001c61103126140d60712175090754a0708900f008807910403200c80c10b520308103107403111005003072800720030f0780001d0f4094800b401c400050f860070460b8003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 179508902 1250 179507652 179507681
    0x15060d090305070b0a1e020703031803020f120f1e12010e0106090b030c1204050a0c0b1b070b190509090703020c0c0901061b0303140708040c0806010f0b0d 68
    0x403042010590b0090003080410702136112426a62140200380303060b42c010203c010032482c9030700005540041c0700e0340180b842c2442070400017440000d5802079405c3c40c00310780c0240c0250300401d5030100c04003828803441400d5449254001e25221a0800e403024a02420884017100000c445140b030546080f11b0480d00303440441e8100b241c442d03079109030b0046941c5090080800040141400003500c0c508502604d018200c005103450070540d02680c1d82e80d2142004200742c90921070403542c500403d00b002c89400142030300c0c8458a80d14405031240d00c00c07040e01c41c424643da9074040d40c13003000070080c2c0109a91641901450011009500340801c880500880700c400d41d0000c80c550600ca0100d070542d0090540c0018502035400c05034035442000030403102441000041059203495040b071640a200b465400352107401c0000e07a00482100c441c5003030008654440109010005110500042d00100c800412402005140d01c0d03041000041446010788502740f03c500d0003103120f1050341e0668002200180051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 179510152 1250 179508902 179508911
    0x6090405042303040f0b070204150308030a0c110604122105010303140903060109020d090605150102011415060d0f0f0b04050109090c180e0d09080105010608060915060d 74
    0x142400103000480b01540000107400041d42c82002c1404001d6408444404140d4251281341034000003560303001d118101ea0040e5154940c5c0050103190403000007441c001e140064403850283c892030100c800b440d48100510000b003104900c962f10001c0d44c5903000e60302040d4400810200d410a43e0000030041410504484045890784544159446941200d00a036280d40d460014a09075034090300c10740c2c0c070058042d00048018040c000d20340d002407a10b09206140040c59000944a0303200301d034000e40d0a1728090100045804181d030b8240140400a1580c0b00c0400701802c1403a0b6040080002400d04d6014040114111840500c07a6102c1c8100700c1e964002408400c0e4180640310042c10042210762042d840d003000800d01c003c003481204152980542011034040c20a1030311701e81d2601008a207107285031200001040440140103000040402d500c03404002401c0c20304860948a050b0415400c11050030100701c0b09035209402c2c107030400400084110403000b9080070079514401c0d5522a1901400d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 179511402 1250 179510152 179510161
    0x6090f05040b0118030b190501060807080403110a08090a0b030c0301030b1f0b0910020601060c030e19120507080318060c0a1b08100e0703020111030403020904060905010c08060102030d0b06090405 86
    0x103208004c0c8540c07e1141c0d0010f1140511102c501150706c280650800120502c001400450050641d0b80d0414002d05000013494820440640340c50942182295581c20204403d607035414407030503880280c80071030340150030340c9890b17200c80b00c2d58081440060441c660712400318900c01d00d100001100c40e220032282c1c88d20f0a4681c00d1404040e4481603e140c0500300034540c2e80d000901c04504203059561560701c840000029131011a02034038694020b942c8216500c051411000260a02ea40113051140340e0100b007410508001c1c1c01c203400c0d9440030318035400070009034039065154080c122061008642c035030346445c8079045580c41d00c8075003e00148580216140941d110a410707440c8011201c001c000c54685400d07a030114816183c000c4d42e15103103544031503418001980200c0c1c80d40421580c0c541180e040a940e500041c100328000e440940b140c6a0740c190a00c248402070080c1c4458240d5400c2900c0f203800e10b400002e40d03d01c00c03150031440f211f07a20b0000000f159109421160b03100401007050146d401c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 179512652 1250 179511402 179511413
    0xf26060408222304290109090c020606030f06010b0a03050901090b0903180a05031005091f09023c040207021f0813120302030a02090d0302010c030606090f05040b011803 74
    0x7011000c00d881480080c0000d071400b4065030041715640b9003000d010161260354029100e24442010b030602402007000700b00304e2141d00c101c0c0202d4013039500610141c01c01e50306242c10f00704100700c006800d80100006104c103c0268040740c5240445240004a40e50b0b0240c4040c018844058001c1450070f02e4424400810800405091824070700f10f0ba02100c15201030400225203400e10a10b601508409903d115080f015408a0b9012642405640c80c02da1847c0320310700a800100483c2c00080e0361441c10006508150482c031981c9120059844016071801e84d2500d03520042c01d00a40419254441414140c0c85a40548032290307805051020b22083c0d00741c4d0074a04114a01110780003882010015070394110003800751900710b811a100710072000c00850201e010f5400240200a41902007081400640718442c1103039070b84d806507000148011500c1c00081c1907480952101041044010051002c0358549103485e003158800c0340c0014241c4820801079440181c1c88028049510040c1400410b004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 179513902 1250 179512652 179512679
    0xc0201030b090403121523040b09040c0603050106050301141207080102070f06140606030c031003080a05180103050601020d030f09020d1b050102190f05070e010f2606040822 76
    0x300144001c1c401241c216651b608101110311450005014000ca400c40a0743c40720040c040400b07000d03001280c0d500b184004541c0c090011340d001c9504080c4030a080214a03418482c0c076014041c149040c500d19494001c0c0034600309126865544180c59440d452410400d0801040f070092441f640250b40341c4816082000081c001d030794084c3c07551414014881c1000c4c0b1350f404c0240c4604030081c9043e0031034032075001e40c0300280c01c014050200c1501c05000070022980c0b041c0900324007031490780ca0580d240c191240e0104e42c0880044018181400c241c2440f0181e83c003ca8003540324900c924000940038581d401c3c02c4064100c051000c0d4005e0a0354540d00140504100c0c8400d040c0c015000202c912940c4200490356010504000b40c40130a80c500c001c00000c2d41440f123140390324000c80c211650251101712001c5260000c5c1e01100b0000d50381c0008120340d40d009403021440000c2020381440700c400e131085068442c039000303100421044000a4070307450401c0071184091084e4000b606203035220f4442c8418032140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 179515152 1250 179513902 179513927
    0x160801061a092103071505040629010f180f06021227030a0b0705090f01080405030403080333090a0e1e1f0c0f020604050d0c0201030b090403 62
    0x620150903441c20008102c0d19011000b81c200c0d5601540c00b503182441c90203401d02c41469001c10030940c004144108460700846da486040002c0c00c0c1803e141c020225034140f0300d200380350001e450b0909140c0c07101a850443d200d0b404e0034100c0803480036407801c483c41e080da22380040c081c00783d0020202d11301c041441d01d00d00303680854080700d24080550001c00a240120024688021140d840300d07c001903407014048000303040502292000c400c0d075541e00054403812180180014808a002d00461038141d402d2880350000782071180507801c0944550740c5910460102401c0c44ca0004046070182d42c09104ca0031507007070319044207100b400d940302152110380e840c1c0da880381c410040c01c40030459503400d80c0302e03950120710317041d00500c2c1510400509600d5045054180c02c400e00804914951520300c1c040e0b2005100b1080350009000159442d002e001d1464104c1044d0440d805402000001130f000203869164440600f410980c2c140e41344012009011003e0326140c1115540e014081019001048038001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 179516402 1250 179515152 179515169
    0x10030605070516080a050705010f1a0604030506180c090406020307030c03020301140103050601020102091c170a020a061a12160b2508070204060b0304030e01020610150216080106 78
    0x1921010700031601802101c01c010000500019000d000881d40d0009260401c0582800d50a080440c0c03034940c211107100d0031250751aa11807014030003000285c403000c0300c000400c8030310790b060a095803240e47e42c900008000c104038201c0707048001040302040261140d0400c0080214105181c01d141030800b039002600d25101007400e0000460040d4040d00a482c181e0300e01c440c0d880d201c2c0030365600440140c40050300160540d5803c10401106858101110005051000300c175802c603551842c0000c81140f42000110b0a000d05002e10441a5400b2880c4c4201d1500090301142ea0343d60012000541000c2e140a07a600c1100212402e181007004203110904004000c443e0345002d07074800720000f0900c144198143c280c0343e010410701020840000410050b07000c0c1d4035140c01d0060307a0307020804440c016045400c01400200c2004101a440040d881305241c087c406841c0300c1c18a12038114481d94540240c0b10a0342150005903d414820004101f0a010034010300060590b10800107000340001e0046c42071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 179517652 1250 179516402 179516411
    0x7080a08060405040210051b1b1e0f060c010b031b010f080103022803020406090b03060a1e050c07020406090519021305040905030c01060315140f0604050618100306 72
    0x76141c544140761040f90060b240484200140d5400c07649a48200103a100b0421051045100c2960800444600701c1c0d00c400c0c5690304004000401190008900c000c0c108005411205040c40c1c8454207690303094001682c2c0e40c2c1c0c81e0001c810340f10340500008010150503100e04901c408003031102212100c4850000c0c3c90b92441080f09a10460306c2640900010b50000c80326a0702071a2020769103002d080d008a030002220308280c0301d034000750948400360710041c01c10f81c84400c9200070380350501504d40c120407603400800804007011120b10b9505a059070080c000c5a65500040000315181c00f00c6031603030b070f00038010080b060b110002d00c1b0007040103881401d48515800c2c001100f240e034078402c890317001184617501d60402c0d14181c100800760445c60400c4a040c041440200340c513500c240294409184038182c064254114202d01740100e48c04401c0011280c01164280301c00000036500b0301d90061400d440c003040075a61100030034101a80500c0b040c400c030181c20100200c2a00d030b5441c140650340320303c0c0240b2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 179518902 1250 179517652 179517661
    0xc1902100309050a0323070c0305010b01050705072916050f0111070b0c070206070b0f06060a0c03080705090a030b0103050607020d0f0c050703140102030414120405060d1107080a08 79
    0x8040300c4881c1c400a10960058200c040444d00903007041c40c0000031240c41000040c400c1b0300004540d00021003c540e40110200c0900800c1428010880c0c1c005083c6409802c020340341c3c44050303903005a8450401150000a81c44e035850039500038041c10703075880e0310610f07603160149491615046040c0710192110f0040c0c542142c01544127000724068502c0365002e43d81001602e880d83c01d07682c03c014003203c2240c2030400c804030050300c815019003021406010b207024140381c03024a00080070802402940700d040c0030409054610b400c5108013980c1d90301407810700d000c0c2d074502c08103403454481e091426521002144002040108490001e4140c03031042d0190b4a1a80300c214041c0d07541c0f065400030784081100d40500c801458440c1d2070801d5294003d4084076500b0380c0c2c940f42c1022084181d460344466940020030041030000015811411420710030040803640c04e041d0365140203000b1401418410031001400010010903600808602004c841441d0b07601c80c05860300842030b03030100c10b000700820044000034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 179520152 1250 179518902 179518907
    0xc061401121506061706030106030f050d1b0c03060e01091401090c051903031101020f0313120c0506061003021c140108030a050f1b1b010908030c0c010e060c190210 72
    0x118200c48460b12080111003c0324001405d2040080c01c1981566860000102103440c0c00980c100c1180507101130920b00c4440e06004000c0c140c80741400d0706607100c0510010001328141040b004980e08810006041d80c88a001c2e00e024242c8a10050302c1040c104200d251100c8040d442081c865200301c0012014070f58a0091100b150b41e50031614507407469803174040003c68051407480b259501d420000500d046a10306000d240380d001039460540440740302c02c42d0401c00050440700b064001290070041c2d6810282c1c0e451503075820008190501035035210150f400854003d406840d0f509070032112088100114526500007480350700b011501d2800d003030340000788940d004800c407428524140d03115450107500051aa010358001407001707103a0310072440708071603041c4240b041341d01d100a100000d02a51000300c0004103410015001034855400404c0000560a400220549484800c0c00d2880d038454100c1c001031b84034011303c82140c4e030a002e00311464009068203ca01a0101d1080300c0359144d280024904 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 179521402 1250 179520152 179520161
    0x3010b0604050603070c0606090203061201050603060412051c0b0307050105040b030c0a2001050f090c0918070b0f0705070b07030c02040519090501090c150206070c0614011215 77
    0x515030403803410481401182026401543e2000c09410300d11940c041545e64002240c0180c0d1212142c0c90f80070003444240d00d40030803008654443d0100070300c650f003411030009803140c00181c40200f20144008060100d54054400c3c0d0380900841c1030104800c0c580b80c00c1e82001790072420344082c405d0140441c0480c0315030046007a40c0640d82c102c0d0a880c00c550302c0350304011155010010041c240301456034502c00102000340b50140010641c400490f0070304008103141c0e9540385c0a0303c801810307040b900c5191040c3e2903421200d81c0c010009403092151400390081e0b01d040c1300ca550464800d010002074040074000230b1030010300c8814800d000315401a550b910010659010311040180005c140e035030030801502d800d402064106030300800441d03c0070148207605080303030043d80048031165107541d004028820b640c050764000702140c80a070085501e020304000e40300d0700010001414003007203180c100240585503104000001c047d141500055840e1401c1c0c80c0c00344d41c400412900f14000100a40400300c0c5800b9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 179522652 1250 179521402 179521421
    0x6090e0303130b06011e050c15060d03030209040f020a2007030c090b010212030106120b06031608040309030501110706240b0a021015080d0801140105031f0b0a02010b0301 75
    0x8403500000b040d0380d03030740003030100c0580314604010405404c00040303522103946500c3c900701c0e5191144c0e41c50508841504291007101864070268840701007040d141c81d2824500c2686605148c0140c0d00d0390755200103001004426000d60740c42d880841c403c0a8107401c01006c15180c1c100002c0040400c00c1d41c007400e60b69025070b000080c08034001c2c000c20424030200d81c101d1401042c0500544a4515201c0300f450071907002640300c140001c1ca070b0400f65100f90090f00c90303003008007415078490b407031850070800709221542d070801c0100070031400500040a25220302d11450186030b1000080c044846074403d40e40d1983c10a0748180d070014907080702105001c08189000b0141428140ca140703010b8508440c0541c03c1e04590040800e6014000aa0110941c0d9103d0324680381800b4003100c820750304060095242c0384041d9100c40501110390018001089815603c12606000340703401a0b603950f408502e2180c001440f090f0440501c0d25403408a907a00031000a07101c81d40159000b0021100c0401c101420b9526048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 179523902 1250 179522652 179522671
    0x6090612020a080109080d0c02030903161a090d03081915030201110c030616020f01050903070c050a0b032a03040609060509070f0b0c030910030b0901151209061e06090e0303 76
    0x1c0043c1f403501080c0c02c6040da007205070040e00e0a00e089007000c00c1c00c090841c1010700f45400001002e10801c54440041a00d105103010164100f03401c40c004168161041c00c0c000d800e00485400003181c054581e1b049481c007c6220340203000842c440402240880f01d035000c12800305112404080b03034201c0001e4000100e010082c01000740b500d0380007204400700190800341c0d0440c01080d04280941d07000340507541c05284d14500843c1d40302d00e1401d000c550b03240d0540011b0701c0340b400c40a04220012040d030039203800c00c0c642c0280b030b43c1c007000c0208152606601001072120101000c810003007804810741c0104e9449004400501c42075591610898880080c1e000c1c042c102c0c80c3e1140240000310122002c2c01c0c400d5030f41d41c112454010f074900010002920200d039400040d44035102078030342d410404480340c014144000c0c08140051f0300d100c00f800d1206402045000103545075000340c22b100e015003005030b4548540e0041c4041d88582e02101d400781c00341d8081c020b040c500302030890b0000940001201d100c1c003010b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 179525152 1250 179523902 179523907
    0x2030906040213020d020403030905091303140c031306020a0c05040b01020a080c0312041412030615090a05102d0c0f050a020310020a110d0e060d06090612020a08010908 74
    0x690070030118040350029480011341c24001000031492a00c0100040d500a132290040c641ca4102004034916004241d0b1010195518004000a82080692010b040e110480a0702c0304403005e070141c0386026000c3c22100441103810001511a0049a003007140740c0207200006007280c80340d0900c4150f4500240c1e40f40182e01c84142a00410900b00161125850701c1c0f003640d250212000c000c112000060742c0c01d80b41e42c04040c2c0c2c46849204100554003d02800741445801c0d071030000000350b040480c803007450783c01c21030002c0c2000300c5503110041080030f080000c14450030348203110001007805501c01c0c03a1103800700760f00012166071f00400c2c841000101540c1c1d250149412195560031504130042070460f01d41c41070826560040e80d09110803805219041001621240648401800f800150b850035045400c44503001c586142d0200700c17000c4000060707822542e2000c800e1143c00080ca21a8000d0f0482d038513110010071142ca03c600351001c01402201c00110040e1114515400c0720040c0d14010000d0031b04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 179526402 1250 179525152 179525161
    0x70e030616230403080414030f010c0906110a0506010906080d020a0816020a0b04090504021008062d041503030215010f050d030c0f0c0302151c0b0d1b051302030906 72
    0x3000900181010440d102803c041d40c1c0d0b5100e9105030072035004000c1300e407000d0b00c94141c0307410f00f0010342c100b0040e0b4000034030091141980c05400e1040c135000b404100417200071a9586482c082210994091340036003201d410750b9454614a00400341d40c000c0310010300030305403503420303181c400110700741030f1038110810600c0c04185200d5400d04074080c4800b01d812003c042c1c1c00140101d121405003004110400c0e002ca1a860f003031040000c500b181074001802c2c40301c59400d100d0305869111755010450420310005030450201c00810000a6a0542c5554481d003059209010307000f030720410a080b00d109400302c54400c0000da1009400d85824011456820051102042a450152808103a0b14080c2c00d01c0ca0010340540c4035400345808a10040d100011808820011400d194441600148a6401032814078001d001400c103421900c24480402c0c94130b43c141da06403583c5603001a0b4007030750f2045001f100489001c7caa0280e0314801d22800d445400d40d040030003400072060003102d00c034050782005416256903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 179527652 1250 179526402 179526437
    0x102060109200d09020607050109111f0f1206080a0c06020303010803031306020906070b040b06150d0b0a0b0415020f06070c0318090f06050a050d0f0b09100203070e030616 75
    0x40c0748040e12640d1140030500242c3c0390800141f52444c0030b0000815260980c0c100ba02840c2d2a000480380a5520002004083c1c004440090074025051510758041003000070111f50034800c1580e941c22031ba182030000507200c100041c010007454429181215040d03510300090b612400244100040c036001000098142020f0702c00c008000ca00c9410010300300341c00d00010440a403c10b40c0c00311482d000c1d00003884144203400040c1c1c0d900001c00c2700c5140800f146000e1007585402a0500700071000e48802c42070041e5070f500c3c1c4040010300030303281c1d8040d1075030382d9041200d030715950b1000840054021085030105800340400c41c50300c15866606d40c803400c0e00f91642c1c200c070301103859024403003025210800452004000e01410184045540c0f000c40c081e8142402c00801d00d07002e03407280e40304450550034580051001c111000e4019040311041c0407a5585010306400d0010107140c0c204010310004c01c11020300c0d00840b000150b00003d4046580d04e0703641d014044e0000e83c02c1c021400103d84900405402c603070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 179528902 1250 179527652 179527657
    0x12020f03030a0807141306030f0b090705040b0f0405121c0f0905060f0d0e2503170702132406050c1002090103020c0f01020306040c09121203090f05010b010206010920 73
    0x200c0c403154841c0740c407203414101000046c0700d8021000081c0c48104291284c481c902904566103022501d41c103d03400c0100c001f0304580308901c070300c10340c005000c241e41c0002e520303890541e030040c40050034040c60f100181803065161070781588080843c9004440c01409544120b0814000e18000d8813424460713410701040103d1900403c94400f03000c942004000e08003451401142410707501d090043c1034840c501c4d10300f43c120201415002c1c1281000100c03c2002c158440c4290382001c1c50412034030354829031800815017100d000c800ca85412800c0c08207001000ba12512201035602410800703460300f031b031540012195803140d07070381c0045298400c000040052030698002c00c010380c01410b005103020300c2000110704080805258610a03503010080081030306050042c9481c017412440c151042c18206615035240400056010748418030344030b002e64442c2d020707500c881c3c1001c0d000b0200482205091900d240a01580903070b01e40117008920001079003100600409a0848409040c519072103220010745140c0c1c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 179530152 1250 179528902 179528927
    0x80916140a0819030201061a030c07080405060307080901061a0d05101206060e070e0d06021c060e07020c030c01020a110303070c0e090105010b120c030a110412020f03030a0807 77
    0x11039001c0000d040041040b45211507840314000d940c06064070b040203070841d0300304e920280c2e0705a40e44914a040c008080e0450354054078030718180e82c9a07601420050158042e64112507001000041440942904a0855031040c040071009101c000c4c0c07a041c10f07100d044041c0032126200641417203204200c40094009943c010110700141d594250f48445090b4543e007034480136680719175039803020b012501015603601d50100d02400c240710781c010440041034054262404c090305540e8003156042c0402c4440c03403919075860f040b00c0f06001040d00d0b4040d502c200c0f8030a07541343c1c02601c01c43c107148140e030801095801800105030083d10540c00d2a40f0748e1200141d44e5810203606020400c401c200040c5141d00c800043d05100c0b02c08986441c00403c890308598060300000342940040c095107002e9002003048030361090411131800d80704c3e20384910035006005422804032840d5400300300807540c5200801c0b12000180225130f00d0f40701c07166800a241d00e078032401c0f010900140208000607111030281e41c0120341c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 179531402 1250 179530152 179530159
    0x906080a0320120f09010809011815020c0303190f050606160807050d02060915010503060a020906071718040504080306060c0f011532010e1c060504020108091614 71
    0x42d03815401c03c5052640c00f0300043c2d401900045154001d550380301d40e40c2c50f444035030300008001d840700b07803400344401807a412001040341c111102c0d00b9032070300087d40541c0c40040751401100c0d124100400107110348012040400001c03490081211003070812030003401c1c0144000303001c403440c01c8126501503003030115070201698074070000c004480019604001010160009a000d45030500340100c14030304001080c458100c8007210f420040c480c59034041400c0b0b80140c0d0894006985204440c00300d5828014141c000d4400c000ba20380204400388558003c2403018200f642c1d050720004000c04000803500300b60350140600d00280002a4a410500002d02c103003900c01084880da0f840c0451a41d00350354600c0081240008488010401039181c411001e117001d00b50324114065901103081480c2d0b401915402504000b440b82d042c40b0706840b0b40111544901040310454001c0990707040c040041e01003510b049001607920300c0001c42408006c62754076002c0e61520550b4032040c1c0750410144e21a440014030a92 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 179532652 1250 179531402 179531413
    0x315020c07120203010b011d010e011b060906050c070f0204091106040308040305070501030902061812100203060a05100504030602030a020f04080a0b0a02041a0d06030501050702070906080a0320 85
    0x44480d010400c4a0003440090002d1810182a20606003500c034410f200a05126100548001103042d036640703951941420300c0c00c99640da4038500103d031901004000c0c0c0440b4100810b0000a001c0c950700030700040360181c80e00740f115845a407648006445030f80c0d00035180303245446c000d000501d01340d0000e1080d14040c1d601e01034140038810000300d860b401179004640b444c01c002820001c00500784160700040c0380909041091040c140c0118000e0702c10103422a408035492741c04021165034000101180451200881d07401e0051004040d000f540700f516024401ca001c0d034800142440c0400008401d042076513101420a8a15540d05002e0340003c0c101c242041d4082c4041307030601001c60081c20080200e0002800b4421442c1412900a071001c5e2045c09000e00410091140d404d0b80c9165100780400d4224296854a600c1c003100000c00581c1c200030020350030101070021081d4002840c20640d01c684030b08000d0561354952103980c80201c03401c024080b5070119070750850101041d800720320700182c80b4107848 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 179533902 1250 179532652 179532667
    0xd02010305180d0c030e06030105060304020d03030603080c0705031203010b0f0c030c030a090303030c03140105060f190f1202070519050c090a02041a030118180f030c021e0a031502 79
    0x3820081c3c0d801a02000a25144404e01459800618444091410f9401130b181d5410324001c40d6043c80000e10180c06034000c203a00c1001c261082e88000000d5410143e8242c03280401c0328607544440c0c035482891f00c01d00c11049240d4400303e600044904a5410403156842c05c1c8800f0901d8429400800301c00d4014001405038000480c401e0006100c200c54070760ba1400710382c0c11440d01a0840b001c040c0801d0405241040d042440315240c5012415100d00b15003480c0c90701c43c0e005000c0214400c1d8a900030801d0711444241a0305a00002c0100311900715480c0c03036969070310b450304a408034021440090010351000164032405a4100c2300c4000c1c42e40614150f405400b0b0180105206540685030b090b41070b54001000c10100c0400f5044001c024076141200d459945460320007800903c0d01c95070400c855580f0380d40c0c00d42030191801d9000e521644450845100c04050901410140e103070041a4055442038404040155155041164030f00c001040b2101035811600d440a125a4040b41910015030801801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 179535152 1250 179533902 179533951
    0x301092a0c03091814012c13061b030b0108070e09060a050d050d020708070311060a0908160317030105030d081b040906140d0f0f0c0b0a1d0f0d02010305 67
    0x59030807100301c440208040900028803985c0c1501640312550640c2c181241e0091002c2c207154040d008074428010007150344503c41c1010000303103103400013000b4502e0240f01c1104445084c20401000540351820410390380984015a04034000310f4100c00059511140c40243d85001c1035003075000070010344455060394669001c1483e000c1542c17411303205a40070446200b050f6a040024201415007007010707000f820300d190340b420401c48121020300e22136500412041592481003d06000a208450440d00c0000c1800304c0ca01c524441804183e42a1078000441d0007030b00006000c480c100c600182c000c05c00b0f544401d50482d0b041c84003520085400204010a040417030012001c3e0029045442002030080d140c0108009050018249180502e11164440300803440c0c24030a400c003140c009510b100c8074072032441c1c255415911a08021006c0c00c0100d00e1500d0b99622031b100c10300c0c4100300e04030b10401c45480010030181103d44505075500150b001c8540c070055100342c02080d00061108140d00c1c00c0160076564 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 179536402 1250 179535152 179535179
    0x380d0504030201090215041a0c010f060b040303081018020a110607110f07060e06030405010f06030807031b0c1e030c17060f070c060902180a020301092a0c0309 70
    0x3074006039124006907096151222000b0070808031100f160345007e10700302c42d9a06100c52039090f500407440216405030301020a40280102005401080240c82d4407010802c1e00d40c0c1140c001600040d4a940028a00c10215016503094604801c1462080e410900d200000ba511442c550340800c03805800341c007086c1700200040e9004038015284c3c103220150a4107040e2800d010303038180503619402071000700314458110b51810322001054942076600d40e52828100d015103414440c54025a151442c0042400410310281c48580e102c2d45d90b1400c2003040264640f000c400c6d941c009450403041a2080207603824007000f14038100c06004c3d9224180d952500d0f40d030074105a9601803680040900d0302c4036180842440b800f9440000c0c3c898240042c200900018600300e410007004190644e1a4a904199603551044907401060044003c03194038198425001075007007071141444031410300a00a4500c08961500702c10900c045040d620700c4003241030116403201c0d80d180160284442c40a0108107990756016 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 179537652 1250 179536402 179536411
    0x2100f06091808031f08030f0405010e01050c120d0b0303040f0603110301120f0c03050628020901081b0702060a0507021804050a030f0918060807380d05 67
    0x40000d940d601d41039103201910290103003620604907030b40010b40000c45000c203a940080002914014428101c20620401071058004440c24880419160b14065090b4003c20654100381d1300c0c13111082500340150b40c14090980c0c079100f0343d0007807414162040010000307880a13011803100803421107044008a42503a00070f80210a040456110903c0004e4260103074100c01080d080c602840c42d850950010f4000c2005200203100ca040000e8560030f1000c00e10422000c1c640010a4420030704003200302104901c2d84a200d18118100e0740c44051315030506100392a421141a1281c0c1d9440d85d44116145008001c0b07081c102c150542800000d000d0386403140680004200c1c1d4031082e1b0f550445004100d5503100003410015404a0070b410080043c03000b05030118940ea050400109406031454160340010a642088081c0d040c40810145003401c5a0070250845040b0300030b07245140c0c0c550082c011090f00e003101004011848203403020000300c280030390007403040f030000c1d9a50070040d140c141002620360070b48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 179538902 1250 179537652 179537681
    0x6230f090c03341d0d0506151f180614040e06040608030a12050f060a0e07031d0a02011106010f05120304150c0b090a03020c12190b1006020304081209010210 69
    0x10009183c1c0c4c0185445070300b09090403140048010500e60f65269a618010b001c4403040d03d4840c541140380d10341c1c000d0310407000881c095801e40174901001c010700d44080f48000c52641441c90300d00041c3c80c0e0040b0503d03400310014217411881c160a00d0408428050b0141403070307800580e034400001e1502d5050003e080c0000b2070b6036403203a00c0d1407500f06800036036070054407060410880505103c6a0359a180010003112402c644070001ea540b054000d5004011440d1070759110301c1581c400c02c2408102080c886250f40c801d88820b082607800d40c05150340c07032400740110355980e03d440d9400d21040c60300145000303c0c0780321842160b10303182d102c00450b544070a42c5802c40001c03c4c0e24125090821008080d211f920043d1900100205415501c00944c2c403191050540c0c0105040e8404400c109000d200c130380d150044400803986021000e1800d10705481084a80841c01c000030400402c0441c4080700325000c0303403544001481515044a2860950b0780841c043d00d05521415030307900e849503020f004a148070003800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 179540152 1250 179538902 179538917
    0xc0501030e0c04090615060e1305040206090901030b09280305030c0712030203060a0905100506030c040302040e0a0302190b0109050c1204060902120d080103120306230f090c0334 78
    0x1b00600c00200080d0043c00a010440d11902d6043c2c5440200540000301c40c100858151564000716081e44034140d070554003c1d80070340002c002d00100300d014038020102281124040703031180c0078070b2414500507a04212502401c3c680b00300400d1140018540008071084580c1c6002c2e40c6941da0759002e101c407038132034000c681c000c0200042c3d8505040d224008100c480c030144007903d400ba0018030300c8030f40b500445114101c00310125841045441c15038003d50b6000d2710030829040c07640a510f40d070381c00914007100184101e078500c1c41d25106400c210551079034030150981d800d034203028100d0302401008040a400c650284a820601e8603889c44180c02580941d00c0050101c240340140103030203c500784110403961001c20400703201c0764402a030324112030300b2040d201c00c001c0312000c1c124080d003080d9201400418800701e40c2544031808516a80d5038441c12541d0f00084030821302803007002d00044a0074030087d9800d03c0028211045801181640300b1540314402d408030300302e03001c010781d0701d03c0c2c006540014042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 179541402 1250 179540152 179540171
    0x4051501030f0c05040c020c040c030e010c02031803010605010f0e131107060609020306060a0302130305120c100b06030c070201140c010621080403030c06151517040c0501030e0c040906 81
    0x43c040300e82d015210554050064601c00c1030003070354480f011490140200d03a1100700e00a41d600c290700203040314610b44c009003e03941d040e80000b5684d820445214007543d0070150a903015240503c9107808543c01038450b580d880a1000042c1d03411000368002a8101c4040340550181c119140700d40b04620308070b981c99a072500c000341001000c07925148c0100110030b1040013070000301e036103940680d28803001e039140150703503400d814030080c584010940c0b0080c02c034030401d98604510700c40d050142a8250340c00080300c1c1f04280c1041540180c6002072400e541003601000410400c606200007003e400780103040242d080146691545000e0340948140300d23041c0d554071001c0c4000320b03001c080720392507181d1a1000006000c007912404014031440c44001c0910804401003410020180c104862035028000c06441d8150795103c01d200d03c19044252600007425a44025460259108c3c00ba006a401070320120a290030070700190001e000380806441e5500c18507034119070981e10303030143c08011882511b004c50100030f07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 179542652 1250 179541402 179541413
    0x406050f010e01081b0316020609060114120115091b0504050d0b060613030627211b03020109030e1801031e05010f020c070b120a05070905060c0604020a060509150304051501030f 78
    0x2701500014458200c00010443c00290324940400d0b5082221700d01036506048035482e0051414001401e1146803540000400c9403071503001543c2e1107154001400040071610f001c4038584205c0c0513581c1d10184e41c030501d00215031131200160340301c440500030900e4041c1d036403202000140c02c5d5204a5146444081f02001491180841c005161b1034007c4032048850b260350f60601110801540c61a4550103451030000c00d11856411507068240c01054103444040d00300280a06080d05003034010581d10f514030a001d04000d00c903003690480040340b0400e40d0742595a64249030400b0300c3c64000c015500c11010020a2080c458080c190343c230002c005079100c17251703d035990600c8100c1c1d0164811000170300a80f07110149250071168000d8011300300048558030b0781c1c0b080e40d15200540106402400210703022251910006609014500850b01083d000d43c0e5480d04807840c0c0f04018985800c40c140c00e5101403440c0a4801442c0c025203d4801c1d20b0100041e0300c041e0040071003d03071080d91080c5019040205001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 179543902 1250 179542652 179542663
    0x1515130903110a0309050906031608030a0f11060a0f020d0f0e0111070f03080417120403090504050106020d03023708070203090901140f130b0406050f010e01081b031602 74
    0x25403030b0300544600303100f98401404600d618030800e40140d05803000600559400d119141143c4000e40d150b40f072035501c60711055641e400100c94a004103604180002507a4041d15200f0b122201400003015a50303200080319020b00b0360302c002c54070780340e409001e02c000506c500c2c0070b14802c80450100010385403032194400740c2562000c0900055680342000008013003060740c000e1400b45a010704001015482d1450518a0b0a01c0c151600b20500340c082a059983d071800c4070102d01880c06903503092074007034450040000b15030080c482c90000d42e00184064480c5400398021b800c0e080d012142c441d01050001501c034075600090640002c03106500c10b0900385240d00681c040b070300f14000d44001c5040400107004181d9660040c051071a005d10017040842950303444c0f079800300c00c11030080e207220310300c40b00f4100720406010389050f0035101c1d9040000c00305240c00d040c0043d04035a801656100b018007040c00041d600140050080b250320804880c11000342410480190702902c0206443c00b00014413100c02410b04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 179545152 1250 179543902 179543927
    0x715030b0402030f0601140d1107111002101e050108030a0809030405011d060c0f010c030c05091e0109030f0507150305090601090b01020a020d05070f080a03021515130903 75
    0x4501c10f2042c40503003034450030201d6004ca400c1c2041e0a81a03d012440c02560245401040005050561900c075004010000d004043c2c80790b200700c0d0918203800104190842801c60f150010b90007080207000d10400ca41008a0644001c100004040d9007600300d4426a0400d81005019900008410f00c002d544610555440b400c4000518285070900b40001c0041d0410314606051031204a506825a070342e10741144d1f000e0a620040740c0b142160f8458083c0030704a1219410082444c01c0c04004486008a088070b00c2e00c080242a00e0b00d10010001d100e1000040200c0c21f4104003001001100140c1c07d0803500a080f80100d00400210b80f50803c20101200e00e55540c4041500309406d000b018100010210b0540d03c3e07602c0007041410703103600101c0c544190100080d4dc400c24128820080c00400700b0140e041e21240d591000c13400f0340302c14503503540b900d000c14000c00680c48505040b10341c22144003510b80068844206000007807060000420748103c412202d6505039075001058105a00f00302010b951 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 179546402 1250 179545152 179545159
    0xa06050a03081b16052704030e1009030201020319140408061b07050d110c040603110a1409040b07020c04020307050a1e02030f0306060c0105070c110102150610110715030b 75
    0x1541c0800405400c4c1500038840d8034000c8086048500420104401d0500700707010140c0585220302d040d007402002c030041040394034000c4500d9003002c200d1611940d100c2003903d0b0181c000354a49074110000d00034020041c801130007044a0408550703c03034840c500c000c0004046a070f0040000d401c00d2014440e00004450103000681c078108506800118013058008001c0d0843c10308070807204494250a080241d10b8400075401840c1c144044100100d00f1400540140c003604c0400f0550b803900342c4264400d00701350702caa52018205c00003c000a0807a00c025038812407920569003030440801c00304081c3c0e003040e2024030101e030020540f5901d05070f10105092101120751b400041c2c000d01100065103d204203143e013a80382d04000700180c00307a200c0200b200c00c01d1800e84000c000e00e1800e00c0000301041c0090380c0403100104640000d06640d840000e6180300719a0180c40e4103400e0b191441085211803d0400c18420700490910040109109008010090941411422070520040b20040469806ca14020710 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 179547652 1250 179546402 179546413
    0x4060810081f09060e07090905010522020d05010f050a0507030e2b0201020f040801090203060c03190c0c0219060906020a080901140d0e030901030509010903020a0b0a06050a03081b 79
    0x250040306a4400d11503040b203100042c3d80301041c20504040c0c00a0100c40f01140709002c2c00192580c4590f01c50313006517014170020001912041e0046200c0c0f262a58521041120861100050b181c403d02c255820f070b00c01d03400040e03400c4017140e011054510840e800d1003c0d07650780742044090342d0903020310781d4119a503a01a1400703205c0c048107007413154980d160807000041c02ca4503042003035000350f04468105480c058503546a980d207034580d9001e0310500e4422806409840041099103440c1c00580b406a54404206840b4043c2d51442c8401040680030880402503017001c2c0c5d0002d0f07260030400c40081d007485c4940e0103485086c002d01410508955115004640c080008032000c1030150342615142902443e0100c05005000c0d00c06890f0b009028882181c14580006819032500c00801404892000c6c0c07401d0000b0744c0d40c000c0050898149d04000b50258001c00411000110130b01940c0347d01429101000502d5a103650100b0807031600e41c2c204444640c000101c903103054254844207500000362400810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 179548902 1250 179547652 179547673
    0x60501020a0510230405030403030e0306010b19031409010b0a1401050702040b060714151003081801270801051f1e1a0d0c0f1403090a02060406081008 66
    0x1c3d510400d0007100700c3d0840d6203a0b1208407090388241c2e0344407408862410750000f4103090800d65182d500c070f40f00450125011880c0565107050100721241240e80c0c500e825400c0c11000c0038044400700007640c40c4020160b642480020701144401c04a0003126002d000042d6407000a0a1213070700c1d00d00b50040d46460008a81180040c3e908c1011541503540c1a1800f0030020300f981c4c04500d203409031078002016031000019149080c80d00042d0725401c03040700244004241c40e08207401c0081c0080e8000501500c5040003051703402882e91040599a510624006680326281301440510110111032002d0100c10300a003045900350902a9580103008501c18070541c1001000c0075440041d50320586103014162441c0400000380034015500502c0d0a90080541c2e5940140b0300010383c0c40045040e100e01d01d070800382010288100300840a45032261603580b8542c566400140b40c80e040140188900c1c40380c2070681005840340d4010f0401804142c960801a041401c202c422445540d044404c9980c032022840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 179550152 1250 179548902 179548913
    0x3050703050105150f1b03120606190813170901170f06010c2901082512060e0102180a0e060109051c021008070f18090c0c0c090609060501020a 63
    0x4034554002c82e131119660355030408203000901880c40c0f0090811342c440e0540c2c02c910004001402e1410300071640c0f102c01c1c0d0b1401d0804c4024000c7d04080c808043c809800381c00524000c24403e40c008150400d034503601186541d800e202460710428080300c05001144412aa5800528104d40510307054a505000d00d4840f0854400c11401000203041080d540d06040c24001043e00820003c51420f610b1b8981d4000c2e4011150300c640207200d84501446460b001c501ca80c0740c032045440f240d04112900000040c5084400414031307048103020390740a0340d281c21205002c0c10034401030880c0118200c0c00c5c00c0c075108640c00c0007112201a8001c0c2c00c008080e104001060f0390111035581500d6040782c4c80000c071041507410039000900c03c00300942041c60410328003042500500c0c440c0c0318280c40d903a41c0240e410380c03441c11241d5007107100c0c040030f038142ea80c40300f88010005904000040340c0140742004d03400d009500d81c04041283e590002411075901c4100380321a59082c0500340142030203000404080b102583c0e00d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 179551402 1250 179550152 179550169
    0x1503031805030c1c02012006010311011106040210050906070b0105030105011a0d0f0e030c0c1207050904020d020414010f08010f06061b080408010204030303050a0e0a050d111903030b0103050703050105 88
    0x8581016244011300421a80200c01d1044818000107043e13910102c1c204a86949400a000c140c4040c8408458180c00e1341c810100c001000070200064046a180c0f5420b009545e1560514501404014446038540380c0703c2d030b0007814a050050b404514694074003020702d421540180c0000564801c0c2d0f4103ea058440f01d2421203103859055200040c10108002c00b010007031980c41031b840010f01001800211102000030b8503220b5140407035019014201010b4040d58440040c400c46401454000c0010098903001c114120280e0019001090128199035148441c00098010004800d01d2402c10b0081030000d2007240c0d14608002002c00c059030402d04c018040b0041481c0e00f50106d20040c628600b0010030b202640c00034a112402552116100d10340900030303100031100b10040601d07040c0b445c1c1e0329900001f140c0e07039601e070040051b146230059136404803134601e407402c580030140c400c6030510400301c0c400c500318640c050b0281e540042e80f00c0040c00010150740e405001c0714205818000180055038690700c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 179552652 1250 179551402 179551429
    0xf060d051b0402190503090106050103021305060714032a01090b060d0204060306020c0c01031109150f0403120804051615030906060e15130905060703050a1503031805030c 75
    0x8941c03090610010000c0c0207449602c034000035000c454140b8030302e4240c000e8090340c082c191701c90081c04641c1d202c41c0110704030300607507040b1000780143e00000c12840c14004e008008150180d040d007001800054059480e40e40b00b2082e4146812401030b51140c000344c00c1e4981c3e403a0900140c001d0001150b1503d442d00481c001038000f5120300801486030046580e00e5010701c00a6500c000f06640f00c8040c1c17101c080d142e00303103120b806020904011480f2211451142200d484407030007400131046051900c0c0021054000119050081c8803c000110101d6a401162058411260368a5000e4900352a0140c102004441d0750040038a8400027844182500002d40c0d60492992400141c488070a044c05d00c0076041c2603004a00d030701404024821048134426158440d1201641d42c0300066210800070412a501150f000d42141c21040115443d640b0941015401024003c4003040c446244102080340144950003280450801c20052140200100d00f2400400c0c0132005802111020b9021510301440c050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 179553902 1250 179552652 179552683
    0xf031a0613031a0f04062a091a040b0d0506180a02040302150c06041103100501150207050901030f060b06091018090b0d0b071106150a0e01030f0f020f030111030f060d05 74
    0x2210f47c1101c0c4010400c4507000703071041c0308226006420f202070080d0956001e510001f405001e21448103503001310456045450a410740b6140c102c948000000800c00509103582c0030b16403007a00060304040380d90043c003d0600000051359a4038620400400d90200008503444440501100002440100d445a40190081d0b1055114043c410000f070800d51096041000c40d0310b004000710b26000c0400080b01d5500b081c1c3c080302c0040c0d490b4001c0002207082480010101c4909290840c0043c4890300000340c4110050320740c80c207041031100002c44400845080c4000200481085507440d4a0301d020500240781241c0704000650030180400c90300144002c000d080c809422020410462040032000500c2d0401001c1da21182808915200b00c0c4000c0300166220f41516400418014641c0200c2412650b02940c114801c803080e65644c1d611510044069038807040c050031503505600c003809060340c520403441b0740c03540d00d150180841e0320242000c1c0c802c9004100c801c000c0800208001000c0c200700c403021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 179555152 1250 179553902 179553911
    0xe0103020607020103050c090a03050115050303030f130219080d0905090601120e0c19030302103b19052802061b03040312021009030f031a0613031a0f0406 68
    0x2122100c030f07229004416410049c1d0000020503c041907001c41150071b4200000c00b40c00e6076406c01c040c0d403400280d62502c041800100440e42441e070403141d807020302d84081c2131b0b44894685140081880c1c3c0c17003507125000d0b0b900822601d0252a81c440c15500103868203c4d601820383c100680001c02c0e403a02048011030043c0d60310403002843d4000c0003103902c4010014446240d42c0c1e040182034141500c1e40c032041b40984a44a40b02c025810745010382c01070070900000405100940302d4000440d170030710f410390040007004a0201c200e0390030203001c400e44075240307000508070940c0b051402e180342034103c2513160648021060702c20021650304140c07a0b1300c0c80e0101e5000b5215030a4440462017100c4a004030085440005400003c01201c00d0813080382144030340035107030b544200601c01e40a03650072410050005120082030b28000c0d000341c2c0010114404040e801e049003001601040659202e4091074100d240f078980108100001d03041194008107101c1c0381c8540c6420700700c402c408200405840140300c0b075182c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 179556402 1250 179555152 179555161
    0x30601050a090e0408071a01030201020a080f1209010204061d060a14040806070c030e0d12050a0e0301050a02040314071202061b030a0c050c011b0b090f0d030212010e010302060702010305 82
    0x7524480090840300c0b0f50701a0509003803500666907440650203e0f650701101401000c00045588014122501a00a81301081981e611054140d101c4500010b80e60820302c1181d1035518010341c900c0c416503000c0b0005940e54100603014144001007400b454900c041042c2928468482d80240c8400e11410b0400c10021102240301d6a002d00650b0001c400520480e010006d00640c0400040c140e0350080c1c88000050403c0014080898279004001e00090045d40524042620510007042c1d490020303e071816030498a140000c0c01c0d550281c4410b04010340104040c002d01c2011640720083d052000024507203145016a1118198018a0060306c00d01d004100c51403901c030618040c0309500b5400050301d5440000d860701030006110800145e8061180542507900c41d40a03512080c20a403007a00301c0800300146a0b10054100001800d8074021301414445004a03101000910200d00140d2805611100c4d2504440403504e0140d22241410301030100410150b140c5d8030469040341d80a18002c1220350790f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 179557652 1250 179556402 179556407
    0xc0e04021c0b010306030f060207031202070305070f0305040918062f0c0a0c030311060702070621060b04030c08060f061c020d08030901021e0901021905150c1c0c05030601050a 77
    0x40d1b0020708040c0c441100c0e1002c0024503401000003a2090301d034030b188142c41c0f107005070807400343c0d03100100400c01c10007114000c03c00288030200075a1107441c01500d041d0319000e511041e0b5010b24100013003982d40000c01401c0080b01c2c004d014184102c184401054504241c101009584401c41d400100c200044c0d5401c01510a001504644c0d42080440c0342c81962490020400d8071118440b0006c5d000d4003020803202c0340301040300e2080341e0f02c682d80c5c80c80e510210707208801e0b007594103c413017984580d603440006451fa04c0d01015000132f6005502e5020b00c41c1c40c0440060610000500814828004404100c11642d4441070811413140014032601002400c0c07001c46c922602d0007002034080e400c08010030904903415001000000301640340144219a0801c26800500031050088e0140e0002104a4010782020880451031030080d011103080d0300415242c42035102041e03038890b25500000483c000304000c04580c0c0c050540300e2100820070741c0740d80c2c0001040742c00050001c60400000040380c1c201c003803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 179558902 1250 179557652 179557661
    0x130506010521061014040504050d030e030403202e1214040c0f0602060c0403080f040e0708150603091c0207090e01060f050a0f05090c1c0c0e04021c0b0103 68
    0xc2c0303000100c4005061000d01040205035a00c5130b1001210b11080b03640711400d01d401801e004603441401000e144032240e100750b02410003020302da80c0f10300c001c1c080000401c40107184c3c1c0f2000200a00c07131101c012101f009003d038040c1806113030f0042c00b0840344518490045600c140303200e004546801078100402000c1c00014100c800080c9000015100c2440148101d103184202200e41c0e0000f04c8000c550344640c01d81c1c45601c102d402c500c09440a00c41000490303080c400400d00b41f050f44004d43d16040d1110341804058400341c400c900010342100800801482c0c00000602c01601194a6415450507010040e5600712014015107443c0da08034102452900821155010784028501400300e01f40e20143d40c0e0003010750b88150442c070708100318000b4880c105580040140c40380c40d0251041582408140055801c01801c0004030781c40c100800040c0030400050240c810030b0300700001c501a8030041c0001c041d9146055010303c294810054000341001e14500030310080c200384008690403200e41c00680080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 179560152 1250 179558902 179558959
    0x1c170322021c0c060932040e060a0e060708061c02010306050607050604120f05120916080d0207060f02100e0a06050c0406030501120b0601051b07080a06051305060105 73
    0x502050915504000c0b070880504140c0710142e581c850101c2c0d031b941c00e0003196040942032000b40300f44004008100780840818101c002d0001e000800c0070f211010003140b13084c07802c82e0f2007851940d590664481540d810301c24036400250340d14042815041480003e40104c141284400e0111511074801c011a4080c1c0c20400c01000c00406980c2c4070240382c10890f407140401c4500b102c59007200d0707900010b803902a0011398440c2c1e07a00e40e5154200541c40020700050f14001c5d03c0b10071107220314560090419000041c8801800f0300c01c0c09005090b510f208043c2c500301c4141c02035070070300c00c090342072010040d40010500312030541400081115007030710322442d04040c480303600a404281014100302004c1200001082100c20a03641007205030390794052040314014491005110668600100d1800d41c4150080c0014502c450341d41245c00f10900e59140c134040c402d0748004003a4120f05607490130b2000900c9481e610298070b035007180d00e951040e9502d40d2104014000c01d845140e01c9081040710307020070355222a49 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 179561402 1250 179560152 179560189
    0x209040e010615020f07030b160e0a030303020408010c0215150117040b0906070f050a031e0608160902070b0402240403050a0c061707050306010e1c17032202 69
    0x3125112011843d09a250403801409481000d001c2e0091010001e0448210b035007080d06810030340c9a40c00208181d40304d4028450070002e9810b5000542d64810048900440c807176200180c5c0c442c6011805429150001e0120003950080c80c003206020b12030380441ca40c005001e2500000c14103030b40c0010303500c00d118140300310310036580703a800c100402904089041c000c80740c04044170b80d20750303807850126041a0158500800900d0602200d0070b298000d0b00418401122450a20282101c0c0c1440c80104c4800741c0c030090055100700e1000a07180d01100c0391802500702c0c1101945089865100c2070840708001d40024007c0412803008100c1030813071400020014042212a55100e03501c1c14626524090303548140c4d0007110503040006c456000b0001406026000c0d42c805200743da070315000341d44030b401c020070503030602c0303200348165105944d5001714142520382515410400c00746420b103100d04e00e422000c80e2820b10000c205006c00d091101c02c40c890350720580386400140d22040e1021840c1c010240e061441c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 179562652 1250 179561402 179561411
    0x80301090501030c08190308040f02092e140f0f221a091506040b0417010506060c030706020901090f060804020f0105090a03020d0c080607050c0114040c090209040e01 73
    0x4400c50030780c2001d0304a900900f5500762036a1910403041d240d4214502241c90030507086880c00000f4051248a176200d8094004043c0c02440754001c940d41800c2161540c1708402e40c8150424900b041d07080c50700e414125909251681801c2140c5c8a40c01d103850404544146031100245071556145e0003c1c04060b0006081805081d1900c4da01c2c01c420901051340448407800d100c1c1d510281240034440280c2000000c05103041c1e500d42009100c582c18400d40c2e415004882004081107481e518002000101841403854103081410340605027110b401912091250700204000fa80d048000001d8560b00c43d0030942c010b9886c0380c01d50050b0307a00203440d8466525445407003400944c2c241c05c445058401c3d4002e03980d0454001e400d000440d0180318401ca8564440d10000081c405030802d11a003d040610401810f040c036925000b60714681182125400005940010b5401000e00d0078000d10b01306c5925221140040d0503d5500d1800c02211b078007503540065408126040e040d43d5a800021150035814020031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 179563902 1250 179562652 179562659
    0xc09030d12050708040c050d0609080c0c030f0d08010e1510030f0f05012301210b13020307120c0c0c08060703110c0c0607030c0b0c04062a110607080301 67
    0x1441111201c040e00325140c03520780001c0381c06008407130084c801d55010101c00091401c200422965020b400c03002d45541c0e40c1d03200641c0000b18000002e0404104070310040841d00882010585001d00b52002400b80b07400502120b6111500b010001d0305507541706000c1801540c0c4c410080e5482205111150743c8103a1151182c00f0198140d4081944070800c000180180740c3c185042000703540d028420780c0942007842500d00400c91801684441d0301c281450a20019920f420484c076200c01c0e000501d90203d41c2d2981422000d2074001031119400a00200a50662420340400b07000803d108800800e01034840c501c40701810320515280c2c5149030300419014100e625200040c0d5552000c54685c0c01007480d2079082005e405149042c0e0b81c11204881c004e140a4030860140845500170100031002d008075034283c5800550510038180c807400701d4100b11a191450140e006201d45040a02281030000300c0d858140380789541c0010200b029006600700d0000d0448801007885171146c0a4082c10414000c8000b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 179565152 1250 179563902 179563907
    0xd0201020f1c0806062b0f0914010b090c0403030c030c020402120601030e01021206040b240a021b010c11060d0e0703141c0e0d0602040b090a170709050c09030d 70
    0x400b03003241d0b0350301e01d404c0c0c2e107581c20f01245110f42818803000c02606401c80d4400030784d002241c0c20480c05040c01140c0e82c902a00c488041d1102a00d089981180e03049001d0000102442180d60710001215410b03203d040840200c0007521650101404001011504030709050103001e10f900340941c090011541c0310328400490807681d00541d01180081e052500d03018420805000342c2d0190400340d04500d940e42c840400300030040149140303c54100751800d8014541c1c42000c80da02c6240e00301010122b542c3c050380c090082c18050140ca108140301c003081c440000c20f991085045510b16400318040011b41c40000015049000d6047d982c111982410240039040c10302003008000c8078401e205250303d64011100c1a0b0300d4201e01001c4105c00c010400100000074480c8072220b88211010b02030140107941c03500c890044e0b038400d030408212001c0004444815007820342e440c1c00140f40c1f40740724244006448822645078401442016581516200403c9600c1c1c007803c11a004141c0040895501085c4841c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 179566402 1250 179565152 179565193
    0xf100513050411060a0504180603060e06070e090c0313060b0907021605091509040f05010204090218040c0906050a030e0d08060315150607051515120c0d020d0201020f 73
    0x100c81e014880f1102c1100e6090404c00c0e40d440200c240c403407605040c148005048032410204200d40c250b0340f5440c000010480a201e2402c864840c9000b41003549010b0781c000c2c1015590119070b502516854080100c11240901500d03006003d511510301075081a040940282c200d8081950b400000305003400132040c0c00041c00c202c00c0c407110000d00c003035a0390b420402c0304a64041380e401488501d00400700010b854104092035100d1b1240000b507682541540307901e804ca8000e50440303010325600060341004801c4c0c60601c0c460320242204c0c14043c0d02502e00d401801054240710380303424814040b804549060094000d206460500320854402e40414000103041c0712090310200d0190042c1c60405141103181501c0780c1c414120b505140c80c803031140380144109940150020340d00b030300130002805040407030b074400c50780188505444282d00b0b8410004010030503203032107603403001e50f030013110510f0031600d034103504c0014260111903c0f00000385600041c0e041c20f80020301e04c0e1107405201d20b24603012265400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 179567652 1250 179566402 179566411
    0x906120f090c090c040909051005010603140a0b01020c0f04020d0f0209100503090d050a0309051009030906020c030a17040b0c010c02070f05060904270c051201090b0f10051305 77
    0x2200c0b8000480014000c050780d003642d5441d00c104040000748018140e80d0841205144500c0490f407421a0002003003007200c0b03007a000b10000a07243d20b8103c1e034170010580e185800c170b0301c1d9510400854070383c0070000c2e55640003016240e000d850224452405a074032076040e1140c1c111111130512501d0b08940c0802e000b5449104558841d607001200c81e00c565104a09030380c8035003450b10003000c09003100303c026243c54026100d82c01c01c2549030159a00061002d04c1500d001c0500f40b50007190000e51441c01a041c41c100750840c00031075006032806201070b900015280080380d04a401d90783c40c40907a030804c8140f403085810032102180002809581091305520100345c003480c55003075540ae1900c032105a09a044c0b54400c00d54010028004c41919244c143e003c00c1d401e4101c0c0d00a01c4405981d5102060100007002080d16408800d410401c03180c14540c040204101ca150020810700303013a40d4031000505400390034510141103950000d08155030744500318028050091040102900782608000901070403038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 179568902 1250 179567652 179567671
    0x30406030e0d0c080406030b030c0a060c032c131107080a030b0303030606040501080a1b050c01050a0c0f0f0e0d0f060c03090203030d0b03070e0a0203090d02030703090b0906120f 78
    0x408000c0360724440c0c1c82c42c80809601040344c500c2e103860088103c2c040d000301c0b042d251703160082e00003824440c2e07590f400c0000100b4094a51001100d03881c10003400303400c001c03910807407034041066120710303050980b00c2d4490544a003229580c84500700c19030404001d1840010100c01ea0400155000512260902901441c08c103070780e0a100320010201410380b640016907605420010030b04c0309000660041c9840b03540910401c2001600c094040d140740c45410104110001003030002460a82c210f400703005607548031086c118188022408601c1c010a9501642102010015101040c081c2d0a01c0340544001010780285010841070031820524110701510104882c200e01d007c2d441030356030b80603000340c00040d030b0003c3c00b540c1404540310158014062450420358180600304001c100c1d030100c00e10301409800d03000c0005807246444070b031151902d03a074044600305642c4284070110029510070071710000d50394901c041a444404038004544107000b80c55002d4040c6040108004840640c41d03040780c40754070f008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 179570152 1250 179568902 179568913
    0x203040510091502070503060c070b07050d0b030a29040c05060a050c0102030f150f0108180106030203030706090204150308030a0c140a0e09010609050109030b180a030e0103050c09180a0e030406030e 87
    0x9c0880c00c030621903c0002452a9007080000741101e006102402c102c040d0540d010a621000200180c20410303803040c01c59911440c124076140640b0720326175500c40d07801c40403681525410b0540f28010400554410b091003940000b5022030030764426421390b0414004040295203d003403810009144c0310084a10012036018442660040e24080c2441d000950040e101c607151602c1d18070f0203011845c511302c114001992103810010060710f0800c014100d09014400000b038190151042000382d0300d0302041c08003540300707402040c800b041f07102c4102d03500315058020001e40400d51034030503146015000124080344102081d0b403c265504103190340c0f81001d04036071074403a0707a888840039140b1503c14020180010300d122028000100c010300030710b402c0010540310488402c004c0221600c0c000c82c080c811030026824075400380c0a0f503054050603402c407000c49040c1c2c0c1041094000f1900c0d10716200300740714030345070844085003540c40309a20605100020714143d80d07640352101405400f41810b24407109180c8980e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 179571402 1250 179570152 179570161
    0xc03060a060303122a080105090105040b0604060804030e0918010f051611010b03070b0c070807030809100921050f0106031a0a0b04090c150206040201020304051009150207050306 78
    0x1244907020541c1c0d41a150f0901030400f101001d8010b1004914038107411040c071102d00c001040320b5103601c010030001c2d614071440b981048184596401c0c180d2200c0d003d0f504081c0c4520559540200742d0f0195206441c000709039030384504007103c4542c41180d88a420100300b01c14003450b010200b58030300308854840000e01503000c0300c007078650441e007080301c030042922101580e84500510032400c014a11050302e00110303440d42c132071000905014040e03000c100c864000258400803180f040c010300c0001c042c00c8000d4102036142d6190300c1114880ca240c03803803180714005000d400240c05407507404081c1044921030a410551238041748a00f440400c1c0549048c82016404154080140614400e4a034450310800381600c00d90346140f98140090995400e481d00e0790042d804035201c1b4403600d85214002c00c0d00006041ca0092548048003010708041c045400400800c80542d80000464080b80e1044d111452a842c0d1844111000880794000d80c600e074151002c0c80003200d07400948541618401c805803000c42c1c54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 179572652 1250 179571402 179571421
    0x10602061602070b071a07080402010207060503091b060d090605100f080a030c150203040c030b0603031809090316050109050f030a08011e17070612061202040902150301080c0306 78
    0x8181e181c481c010380c06403505114503080040a0301c101d9200359175120811400407003038000300d04202c070544009541501000190340e410024400140400d0402a2541c01c00342a0261078961021070a883c004040d05004515160741c021581c19405098040050403120718040c0054041030745c48240d56a98000089403031002c5d00420b600303c1c0c006a0003003140b001c10b950b0654500d2490442528a40003480000010039418001075114500c520410410103086144c90303000e161018085a00a80c41803100546d0280d070007141a503c0d1b8812036032241c00e0342d42d0403501e44c914800c5a10007690590314010340c1003007100540114144034465001c0c0e0720f1501c80001d00e1a542e014142c45000081d0060004000d040120007000000c0404072404007003240d200c24007085181c440c176081c0c4445a01c8901d0403c00b0350352140b080300c4020803640c400e00000e17182003085650f9940100c0003074400d613035440e040c8046594840c0c4254841c14007807082c58a0b580c1d0341f498143c851201402450290003a1400036100e00c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 179573902 1250 179572652 179572681
    0x2031f0e0d12050a0e0a0309030203010606030203060d02040b271e06010c110411041e0503010507050d0f0b0411031501051303060513020a2601140106050a0c080d0501060206 76
    0xa080d81c032044601401c800c01405494040c0070400180c0e65481814917180040c0861010f29000303480f25180f1a1461040c1401c4542c03d6000504140c81481404101d6480b813003001d024070b80403070b40400c4100501c00000c0705071010f0800c0300c4446c0702b1440307490a88101000801d101e030340715240701006082c0c00f281030b90402108980c4c4a0000704688000c600103075095074501440b01d009040052280201400c042d0943d110340c10100241800d880585a070356000c0481202600040d8000d01c56810309120107081e40c050080040e00c0c498403045584011900355200b100c1548000340140040b95046040e43d94691050f1448024100306d1035500e101e950003182264182800303600700b110b0b21480d40d16960000c1602816807080ca00e070030007070040235940d001c00010107010301d0354a1440740030140405080da41c00001062007264100524015881001c0354054119407840c00d200742c0d9110705000880b09083c0c07050004048600c0800c1c0360300303400b400b84d009906030f44440d02182d1841e00c3d00300325150101c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 179575152 1250 179573902 179573923
    0x31509010c260103170f030106050309010e1c0f1101051501080106030605010e0607022202091c0b0f09070305030c070f0b030621010e01050f15060a1d0a0302031f0e 72
    0x70102e800400c00a0755050140b03a1500c00504503074104a400c1209245c02d910030317030101c0f000400c040148000d202c0e0a12501c030b04181c1040051a1585401080c40607114030103800344244008101080e12030b501604401008408410081140740341c202e00824a1003020064240094210400032480781c1c064400c000c1981e505071030300d68543c61142d0403c041c0d42d1180c101241c12814540400c4001030540740004e20802c026100980c03110200d500748400c0440902030480d00c1020541601c1c0840c0803256100d40080446100310000c1d5104c2c03403030a10380086648010100d100004810070004008a642d20a4074003a107649503010390348aa290a09010548020f6840400309011504041c901c40000005100200020400b2031040c140399003111000c440018105c0e203010704105410a03607503070f0002d141504848690070030800c2d020007001080805040d1007c5885482d240e0240d54800d203a49004541c01021200c800321940b03404120443c00441d881d03030a40c103102860580000c0440c00b0742c2d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 179576402 1250 179575152 179575217
    0xa020c0d210f09140105090904140615090f13050a080403030306051002030a03050405070f0b1308030703080a0525050a08010803180f1201060303050a170103110906031509010c 77
    0xe820001040c1300c80c40d03486000307410302c64100042151511400c1081d40300340d0061084281150008140605010300101503007560580301e03007429465518401090f401407c4c21011122582e2500714078500040182405440c500c06d50440104001d81407004006481c0f03c0d55090000c156110248a45a40c10345005405078200740a4a000240b00b94401c55001d4000c00407100440d2356640e14110198003500110340d1298001402000d4403100c0d0000c100a111840040d0314011080e1402030000001400d1544115100d001080c40c01605445d501741c00780c03541c2c0221034524035503d0080d005a020b281601c0c0400c0071300c2d0000604201c00310039030b200303204249010410510b0040c200580c0c401511300705030b804008081140c50000b8241b003a180950300c03948800d41d40340d00185000c0d01414200b968443e00c003c42d2030040c00000c5031000c7c5c1e6042c9180c2070710040d200e61201d000103800c1c04003903aa81d0b00d0040300d030b10030440d100710150080e20a00c0b0f0035444490800e918141180c44030061188a1000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 179577652 1250 179576402 179576417
    0x1060c0609170a0509031506010509060703020307050118050609070501080a200403060b15040f17031927081c1110060314030309070b0a020c0d210f 65
    0x49691900015000341c40341c101c58610041c420341803035494019400d05000104d0229800d0081e0404101c064400310b03d900703100c0110718008000900d944070740e070001c0740078801c042200350426000b0025100c265900c40c009000341c60703803d4500c1c1d8898600c441d00703032924030403a00442e10031b01c030201e0703d603082d034006a60340c1e03809558000540b0042c0c0b04030001107402c40a03c0340c0034451116010301034230141d0301c40c480110700385071503038100030b803200d4000c010b01c80038082004200803140c10303000000c2c1100c040406551148001140481c118002ea41d24074001070041003281c1c003c641d110185001440c50a43d01e414507d46007901c0d421044640e0142008540c01880441d0201000b01a02e101071105c0d850148000b4021424450809040400c890031298551400340200300340010340d0440b030081c4c003000f1411840c00328601c81d5100c1ca40d1052a0440000203203a42c01144244450203100c0c4c40503140d0098000c80d86810a060041c102040700030f002442d110380d01c0b1610403030200d1040c400c10f42e03c112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 179578902 1250 179577652 179577677
    0x40c0b07120305090a05070f0915270b12010501050306070f0e1903080a0504140d020d060b010915080103050606190608060102100c050d0e061311040621050c01080106 73
    0x50003083e000e00b414000384641c00c2031030300107003040010101800d60814080788441c42c00350703100b05a0300c0d001c0340a04010589403081c08003600115550030302c0307a0b4414429408000d000320440003002d0128103c2e4006110038003500e800317241500814101c50094003140d03441d907150541100d0700806044d0f07000c0044c242d444000a01d10b02a954044a1422004100ca803240d032a6143c003190f900c081d82100103c0c00c0401e0800c1182c0e190f06059120500075251a404050580e0028106806005005200c2c5036203214201d0355900c14840c541c003510b481542105502910440540000d07000d103c1150780e0302c40e0300002a89410082d5001d44541c0503d059110020b0038014181ea00d464010320b118118450304a00c403000c401c02d400b85061103001900c1d40741d80c1b04141681c03201035034030500305081c0a5021074244940d101001d903410003019000030742003544400c10300000c0c0c090003203a0700411854460040262030804136500c0b0815052050088881d03030a00600152014982486100702140c12a407121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 179580152 1250 179578902 179578907
    0x150409060903121e09080405032d070501122c280f151103040b0403020f01060b1803010f05010305010c11070e0402010e010302070b07020309040e01060e06190b040608040c0b0712 78
    0x100845c0d446021858109a01c603804685403c0403581d40070480514482c1440104031401c01540342511024042c00c006818880003900b0700740c0c002951100b0b5a503d1103a4000d0814484083c0889096483c01200403a142c000c219501c0004801c1c005c80783c40c8c5c01680c0e030310141800d17109080c0c0f41d600c40302c3d00b044000d607a1100108050305489500c21143c54400e01c803441900140114070480c81a608042c903800c250800a00d4401c20030a00301152f0f07d40002844039200c44410303035803100d01003280d8401c04044c49011a000d0607014213a074150505120003c02084019009410260300c2c555910b03c00e080d09501c40382c0d4400a900c594a2011a010082005548201d0800c0d02540060501500c0c148280ea07030002200021100d400041c0c00c0030540315900d1030306020b409078846114000340007803410180d804030740341c0d8041c10191051110300c03880801d02d080111080004d040c40c01c9403035262660b42c2e0002e444c50100326004ca4200034507210100d81e40f00c1c14026580e666401c80750015041724a940103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 179581402 1250 179580152 179580161
    0x10915080a1b090504080a11030a02070915050a0803031b04030c06050f041d0403120b031203060d0510050a0b0411070303090804090f09050d0f0215150409060903121e 73
    0x65507160007402d00d000c82d000c40715014041c0514425038a07950b85000d980c0000704140c602c0c0300c2c0307820942c204200198074a0b600240750000e0711440b40300007461840c0f0205140c0d42e041c0e5680050780101e4060000250303641c0c00b0015601c035003410043c3c1c5c02d400001c280090345a04c91800b0091401100d41c0091020034405c101805461110803042841d194852030036450b42d8040d012202c2a25284204101c00c06074020100040f0008110090020b2411800000d07154880544040340e00b80d000f00000c2e1050380e0351900e14001541110030354000861541f551400b8000c211008454603091008004860900307102c1c421001820309841ea040202c01d54048014040d42c45040d120a003050001240020a503c2411441481001c00080b82c1d40c0c6232500606004807102d6000900001d40d0401760115004030311300c0b0070b5070001842d0003c9030fa0b82c0d017403280902c9003088003107800615250b2010100841940020450b0f070203500c1d00c16060310003100c840f00f965611603800d605440509181581400309400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 179582652 1250 179581402 179581433
    0x12020a0c061b090504020309120705150403020a11010504030c05041505130b1302070b040305030703090501050c12090c06092710180209060703050c0c0306040308010915080a 76
    0xa060301468200d4490105a60b03060066060120801d05019502070b008000c0074000c1400b07a50550641c507080541d640c42d03203910701d41d04d13601c200e00003007280801c4410302040c00703a0361805411810a04041c18000c0da100003444045801611b414102c07642513003d0390603602241d038803410500c0d4003030800c41480090b14032500315050b1051001030108080d640d8221280c050480030074005180c0e0b03000780401500782d4071800340b615118030401111010820201c1119401505410300740c1c1d42e03840360030046004190700b00c8080c1c0154a03020501c0180080d910080034840d503d0802e06c00141c652070074403910340c0010801c8035402401048101c00d03a040444280c040281035241180700c148508403020503040c02150301c68241607807900c092000d0111851a0500500d00300011170518100c100403803542c1c070034018040c00b0b10134049901442c00300b00b00000c0005200c09400c1c1e9070542070130300e0090711080003030041a450034207001c00a00e00380d100c90000300840e82100d00070404201c1503182c0d41108a1a0035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 179583902 1250 179582652 179582657
    0x7080a03180605281407050a11030711090708090601140406081605010f02030f030708060f03030a0c061803050d020d02130807050f0604030f02040f0b040c050405030f070612020a 78
    0x81d210004038903584101c5100e280c0082d150701284405007142620000005000900f103807504100001c0045004005a48240c4906082c3d6036030301d20504c1a9072400602e00007405a1000017488400c00080f0f640840c0c0d0080d003070701c4200940e00c80e100151081581104c401c005a80050010401480d4004401614070170182c400601c454645169504101c1d01100c0b00307842185010b400c0145507030240c036808034000180301860500c00001d5080101d840003522030320400190324003050f8681d4450141c075a80040c000d007120303030320300900c3c8019024038440309054401501c0e092040b0f84080e5041c994800080d4140e80341d44c904154465120001d40180b404540e1060342800340c07400300160350610801803c2c410f0010585d992408040002d1041d0014200d8000c1405000420010b18a0340d07031403d04650454000c00c180c10014009401011400c1c201c560240c140900261440c0e0803000410a07200143c1c15202e8401c0101005030381d49159120716400104258192202c407a5580e026068605062 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 179585152 1250 179583902 179583941
    0x3020c03120f03063106050a0b04030308010605130f03060c080c030601050d051005041503260f0d0e03160b09030304030c020904060902091e0702060c04150c0b100305060a0207080a03 80
    0x3034813410b07117400324200e010440360f81d140824800c0d4074060038440010404034000314500f5040d40d800910302c90062258009010000c100c44241103551800c51024140c10200c0b02405592030401c100a014090704827404039161101068481c03040302c003160712410060711400c7c03512920f00007003802480300a01b60307401d0640c5070002103042c1c2c0d01c501800c03198000001c50302e60034900314189100750b00b102a83c41201d6407040441e80c2d40002c440c1003034842108155200984440c000114036020744036880d03200c101303408005011411042d20030086400349005000c40d03040b564540400590707900c01038501801085425802c000180303040014a60711900c6a4008103112075942d01088052070142d4261042d010309680c4005058250f2000702d901101c94070007016981401c2e808564a880b44c1d00403d00c3c0e4100c01017080207404c3c0a80740017954643d11445000c071a01d040307009103c4d5003004c0c1c00111158000c8030003080341c030f500b540240ea035059042241c55240c080040001d500500c0c2141d100189002c41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 179586402 1250 179585152 179585209
    0x140117060d06020f180319110f010203190201061e0e0408071b0303020a031b0b04021207051201020a0323010e060109090507020601060906090605030f0606040b0703020c03120f0306 79
    0x90050310508a0001885c0c841d003650508143c1040642911000c0005d1641859004103085444401081c01c0c240c4646c075503030806a004074150b10600c6001f90180d41000146d00e03105074154403190442d03641071540403542580459a0005260754841c42e00b51446c0310b03002c1404606020300a105091003000c40b56840a580c921000da0640940d1081c0c0160700a6100c4100380340c0c1021080340c015002001c04500c1c4c0110703641e214209000603002034000e041c0c0c1c2121400c02d4804200b02c1c0050140240069002d10700304910901179440640d00400290030600640c1c10803050303803070000001c0c6c104942c1c0011603003000c0800c40c8809006114504000801e4130029001800d0f10500303002d0903080e406440550305040018040f25403030341c40701003000000b40081007660b0344101a60741048401c0d264032076980350080060154001d5820036000c82c003000a07240100b50300000c0300da030150015815548d182024103840719050050700020704104204000042040c50091048161036130503040d1320010080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 179587652 1250 179586402 179586427
    0xc08060f010c2a0b030403080a0506131a040e030c190201020a020409080d15050d030c11030609060f07020c0a030201030e12040f03021c080a140d15140117060d0602 72
    0x214035a8420090304441c90100c0340c070b0301043c4100c00392031405000c40ca0b5003090740d402000740c6401044d0381095130f0340b83d000c00c400b555190400d401c1d0401407030003406140d0203c40e05480070300440d00c8881c8a20b01d0154900d8091001100f80c0c0d4142c2c5030880a007000c031048184c102020364840b0012030450085100d0040180c1e2244519903600380280b4a41c0c1e1a41c0c80c401a002c202c40c41c2c0c040826280014110810a0f540c40c0812401c140d039061800503c00600c2c0d10380160500301d41700729aa4180903580c1042a03100c80003075602d1251000c11041d510310340380c040f0140e0300e070041c64641c59048608810306001650198000000c441c0c80720701140c0314401350350303560b00300d640154020f074291340b0f0381800410a40c41c0100c0c08a0041d600241c074650390740d40340d6a035074080c3d129101201c1d00340101240711f41c0ca0b04205c002591480d000c805418050401001c485d65510103c44c086c0c04050324881690303100c01e5208448108101100e03016002c032540b81c00c070400c422140d402404940b40c58080000254034030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 179588902 1250 179587652 179587673
    0x304030b0c040302030d030509060c130308030a0506031b030a080a02100e010b0102070801021309150e040303020714061b030903090a0e09060711100f0b03010912080603010c08060f010c 81
    0x981d500d003054542d41948101802c00101c8032400041609010510403880c0000ca4500c1e00041d00c034907596500c0103031030f4440c000c0380d406070300c0640a0480482009140c507d00d40210744a06412010b13103841414291054080e00f01d40800e00c0c0c0c06505c1282508001240305000309170550702070040350286800c0080c024161800072000f0354580e51900076070300c1c555030100072410103000180d0003035084c074021103940c1135400d096200d590340343c54840016021082c48600c40d18007500700c0e00c910044519080c01c0240c013a601100c012640c820040d1100b120011021500740c0c01111010004050500000101c0d0304907000074083e52283c1c0810007001340c483c0d54840c0104000c10448201200c00e117843d40e030b20f40c01d0600044c000d00c2805030300316020f5002000442d4050b0b40700c1c100c140016a1140d0560801e00410920800d103070150310f070a50400510400c0b8100303818603404d540e10300d01640d030703240280350a0320104501d0001140b005804101c0d20700d0000d1840420700c1c012304d0401c0894186844044441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 179590152 1250 179588902 179588911
    0xc010e0703171204060b011404060302040e0609010302010507030f02011116060f0c0507030c030e0d0501020921030904111201030b100b040303050d0203191b11070302030a030f020304030b 82
    0x1640410010800c111240403a4030750800c100c00b8580c00c1000d0400f80381d202c0e0800030b0000b00001e658080040c0303e03a00511011300340075460a190b03900c0707640320382c00a00250300a0096a282c64006d5000030080d140c0010b1250503681d06075680da0805509503401d842400348031807900d00790754032188010860282030020703005012a101c101400301200b410040c040305c5101c02c40804044c2000d10010300c0035000802c559200d641440c000341d0042d400d01f41290101d4043c103120b5449030440c4100428460150050907105d00202c4824441c030250b40800c1070b0000c1c010030380c03920340d0b0003d02512860b40b600303610400042c41d44102071890200201c5610180050036002199841d8141c414040d401141c0001500948040c0c01010314090468070041e04a000300380c1c0803034805130004002511500d400382070500020140d05c007401210048914009042802c40b02c840015070000f8120030000000140070742201d4024001d41000c4043d03031011281c20780101c80c0b08080d48000c10001000441c400c5001d40705 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 179591402 1250 179590152 179590181
    0x40b040e0a02010905030f030a140f0a1d03010501030201091203030917030912090d0b0601030b04060b04140117070e030a0c060906080a020c07050907030f050109020d05060a15050f0c01 81
    0x100711240300242607401c503600018066800280f989a47d120300100700c0714202d902d0f0400000003410b0013030f02d201078800d0451064182d400440e81c0e58040b6009480c80e0000270307501c13209200080e910401d150803034009101c064002100300740101300001102025590346c0d40a883c000c52076550301d44802d0316581003c1e05c00c00d00484000704001c412202880080d5129005503249031400310464001a40103c4c0c2d41070190601c41c1c070202042d80c1d41e01a40c06041d4036a4060001c0c4881a41d40040f24020f420034400e12220502e1400400041d40c41403001150140030703d261108503803280c06007124a5203230404c18507010301c40c281c00a0049810f03a40d11800801b5142d840241290030540000c198120140003004d4031401032000e11520707240418210141c0d1000da03000c59040e5a40c1c1c7d0100d0140c2400801040a58500000440c80d4100342d001428100012481800652143c000740704440c80d2a1080c100d0721040014160704080c4181c0041c40d01070790041c0500d00704061800d4090840d0300c1c00b07000604 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 179592652 1250 179591402 179591413
    0x606030804140a0b030601050a03060e040510050105010c0519081c0204150804120e0307050406031104180308190f0509100f061a0c070e0708100f0308090d02040b040e 73
    0x150800d9641030740100002511582c0f0541d01c0c04000c00c1d140d01001d000d0700d05006021400d0b42196200342c0c085e000804001c505418a8101030411580f6611198101d40c120741c240800450039501851407407020382d41c0400103008488505540312000c0341c5d95003044a003040c0400660202411a050780078a06428000045c0d94900e4411301c102c0c031401d85104403003800380703840400c0049410440c1d041040c88013410440d442d60000c10005c4c4c1461402d4019035401845c0c0100441403183c110003041451000b990200201010580040001d0524078801000129140700180914221148550007480d2082c0302149240300d50314820181c8100321586e64850f404421080880c400c2400b91030100d1404100400c0080d00381001c3d046007a0906030145a0300d0400248024694001c01003240104110b094401c040c0c00d2410000f802c9800543d0b41d140007509410340842c030f05107449105030869038005141c6181131044010702a08600300042a80d00643c0c803480b0303110f607481e103004681100a07020090075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 179593902 1250 179592652 179592659
    0x20c01110c06100501140c0c060a111b210f120a02100b0907030905030d0911190b0d1107020301090624081024030b0f09030901020a031103070606030804 67
    0x38a0030b800200b002c5802d00d1150030402c0541d800158030380415510500c0295980944800f81d4603040d0b02d41c003000c1e00031308005058074049034001905200c20344248203440c04141401c10005100d83d00e0000107a20003203681e6024811014940100007401620068030844244004030608110b5041f0311200c0002001441c504659070501c81301d030810036205405c200865045000c280110070092002c0240f41d0b0fa540c504c01840000c200b079594024496006110300e40d42490702c4c00039002c0980c81c540c02400d5002c200300485c114280e1481c140c400402456061501e21000d0002a00a220807003150407020012000907031070a0041c00a1180124004961041401d009402c4042c18100f800f000b00b84029081c00702850120301e50710f29901442c4041080051415000b0b0340000301100c0d8800d52900d403400000300161282801d00c14500ca02a100c031642d40d556010b40c480c441d80c40840d0041c0c11850010000a000b07402c54000c104001c002c50342000700950302c80d401c0307600c00c1d042030b5041d100c0441c040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 179595152 1250 179593902 179593927
    0x1c090603110a020c060c0705060c0109060c020a0b150105070210030606080a0605061c060513050708070801030f02010c210c02030c0a050a030605060303070209040f02030d0201110906030a020c0111 86
    0x14014060940032860a01d40d46802911000f075020113130b21502d0002840392003540708000343d4025110003000130760359465000d6402e00070400554101c68044c145003032100c8007030001c0380150107590043e6030300b011556040c0b12401508060006207043c80002d00800025840c0c2100d00044032103503171000144a41090f901808022004105880c06820118140466220401510b0510894500340000700440644000140a06401094011b103600a074180100d499400590243c010358880500c0303600c0b54003044603160800d020191110842d4130311480107500c01d00d40010024001e010350164489054003102c0350340310b6490310100254032210b8200a624040c0000c001c1c062003281c1d001703440ea24110108210b240e540c40007400280d07540b40054032035107042c800ca4841c641d00a048242c180f070a49462900c0d05a21201030340a4841c00d07003941d0700140144a166224600b0881080c01c0c1420503081000f80d500080c10203100d0b6030244034044507a8807d0040e4445101500b80c06a00c820300208a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 179596402 1250 179595152 179595161
    0x70905041505150310050a060b070b04150614060304060905010630030912030309120f1106060a26060c19020d09180b03060a0f0e010225051c090603 65
    0x101e0000441e203e2248581ea40004141500c50486030000c0340c43c0e654200c0e52401446268801c4808040008901041210032840144564403c21003155960074098880c8211815405410702c4003240b0302d407c51061400c04061540984100004290107815503907a900790351068bc4401300000c1011044070300741c1001d14610700018401c00c0a52080030442d1402040c284e220712a0751a02e0a12030000800e02d44607400180200e40c01c4499880784000b0144001e00b210441c0509034001030140d00b04201e40d03403000c9181c41c000d03036000b0180c480080c28040c40d60b4604030140300e0100259a5603403899024031086c0007251003241c02c1c20302d2540303942021402c034540f424203e074101c00310f400c10fa80715400190814140d0007501d14103034a162410b001054003e0081a0200002d40d051080c0c0e410410103807100c0d000002b408401800c2404001d4040c120300d4241d010701c5d4541c0780c00880c15070544510341800180c85001601401c12901d901c0316082d100c080404101881d0000100e145074148445a01800b8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 179597652 1250 179596402 179596411
    0x12020d020102090303090f0d061a0418020a05040f022109060906010609030b0406092028050402070611070b070e0109060804060518011109090a020a0804080903070905041505 76
    0x940c0f41c455150b000035103d10625005a20484542d842c596094807210b280f061001ea01400030003a000c0e200b4414074890308400381c2c0512403070400d101100c144148844202c1d20560241880488904120800002e00a6a142c00c4a916401e0021a0034005002c91020000c001169a0242d07414101c3c1c405081280c001d000c07201c01d82c400390040002c01c4d4848085811030343c00240c001b500d42c0716450640003900541001904510726034607034090030420805032115201c8101c80d2103509110b0848040c0d40550b208048401d00b0403200da080200d03003071580003000c41c14440c200c001082c00c0072070459902a04500d03420740d481004c0c1402c100700e0580113135681d0000300090038040106480e00308014116800208010043e54841c1d000c120700417115049030740040040330082c4044800b1240011039034220b440c0c1584901d0302e21020a43c004014802c9411313012142d9107614441d5074a4541c9402c650084403415090300c1040300001e41e14100340b0446001d64402c1c41d001c10f00c050b00e04200e4086d04c00182 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 179598902 1250 179597652 179597657
    0x304020a0f050303030112080f1b060105090915060f04180309120b01030201110c090c0d060e010f1505370806031f0e060901090c0806060a0b0c0c0d12020d 68
    0x510911140e500013054904582c07408100310181002ea203403030800b900801000001200b000300d00701e40321b01e00700342e240609000b0750300c05ca81c49681d807401040900c52041e12641e03129001700300302c0403240c00ba40660301c2c0c0c8900c2c0a414a410a6289804901190b00a07000704211091100991003019840042c0c035008040d00d0110402941154844501030901840000d05128038100031980c482000d12202c00702c844028a00d801e9071914004203500c0d9803005100d100c40e03600d080404281001c2182c01c0b9810f98011070f40c400303c0141811003031311850f00100002d4003804404e01043e0f508000344181e1030b0501074641800c0542c480e400140d122402d00c4445000144003491b0704101c0c664400003114184140141c80340c03043d003c9240500001091001c0f0386003050b01843d000c00034022815009400850711402540d9841075aa0031060384550040d180d042c0d11240c02c000800c4402040006015071182e8081968014000a0000340500c07040e164101e420010703660b00d80100d0b540510055402c00b1450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 179600152 1250 179598902 179598929
    0x190504050109060302091305010305030301060e1207060f11010f0b0f040c080402091e011202030d08010e040314040b030406061e03111215040b040209060d02030616031b050304020a 79
    0x44000780c08a42c241c0901d100f0954085200d5284c0d81c1d41034074040c0e0010300d44108112035612400d010307450344d000340035410200c1e5030200d054026041c88040650034130075410240c003101f0b0070701100301c031102e5103c806c03d000c008000742c1c0204124000e115000310f202c021140052034000000a120000c40600b013840d10641c98001c4101c2840e8011388210b40c85541251540d0043c6d80744c2040417140c0d00446554a140c5001c03400100315200c040d031554004500807030895010100c820340c1114804030900848400c201e10401250000c1d00600c8007100d0b144070000e81e142481d4a88402e0141c13030308112001e4842c40e07251042041074000d010f030091080b800c00032030b5016450031a03c0e6458240d07461040280074800e68404010b55031018021454204a61100100581820708240009803030668081e441004103001064541c41c11607121016250b019010304039564903d5038031400c0140580d0220281521102016800750141000c000c951843d5200c1030b440e420180140450280c0b290018250302405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 179601402 1250 179600152 179600159
    0x507141305010e09220501021908011412031909090c120e160315060806040b34110a290603010209060405102a051027020d0512190504 59
    0x103a5103464160241102017140f1003545020740c020321070504440701000000b006200c149030311062440c1201c120b40d1007000010340113801c04c4010345d1128480c0e651a03004100384600300c00342c080c47c2003107082e2a050403251281c0e500e8640c4190380c40c06c0c484100161494030690a010074510540503440210002002100341021140003143c03900d01010340f070f01100c2c0c101d106005401d13422020103446500f0aa624a052900e45841180300540390084640fa0700d10074a12807245146226010003a03000d804c04003504c40c034006441c5d1441180310a4210301903d583d42020443c6540781000808840c10348100c0e0715904011910080700c00740456100b80d0040002c0f00682c1e580c013041d50262581215159141d6000714000d9540300701b07072a41000011f54612000404010403803580c60b485005800385d6049514604ca42021551039110130000122070100c0c0304659541c2c10405103440344054040c0c4a000541e03140d080c80c020348000960700d030160014040c11b0b00e1800c4403e03101131800504005080906 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 179602652 1250 179601402 179601421
    0x603050937020a030c06052d0f0c01150803090f0307030f02060309150a090b06030a031d040b03120d0c0507050703031b060e010c09051207090507141305010e09 70
    0x2410590214154250000402555030f40001c282c0115803200c50b04050325a01d032009007558001d05c2c4100000c4030b4400b8403891907000c1152642084810b451014649202c05030205015001345108001c103650356001c090415070406624409082c0c00001140c0380d00c002003c011550304600b81d0310f8041d412842080000421140c54800e80c19030440b00c141c1c81c2c0e5510701d2410320305495401200392202d601e41c140440c6540c0c0c0d0307000c1c143c818044c0d00300d400c075960ba0f8001d240d60390b540204010001000000c04103607410423005ca1140c1b007000208089980e040d42d20010349051112010f60b25425000500c1690a9926104140c81041e031030611130b08100c0e090711031316100c010611014090100e01e40b1100303c002080460142d0190340320a04200110f0b00a42c1c05008040a80704200850200400441c41c3d290850110742d8282e000c0005140460804040b2800380202a01500500002014118400c04444040c00307a10406a0f04001624a060001444841551307402c078007500c1d8003020700460701c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 179603902 1250 179602652 179602723
    0xa09030509100e180702010c08162d0e0f010906122003010308070b010608060a05010e0f0a032402030f06091506031504151d041103030406030509 64
    0x8804540c2e0502c40100d03400260307021552442d66950000c00c0e03442d640040080c0068160158026a008000711503540d0420f45040400342c0d04c1060008203451503604491240e00c0c50706816101340a1000301440721281c40300e855000e44c4041c40811517225030095981805030031050303500024030381501094a000c0c0054046100303c584000c059444044010750700825103941500164000051b42e642c2d81d480c00d20000c1c1d43c01c00d1000300c0d83e5010741e00000510030300c9a00321350301501d002850f01515501c0d00c4010740e4016502c64505030000342095154031950354181440c00114080c62030001c03820194401d0541c3e805480c19414a00c40c418003c0c800c114520700c0107107521000503248002c81d900c68805982c0ca60182000003584200008100564250300d001d142d07030742d400d084d10180005540c404c5c00001c41012401800c8440100201300481440c003842841e400900030030048034562140800b0038110b62291b0004408691038005000e0b101c9000c1101e5005400200b0314114284002e548010140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 179605152 1250 179603902 179603917
    0x30e0604080f0c210a030c021501091d030a17010b03040308131a15010908030c031909170102040e060d0b010306050c0d06030506040308130314030a06180501030b0a090305 75
    0x80d0404150900309000422526894484d031482c0d9000303c4090071020040c66000d00e842600107410b01496a1840380005000080211064900c1040741c1c01d06245200412000e1540321741d0303520000c0c440801c0031080c4001d1a11841655a00a05191209001c500c1c2070069000d00c1400c1020420040440d510403041600128201110307841860075060074450ba0000b2005000803403050401d2100181d2283e0f200000d0500a0b2a2018801e030750384c440507240c0c0070b1180c0e001c005820401c072017140400c0c0503800021071641400c010b0130781a2074081045d0400100c40381d081e11a03500240a215107909000459802134084a110a2240c8255110385c40f503407061000038180b0b9203400100b00c0c40840c02c000d441500ba41440200515952418059551402510164046032020340812620259810030310300e116059294a5074a00030a0981c18080d40010600b0040581d1542c010882e16803c14048041c42c203003940116955046091490303034001c025000c040f2840c038112100000a4001003517840c130 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 179606402 1250 179605152 179605177
    0x160605040303181d06030118240908030405060108010f0e0309010f0e2701050d0b040b0c04090204081b010207150507020d020603090a0303050601050403020d0f020a08010e03070201030e060408 84
    0xe03540c604010b00d4504a06410501041c070304c06a01d81c50202c0408111441508224001d0141482d00c1d08098446041e8507030180441259244407680391001e020074035201c01c2d4500300042c40c070307289449050385d079017040c0c50031500340c1c00c01c40040007241404d01039444c0200895508105100107585c80300c0d0749100d1800e400d414030a0b42c0e01d504000fa4041c040c01c00180310050700769100c070303040303100c2d0090541d0900742e6246032000c0c0400042401d0411040301e8007000e5002c3c0040c1950307241d91700c81d00e001000040200d120b10f242000b0124a40c00c0500142008100d40740013412601c8407120709010094220303c2e86411503201c1c0900304085640c00380c00303402006030360030016600c021600104602d1500f140010390440000802d101e210341c000079101035582c2c0290b42c104071316120100111810302c541e10010354008841c00d80c10001c94220244920418801000392502d299070358004da086d14112011002e071354101081050555806004548140c0c5501c40a0152440c01d0383c0d9070b420900403629564031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 179607652 1250 179606402 179606417
    0x60117011a0904060f0f110403030206091203180a060c05090f0d23010207020616120e15030702010912030e070602151303021204090506040b040515010503070c020a08060702160605040303 82
    0xd19070746d01c0710340c40b0030346a14148030400d04805038a004d94802e1200301c00600c25000007880307034007004c40e41d04030340a0800547c51464951542003800f88649001c241200d009180702e041c00940304d4072410707014032595242d568a6165a904001c074065200c3c19403802a4281103245000807440c16a0004030501c465030101c401501800c954020300450000035000b0320001130005000070005004803409201e0b6494a8032010b451008490015000d031a803a00800d002928030308a0b115540510b070300880074800041c1c1c5a0301600c511420392a20349407080440d64480b80050110f000b0300c680405003100e40010701c4a0b0b040e17482c1c40f101d00358004114401d101d04046d0034504040c4240030b1100c0070b100b81c3c0e041039261a00d5030b00361001880d0948201c1e02c9070f49444800b0b21142881e0240500c5041c032070441e4221400b10600558147d03100401c2601000b680080b050016a21145802d000c1c005250013048030303160034071000c0d00e0406425410a003485208404009042c0c0c04021502502d50601c0c01c0103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 179608902 1250 179607652 179607671
    0x2030a02100306081203010e071407030c0f06020d091115160203070b12060307050d031d01050c030409091e1205070312050133090909050a0203060117011a090406 71
    0x4000f000c031900502039501410f2030202149443c1740246042e50340d80303060040070303032034041c810f85201201c6019036980303400a20020300840d0184030300f6403146008043d100803218495039603004076030050304204800c55850781d00c1e2050140a5826103000c00054031642624100b01307140189500035021070fa066000d503e410f410440d00c0030310006009240d51450191078052100b0201d40314501100d403240280700740d90002a071403a01e000c0d003015860b0143c982c40d21540c14440c510200402040c0c1c002c1c10311904000b84015150104000e0000b0041510b000604e0301e0b50340740000042072202c0e1040b101d20656410940455091140c0707981c40301180c1800e40da111400d28041d101d40c11401200c410041c0791a00020b03400302d801c000f202c12501c0301c5c4680382000b02d400c10f100b0b00c0545054441e800060558905002c44c1000350b1043c10301a019408586002e40203600180c50300ba4243c000c4240300001c000414900d40090080b5050b401d00398860814124442020540f0307654000d20261140c2d441c0c00410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 179610152 1250 179608902 179608907
    0x160903150b060c071e05060403030f0c0503040b0a08010e04170313050307210f05041205010e0307050705011403130308071205010f0510030b03030403020d03020f030a08180a02030a0210 81
    0x102070100c05403140b40c540019220305500c40f0800c0c0b00c0e100e14070501401c0101e002d2040704091080c1c0d14000c02145c10181562411a9803050300d4440b2002e000e01440aa0040740c0100f000c0c2000f000c40300c412540d10081050000e003201e2041c0d108100d411010b006200000b01950107410409070340c1203907680c4030340d900c90b6a02c544415024000c1c180d4000060741206012811844205000034141d036112030046484084981582110b82e200000f2400e0200344503041c10303881078002490040c400419859400742410b81580d1040302c044a4541c00880208602d50b0090060381d101c40b41e006a081c258586807140100003402c50500400700001180001c0300c09005503900071f546407056100708010768403641c607556511418000ca80c03055607000c690328001d46c0700b40680c0780a16400380184d4141341c510341c00c0c000c120a040004805600030400c00305481c5c2c2c41040901b501018030b90310200d45040007107020442140302d0301003c06581080e07401c0e4000d80c070002004a0716590641c2c005000c5500c81108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 179611402 1250 179610152 179610161
    0x2031b19030504050a060504050a03030b101d0607020307090501170a080405151204030207140607350f030a0c0e01020309151303050303061003200304081213060516090315 75
    0x1b0001e616000a1209010700040c00070300040c8281c4080264022007401c00545000503540c04001802c191072290403000507200d207961400c0040d010038200711485d400030b07042019a80104007070694032001008081c001900284044070440081d00c0f215540d91608401807041d40a40c034001c0d4002e80090b0304081c2c0810407500342d440d14034620300d11805d040c0b900a484016a11604480301c1c0703494070440203454844104c0740c52541c003255249205d015100c07071540700920b05c15018074902d150004901041d12000003013824010f0301c10394a82d245001c4100d4400c680100c3c0020b010000c3c0d40da04501d09036000011580ea050041328180c0009004511559840c070611101c0c00d01c0c658950000020800e0000c0618040e9070304658040300004a000200d046174101102601c0b2800000070350092901081c0040d90080d01400d5071502d0030701c0c8410803100b205003d580c044003c0180c0d12034a000e00641d84a0542c21412180300c14440384010700000f8890321144c000a0240020517a80969101c0c16520 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 179612652 1250 179611402 179611423
    0x6050603040f140a060204060305070e0906060405010e030c03030712080a020f040504020d1d03130e060901031b03020a030c03050d14040b0a0201020403060f0207020a0801020a120b19030602031b1903050405 90
    0x100750b6803a920382300006d02030102640d02002141007006121201c0c5452122607114100203041d480c03c06142500459840300a4498180c02d401075054500c01510140300038800035005031b581003003844007145e0090460030000d001d40c00c1a44140440d00c0360300c07642011641100e00840c2d003d42c48600381009800248034448030034080d1150000350080c01640400501005a001d000080c0307065030743c620494070200d01b103980d03e601990600040c00040c4008818922400e203400c030f03030381845841f0b60204002035070540060322041c500070800c00802208020101d4450740380d00d0719a1a043d449121400c0500807802400c1d003440c1c0c0031400f1500103100350306840055422203402d0109040c2c000404000394032610050340215050740000c21450014005c482e015191545c41c4000608001c1020005042c05000b0700ea001103010520000740e4419071039013000d1070284030016940e0401c160b1454012065496142c1014818410b0460f0200c6030640f041c045000c41c10080754940d920f1403e541004070040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 179613902 1250 179612652 179612663
    0x5060a0905030c010504030801090c05120406020a1407052a0a0b0d0e010222060507030c0b0a090f03020606010207061d21030c070602060105010804020f0d0507090908030a06050603040f140a 83
    0x4200400d155000060a0480f5426103003005032808c0e1401c200e84cd4400c101c624138407200c0900102e40050060b50007080b6104691528000108865034804001d40c40540d0599044d40280d450b2100c0ea5141c5908105100c10000c100301c00200a40109420210a02c100c403081400401d0307080084da155001404e42c012a00001c642d00c505c4501b80540d00340d024001ea01c2c0d180844c100208185000304101c0f4000350b0140c5030410480c6140d03540300a80c040c010305040510b40c440210800040e2102e180844880c8a50082d10091801d500024500005a80001c080110000c4c91490b81074000362241d81c2c241e01074a40340200d01646c0d807800c10765100e4030000c0105110004603100b40d60700101d580e005460340381d030039542c240e640e400044403481410f450207540441103d0002e00c243c6001c4201c0000d451146058503001e13a61411060100c905048068a1200300042086403400c0c4500ca8080507090484080c0e00350b00741134076a0842007a0b1050014001c3c07086a194108a410401c01c0c08003c40e4040e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 179615152 1250 179613902 179613911
    0x50702030c16030c050105040e0f0405011e050a0b09100311030a1a01060f1707030b180a0b0f0603040b0f150a090603051902061c0f090c06020607020a05060a0905030c01 74
    0x10b46260400e40034610090760400007440d404560b640c8550b0485085400b506500200f030b84900c0c0c0640c81c482c1014100720307443d40d030b104050801116203000103040029280d20000b86840d100c0140c5d41038071410f0701c05522072a403502c10050700018901c1b00e681641d40180781c010110041102081c5024000352010b0003075040da281503c840d00f03488c0c210606036021961102c40c002c1c500a0159000c500303160407045840315201c00034042c1d0b4481d500100300f0400040c91110701c0c0d103584803c0035a079403007a1101c1100c1615403154034040d08000b001442a0101034542c01d15500c0d1544540440c50805001200510300c20340108945c05800b8040f42046070000381124030081c1d0720000c41e001891544400c43c1c140c040c44400d00c402491417041c08600783e0300503016611740005841e1030481c61a900703040100b055a1504000e00c3d102081c450000868811440c1c1003413242032050291500e580241840119401003540318000b82012812030b420a1244002081c50702a0b85801030442c010100100c003603600c1c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 179616402 1250 179615152 179615173
    0x110c01111e03040209070509041b02010509070605090915060d0e010504020f0102152d0103060903030e0303100909030309021002150601020a0f0809030a2a09021606050702030c 77
    0x34000a0884003440108584a0710003100074980a02003214007940c81903540340003500b0f06d4050030060a01d440b000f030002685003010f00c2c1c1d9580010180b602900141e56400422920840800989001d0000d60814609103114880003910598000340324a0703450784041c160840781d480382c00980310b1910300402d0901000380f118211a001b84000c40e004d83c400c0079544501d10351307540041501e603810b4040c1840714201d961745a41e41d1221217015040ca8070038441c0e86c0511140800d884121a01035403240c01c002c1a42d40d04c9080090a440c0e109054055a030010805e0002481c881600b43d4201d03074046501003003000550606034002e10840c00040e40124010312004605940480c041022200110125991b61241801269079840e820300081481c0c51083c0c10700f02081c400c40241881c0c1d24000c1c1214109605030381c4004c040d071707080c800303c6018401003000001d403800e03449007240c064409401c046040030001005102009040100680000d540ba801b05281c184284100c4d5030003012003040b03030601e181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 179617652 1250 179616402 179616431
    0x1052a19060203191116032007051809100c03020708030103080318030408150901060b0f030f0f040c050f0424080c30030c01090b0906060307060f03110c01 68
    0x840780390b0078151280012503007a07032681c4109000f85d41c58060482c200100007405e015501608541601440f0f04460740180d41050f01d19600042220703080504012407402040c80511420702c603800c10910f030311004002030104000b8203103401d50035051001c604180c0301d48064000b44103252025104031000000401888510300c011405400c4490718a010514100781240c1c4030b000340e004508650b0003000c4009040540a003c86030020b100c540009007135070759403c80201c0c2e40d0146544003940f042c04405c101c00100c184499650118003210420f00307070310f06035561180b08005401145d00c19103410038411a6030301c95500130300c070303801c1001d00c03144503070900701c480149203a441e2150045501c9400c1040c4e840e801c020a403400030354003264409040f200c0c103151000d50000c01181860080c80b05101c00fa000c0f001c24040c1e204418010b051658041c10410109828000001c1145000b544070310b004001c0103500c5000490041200d00e4002400001c00c00ba490722841111003409c4c107582412020998000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 179618902 1250 179617652 179617657
    0x21f36090221010324230f130201020c0409060f0e0313051903020607140a0b040212030a020703110a12060e06060d0b010504111603021b01052a190602 66
    0x941c1c40d26040b400c0681e94045850b0402c090000901c026030065036400258081000e4000b0941c80c240d0204811380c0b014031020480f101742c0e460301c0c02d210204050122040087d81540d40202491390394044908858002035961941c90841601403039489000b4001d001c0c240c3d01204c1c0012602c041405521407148042d44d80c0d8002840a51440c8010b04c4001498a88001e00d51100c02440c440060614a5a0204080e0350050201510240d0550400315000881806001602d91042d02490081d0500d40144100c80074600b1004100c1d034010000720354107176000541441100e81c02240c0341200440e240c041007503030000354009010181400c0002d0100a020b41120401508002c2140d0715645c40604111201e1043d14014007140d41b0540103200c1800c080c0c1052507100301100b00c0c03a02c4c00d40e02c0380035020340e48854002500183c0007404002c8490420340300d903c2c44d4000900c0c0190a02c0c1c0c0b5000b4544400080b00c11000074540f601f40c2080358608140000854460649041031028003d41405006903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 179620152 1250 179618902 179618917
    0x3070e090412021c0221041d01031101030e19060b0a0902120a0b01050d050601050403083c0d0b03070b0f0408010c0f08070e0f1309021f360902 63
    0x5001e444100b20106011000107591030041c0c5e8002c080400550240828800484000520240041001265007507006061450602c0b15001c0d54050350304d1070901845c14007030703d140302c0d040604200701103021a0b0300083c60a01c40c141980c81020a148030325100b00108254140a034200c0c0e0703914070006465003c1d60203844e0030001038600d10349079512410100c3c2102e0345120800c3c0070074030600c4500d559101952100d07070301601c1814101d280c6074880c2c0b112040754011100c100c1303034075035405a091941e504442c0001c42c0500c0300f4103a0900d51112070198460b50040640103020316603101da90380910358041001c400101160415580e5846803600720048039806405100380540c20030004001292150f00c00307042c503148995580049840352030b0704890b8450000e10b85a03100c03280741c162000a5a40103880307114544d4109000444104600c14484440e085100c50f1100720b1040c907003510069080341d48036288112401004c52941e8030034600b400030b08038002120349241540b10000c034408407113a0061154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 179621402 1250 179620152 179620157
    0x10618090b0a0e06010303050d150b0414030703030503060609030304030f080405280605090d30090f14012a0b010e040c0b2b0510150e0603070e090412 66
    0x55441d0b00850081c1ca40c000030325501070b0b01500040000c41d1150000d048151100d02c000301c0d680d00420201e02c018010342c0c0102c152030400007810405043e5007146203d0201040d8050b1000a181d0348001e421808018541409040002800d41017aa020b00854000d598002c000700222415400c1000301500079005250181c0c010196031900381c544079100088001c01e09840c0217505080a600701c980b1780000c001150448620b080c0c02e0300050b005000090804808024011513004584200b82c0ba980188072401c2030000c401402e1119090220a40054441c910103404644c1c24180049070803c00101c205001e0703448001e2046401c400e5000e0342045c8070301980141c0242e03600d6503101c0845e00416a4024100311040804110141102000d441c6000d0601c1e06445c15481c42e034039110080108040802c0c08543d61410450250301903510100503107034805031400000041070000d040d810403448200e20503c030100c00640300d07a01c102c000c0100d0070030192080c0d00500301483c0401c9000000545c40c000b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 179622652 1250 179621402 179621423
    0xa0e0a090c0806040f1e02100f030501090c0504171509071401050306010f080603030c01020c06010504050c04030201080703051306020f0a0e121509071d0415020310140301061809 78
    0x449010010f060340c0101c3e045048070046a00c1503507451001c41e8004140038654620302070000150303443d054103039a0f4105a8590240c4031401d081d0080032a00141c0101210a00d01808003140d01e03440010b48064600c42d444800038450140040e62500c080030712684c00780c1801c001088103148000c11b11130100c03091000d82440e4004000c0042d68107000c126203450000d0138003101504410302c034000140e00700601806691415a031000e41e2030036030f444019440300703c0d44000300400c410305042c404e960340402e1900300d080c141400c55000030000000600b40004240d21000841d0344043c454104566031a4445803c56030354001d07291821890f000140c119021480685078031a407420408248101c900c2004c0c0546000c0c8816603050046050180010004d4031a81c40701051b0004202d1610340750138801130364218945054a0504100e000e11059850fa07640144103004071000904020400ea40300012103812030103040011a00403c001d60088a5041c6405d410a56248240d400540f00ca80a50312030403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 179623902 1250 179622652 179622659
    0x510060902211003060c0e0f03030426030d060906150305040b0a09080909091509070303020c011103090306070504060e0301090507120503130303050a170f04030e0a0e0a090c 76
    0x4124014020301040c26030600400c4052805440030300c60340200d0644403c0e81c215204d03280c02045456039031040c804600500c0c00d001603440d01107401c4003001d100720025403070181451403a03540440003095026036946c0001c44991000700074416605185159001040015a1806a0340207098280f003007400c120b0280c94040099480b902600788200c0d00314551680329224039170391500410b00a00c059440200602c200f90b280d6071094511405200c80e02c00030002c0c07100d00c000d150a420805020701080c0d45c0b24603020000a5004900500100400d00700050303982c9a00b001c03036003180b24149245134180191400c01a07500d81010141c001e0350540e9848581c2c40d074a600500d4201c1e117000501402c1c5074080c0c0760803c407100c0101180b0f4800e42c03003002900c3c200303004421004940d0380c40d80c2045000c2200420100e8055600c1071170f0b101c0c40000c40c00000181c2c24468507140440001420207010002d0b05080701c1038949a0000c44402070060441ca05404d00d0034007050001040b828004488050140d0f5001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 179625152 1250 179623902 179623919
    0x9250e060907090e06040b1302040603050702160312050705030a030c02060709051305040218070e090c04060c030c0804080f030408010c050703020d05070f020603041104060f060c02040f18051006 85
    0x294410b01c801c1e115201007604003100902c482e24000e208550140d00c4030584504e54030b42034000300300360a52010250b240c0382080700c094103a0781c00911480855015007101c40b15042400d007a00304030f0350400c60386101c484001c01c0448142c403a040c2d001e81a071100140c2c60038810fa0680c042d4080c692664207540d41038030390100c100c4940606125040c0c0c840010900402405026442160064070003000700124003514030201112071021034040d80801c02c080074440384e504100c04110707446503c942c0a00e18046c107204002e4240080c00b03101404004003d9103040800c1540011600501005130440e03080001905003241e0383c1c1c0c4280181e50781c6500748070702c00340400c1c0100c050ba0505a0700d50050201e1102c050030032101e9810101e02920f40c0440e4505613005a101d03d401940140c3c06071140045d201e00600501013270383d80641c861a00c034100743c60100041c40e44100c54a0000d03604640101c1d001410003150300c050b200e003003d1b00908405051450040280018020000b00ca00c410103224495680c0d160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 179626402 1250 179625152 179625169
    0xa06050301151202070221070509062b020405011502100606090e0a0605040507080a0b0a061d010210050f010f08120d02070212100e1504080a0809250e06 67
    0x2442014560b0300c81c66429240a50014595041c40440042c00c02c401c0e41c002034643c0081c54841c248003101152007411141e401e11284c405000d0075600c28200d802d006009c59031090b010008880f8600c90a0620304d140100d00d01100522a0010418850b03542c40d0b40c0312030b154002c40d44401016204123480c8119018450041c0400c8410640b104000c841c82d000d4504421038006180c2d9585a545040100e0036130b40710f00c143e5010b208941d0301d079210b46c03400000c2d0000710780c4200c20083c81445409000c021142e804803800000c40904034420180104100041c0d00d404180004e05200364200020408070b41da444403454105e801c248094991169505900c9444030400704600404440400c40c1c0d03c0c001e840c5400504880380b024100040c80320201c644141068235260354a0b155645404480c0b5400104000b001465000050301031050b040aa42da004148120400c04042c4094800010f000410a10458401c4040b802c0811141c4091041a9000702c006014400c072450042001c1141400c10b44c03807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 179627652 1250 179626402 179626409
    0x90b06040306050c0f030c090112142403010908070506060d0506060f010c0819030e03090904141507030f0507090503300a0c0606121a040503040504020c03090a06050301 74
    0x401440e06003103898000240600404100c00f40780c0070050a0081000040110320482e14200e0311340c1c403503c0c10000100800002c410012995040011070b0a80d00505d40f03445820040181d501c1d2044105141001c5d8103c0000096951551805103c4030900c42104000d1001074890015144181d454904008507a14100c40c05811903001c20300051441c00c0400b86008400700504101035a0700d4150f940c0c8100d0341c41b094500c040080c1900714001c50300c1c2c15014802c0701d0300d8030101441c1001a00c00225203400c1c00140060000c0083c284600036101d824440000040c0d0007440d0444140b4040c0c4018010300000c400c58502030385400005203c0b188940a107005444006018102e012182e00040b004080d46016034040b1482c00e4484102131403c22000b404012240c0d2070702e80c18070505040c4001100d540307074400e0b4408101f020003540010f445040c000510300c0b0b90004c41800d61141c1c00c1c01c03031070f5019940203190014400036030303100711441c0080602900c403021a091544c0c20b44480007110f4901082c030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 179628902 1250 179627652 179627659
    0x2070b010311061207030902030c1f0305060d1a07120b0a03030f180f181103011e08011805010f06050f010309050c060d0c020d090518060f04050f070207090b 69
    0x40103100240300c02d5048004103030010600703810000d01901401c16800196000c5012aa45202e40411818188444074100f4412212100c050348241294050000140d4a071010543d481c0001a83d6640c0d9480c10042160001c0104182d0481c00c4080000f0f40b00541ea240301140030000d98000c0e060040c054222101c0014120404851a59600b036034640c40c2105800144410b55540d803003d981d140110340004c081d01c0e021071920503c5d0a030103003981c240390458090031a08080e01c554030301442d442200e04540303100d50003a08901942c1d03041107401006801880e07841d4240300c064190303490758100080c4401c4c00b54008000300ba01400c074440840d111441180c0d0041e02a40310641190b010794017042c0038501a10607140401d51034000103925500c80a17510070516a20b03806403100030342c1008140d40c00c00c0181801440c50b801d010001b02a80c9081110040d8600d1100005006403501c01e60401d0110028005000b0350410000350703152084215416070051040b15000150140c01e8060800001c9015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 179630152 1250 179628902 179628923
    0x3050c0f0a080d1e09030e040b0603060a1e03050f06011a07020307051203070807080307230403080d2d05071d0402030604021204050a0b16170907080708030301050907030207 76
    0x40e00d00c0a8100842e01d44001449034071044e2030400140246000c040c4290384080790b0f03100300410002111881c110350380c0200410f02c00c110f80c0b0b0b240d01c010302041d19221218605600d10421b41c0c0110303450319410007031180c054031581210b03426000401c4d5040c2c89142c245468140c0c149944000c41d4040e48101030b5251348480c1040100781801034460034410141030a0342e14021039034031040c9140c0d01c4030300b00b00e40c000f178000104079217168004a141541001440321054036074000403010420f001c0c034080641380100006503412419180d901c18003030800d940751111020822001c40700040b00750355180c5150282090300013100c4620840044100001000d03074007403c0c03c100c0c800e000081d00300420482d04140c0c00c03c04820f01100c40c1c0000c0380711720301c90001040740307600b2803038903d45140d006484181282c3c6508010090a600400c060b00c042200070b403983d0443d0b9481c2070345450001c80754401815805001008a44854084000d42c180c1d402511020a40d440d0309804404a03c25048082d102d00b011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 179631402 1250 179630152 179630167
    0x70206060118170c0a0506071a0a1401030b07090639022110020306060304081303141b0d05030a050a0201020d05010b1209010e0d0c030908060403050c0f0a08 69
    0x3815070a2048000152000c008503140c0911006064004a400710700e54842d685110301c4d450300079400006014140c4201d420581e00d0390f03c0455200c94481204240b164080010781c90000c00c0d44190141d00d1100d101c3c12040d43d40707043c14200ca500075644400061200c01001c20100d000c0d007401080740300044c042c081c6141d0321161000b0174071100429101180140e400100260382c0d1140000c110b0108000040404104511070b00d103890101c500c1901c080f4014401c104060395060b003901d901541042c09240ea56410b0440c0f49501a0750b5007000b00041d03142401c80110010020301070f62165603240261020488020401c800761305525401070041c1d0040201c204024490b4014009602c007a00025040c18a001c0c1244103498098100404402001c80c86000b0301c4c0303a0400e200e8002e0b1886000700015007510b041c00c1e40301c5101040500900c44070341e01b854101485260031784000d02d41030302901c009060919000f006607101d942c00c42203e101c1e040d03c4070803506000c1030b03a4403070962000801d440d01c02c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 179632652 1250 179631402 179631407
    0x9060b03010b0a030b0112150c0207181109041a030d120c020c3109120f031a1504030503030c0c07080d02030301061b060c020c0a0b04031a0a1b030c14030702060601 72
    0x40d141c0d040b00d4035104841141c50703580027405a45e00200c11500034121590a083d49a10640c9250320305560050401c0c40c0e125542111004903070810f20300783c80208410064103244c0602d8050000200d406200b0200440303010340e8400b508481c0d960000d5000c0c0300c21000803500326503d9840c0a4907660002d043c2141e40716019052034205513001e0340e85218500b0340a11441c200840303194080c00d4071400b0707007000031102180d800451503007008590304040194402d41240c95403500503205200380507400c410f190700990703034030765090b50000d603446400c5942d240b50140940340e85030442e6a080c0c001c0c1c410100080f8200c80301251201100300310398000c50941c0c0c41d0580032112500055100360180c3c18604514011920754001e154100c52140c00512500c03402006000c10712480394030240320769109220500004040145c580d0a052000500b0b0505855441d40c900060030111032900004600b46034450205426401c103044404040d1580b00d80440b184140c03041c0c900c41240d0b5100141c12880000d0041d60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 179633902 1250 179632652 179632679
    0x30c090b010201060305060c030702060714070f0203010e03040b090a0608010b031f21031d03070501050c16030f05010f05061c1103010c09050f0d020a0614090409060b03010b0a030b01 80
    0x180c05100210313202c1d0703503a1140b5040840595038000d0242c000410000e0740764042201d02e811864929140e201c8940c0c8000f0400140501034008001d000c00d0070385a000e40d80d007500821102c00c0d154007aa503582d6510522600c0f01d912100415015444a80b00065000e010340c101d20f040380c074801c0a60346544c1d2070b5020540a100c854030125a210900000071809139854601c1c1410110084100c00a4010504024041c54031106604849101940b8401980c5d00e0119283c011641c00382855500e07001030703c0c0310604016240c1c1d0386080c0309200f888000188103d11150312a428000d800802c020305016951000b50345089070081d41010b1026401d01285602c6250b01c0100c9015039000414101d0a5002030309440324410312000141580c0e80030300c59031504400c8280e0500381241e4a1519426a0b80410700354142882441c09010600c00c4815000000504036005048010000c0001c44a5851b2010060241f80303070150084d80307401143c04050404510490a680c0c020710150503e1b03191072160504c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 179635152 1250 179633902 179633921
    0x3050c060702030303130f0c0306270c1203030b1203190306030f0f15240f1a1e0406020303040b0a05091f09050712111f0302090604170a03110304030c09 67
    0x1441c02c0c400003000300d08c0105110002e07520039100860082e01d2030014918131007041c65001c245120074046031001803d0200e4810481c2c0280300600c01d00121414241c005055130f0207426000f8081a5090b031000c5004070040c40210f0340d424000300c01105e403920031070440d80349000051080e24a101090040b0710302040380c00c03015206030350410506a03201c422500381c900401c800500301c0c2d010380c0c5d003040311155403902d0809001203004125405180c800d8140766807150b200307a880c8203907000460b406048c14004400c4003580390603640035030304d03503030f03078030004e5607940111410b4aa466040e030110b850244107025107801090076a00a02e4900700f80310340d805c1e0081c024158400b84554801010300014400e114540040c06001c982e01059881c03800d1002e00b130424800810322800500102c060b010f4240748440c0041c02d498030340142c5414100c80441c000744902e03080781525501d6032590150060300094103000080c440c1d6602c0340e010210070800c41e80d030300407408024080c00b00a0030034032101406a0004903003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 179636402 1250 179635152 179635163
    0xb0406020705060912010903120506060708190c0812040302070e270c19090b0103022a0c0d05030a12060b04031104110403030f0e0a0609030f06060b03010f03050c06070203030313 78
    0x4130250500d01d0b0b01f1982d000c034084000c20103a440803203009034140301c0c45034800401d48242d031420406a40d0b0500610034090350101c80c0a104504054440c03041c107602d46d20301d078804401980e8410009400c440744d10300b11800c1340103104040001c00d6108035041c0c4c2d9030066154a040b0f008524030300e64421480c1070159008002c42c0304d03003001c0d4003080e176a1401e000c1d8007407100c03210380380d0490030019910b003584c004408103070515004011034480c0340d00354011035002c2d14580040c54011007030001d07003c1c00d108540c04075542c0941410710a50034080c0c00700041c400e12101d5120b845e0801c04076940702040e110f07070f441800c030100001c3c001007010640b90741039001423180c014030026203002d0100059a040e0001c3c0c00070703000a6401c51084104a40226028038203090840301c5403003480c03522100400003409400020b007100c480c000da1104000042d0400d4015012080b170300b9460f582c507000c1c04005120b10384001d41c0e841c803410050600509050341101c40003038003d0040c510319958800c0107490b080309058202e44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 179637652 1250 179636402 179636419
    0x80d05090d060b150c1507050412060603020d11040506010c0228030602130503060705030f040f08072003070617010504050c12040f060e01020c070e090f07080601030c0b04060207050609 81
    0x36140e41340d041c0340090300c0c0e21026940d25244521202490070300c100c1e06d815407600100c824044101d400005490860740200790300d564262007842c3c41005080b0661000303400c01030b441001c0040029221481494402c02d580820140e6590310044801224410010303421044100441c00e03449004604008050f610f40c0000065a94a0341ca400480c0e0040071298081c20800c0c401340283c1c5401d00000360031000781d2802c3e50540c24841390001d40c0340005032000345580d00345040d100c200301e141410350340625003240c0e1000c00408110001d240040081040398070a0090f5000420711901551001d042c0500d030480020382c607801c090500004002c041c180c0741e1002814000d50800c5061424030034071607072045446c2d94030100117141c0b0005070750460f42d034029170340d0040c4502c0e9401440018640100c44080003001040c4d02c1e0303240d04a0508041c0c9a004503c0c0c000e004000c00c9400c80014800e040b60b100d003c0e500e00c81991031158440501880c05042c0c0180c0041800300440e103041d0014010b400c0b4010004130 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 179638902 1250 179637652 179637671
    0x807090302130e0c01051c05060d0b0f06010f020114060907021e030901080105060414091515031e0601090e0a060905090a021906050a03020c070503030c100501080d05090d06 76
    0x40c0d03070070386064012400d0354640700c0c0e8810f0300d0070500c01c010003180e003800d0517410304142000608440ba005651810b0b002d64034400926250f60380c444203c11035070070150003050303403e140e5a84240d440c021240240481c40c0a92128411403052081c80c2d250031540110b50030545844040081903d0003900c0c4404500c030394140d004001100c0c90803906070318854401155104000c00014214660581c4210b200e480240402c004800e07441c200e02101e42400c9806030120360b1002c030314115001c4004581f60300044000c403041ca180b03001d840218081c04d03003005036210300c030004101c04905c0c2c80219246e500041c5c0b0808104160071066020070b0304080402c801280c91503c03141c0500c1180c004540341429680f00b1014001542000010b01b00341013902814609007900707144003e0300710b12926032150f04040e03000501070f20760310b01400307940042c150080c26a9a14050a411107580311804404200450b141c4000005c0d541c80015001c41140c81d40d48071300c2d0031304e4041c0c0e041102c1c00c40f40490642d005070302c682ea400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 179640152 1250 179638902 179638909
    0xd0908120c03010608010605130e070324050108010b0f0a080a2909090a0809060c0f010e0309090f010807120203010f0c02030a02071d041113090b010509070f0c030807090302 76
    0x40c0301c1c0040d58262600c81d032405200402e2410103034400002d00104102281041070100d448030159420522000b1094507a440304800406402c000c003103100344500d8070f900d00b88002c2150141219003d90b90300d100ca03601c80300000e21a10070401c40c01d9500004000000d94030340140e03802640050810b00004c1c00e900c1000a103022810501680c41080c407040704210b40030701c0d0466826030000c502130b008054150340707590340e1b86643c812180201d00c00c3d5000b08084050341c0c400c2128103014007085009004040071065520f90300e8100c0d007000c40c40b9258030000a1310030450010003604a0b0100c100502c0074501c0c180098103140700b00e00080e6055521741f110100300d80814014035103407940c6a401596600c28451000342400c5090f005404a040e00e95500082103145401035034110b900044103c01eaa0b8a40340000d425101441c1034142c0a4248604003091141c0d0341035140c125101512081d405541c1c1d280119202007548000740c1c04504a11040008244030703070103181d8818600d081450b8080d4032500003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 179641402 1250 179640152 179640187
    0x303070605100b2b14071b080f120c13051005070f030e040506042a020f1209011d06220b0408100e15160306050d14070b0f0d0908 57
    0x41298641c19082d0350781390f1a403d09152101040d104500b04841101d81d0031050140001078a1803003008581201102c2a20109030300c1e8503466800701c5031513510a840c4090700c205800141e1940c01284140b0002000301c000c01088070341c1c3c030064120003207401c1e0402e42001101c0b00a16100070401130203220344d80c00a400c00f0044440c1d40d000740c0351794011180c03a03010001600c40041c0481e0140e030500d03080141e80003042c0e0101c558075410404c440380307800600c00101d01d48820311001104910856910440d820004001001412070a03622503400d024410710120302d012408940c2c0781c020000300041c10760041302c030602c0d0301070400e050b00e81c0034a141d950116800c0341d00310f03801c04140394001250844511001d44182241d082e6040080c0040541000d5102d61b90345c0002e208880c00720541545901c550703c25804080034010041c098000d0790040d0800300321000f901c40f413a0b80b140c410b242e800f1418100103400c0d0707102c1c80364240321103140a0302c03c07082d10007802040900720b8901c1c3c8140001c1105a01c1c4494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 179642652 1250 179641402 179641417
    0x9150203040210030b030a0b04050313030c031a01062a0b0702070e0a0506030c0603070201090204330b090418060204030b271c1107030b01060f0503060303070605100b 73
    0x405612418603004000030b1071014505401414500715540c00c481d00c0114030410710b00c1e00200c08105035512400c000303045200e0141481482464450040208203151035240150303800307080040d280000d41c00c3c80d000c18032004c3c0150000314403012030b00300f2050703800046004041700402131094450081d96500c485040107036124809600015024425580300040440e0b20542c9040709000ca42004c602080d1244030301d942041c040c040001c00154014001d410980300c569000c5d204010258104c408484190191010a03962003940c4801541c2d071010103801c0c4041d52442e08400386402480307801c0100400440341c80c0241003d100ca0b41101080003032020308001c50282840180d80d103403208400c151343c0070000382c400112480c1058110102000104502d6030141e107482011545050103040c1d0340e82c60038400d040340c940b240c04c0e0301100b000240f9003079034100c44503138a8034401c00b903c10206607440c0c0811101d003600f40c1e2042c00420082400c4d0f81240f600031200003100c03090203485580300c4d0030340d034420017 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 179643902 1250 179642652 179642693
    0x1202240301080d0306150c140d050a26010b030613050a06080c0d08040b03060604030210210905030d0c1808030717030609040615050607030c050106050303190f020109 73
    0x4000c0359100f4440c040640303801e0b190030080c0724240400e04030107030564502c2c08100200108030740100011251030404e90240001120ba003c0720302000200103601c0305400318005441d0903180c4041c600e40c14038443c1e01c05000d80307118445d030303003441e0500000b9000100603907032001800000d45002000b81c45058024022038102042ca94100641185008081c028140c060100b00359904081f51506c41030764240d42e505031aa0b5540e884280024401d40110b8002a41c020101c4000b01c4620b50441480c3c540708488084221040300126100f40485614500241c0b068004000b00ca4901c1e00035801044c00d2202400d0143c500700e100602003c0c52503564014500d01d5100060a00521040c407408044158020720298038614144e00440d0149030040d1000301090b49132032560200074030322501c4030040e11001c1c01c0688c0791041410003c04260540710140c48a520b050800700c4d080c10003100b280d81e900e440c00340006001400d0300d81200c5c51890101c2c0ca00031550b0320500b05d00001d41070b40c909400f60360b10b807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 179645152 1250 179643902 179643907
    0x41d0403200601140312160f02040f140a1b050903030d051305060a020a0c0321020d0207060509070e04020d050c090403030204080c03060907120303022218020a020304120224 76
    0x90781d001e00708582004c18a100341e010890440b0000504070461341204034480b040041082540742039a10700c103003194020761041c01c0c079590415860141c3d003c400111391002000c0c1c0182c8621503044122002e080540350860942d14940c624140500b00900c0f03c01d4024084038541900c400c0032000300c440039141e000389006455400000e102d4104500d43e04003201d80c804500d0190088000380c84070400040041c10b10441908a02e20780701e00f003c0344002c06c440048107660351420056071100a500c800404c96070249802d000c21846400020300d007003641e01303590000086d921107800300b0841c003903240011a00c174407502d010084151550320040340a24440d4401580303403070410140904000c890100c1c240a03501100801c54440d01c00150a41110b000907503d07600d01c615420104c000c0d115504020300c010320000440e80070429076107030100868045000340202c0d062400c00300c00580c0f2504a0720340040c0c0c800d000502c035284543d090350205510007003403900702c60600301100c558a00074051950480030301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 179646402 1250 179645152 179645159
    0x90a0e01030303021b01020c0a14031306030e07060c08090103180501380907080a060e0103120807021b06090109170a12020c030a150603020d06090203070b041d0403200601 75
    0x82c401e00c02d4031002003402903043c234052030314440d512443c801026010303068130607140e12064402c0c0100d850300e00c1c00601246803070352690b5015014010301d0500840138821640c00013001d07440340481c001000d0380051020315000e00d0b10300441c00780a00c040400900c5841221080001c1e00922a04800e480f260104018024030401c2c66144141d0000038203404010040420085985115409500070b08508ac01d0b009a102d90210030001d082d180c100304102440d2000100074400d08003403811000b891030340c96000c290f03030b1000d0481c1c44448441c4000407107204845c3d03e80640ca02407014102c5100185001c00300aaa281031048492204801d2609070350042130000081c06079140e101d10003c492400100824074145000c242d0710310001d04058020284082c117a03100e02c10b2a080031f4010740d0001d00d000b4142d2080e08095004005002c802c134400d00c500c402c0051940340650640c0d0454a0402100040c0d0303e48080d01081400020011820006c175070b44901e000e0303410051000f0744100c90b01d004104030340c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 179647652 1250 179646402 179646427
    0x909011401080f0c0901080a060f0e04051605010210020906090603041a01060f0e0d06140108030d0509010c0f0c050c120f10090803010515070203011d0610050105030705090a0e0103030302 82
    0x608284841c203d82400c0003811580c100c200d614110080c80e15502955525482000406454003e40e04500302040d00158540c8014a02c0e40201d015405440403400100e00d040080503162250501580101100d116404107580c06000754a43c0074140078641180c0d10000f0303010b41d100300ca0072503103842c40318010140400d80ba1801405081a420700c1c070740004072640054526441c81c44c485100e55101210f003402c120030341e0020102c495000300b6403034095840d00038103034407508103100501003917282000080e6120014001d2880050281c3c0b95915003010b052300403114102001c000f518544a0050302000720348407403802032508a402c5000e0100030541851040c1012618031020542a0074080444041442107044a04444040b60107004804242040e50200d021f49940a5455464000c0340d030030805542d051001c68400c18401d481c643d60fa40c0d072000d208540e26000d420300040b010f200080d1b029003d03d005002c43c1000411610f000c0380d03141c3d2580d045c4a003d03002200003940204540d0500303035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 179648902 1250 179647652 179647667
    0xa021c1d0a0309170f060c070203060f0606070b071704150b061c090311011401030c0503060f01060e0f040e0309010f0504031509030c06020d0606020f010e10090501020909011401 78
    0x200280c06030101d00c016480007001e603c02c1d401100340e03458910b9124000306804100008058a19006503a1980b42c040c61140c540c1d0040300042e402406070310300107100925220413040c42094010300c06820304840d0b4403410602c04c00140754100f03101d0036800140c1042c00142045200d144100d0b070100d42a029141d07204143c841401116004090501c80b0102d0103041c24208082c06003072900000d8071b8400f504007110480b05000c560b540c15440d211011b03000d03410031001c49040e28041c1190344051951541450784c0c3e1241203400c0d02840595400500102d880b0307804050140c003008000001c80c0360200002011114030300302818050780002006601540c129101c40708100710382c2001d50505245444d10510700c0190310700f04c412b80341d0344c2c41e0035001c16000d9900c54000301d402200c03c54551065504840040845004000c0580311b0410301c141c1051050041c000440e0b0b050002d02032580204401001801184101b01d07041e5400703000300c41d410345442680034020701c00700e402c090341507245070000341c80320 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 179650152 1250 179648902 179648951
    0xc0f0708011d1011220503210304030e01140d05011508011d07020703140f0124030b101a1905070b01032406120b10031a0a021c 56
    0x142924402d820b004000851540d010008000d03010070281e001e0001600305100c2e030000100925181e0741011540090140c2407820f0710000d07400c0b120030310100d80289850407905915042000c0d810030000d40064403420802c0c42e1204107040100490104401b10380454100540c548190365840d401003015008080d40300b4802845800c04400d1941002100c402850420101145008126001c41c003d103208000743e4006503040b0024001015030402030545519803c9e4040400e5800c11004400d201d60860030400740c0b8036002002d41e400380c0356581c0c01c14030f448001c01c0005045901ea40016051840341c0d0000c101280400c105555042d166000c0210442d40d006a034040101c14865000000d220f00085415a60480c0982520307000c540841e2a004400303011019a650600d040018000d900501041c1b40e2031140d5600d107940e42d036400da0000103d15070321000e051100031a0360703003041a801d4020103420020700300c1c001d4070b00840380141300750007581c01510394000b0350759800c522000a0030f402c103203512 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 179651402 1250 179650152 179650181
    0x3002060a0b010c0308040c321e040c110d0314010e010803071502190305070e0105120703020f0f18010e0301090b0a11090a030507090605060408061b0c0f070801 70
    0x10384108000070300c81d030302c03c1000500313228000300414203004001c12084018050a1005c071540360b2880c02c00d0b40098640ba0019a0b4102041350040d128508070114600d00880300d84101ca108003a881000050b10914848200f0301102c69240c2180510600c0b08141080994401003a205c500e00103040d2541c0b01680003240740c802100061080110210454260300d0300800704110012b564200840248548010004407800c00c4040841054064200903c0b41700c60703880b055486215032005640e03500c030b2768594107501c80c1c0c03000005108034040d50240c41940d1034030248508000c44c600b0703080195482150101e10034070030b64040070391030360740b14685400001b0b0030313002405011025a5421402e5101400141480b6116148a07521003c0201030b00d007040c8004011124099683c20220b440e201c25000d074181050402e40c0100f0141443c1013100d085070b03184401020f00340c0d03ea860900c42c0c0b00c24440c100405000c100b096842c21242004103158000d21400980391807843c0812076421510380c0502d000383c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 179652652 1250 179651402 179651411
    0x1140f01080a0305030c090f2d0a1a0c010204050603010e010504060b07082d0d050f070e0a03061e0f020a02010c09050f2205090d02010e030f090103093002060a 70
    0x1d0703004d0140c0e50012070940800d0307103442859001580701a4640c030104d40001040200303200a885d449250300301091100f10f2500000f504d0310a1019103001e90040b842c041094013508040c0d0103010008001c00b00340d030f500050506880e60002500799000703070300c500c0d1858001c0b001401180341a21880e001008030070203680c230340452a680c2c15210700039070301a01401015810550303030740c0414030640301c0f052007a080c00c0c6907907400444c0c0080040c002a900341030b00ba000d41e00010030f603034028596011011801044110120300c0d40d5141006882c1002001403001c80b05615691665003038021030440c1e0200702009a01c0c1c215015000b070031a104441c0060801c01044010030040d2500541500210802d940324803000c415003140e1186c1c000c40b00c0f4400c00061401c0d0030043e22010200d0340950030b00c551750091205a0860111a1784c3e1f00072a0404c00030b81404100e205050360180c0c0c8000300b100c0c070500243c810782001c2d0038070390000342050420100740259180445003403941800001d40c0076502400401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 179653902 1250 179652652 179652673
    0x50a12060c08100e07020a140703290103140102040f060302181f0e04090503031815040c0501051c110301090b0a0e0105060c0a060606020d09060e2d0301140f0108 71
    0x98030a03000b072041521a00c04c070340104503214824405114180d0700300140e101188a400d043c10f41d16840d610060b00c0b491505280c1196102c180302d098502920920361441c850390854540c59581481042c00600759982000005201205c40c0c041c80001c02958400684500c410400b090710303914281800d51260725420700c03a19a50700e4043c0003580401c500d140040c00030701d02a020400600303052034041e0541c44007200f00100d240380700610340c400008420942e80c5220300c156403901100c1c01568002c3c44900c40c08003d00541d44035001400c0e0051595041c00d81003000e0306840d030708031052220350107882c000000061107000c185000c1d64544000a0b134600d0745e414500320040684075418002c2034401d41000920070380c00b0fa4100109401140c1114040200c196288400f079a900e12454031400840c01c405000030f14035004030140a580007000d0140900f1143c4440210003035030640c6c21012040b0702042e24480591004d00c00d5202031440355020621a0812a07818444002c0507031040c1c03601c0e4017064401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 179655152 1250 179653902 179653921
    0x80105060a03060b04020f0304061b0516120c080d0b030f1207060207020604080709020d0c0815090606040f090204050a17071206140a0209130c0c0813050a12060c08 72
    0xa41c200c83d000040002c8001030800010082e100307021403a6080384001c01808140300c0540d200f8040388410400043d0140383c0400300f80c4850040c2c0244000c50200e241d100700104641d0160b801c079030001c502d480304840340d803544c5685045c2c00102c9141e100c59030ba2400c0148a080802030b041264810030010460031040030082e20161041000003400d042e00494118115200c0c1d00c1503501511020702070f100625103440c4034000a40040740c01c1c20b101c07814044c455000a008a0900b40903491440003100c2c070ba034081d818005080c0c07028090b650800007c010016806003403141c00d0002d4110705c0e101681e29031405081000305503064000640c1620303641c0142102420000702d00080320915640440b481c0081c0c10f0800c02000780c0242c140d51481c0d07082c00c1003402e01c4541e004080420044607034100694183c030082080311040c0f6603080110b10194855000f10702d050f8080d2007403182070354043d0060754981011038003d611540c02b00060040c0c140d1a10100b1545000703120078060b00c3e2030151421328200680c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 179656402 1250 179655152 179655169
    0x909031608090f04090b04060f02211803040603060f0b0f040e040606080105040c0302011b02090612010e070806160e10050a0e15030115020705030a1b030506091608010506 75
    0x6161050000d03440e402510b8600f142000254014820001e20500d4180260040c0040b101164800e00c1d007400c40030194060704c25654090749102c403030754990784043d01c0480d118601030401c0d100341100035096144841c007040248058440e40e03501041d5180352004007040340d05150043d90240200b8400110903c0340c1000361001c450318030603035141686480c2803180050042e504540300b65401c180812082c800e00c00b4000d000c0b42d200303076500c0741e20503100303c426100e50130000d200952002c4400003090301c03441c000c000ca698484980000140c200d044020703042c0340850b95400442241c00a41c10081061041c2000007600592030130000c55450480d00001d0070b02084410f403109020000c03036a101100c2c4a088803404120340940003c1c019105110a4070b61500300340f040c2089140b1010714030841074030118065003100d80260003000e2001c16a501c008201d01400c0345020042c0c504000040461403c201081c0a44c250078098651249030001c503a0f0729003441c2e0400041c50f81032100740081078848018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 179657652 1250 179656402 179656447
    0x50303031302010c0f0516050f0103200a0e040509060106140a08040b1b1201080106060309080d0e0307052b080601020c0111010213060509040b150414220b090903 71
    0x20b14000700e5005140903d00c440c0d90490251541c460884000e0b0390801302c1c7c40d00000d5603001c44034900000c449800440668a42d180409040d01e0f40011010807224160003610450800e401c0009000102c00046000c0f00c0e42124441401d9018100400450b0307049107502004005c0301e01074a18140c9140000b500c5c000740a00020640c0c2c81d128001504810003805540260403110f07007080c0d0b13030118000044039048081c0200141b5518113040043c00e03900900c120a81c2c180e014084605100404043d10024150030580d40c03101c0c00304120000000346c0510200483c2c0615076180034401403501902e2411400180e108410310040000b0b2020913a00002d501c040d002d000d1134600807503030340d00014a029000e03032225403884545803030005c120560040c0103000d0700e0800391401c11003041400100503000000302c4a00e00d80d040100018440c1200003030b01d0a2030080d002d080b80d0064641140c00e103013481d1000d500c05040c243e440e002e42c60366250104c2400e400c0700e00f2000450405000401d030707450010300204d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 179658902 1250 179657652 179657657
    0x20150310060806061c1805010c0206010b1801050c0304090524030106060c060f090c1202041b08040f0507030f0f0b090601060509040b01020f06160215070e01050304020f09010f060905030303130201 86
    0x20402c900040c0c0c0354022081d80350101da010340caa41020315240f03012709040e08480001d07001d050700114650700d169090b160319600389054030b29007141c6800150345960017001c0483d920f01080001240a01e400d02406002d0000408600100291040b10200176545088203074440d9040040810215501000101c00d0784d410080020790310101d290154001c0480c2c1400824842d01c4c1c0702c00041003440c0d102c09e405028000d441c00d00459070469182009030a00e000303a00c01180b030001c04500411400d000340e91001d88500202d40305151681c0b6407910a0498010489041141141800c10070600b071404e107800140c8240141444e50410001070020b001c1d10085500596440201c481260320800c69140c3c441105c0094458604005200110082441b4200d401511071000c00342d6082403404819841100c441d6100b0210304003500045407980d02c0944207903030090348510114101e642d5100d403c3d0007400801d512001e000d2034081b02601250b0241d100f00d11940090041216034075019a034500383c1942433 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 179660152 1250 179658902 179658937
    0xf3006020307050d05010303210b031e0717060703060602031804020913050f07030b09150409060b030124050607030507080d022502010305010b04050d2015031006080606 74
    0xa4011115130048540a00885041c400004289074118540c070410140c07010b084e80c4002d60501d0f1003800d840900406a401d50f00000003295601d114041c0416160350b48001d903040107070741d02044586445841c20104068210381d0900c0142905840380b44001c02c0180065424006400ca02e0704d03100c00f0b60840703a0702076034000030341d054039507130389840d8880704070502d103081086003005840c0c0b00c0305480444503000031030b2811030244454641550054820b10b0615402c40c1c01201301800d000180c00b059004a480544400500009507401e026099411041c05031500b21284e2040f200ba00740c6005601c1580a104100f05000109601200310f0342c143c2d0300202c015139504100e8444c60f00034030447c0c4190b403242c0000c081910480045401120704603000f6a0b06102d16600c070414080c0c10b104a1264550018846100c8000552402028802008112070100c0704118000100e50b0035407108900f1032009000004104c0820780c14280c0c0400f600d038601e002c1c0032901d07111020401c180b0401c0c0c0c515180f810107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 179661402 1250 179660152 179660161
    0x91b0108010e070804141014060603010e070e0a090e03030402010810121103100903080a14010e0703090f02090a020403030206010f03030c1b180203010528060e01090503070f30060203 80
    0x40b581b00f0040c0b41c6000048489080c1e040c064800100444440b40d10411781c001c01103103243ca0800c040c1c170305803000072031041c1403529455010348a0800b4180301d107402c9846450700141c041e910340301d0146a602c60102031941c0e8030b840e00c001402d48d44000d002c8280010284d20503c40c4c00e11100e2201010380d40060900083c8810b200080d182840c1048440b00440c20528804200b40d4401d00450241c0c10405040c03008031004542100c042c2401d0145038a900c50210010300514070039040389030454020f0611520300341490300403900345c5808a40107071102c8e400040c10420968104061801058130010304401241195030080101400000c0504258501440185000d40640680004220f000c104541c08090510100041d4000b440354070720403240d200c2d0b066182ca448030720100d1828203c019200310582004800c0c1c0781540c3c6c1c4462141002018800822191000c00800e4007802d0001c903440c03a030600e404a030110240b200d60356103070315040c403480301c1084a52034040c000407144c2c0b108003da260faaa = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 179662652 1250 179661402 179661413
    0x70302010f1107140c030c010c21020f2506080c1308010b040b0603101a0702030a06050603010e1c050906091908010c111207030512091b0108010e070804 67
    0x81401d402400e5500d4039041412494080000b0540548141c0240d00c841114a1a09458510740b02c00780d505078111a03a5440158400c14240324142d22030042d118964070140c00540b028201c02c132000d00036a00072083d20741101e404102c1d004200107000d0015456001d10322004490030001d00c03440052042e0074010a2010006909a07088203035008583c10f542640e07180003d002e445602d28882c0290700e05041078010b8144082100d01c103e00c2c1d42c2030a5841c515101660381d403000b42440f0311340802410311030580160380902206240d14040c50001c03580303040001c101070031956441400a41c1d58003110001d01d1810a0a6010081d01402c0c1080c917211098100410010302c0741918896001c04016031304c083c100000204602a507040c0301c0200150400048155031003c088140342043c1e41c408100c07844002041c40c001c1030346c40d00c030b0302e040c1d030401c0202c4507200f101446c1a121890f40d03030401c00b02403807007d00e0000d007081c02c42d0092800c10900e500d031181c824610b10380540510100708202c00082d05120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 179663902 1250 179662652 179662661
    0xb090a030903080c0114040b04020a0b042103020304050a0b0306100306031a250c05060601080c040506030a020d092001020102030c03010905130209090d0806040218010807180308041d090c0607030201 87
    0xa441001c1040b40340608d8400d45c00300045500300d05c43d050624002c039502070904159000e860008103100740b42c41c5146d016511100800750304134218031007004045140d440340d030b40d0100144803502c000364503803e104003004402c00401080100301890008100040360034080081c0210031420301c80c110030740740c68000d92544461014036010200044080300c03007999004440c44041800b0308251905038a030b0b80300442382000162403902d41e084081c007090001c1e14202d801903130006035a0f03600504c0c1480030840304050f500707100421364084200340e005a00e410512101d00311281c00901c021841d61030b100441805902060161752407496a42c000605a05034104015500b1500205200703400c3c0341c0126025614030482c41108009160391010072082d003000d0023918034503024503030303010342e1180c05100440d11014020440020448214020b5810007465034000f0007950281ca5119503550401c81e80e2070b0004694924010300c15002d10070002082000700d888440910f04990260399402d2a080403405030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 179665152 1250 179663902 179663921
    0x90911091012030507051e0606040c0e030708030a02070e0106080406020a030e010914010b0307080a24062c0f0429090f0d051e0a0c06090606030b090a030903080c01 72
    0xc00702400060b003495000005010494450011600440603a200c600c81d02e2a950703242c80ca00e41e2222010035020f117095007204128100b14940a0329441c490000285880c085a11050a5410010302ca090585c5d05201c280040c204c66541e191055142200c0200a044c004001511b0304d84c0c08608070f40603d200f42c000b03461a041d40d01c0240b041c0b002c3ea0801502c080141600b0300460340c43c00075402c6042c1030108a8070b0407100220090552003005403070b00b14a40109400703030f200d213070b151510b22070000c26644141400381c4a0540503803901140340311031140d0400a480b09140c40700d090800c024a45c1450071720700d6031181d4000094030407110103040001b400c505a029201003000420104016034a000070806942088442103411080f590f01c4c0039916886003001040b038441000600329402c500301001001c031030480f454565a140c0c1036884d180112043c40030115500c6445400c00c00074080000407580c2c0249114000d00600030866030090100d03135140c480245403440200d90508513040c00c1d030105a10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 179666402 1250 179665152 179665169
    0x60a020708040e0f1602070b070f14030d090507050f0d110402090d060b0f22051005061902060108030f160c1509031709090106050c0a150c090909110910 67
    0x1a0f08110200c1403a004c02107510840f82e240070141c40107164070009100040f909010051403410300252960364084070110000c0d620040c0c003400b0300f40b030b1136001c10040140c411240d500061901d618682076082020580c451842078034840401502a0749403408034482540c84030208076909604070108010b070043d014050b500040580721901400102d4214218050342121301c124403006000030030200e071001c40c203600d04040c0032010320030741c2510079404981c01028070b182c5110720981d40c40018556038403010703160801114412210b5940c54042243c20f000d0072440002c0c605080641c07009071110b0003890224442d40b02250810000d000c60740e44014050050340c0905004900519405400b0840c42c0c801120090711a0900c001c400e0b02c90010790780b84041c02031410030710fa40b800350221040e40118201500c10f01170215001d00140c44e42c144410f1941c1100c002280d00410301c1400b038072203003190340400402420440c1100c005020b84a00141e24441110f4220054450324506442c42420380c0004a8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 179667652 1250 179666402 179666429
    0x1090501050a0918091103070308030105060a050d020a1710030302030a14040302030a060e060a060b0304020d112d030609060a020a0c0503030f01140303120105060c030d14010503070e09060a02070804 87
    0x300681ea40d0404001c00c1c5c01203000001c01a1b54009144d034403511440040d080100a20040c0203034582140140803950481c078015040040808031a02268441c08500010034501184540920011a1480d03032040c40301503000445465600d01a40780e00c60030a040c0100020801044900040001070314099030300581194442845883c02038000c2c050407200d41180c0c4038103000a8071000490255400751181d5804039400c1d40c035181d09004002601c10801c859451810f4008030164540c2d807504c00b1403003000100650a0407050417003410851401c003410f03000360031000c100803442600050f1207800041c4040016034401e44101c040f1110f202c1420010024040001032010001c0c0c402040340c16200c0f54903c106007140d030501015aa0b00c510500450b005045500402540c64058090401009144c06903031030507000c00d0000007154020346045c5540c400050050005040801c0702d10058450075a555180b030030820186540c50400600419520f900050301c502000b5501060710003c0445148500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 179668902 1250 179667652 179667689
    0xe0906120313060801050a03030c020d060f050a05060109060507050a1218060806090604020415141303060203012606040b0c0d05090607030c0306051c02030312010e0f0703090201090501050a09 84
    0x381288034510800f00020b8542c4000303d2036144c1451003104403503143d2211580c1c080e00713600b4483c81058445065409503036a083e5260300350b5880c001c4900c90350a946001400d86040303000580030040c1b94000340c0400c14180080c00c000764000800c8542c0d00d4110050907800314007100222041808085002c91403030010100007035154220890324000c400841c1d4658095894009000490203a440f608600044103102c1d000503038060150420b0804540200916103186208150a04d450b036900443e001c2e580000100403252028041c80c1015944c1409403000004030b0004555614000e00040c20340041130000c581c5800c4007a040b1004280c0080040c0b003280703000501c403500d0f0301e0100e0381500400d00303150b19144868428444c900580303c000f0034a120b1005011540c2c244c94001500490301444104488801c0042e0b10106600a05200480001502c1d00105a42e0760031006003004080c181424401030060381c1203038011055400c2803800d103484d012100b004903040d00b10fa81c8911055490404500f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 179670152 1250 179668902 179668927
    0x2160b0d062c010b3603031606140c040611030c010f091a07020303240303070503090a0803090306060d050a021009080d11030307050a05040b0319060603050402010e09061203 76
    0x11618241444201c060613039a0300d01c0520320341305600300d000241000c055080200060b000c2003006502650100421054500300840d2440d8403542e1402a11107031811000100841401020980713034501c0020351141c1091002000503000e46d0140380184550074000d41d103610410400d4600140d0b000d4001c0c44012010b090500040082e000c041d100540210107000311000350700740890140390703030b60b008600d035990b902d2003408001045141c0d400704240c10344900b2079564041019201c000d0040c07000c0c541d150030420800c02d0303880300d036400300229400600000042d42c1e404140c840d400007054500d81c050b00c186141540c14000318540017940702100c40315002c1c0090307008507410240c0f258541100d680e05440c0b881a81d920021004000c2e0507402000040d21541c03140028101400041c24460f00306030711801e410311550000c032440100001c0d00300903030540003010700440d00108200c0c10b04000318145900000c0c03201d914081c00902411b640404119140c03910100d01e50481210b070242ca0700d40d009100309 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 179671402 1250 179670152 179670209
    0x3010b03070e01030c02060a110d1a0102061803030f040201050906210a02070222060e090c01021006080303071815030509010b030622172802160b0d06 66
    0x11903002030b031040c20b280142d501a21174460810f9081d00207005c503690781440e190280c00d91217110008094180500d01076824140504032060100001580408803d44002071501e180104043d1042403032890201c82c002c004002c50303410101c41e041d9130b0241d03900d900050303c462003209941034121000203050540100c4140d40400021030071905807941d511000c403807005038000d03000007a60111000c01c80c28050740099100110340a1948004900a5601c00d2840c500c50310480f06107140d60031001024285680c180085869840c02c00005c00007181410317540f40d40da000041040c802c0c00014000302041c0410001210010002e0202000104010400017005403005030b40f1022250b00b04807942010786800f00c2c401d842021000100d43c0c00e03000c0a0b0021038113038540c900559240a0407403442841c0a0300340010044c110080a495902c00c404900c40c01c140d841c2c0850020454000041600e000a070b4102c0440884c0c40240500c1d8540d10a070f5440001401a07910450030382c501c1b10b210960002100d0030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 179672652 1250 179671402 179671411
    0x20f0a0c0c17070e130204090c030506090a08040603020a0207050310020904140f0c03040f0c0f1e0501080705070203030c100e0f031c1a0306010602010f0c182903010b03 74
    0x1c407102aa55412410860342440c01c581c41290000c44003440440140c090681d07008011034012901804542c0104003100e40c5107400f9600100e40020500a00900300082d64000d940c0100810808100307440780300300b900440c050042010b4000032031014080c0b0802902000d0503000303058400d00c00d500356140300250b00c2841d24500940c24030710440000c1d20fa0450441c0f04881060907180a692030018141c25544001c0c01110841503c019800200b440c1141042c0600b006040300c89072103091042c8240e403400500d8203400c0203901e0a60170300240e648880b246030031800e5814038940f500a184006410f60141c041415400e10034028030094240c00c0703800159801500c03009542c00751070030400b82a103c3c03003007074084000d103401d58445091200c1154044801d25140d8002002c1080030500041c0c1015000e82c07014005030744544890400015620a04040d908607040c80010018182c015409509480c815079000380790100741200490782a01c0c21511751022490303019503e603106d4400d07407100e40017070704d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 179673902 1250 179672652 179672663
    0x60d14010b01030b030309060901050327060403030e0c030d0503100308121b040e0105010c060603060e0f010c0314013f03030501060503060603160219140d0503011a0c01020f0a0c 78
    0x513195070941804011100d04020141c000c0d850304014000544184c1d001418030b205141840c008500c60b841a070004120f1082c2580180145003014100181540c981c81a94905034202140390b0780940e8001484880043c0c0c941031464907961140c252070003100c003981c0054480307000095034180014660310041e200340c040008450f00340422001440c02d50040e405100b007100340460042c4860f41c001c09016200e180f080e00b0203d8080d49036550501a030740e00501500c60341e0f200b1480c2024486c8203010300d4141d0307201c80c45c0c100f00e41d00b00d001440400e48018418168050b1000040c4510b00d8001c20a420705001102175410041c006c0c01009502080403070703810f0b400246010b00115906104000f160b01a00e8018001070854642e610400c40040007580d10342d0035442003c1d6090340c54125000703070489036405842d00c900700711012901c440c280400f100c240e004001c03040006200c0e484d0304003100040c920907940c03d10b44a411041e80d942c0240f05200d808000c0342c00c013080341c7c2c01e03c5078807007241003030a032141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 179675152 1250 179673902 179673911
    0xc02010b100206070504140d170a030b03010e0c011218030203070c0806010f03061e060902091c030206070f09030b0f01170615060c0118080306030f0a0201020c09060d14010b0103 78
    0x2140881c1c032800d080e13580000144013000300b00b00101514800c410301444c0109003802c400c2070341d55031080b194003400d0607421480300841d80c3d0a903660144294038140318160005d100b0000c800a020b5100d014180c000ca05006455642508070000e903488242140120001d6003084200c43c10041d42e01e0304080c0c1c007121003a11541020405000200303003d0704807800e024554842504554410010f86011070201e1041e8200740499581d0f010980a014014071451000607543d252450074058000300c00c6a402140d410344011000001e54000350240d801a0f4074607280c1a101c034520342c01c8403501c610307500140c41201c0200c1400540c0140c03998050407201c400c041400c0c034003001412a920b03885d003162450141c9404400418041c10450700800842c10000d000281c140c003664456207469541c10001d658814001c42000881c4c00c0c02c01030400c04506200043c4050342080d030000713603903c0c401255070f80180c1240c000704038540c4884100c02030459020210200505520106d030b402804003802050001e03042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 179676258 1106 179675152 179675179
    0x60e060a05090706020c0904020405060a080307080d050916090f0f0e07030507050604030b01180f0c080906011a0403080a0c0f0b010305100501080c0906130c02010b 72
    0x40d142c14100501c80c40d0030b1094026006640c040c3c2e003582d4156682005407540158103c9001c0b07071540e1400701113040804194064a960320001c50030000300b00910703000d0301032041d100504100559680c01815540d15648442c0c0040c0550400144107041c000d8121185900d80f0030404560700300c2828800086075102e2400341d181c0d80201a082c400c00c8401d025450050508440003030600d411511060b030026018410303400d8011280c103d06541d030803590402c0356907600d0030104000f00d90041901034440d9604958440281c00707040c00101c8d40401c003040d0079842360a20124181044c2c00c598030030019a00040d40e60342404010729840001900c00c1543e034040d60320600300c074041540b446c50002d1400c40c44d002c0c9840c00501340f03030041c0b0282c0d2000441100311581211110115203e00d8080b034900c0044ca401040600d0400c40100c9141d41c054110b08140c80d8180e071044400c0702c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 179496402 179676258 := by
  have h0 := BRFrame.cov_init 179496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 179496402 ≤ n) (h2 : n < 179676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
