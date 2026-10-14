-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2571
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:06:18.560386+00:00
-- url     : https://prove2.me/submissions/051a3466-46d1-4b69-8f26-01e2c09464d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 462230215 ≤ n < 462410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 462231465 1250 462230215 462230227
    0xe09221e060b030a0b0c0c0a060203180c01080c0409090615081518070603050a150f150513330e04050121082b020301030c2102010c08090402 62
    0xc0c0052410304403040e9803603854600c140700a443c0000b40d228200342d0200510000ea074910440002c141c0114140010300d01401e00000300040171480194899040d00417861108190118014905111604d4035418030000781c040c070160010101c10307201114088540400c1e040c14030319108010b0510140f103401003412040f4041070085c800301d2452620b40300100100000d603511103040c40c504031108002c00c540d030490a424401c01d4800d401443d400a11102d0102e0304c00645640302004c8116a80401401c0040220521800c08100324044120300b03249030041c10107804412002c14217019116401100c2c01a168804402c007040d1305c171100c9510078042d209500c0c6d200d0000500280700500140f440b4522305000800d044022641100982c8800c50619010172055524044181e0103d400002000d104040d8040c01c0102c102038004070300c0180301c000da140e502d90318100110920580080a111404012000c3e8000c0e610680c00e203090b0702460100e41c4078505050954044c424280110303080b80c000508 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 462232715 1250 462231465 462231503
    0x2090a09060504141308090a05031504030306141302090109051302070203070510050d0e070b0a09091b050d050a060506070803040314090d02010e031e060108060105010e0922 76
    0x1000c00c440064806200100603030039201240310707003203542c2e01903507072807540c80c2010500001c00780c084011f000d0300c000d14694031800046d2804480040401e840d0300254100310801d40e05018a00042c01100c8a14a00c030880500080a08104c0551640850341c0424444070341d0303220b0f0170700c400180b6001d01200c051824110b028070296102c1c000503070080c03141c00400591805c3ca252500c036900c06642c3c0300360601e5000d94902024200c81c2c00a52800d124505005c284410940020030f0041d40039240d58a54030f2410000c80246c2c0c40211041e882c00c1421164040d941e0380000444011031103840002070195510401c0034001c001c01d0304080e4020101140140400456200950040e03009403103c9001c9400e10040c55610310a0047e415005584003055200550080305c0140001900409888200f200030800c00146d50a4240a40d0241e0050004202542007400001c0c0501802c1c40d10500c8914000d0103e507910170040d00078a5400660f0140300c0a00380c10100710783c19140c1c0700104a81d002c2108003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 462233965 1250 462232715 462232721
    0x3070b0907080f0607090e09011e1a09130305030907080a0311060f0403120915110403020a08150103030f0c060c0809070e010f060806030a06020301061d0607200402090a09 75
    0x50701515103d20507a8405151000520510400d050703940e99800d1810140c0035440254087d20660103903482d204c2c030108400941c010001c1881c1040f0f0001900211030b07801800516003030304214003074407569092261000b80212000b03540390b0141001640c07030325141100b510b0700f0030a41c440e0146000d001e50342020168041842004102c0e28000c03a02c013a1100c80310148a81401c1e03a00070042151580440014150b90300004c5082c3d014030f1010140d280302010802c02c1c0d8060004000000b08001401d20440c075200000b88081d000081c008c0003084031b1680340700f11190040c0409824015500c48104007a4421040100c9256000710280401e031401035010380350050036501e2400034010740038081404034021207c0790481d0401c5003e4001e492800405503100c06000d03111640500401040e207000c1803030f0b030000318002d00d0309a8801622040b60441c007828034a81019040c070501c400c010a40101d030102c107080140c140c040e50300300c034000b00c42d8001400911901030515041080088001200350756a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 462235215 1250 462233965 462233969
    0x1d060f0103150506011d03010f1812081302011b050d0f08150d06050a02040f1806050411030a0510080106090e0c010309021c08041205010504120503070e06030903070b0907 75
    0x102d070511079545044580166203080314214000f0f103d11000c00c583c10000c1045038059180034000158503040a0b200c174043e07910b80710300a28140c8860030140d0402c06810840c004884080c508130390182400d00c0406410304950002904102c003920146120800c4001c3c120361040d071000c01c0794243c6d112100003134034860086402e103007c00d5080340003e1a038003c2600d41e402401000b030611000101a82d0781c00b00408006d0305110740640e0902000c41c8203124403840c071000d044540f0400c1140c00204440100340c40440d00554011810014015140803402c81a61740041c5188030228041c6d0703590f20105040d840380da0004402d50b0070408001504955940100103600500064944449240c2d005605035403044100030740203d18121409100000780070341c9110548100c3c80715192568840c071089050300b028000303071066503580341440304004942e58100a22090ba0070401d0070f43c5402e90014004205001400303020740300c0000060044041841114095644070002c03054030f0604105050f80c444040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 462236465 1250 462235215 462235223
    0x130203190609061520030714010e0d0c080d0e030d0902030c0909030f031506070c0603361407030c0302090106050408031c18050c04140c030a1d060f0103 67
    0x880d501144494541c001d0b00309540301c00c410065202e521240c02ca40808544207000700d048401111044217a400f07000501e000790046080d040c481110781c00311782c2100c0c100d00e00510158010003c0041442d0811600d084154019a10342c1e00c680c4150744002c050114140c0a101a0000240c2d444220032030350f01041c1c8007802a03044441c0c40c0565020302410b00340075031b0804001d41c02440404400b041003401581d1240c0c40c0740c00d2050740c0d04c0c400003280d25500011421036010f4040e400922600d5418820320148100d03402c03000c040310b41040d000081504400300c0003030711042035403071050a202280310000b5403582c0c03040868680b5a51381c140b8800f241a03900080384150b80071400028900d11a100341d0702a5490000594504a004640320300c16101071340d41c145549440d442d2100c550050180b01700b03006070007180940220300c0104100000c8611041c004481fa900d00030a005810341d0190540344d0003410404000340400010b452000d07071400710b03801c40485103d41010803009000103400d4034100d03449 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 462237715 1250 462236465 462236471
    0x5090d140f030313080a0212040305011d06061f1b050606102a111e04050a090f060209041b02031c0b010c0210091505180301090506010e0613020319 65
    0x40030700c800d602d901c019100c10b244000c4540e250303c08581e6001c0203010240c1140121081240b10b080050025041f42d031081d50140d5440444800e44183c2c885c21846004040000d025540352001c00101005000b221103402c85c243c291041100d140600600071240d41008110040400589000d40d900c40048440f640210150701c6400c0d000f40c0603000c0a9242c440300c1d09145002a100c0101030780e54850a0410340e050b142c0020804c41030346030b144007880b10408100850300c071070203600103100c2a1007019103840810b03880d08001902040d00711410075412580400c026955031845000a00a00900100811240340510116003902c1d0008000e01d41010030101408524089000c908119200400d00a0100e07a15001d804010300c2c2240d9046040038440c1000d01a49880e14035401d4200c090026030408100002940101403299241544840d03104030000d10840400341e42d83c603217524042c8600002c2032000b00200b80f09a4807107001030354440d0070b280115100e140c030069201404030000d82d0b604125107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 462238965 1250 462237715 462237733
    0x1e0711011b06090305090405090a030305010501020606101202071202030c0d170c0702040e01020c0c03070510140708090d200316061206030b040f052e0c05090d14 71
    0x102685510031400310700c41c2610606007403615240c000e010195011010010704000982d0f00d507882d48107850142c131660000b401070b0030b04d500d800b40845006800c0241554040001c10001c1d40e519010100a400145891301004580350001d0010703005a05c40141060203c50100745100c0d4000040e00e406041c1100720b94000198090964001c1c00018098199440d44800240c110075150010030443d44090000149a4000002d403400c903000071448040350742080050410b14501080700340083c100071600c1c0e8001100e00c0d44058840480d4102d18824481c0100324282801100c20650384070000c040c02108040c500703481c01c48125259140c0074a51a0f00481c0c1102e541e04000500c80c2c0098400d01c0901c5c011400c141d800d0711990100c41007008000d88580000c40001c07010070446006038420174961881244602c0e20a040100042c10554000302c00720502800341da00120480e035804c030041307002607503c080d101d04072100e02c620a07010382c100d005081148208038281a00b81405000341041d50b010207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 462240215 1250 462238965 462238967
    0x90203041e08041502150108010b040f0209030703020108060a0e010608060103050c0a140904090c080607140c1213090e0d02010606050702131508071202030c0a08030a0309081e071101 80
    0x90507101010b001564184414011905410100d500090309070046030034050340c1452240d1800f500342c00240a0382d440307600c4c0c01110304103070003100c8442c4000c42080d07080000050209549441500c0041d040048801c0820f8807a1583c2441c0360250043c5d2885e400c4231f68480e100500b081ca820742c1d52500081c54a000034054807440380541e4800e4400f07640e45c01c5a0034030500d02d9091500412015584169203055000024032001c058800900040014081c2c42c90b0204015115128080c11742c180c9403030400408001407000304008c1505400070034000d07222141c0c45030340300d1004030940202101902e4841d980e8070000c03000803038030f0aa041c00c2e8001d020312920781c4000c9803203004956001790841d00045200415004940007554494605d070094441d0711340c1c42100301d00e030400d070790f01c21085421034070360040035070030705000c014010340003541c0da005800d25001c0c155a5a00c510f101240030181e44000c8501005222412100d8006400e1080c10400305140100d41d03080c0c1c840b031401c54003090a400c5c010515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 462241465 1250 462240215 462240263
    0x1905070308070c08070311030c0d08100611060a021e034201030b13020a08040605090d080105041d010c0909050906071407080d060902030109050a0e0607110a05060109020304 76
    0xa0ba010404a00b017291a0754141c46020340c411104c11180800c0c0607024406100304011080d10949660341499400d007110811401443ca4000e981000307203c2c020030100b0b94001640c10f800c1139614000680e190600000816215100840e1841d501030001c18003080514603910742d42460440030300741241e0601c21348800c429400400d0300000c2100482c161164540c001d902458a03200b02511400801c00e14200300d500300e030f012321600808640e00e101070000b03000d918424660300c018003000030301215480740005042d00c903051062510554480b1140030f444050903145800d400d842c003009001201440b5001350082c501405003600ca1440c16000402d0040b002494038050751064941741c520102a41e4800160b62040d2416070b18200100320803101107000381718020040484100042e1a5410081082c003503c0b00a0440c0302e80c85d0030200030b030b44006008030705550080500c0c01c00d0801180105080c40c1003482455026050780940400001c0d59130721034008501c694480c09014440e01c207885071003008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 462242715 1250 462241465 462241487
    0x10f030b03061303020a0503041e0603200904020904050123011d090402030a080a030504020a05012610030c1d010e0118110c16060f0221090105190507030807 69
    0x4941d00002c042000c0300e01400d00440300500900c181e4507401c1c529141c1a03d160700c50360013a051400e414462070b249400d20044040640414039092050f410311812440b904080c081000d40a0030b00003540304203a995075412640c102c60080c00500240d81c0d00d01d00307038411a518054042002c040f01c1c0161003158031500e00240310010310038035041a0442003081c81703031811008100326010f00c140c5903000c01040541002c1d01921301c0c560b80104080c600740c4113012150b200c41d4070581c18032030309202c1c14151f022800e80100420300003200c41e0400742d45040c1c8480644190b40d20207030010b2001e400202e0118081d0308080c080462011b001c445903607969840c8260a030007485400f142240d407454078000850b1541251602c070781318901b040c3c1814060700516007002c01ea404581c84401500030100003d0741c202d1354000c038460182c009480d20042001101050f203003840c0c070780345143e140040c80c8070f01daa000301c083e0b442c900503100f0f900301c00a0710618080c1c00e0741e024042c00c0e40820503d4000441d814401d0880101d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 462243965 1250 462242715 462242719
    0x12080f2809091e180b04050a051501080309310501030b062e03020d0c020c0427020d0501060807030807050c101218140d120203061f02030d1109010f030b 67
    0x91940f900094400074088180791441c0440e0000302d15021600c40c14525005500030750281008808925107585003a036100c445060b844401030040004010200a0b83c250003404c0d511016102c001c41c103d010403040d40004009801503a804a44000c850703a4000c0341aa44114081d00168460305e04100804d4914160f8503480540445145051028015043c1c4400d556080150030000e20240e80c806580752040804c0041c0d0003c034481490703203000c1c0118038225032088115003a4088004ca20120411000c602034003580e403145001080001c01d52007070340185542c1058070f030820313100d240000c3d55074000302044d41d83d4802c005100c40740349400044402c0c540242d481d0701308510320310440d00c4041c180c82c079144100a600d41194002145c1301a0000c680d840b6140c000e0102440040700c050024550b04200084c241d1043c420041903440700030020002000604484070071301030340a4101e04e14401c084d002030240d070a00240302d03048060400034000c0d099098944180000c5504030032012502c51060742d82d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 462245215 1250 462243965 462244001
    0xd240b06130b070f050318010f08090715020f01020309071a040f030b090f1c030608010b0d0b101206060515031e1504090b010e090712080f280909 64
    0x202d0300c215a00140070061280071013401c88061a10b40f0b50460300949200c5c28030380c0289140d40019070380901c841c0842202070401c1b04481c10007600ca00c2e650001401144d00940d004a07040c1d01d12402000070765a0742d20908000c2d0341d81d1500e1001c0c50b4607031013188280745141d12100c40e40d02d1000007003070690f0155400601440340e03003441c40e200c08901c42c0c00501030f81c540b0300515500644480003801506510856809134040043c460340008007103070b40d00c0d4005046c80c2d14250f4100c005a0310548058821900611481a82e40390151481000840340e4816410103011154010030040709400c00400c403075080301c9620b02e6040c05001980d00348012217031454186910102c414501d280a15065040082c01c580511071200020100b41100c58142c404c0d14016408401080083d141000070347e072103818100035028482c44d00c0011001c00e00d1101d80148118004100c1000d02c1c00558162070300e404803c032000d0f0700c000b0741d601c244821441c0240700c6000191002c4001c034624009015201420092507441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 462246465 1250 462245215 462245219
    0x106030c172112070c11040b09040605040c17100518030a0c060b0a0b03150a0506120a0b0d0b07030c05090a030212010f06030c0801050f0c0d09020d240b0613 69
    0x200c2c548001680c0c01e10a400814082c00c020b000020f21070070311801c102d8840503e140d00605014030b4201403030034070390710840c28040c03919078a884180030b00782c000ba4802c0001c21079840e2072070b00c1d1001c01942d401c00444003080306103122801e080014441c96441c94a00c0c20001070301d85041080e0025165040e8085a0b442084210061841505103e370003600030300c400108542d070800024000300d415845104542c10100c18420914194000909070580c102c91051540b441c01003c030301c00d030142c1c42c04a03030b407040c1000020b2440c014580102a05401c02030002e00454454500580c0801c01919001d0000780360908214021f40030704100c0303281501c018100e01d0054650340c2089181c00c24017800d146c0654850620303507a0300c149400703214080c40c80740340301e44c10880c1800096030860700000c140c82d8001904d1010b1201620b40c0400300d841010303001078003007190003190021401d4441c01180091600c4400600001e4111444681e202c0340d00c0c43e12010b01103000300b0410400e05020b041040f4540031042201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 462247715 1250 462246465 462246493
    0x80c0702100c140c0108010e1f080304030606080a03270905040303050411030a021c03050f07030203071205090607140c0d03090618050a1512090605161106061c080c0106030c17 77
    0x114075030100140c0d4616801d048040c27004c42c1c01c040c0c168408005030303101160030b00402c00c02d4010700c406440340070028114210f0030b0710010301070000040c01e1001c0c201d80c01907030380088000300080d502800308440c0078400c1d07040525004004240403941038840c0c64078a0000b465520303020411401260b0014003520903000000000d0b585c84110140c22401c0c040208000d104107400c000103410f1a0b03001c0c1c1c001d15100d203564107040c10a020f41161601c208641046020425a12641a58102ca410104101c03054601c0b940c6c00b4513100d820840c042e03001407100c40030b008250303000c460319040d9035080d0b039610000d01000240664081c0030b4080c42d64803800100c3c05000002e00d00c1030640220805181c2903501e402d01c004070004a40c4080015202a600c52081182086a00d904c0030040e04107481c0c00e01d91806050752464450030302034115449910f002c5100c1d60980780c107d481754015500000c045a0700c64808102078001c20b03049c442169082460800000d0b6268030501400581c0b29800142c2010740c540d0301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 462248965 1250 462247715 462247739
    0xd060506060c1e061e040618060222060207080c06180a170c0907020d08041104060906080106120c17032701030615050a080c0702100c140c010801 64
    0xc100e0350071540610a03001803140030050303503000c1c0b5101d07150b540940115584541c00d200d4002c00c8403602107454103018000355496201c40b9030054021000207170107060508401241c080e0b101002e0300780e50003c6101000804001c669090803070340346005030308003a55041c0580e00c501071841707400d8040c2c0064410307401c0e40c10400020120300b0307012150300c1409080100012600310035500004694000d403100265680c2040202c1000204c1c11100c2e190f0510700000020b43c8c8144d01d5815000704100032002c1003c00c8100e000c40e006841d4000c00c14003940b5151b2450800030080e6200d0003115609081b03000510031030514a40f4202030300150302084050811000001984034100c105909200030000c10364558821102810190300c2c0d04080396170b5140a5000400ba80c5081e000500d51101c1c020111085940020031181d14094074280100c1560b0385640d0346180d402407100103500464822030b444005d503072150085c00d00d680310303100e000390101640d08001e6644000c2079000d408188204010700100d007044c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 462250215 1250 462248965 462248971
    0x71703090405150405040b19050c030112030e040c0c1e08070b0910052514030a110409140f010f0f030f02030307021206060f01140a050a11010219030b040203060d0605 73
    0x104110081e0340303d600200d001c0b5038045070305903100d0f00b9003420310000710b01e54a03a06584a4064070b0030310071400c150102e41c070a48018410050840b103404100d40804d40160b151806022000308200702e90401c802020f010510030307240488400c41c11030b010303110407858a061005090b80144555041c528030359584c1d07035080300c0509450042d2046440c3d080c48000140202c91141c51704200d00e07141c140d50400c07083d8540b80d2440326a018040d825480921540181d000c2d658052040301b80803401412600c04003607a4800e5070459280141094525078003404842941c5020b1030b038a440d01c130103680c0d8a001180c81e4074024003030448050255601000859000c040c000d071018002402d80f842d1907080c2d0300040285200300b5968240d0f800550400a003460214084600c0c000f0030701300700c035040407001a0018284140e0203000705101d404210390034000d01c46d6504640c04220302c4004c640c0c1d0042d00141e0318110f512403000400081c1410b07081007080c142402503030300070b60004d000f0400303150459807100c02810000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 462251465 1250 462250215 462250231
    0x51e09011e030218030d0f05031302090f01030c08070303020d031112040c03050c0f0112230108031305040204050108130602130e06120105090d050705011d0f071703090405 75
    0x10708403a464058114a124195154a031001a55441011a070225148074405070700d03c02d400000e95082e885800078440f500072421454655540e5031060301d40c00a000750200040e4118011404001001a00d661507034140ca0244204083c85555514880d5440c505404001c0040c0c011042c4002024001d030048801601c0d824100f5003841e6001c104010192000c41d02170ba01e86040880410030700200344155064004140c503858921407050b8006001c50440c450000c19095a0382d1103d0151400008041d8041c02e12032000020740d40c0d11111a0b903a500b0000b41411040305580c1c0000c5d061516100701c0d030440d501a1988102070765170134200e8100030b00318103040c2c4000e0b80030004d50010300b070000c912001400b40f5150041e440c1c06e000080c4a505070040b102100140e00d00400d01200720300000d1000702c0c4164030310b0000d0307840c070041c602035001d403030000300c454031000c0c100c48983e22202d030100386c130000804ca101c2103e07038031992403802c8a04c1d20101c0404e10311070340040140d00107505040c0c100700d5005402d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 462252715 1250 462251465 462251477
    0x11a130f021905090f010203040f231c0c0602190303050907030203100c03151a220e060306130c21080c0d110c0f040203150a08060601020d051e0901 65
    0x40705031000c000302e2074020140000b910000e20802e2074034008440f090080020301c0110300349800c040140c5285101400350500840c88141d40c12001c150907246240400006003a03020a02c428101103003030300301d0b03143d41115902e12a0344040b4055200290341c40c0c0e000d40241c441c07a01d10b0015201500209405800c400d80340c040d501001c00562010040d201046034540d0b00095001810308004003103400408041c0b41003540c00a0402c8000c0e03506034a9403003024200c92407035840025034042c1d00f2410543c464001102c040303410000f1101c0302c00384464440e60050f019600f940e500e005000400ba5409a0b000307001035840780042c818010800c4148802c0c0c1ca00c00c4100c0e081d03d01c0d44c1c8030010700790031601c440006644201d82d4151a15403151110f10012400c00003440500f042c2c800003003442040d5005030340100c0d40400054001c040c0405001030940000e400e44507000e440d2300d001c0d5140c01084502d00d01501c0744c6149001e15602c2181250004c0002c0130400d000c4090210032017079613034400b080740c44c10014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 462253965 1250 462252715 462252727
    0x3020307030c05011409060a060602030309100c091e180c0207061805040204080d320a0302090402070f11060c0601050d032001020715090510150801020705060603011a130f02 76
    0x610a43c81e46c3c06604100020700b03c5282100c1e030901034841c80c3e00807000b150014002d005401c40b0004900c092503032407404c0400d400740002412540383d20250f008000d0440d00c41c072404141383e49550500300350707440740c00c9800d14642034a041b0010381d44900090030040c1e00040c81005082d20854045000c03c440381000d070744940d82e031400a002e0741c1103504065003c1e000242c601c80300c1034015020881c5001300c68094036101400a0304031920411201c215140c03500c0c0080c5002105100741d040300d4060b03000078411034440b08507040c581050140b10b00210f4480c5280366034060f541ca44607003a51007091103a80140001d0b801d150a1100b00b8810540803020f0090010040c201503030301c1001400c0c4031040800060325103841c1e0030030101c0705d0186441405450b1503c01d0b110003046010030000d11304048004003088000440d15001c840c100642d011007440d500c04500d150030440302040c018002c41c800c81c000e002c5040f1045c02d041113030005415490b0320050003040c038400c80c90103030003980c7c0e100004500142408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 462255215 1250 462253965 462253991
    0x2040620031b010204081e0d08250519031e091e0f1205040b2505030309010903120b1f0908061e07030509061b0f04031a09010903020307030c0501 64
    0x101c0b85003001c860b50080b0701030060341c00401000406c041008800c06001b0b8444c440161100c80b503455803010080345100081c103a0412103988868002524508982c0750343d4034500a14603003000500c0310000c9509c64446030550b100e80140442c0701021440c0400f00314501410200810f4003400c00c0310545440b000f88098411010150b41359180900140c0a00c452907150034402224058014014004184814090400c0c2c40e420740d41e1006001c6003c4900d0703a451201c00030f05041d01c0c0310003030446c440042000320700c4d00107400100d00d8600c41d8448000380c0701c0001d641d00030340e88050740d000e03008040c01c1041900d40400700415681c1d014507090548205413030f600c00360704090007111103a8944c80c020810f041c01c101d280191503401100d5213410400c508004041c81d46507940540700803407008030a038840400900c414202e5455280001d4010b50b215541d280c03155406a030041501e1851050400244045606004980045606901443c0b401c0020b0b50107072412800c40e20700b034074150b41e2581014508 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 462256465 1250 462255215 462255247
    0x70603090c0509041a0903030c0304032006091e030c0607052a0703110f091501120f09030201060b030c09040504080903010509010b0406141c050f0a060b040605040204062003 76
    0x4e07805001740c40300340310f00c007074024001c108090204c0219510030010490300344004001e0300d820907818a00f9548419507107041e150320080841500030705000e075000b40141d0060006440700c82d01a508110101480d81c240d541c1e440e800703250521901604014000780550b07120304010180c411040d41c94198240e031080c041c42886200009594055001400c103200340516504000d402c81802c503002d0400b0b18101c3d012488001025003000d08101d40c0829031041c0b41e0180c10044a5852504800c001500505113400090a44540250f015510300100811003001500c01c681c8100c1648803910315000480080c0f1005203402001542d61404c00d1044080702c0d0740078011240207514080011581c1141e0804000803036850341d101642c01d180f40340140c03030700340c40e100c51141d980300d80120a014080d0f002d06005003040c00c5e10141040501810b0000c10405c003440c1c0c024030b00800d003540d04202c030f151a03105204c100e100e01c0c090100070a0300c44a030845601103400c0001011400b50342a2405d0040c103000211034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 462257715 1250 462256465 462256471
    0x20c0d0e0a060903020a1e18050916050609010e030f100504110108010303051204020d0b09010b04060504050115110f060c040905160c021c1b03020f0301020703050712030e07060f020609070305070603090c0509 91
    0x1049d00d400920920074000c10590045480c250012a85545400e0004480344240000c00b4103000710040b41008076501885404030200d044800c0d2840070240d0a80400200001c880803a8281c2c0c900c20410b4995200c4c10003141600d0740754603441c0c036200c1454882201c007500100101c0e07001c80c00d0304040c400144401c1036a4096a400700021074000410010042500c3d800c1d00907070b02a5241500401c5891481e04010a0300743d03050801c0982c5110200a00b0b08040410005154512441090102581d00c202c000c00480d20101c008014075140c11100080c000c4d01540c2d200005030307002c40d00d04050b03d00a403004140e6441c2d0500455005075543d100c58039031000e044580c00c10359040d0300403c15418450a1340c000800114000c616145541e5006400ca02030f9003000707060012040400c5003031038007d500c21003580203040700301c0e04401e80d1424001d041141c02c0ca84d1000600a080c04110301400006014050702d50080c003a101e0903090410442c000c20030201c1c19206000007007000621915000c41300382c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 462258965 1250 462257715 462257759
    0x1020d0e0f1c0c020411040e011a030103050a0b1e090102091003051003030e0a0b030c0901030f18020103050c0409021801081b0708030604020c0d0e0a060903020a1e 72
    0x20019900034005061034020203900701207400c00341d070001800c548540d41c0b1455640b80d082180e007110303079400030500520801c0c10020a8520000e40410b000107803144080c12120b080000403109218115200e0b000d0200b0f00c002006076000c100900300146540341c166511180c01b030030322000c1c0d0599001c1c03000c01391420b07105000c059600040c03983c0e0030304100000c12072941550405202134100300d12a010034208510002d42041207084401030155a9500b0140041110205103600d90801c102001c209501115600780443d1a002042149030154000c424024000b076102ea1075010342d0350019400b4140003000c00303003071031410400401e041b0000d02c05070100100d43d13048541e118214000141c000d40f40030301402040807035210400c240102c03d0f000c503032034203600c03400094894660382d0102c2c3c007901400140c5034050046200030121113a224000f08001a4100c45c55034030181d66110944504900c2c1c08060b41200c1d82000900620092400c5010144451900c3c214000e0381c0c0d13101c02c1207200d0b070001500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 462260215 1250 462258965 462258971
    0x304061812091a07050606040f020405090702011a040908030a091b12061103090304030303090602040b0d1a011d06090a0f060503090601060918050403020c0a1e0b0304030e120a0501020d 81
    0x202583d1200102c600c03d101e5050201d034038000040e100c0541e2850001c104038862512656a4025520349806030b031300408001c0d00b0f1701d20a040c039141c0a0302034017011150031651645060a0306541c581405100b8199030015055490760702d800300382001800140405940210040d5030000740e902c0360003040001051400c104040440b0f4a183c19000e440c1c030a0a0740c400700070140244001004048115421242c3c1810002488159894600080c2c01036501c8000301c40800b280042190409420037000340c8003a62140903041c2c441c0c00152480c1590940364440c040350f440745a140380c14500b000303004c151030092058800980c0c42050060703040c0d15410210000d1b9010051205081c0c04000280c05031046040141c8103604044080302d01d4540c0041c3c207640c003034641002c541454000d11031845401c40c05400c82070060f86038080c0c40241441c0038205119441c2d413980000301034030442c0a0340e000725419511107501441c6541004072115000700080303013902583ea42c00340020340c00d02c000c283e0020030403808 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 462261465 1250 462260215 462260219
    0x70212070b070b130b130507030b010603050106030f060803040b090f06072904030c02040f020d0e070f0801050105090a0504150207030906080601050a022a0a030609020a1a030406181209 81
    0x40321070340c201904180c400780074000d43c0000508172050307150740440c0c4c401040032540001d003000c600c1c00060781d1016185400701b40011444603030681209040e50003940b000e0224451000c4404121203207813050505507007084c0400d00142e80d0f0b00303000340030306c000007410821040c1c0c01c04000740c100d0788101d8080705c000c04c0203080c4401c00c4e031000949070182e118080c1e03000b5451610f0b0302c018000d035a403008020300c61f036603440c0c0710158020342c0e0741541c3c5402418401007191a074005c0d00f00d5580c50983c0903141a000300c10000003241da4050040350305998000d003c0485640780e102091300a00720107401200e020610381111180340e1110700c00b50042c0c0b0b02aa81e0f84110502d8100040d048407005090701d410824100580180fa603000a10300c0c0c401442c0a543c95940440c000860b43c0c0301e0340c1030300c0c4039074019460351b0000144000c642003140c02500031a86980c0c1182d0321201c450466240803011007506030140b00080c003107400781d44030841004107901d0407404c80380196110f0445000810280c00858900e07001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 462262715 1250 462261465 462261473
    0x90a0e030d0b011b0c0605070f0b04111302090f0d0f021c060c030c082e12060b060313150609090f06240323010207140c150906070212070b07 62
    0x70300343d400c803030b0845113841c140030701e0312103000c092807501403076090020005030360f0b08000035100f00c094600d0b08410042000d08181c5440c0c01003400b00310800c1c2c8200349401d900c0e43c03800b40c54400c46904003002040c0700030480c084410301221054525040e1841382c0d88400c501b003da117811403070004049802059000701200b5107010342c02c9072203c038540010149001c504110880d0030014554108401704000075007a0204050a418000c2d01c4484c2091990b801c03000150702d031b007040e8106a010744244800d00280100400381f01e660300045801d14bd000e01070021413000f00c1d85800c5804c0704a034400d00e01055080d252a02c0360203031101d007481202c40c0c4d1208034086040c0003141c0b24928484850f416080500c0100d050b8480480441c0d0002a0410795200d01e81900900d0300d0000800c4103a03420025900d5902ca070608a0100301041d001500e00e0092190084140c607002d00c2c3e40200004140005042007031324024000b05420518003242c01c04ea03040348200c0301d4072081107500010a9102007a50352041c4601e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 462263965 1250 462262715 462262727
    0x41d07060909021c1d070909060e0c060304020108040c081902130603172b0b0907090e070503060d02031c091a0a0309051c2003070c05090a0e030d0b01 66
    0x8410b41103503105010391211861012204a0085100c0c1d5000c80d01e4060001181003000600c2510101c074414450700040b034003000d810a020b1140500c104015286050784442e8035003120b0880a03600c240200001001503006440c4144c0050141004a0501e9158440580b0303085038400c28807142002c0450032400c5242903040352002000300c2c503041c4221407440d80d501001d100b041c0c0c0150b41022021950402d0310440d40c031519242c0c50035081003019401202c152000400110002d180a00301040008041d14040e9010034115400000048425690004200d9064002501d041d0348681000807150140c0c1c1c04111803552266103141001909800280282c0440c0c1039910840641c0e0760954151944242da10507107101c100e840c240031a509075075180c460308200050510406070704101c40c1c4112620b40c0110450b9264042041c00001c589090305d20f1030b9640105c1c47c0041240c03001310401e211b1810000d80b91508500006808150901402c42080c1507411100400d039620340e60f00b844801540e8044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 462265215 1250 462263965 462263969
    0x6040303180806072d0e040e01140c03010f0506070b040201050d060b0703080708090a030507120e0a0e07020c09040b152d03120702090c03150603070c0516080a030c02041d070609 78
    0x424003017000408103102400b40c0c10a580c0030751007903503510b000b0740c3d00d200203402040d04855220040420307860825680ca4454100703004450130340c4440034010405003409011280d80725008040c4400c00d80c1d840d80110380640c070542d107000381aa10b8110003c4d40d075250701d010300301c0244030f61500301c40d928100030010180f0300001c0818030f55a010740d0b000c0000c242c029003210704598000c084200042d26442041d1104525000d103150001501c04001034400d0020441d580191343d40d9003034440002e508000c000c0e442c2030546000d400d01c50f0301402328805892010111404403c050310304489204100b011100902107501101003150504401821606c1c0610010042481c0d0300345042c14943c0d00d4000c94945000103000c4031700d550000000c5180d00135962031904107240700808a136582d1034244801800d0380e149010031100c2e40b24804943e099401000c0002007511602340041660007120780303084a9800128009030b170490ba4800207105003003194140f05140e0f0703002a0040c2040e5140c084000c04145440e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 462266465 1250 462265215 462265277
    0x3010509011107081b070b04170601030b0f09120d0e0105010b0a17070201060f140f013b040c0804020108070c030206010905040203011b090f0f050604030318080607 72
    0x2c01d418450320007440a4400039904403480648441c001c0c1041c15640d1450b040c2680d003032141913000500200351000070425100007941020042c1b2000300000c0d540c0e5401e000c000c0400c00408000740b004144150700c29800b480f00d40844110b040c261003c8942d40d80907136061301e43d06840314211881c0000c00d0160034014602200241c0c40d10a41c0c007401080060b844500c0e010166204011130540f5100350441c0e00502890031443c0034003540d461207041d01058035408207001d184110b0f05580d566005000a9180701500c05006980301c01c0c0d00304401c416045080070806105103c1c04040780d680300e511580d0a140210f0302c030354000e41003d000240c42000018451000c0000f0400c19200181e4041921811100ca103040802c2c191100d1001902501c1c0b0305e82041401100c1c5c00d40120403e6010000b8030445000b507034040c0e1041d07250034039011b91000c3da010b20354010340208001c00000c1c1c07107181442c00d0314051442e4040e11079220000182000e000741c501c880010f4050302c01032400342110f0011700c1e490b062 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 462267715 1250 462266465 462266471
    0x90d0503091222351e150f040605090d0e090601050f2101090e07050904170c10050a051303200328030e151e070302090301050901 57
    0xc0440101c1d51140b000501448440010500c0c0000400425441250b000f5002502040944500740b940160740d400140e82c400c05002d4402100c2c0082080c0d50524150300300c1c000d00300c80501d418204010320681804400103110744500401e425030124503071070048401c00084180c81c00c16052000588902500c2c181031500040320300110a41c1051110a10072810740e10301140380d8960005032082c1c02061034040300c0e1080003412803031217801100800d80c00311000900d140d00703989904d401c3d02214079409807a9580d50002c0d1003405036251400850760702a00c01c81c004007100c070000640b1322868203c00b04418441d40141a80c0c00c0180250080650001c00144108860329010701c46000c41e002c0c1d088040c0500155200401018001d00c10a100c100e0b481d00071290346504040402940a003003c070307004484004981e914000910a004503806000001c00801e81c185001d00300e42d12444016004900d000215103011801444840c031540c8205400e0b100142c94048031800d160948100410000451345 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 462268965 1250 462267715 462267721
    0x30c0b0c090109030b070c06020708130e0c0720030102071a0c03060d0602030403020c040c090602070b04060f0516050607120b0a030206040b090406091b09240c081e03090d0503 77
    0x640705000100b00d0303410510305d011035203d1040c290b4002c1d0412a0251009000255010034010321500410104100341484085c40d9503894174441c40c1a4142d4074001022030800203040070078801d040313408404c081d200840d1100020003001908981c08090215101208459254880901c858840b0340c440d01c0c86103624a14035101001484404588400500c0d542d804000300381894401c10007c0e070480340182040191003040c84001c0c141d86003520501005214816012405000c0c52041e201152540d80740d11084240008050302ca9030000620350b10006401a1010b003c04c40800c04540034180c503843d81e524403030340c0d1901030b0181c41440c000c00707010350380c074500400050b2542001c40301181d2703005104580f100103000c0010068050f590100380e8035410103070121002221410600743c03000a50300c07001655555400880805030300e1208440b013103200c80b0f6050913420302440d8018802c070301c1000d07070600c1c11180031200610624030009420407054080204404468104890301403441c0c41d0401600350300d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 462270215 1250 462268965 462268967
    0xe060a03050c070f11040612080a0e03390d050d0f0e060c0105180604030c0809010306080d120c1b02040221010320040c0203090108041e030c0b0c0901 66
    0x48504015402019a544001a102c40100c07050741e543c1580200200c80301c01d2030782014081c4001c00320345140300c0d40c0f8000d400075190781c1c001031520040d9400b038149420b0100c0a5400e6461a10030500d00740c06000d0345004c502150006001e00c07850041c0b40407009590402c186480351000714100c01c2d0350042290700021008540f0010f00d442d1030506a103480a0401e5900d82d0488040101e4004507803c070501040041407814190800303441007403040b0603a208108120b1b40e8035520407050300d000d00440c41c00c82401010459941c01442c8445041c140442d4a66130b030b803c6c081c90b00d00301e0031000d800100e080c2d40c0d0031804000780c001c00c540c00c951441c080030f08000d40e05013800f02d5000c020b4000d01c40d507030019403612480b8010041000300e48a078406043c4c00d41e0f482c14800038034480012141000f1216040740c0066162511078001a00340c40d07401542010120b00055511000127442950701e07100c8008a0b1401c0803031030b50f45200381c0d03200c0d642d002101a03051418600920000e0300c03040d89160203105a140503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 462271465 1250 462270215 462270217
    0x303031802010215070504210605150904060b0102010902060c0c0108010b0c1009050f120a09050a060c021c060c020a141c0c08090306040c03120305061302180621070e06 74
    0x85080c4428404068075040c80641d907c0c030540e0b006c80c1c031540c001106410044007030424501c400d1700405052145540b6071225440361951505a01e900901d90b201140c04502300354414040780d5018000001e0000194000079542d400c07121600010398001c404201480d6800603100d40185240f08402d810304907003000c9182c4820040e0400d112856580c404041804010083c0d4220a1444c0b419140405403584041105600910249001c240c4220000410f030030301825020481c0c0311030b614040a034071305d5401c00203200701c10742c01296100001084000458600e1180b031181d42207940003008400290b1410340c81a5821080c4544280c2089900c142c0740e640e04000802e80d27090525043c00301d080300d407601822500a10800750780510070b00c4100020070003c035404405507401006c4500c0c9074011040c040302035500448400790002d004800242010680750082d00800b00e04002e8050703003d84910100c1c4294004281c69054141d1000b10f059880c4039120400350009030500d85100710748ac132080030a402d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 462272715 1250 462271465 462271483
    0x618020f030c060d2f2502090a0f141512160303050c1204080a020a050933030307080a08010e10061d27090318060a0c02091003030318020102 62
    0x41252209800e280c440c0c0300150101c40c204511710340800500c001030350086140c0004481c19072042120080840c2c0c00007403061080d065034001c0182955544501c07541010b010780c4d25070000169110310940d5010744484103801c0c81500a03803070b983c1c0e07214084c1342013000c0b0011164064043e81c0050724803a80c1d00040320005016242c00d401c0c219920840191220325000c481c0e10051416000401c0101d4002004601d10300c605000f00c1d080c180741901e4404000c10a0703801c1d20ac400c410000300d00c11900d9031000500c490142c01c4640342d65a0900108004a0705543c0720f5001150002c100086903110306801030802c501421121000d0f44c0c092419510000204080b406013034240500c232032b66088140301c0321110180c1a240505240e14004ca2911404901200100c0f00c0c0d81c00c110050004034120700010a46130401105615081071052030b20601c015580044507002c1004100c081610140e25921005806601170011000c5504c0c95400e004040300e0404452540110a2943c004090b030f9001400c020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 462273965 1250 462272715 462272737
    0xd0b03160f0323030412211205060402090406030b180a030f1404050a06021005360a05190524150321040602060604051b0a020304030618020f030c06 65
    0xd4000c1c0c42640011250f00707200c0040c82e5100c0002c004c1030300b100000c5181d034901c0c89080703501c5c40b0300c140308869040d0381000200e46002490f0313148103506a100f41d401c903d1300007901038401481d0107000c402013410b40d60701d608280c84403075013203040c80506603c181e510503203039698101030448902503a0300108510f2300c1036046010001d240103514540d6801500301d500401c402407440d800300d580c80401a44403203046500a6403d86000000b4000031039010421038002140707068103a800c0340303440c04449101026003402007540b05c0c240d1900b001170010024511000a80603040032410164a40304d0f14028402c001c01c01407244100202000d1490396140c40d0300440b960b140c0c1e4003501c59540c042851f1440e800306403c00d0f19400b02110400c141000000e2007600c4040c1c0c29a60300360384640070301c0261030701a00c015500941200601c480d404040010340812100c40c07040d6031619540352245000d441d40050355440d041c80080c0000114601030343c24002e40315059010700344084c00240000c886000343c505540d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 462275215 1250 462273965 462273983
    0x109020607021e03010c0e010f08091f0207060e0a05070b040501021b030f1005150a0b041a1e18030c0f1003062102100207032001030b04020d0b03160f03 67
    0xba41914140f40210148407028000300405440128020031509040c68440c1c045400e14012105c03080c42015064171800445c0000e1200c1424482684002c541c070180161400d6030034050500080d440c0d0140c500d100b88018001c01e20201581000c40c20b040b1503070703c07180c1404403c10040150b030b40c0204289441400400e107181041d0403110210b810018440fa120f0200e000b801900b040c0c00b90340d503003d540910b140703140415660101c0c8080c401d21104600bd0b14040440902c010051244a800410040080000e10604014000b41440480340c0c3c03a1103001c802860208210100010894406a20440440c014851035003610041914401d1040310640a040c0a100001d070540c041d0304810005e111000c80c18444400c10a00786840540c001d03800c9219100303c44120072802e03c0022507000752508907581c01000c1d40c00c4100d2042902d81d41c0701007410700d41c035404a40003994852000d000901d11564011803000d00000803d0700341031807080d81840d0300000003010302c24050381250307420649500503001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 462276465 1250 462275215 462275239
    0x10e01150f0e060f0a05130618090b0a0e19030801050112021602040c03060b070b09060112170921060406060b160b0903070606151b020922050d031d010902060702 71
    0xc0b5010105c10341044d60000451102c0c85da1026240e032119013103499205100c0314059800900c0d6040d50030b8264090041c032401c0000c10b44081c01c0b94000c0c03e2000000b012103080460200c0c4211030145a03c100368041a0808010080f81d6046004440c0c5c00c1c052440031803400ca08802801c100c1110014064025940c820001c000e1502a9202c08068000c2d00b981903101c01062924003040c10003114465240e02400000145142d0f658000c502d03020381c800b054075011080c3c0d01800003960401024a90b02040b001c501c032041c022901d600c41084000304001e40f81c9803030613003041e00941c0c034690301844500204026009520701000000d0802940c0a040954561642c88050f4070354060020302a04041c0b804030300054251503882c1d120000113841e241ca42001c60700e60b600200040f0107400c00f039005407621001030000410070a1103034030b20500311416496044683c99141c50901040a4440800d03555071000280c401d0021120340380810313400c028804140254041900c1d4000c94034001c0c09a401413100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 462277715 1250 462276465 462276469
    0xa03120207080105011710060602060f04081908090d0e0105030105061b01050a2306060f1b0109060213270b150a05120c1206090601050c010e01150f0e060f 68
    0x4030400070560b40d4002c0c0555611001c4001031042c1505d002c0100744a91440c210400d1000d005480407201150041c103072039500c0740321070000600010b0041701c0ba60401c10a21440d0780c82804003071881c2c1e80175600c08003245000e440032482c0074014418442032110450790803031544c0e03100d8210b034195501603510603128424003064207100007078400d20441d954204000c116008568ce8080c1c2c0320a00200040c4c548030702d80340300e2001000c0f03094840c10341050003040040394084d042001813002c0200b80c07548140f0325940400a03030071580e850801300c88854000421481c15070840a245d0003506004c00d41014400c081c20800050a90700d8100740740d02500c51030009280c0c0d882040d003442c50310004101e03940d0755007421002032856002105c02c103030041007040031802a0b48800d0944030aa111501500030070b44800c2c0401454150081c1078504200c010800c4045528013800b40f502c0c2b840b58040045141003d000003031007110303003c1d001204a4410140c0030010b102d140003840f5080081614000302c001c40d1240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 462278965 1250 462277715 462277723
    0x204180203090d20010912031b0516020d0f0f11150904091106070b0a0501090218011d1801150206040201021903020a0c06020d020c03011b1b0515090d0903020a031202 73
    0x60304e5643e51800d402c141c10b0002440c4400c0680c0b103da41c0030403800050300390900864074504074000010b1000d101d4001d401c051000174045450004018942c0d544880d5920041c0700200342040341c0b4034941011084c00c1004083c200c507144001254000a5141c3c01c000743e0740c40c1c0c010020001e02c915240d01d02c0c40144560b91140403901c4002608003640c500c80b40c1000039a203802514200801440d0500001c2c90340c90070310949050f00f0b0815081c090b035404072401110540624162100f13540b800b20110301b0303a03a42d28840c084da602d40d500380b1050250702d0400882025448040c1501c1550000010040140e07804562110641003134414070102e80c2d96828101d00d00340d0490001030403c000014045615600000d507246030306401da00316204076182c001070500340e5685400b0320345403c1c214462039030000c2c0030f0141c0c520390b5480e04050321300c1980b064980034503043c2080c60300c009030303003600d018450b00d20303030a02824001034901c1c00c002d41030900c1c2d90301240800b9411310014000c086600c080782100c0d8403c2c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 462280215 1250 462278965 462279017
    0xd06061217031e1f06050a080901142805070903030206060303090609062b2a080a020f0f04140112060305030406080c070b0a0506030d032906070b09010204180203090d 73
    0x104d805880720b41c4403500500b031940264051404a2440c2c80043c9050b42d050040c0b0b011590080901da00300c1e00c0350105d411842c12840040e140c59001c1c6c2c1040b040503142c0d446098410f0026690310050b052075802e001c3d003032280c00f514885c0a500308106070f09194507444119035038000c00b1742d5040e50b11035000740d210680c0c10b400d94440b0090a0007c01c84070941259401c00c1002c281c0070382c80c2003048214180c45841c005c00c00545840801c6010300040c103c00b20513809000780703040c40c142c0d0030300d05000d0483c8481107512075040044080c2042a1000c40c40d40d2000180701c4800b035040c0104271640c1181c451075501d01682c801c820070884081d000500009982c400d841c90903521401400c2caa003800c0e80c1400152008a4030b031400f910404c50b045000610900071600c061040d500ca40000749120b07000c6140484000450316080340b010405080014040300c2003d12030003000c0001038a482c208640d21842580c1d84142c43e04040c014401e2010460780855101000707052420001c1d40303408c8994a0301c0b400501c61b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 462281465 1250 462280215 462280261
    0xf1b02120f0d1205060906030c1009122604061209230601091107030503270304031b0b090102031c0e0a060204091103040c030b060d06061217031e 64
    0x700b612507030603040382d9640c034030030f07082c1c0f200380030319035440741803003103040044844c90b6040e44030804070240c03030a1010000da0702400525050243c161600007000141004210032120340708103c0e0728884039200700c00240c898462116100d450b042c907014004052081c4120f030b0000642d0b8404000082010740400101d240a403210b032204404034202e010f58881a00740714260040d810710030300680d24103201017280c46060f81620f8050550710b4481e45080d8440281440f114040c0001c0c3c2c100001c010104041c00007584201c0d07502d00801c2451810580308003155000e16071178103091290203196a0044240c4d01a2000403100c3d00044450030f0f2000c0c0a0440700d010038a19005250101c8107100164009009803010f080d02400038140d80501000c60748000c480203840349054a0041c000148181c0f0340d40d03008100100011401145529030701c04a540c86c2c4c2c070003c0e100c5020042c0e076040080b451044146080c03903130855421890030f04400b0000c8a003082441e42c000301080d000442040e04030030600111016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 462282715 1250 462281465 462281473
    0x240b06030403111504050c01090e07050708070c17030a1103120103150b041107350706110406080402090f070f180305060406021209030301080309100e09160f1b02120f 73
    0x175040103922400c100000d103000901c40200444c02e4114a000640603d00c1c0d541e80034502101622800d03c0c40d00b00240450350404001000a1389142d80c00000c065001c1700d1014603070300d0f00c1c5414080c00b9608680c01d4510150018007120f40c1c20f80d5005180350440c0c1e0018950340c00055210300200040003d1409154824036003070004112000003005406424414a01a03400010354030200c031004a0881518014940c00d40070800550141c0010b404c800344918408100390780d02c540010003542094109400241c00102000150325128040a412002c8007206014030700f40900001c0107075120804c1013091007000210a801c261030f028a900055030010181c0346541454504000a507104c030020304540220718011401e4101d0100440b8100d0b500c0b040114602181581400107903030341c0000341401e20200e900c0c000e680380c44400c44036202e000505a0500d020f4002c1101500e40f10381500c1ca04100215601911140d0108903c0c00480030340480344903009059009060b0301c1d211101090350b4280c05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 462283965 1250 462282715 462282721
    0x1080a0e150f19150510090306020c060a0f0e0a02010e0111010504060f0e03040b0d0f0902090711010c030204061d0d08040e07391509240b060304031115 67
    0x8581500240151010f07940340161201e448081c10070f4510040540b8182c007001c1104000619007643e60110b0249035040100714955280c407004200d8101e1583c0440d980c01107030400020003c0d6114210201307010460401041542c40b11456440441c0d840090500c014120140410780c0586415501514898000d002c0717882c4c0383c40e01030058280040403440031800d0035280780014901006880c151102040294140901100554080d101803001c403480f40750341d40f0828015842e20a1000d1041c0000e8403000d0000c8070b042020307421128a244103400301072051205000e403c2c1d1101c034615010b64a0f8506a103041144000200f0420301301c14014914840000c0c0000c1116109280307a118808235200c0100031800c0e900c04441c12604001c2400452034403407195010055000321000c000d90044108000791100413a61000303d400d480c4050b5000c2d0782400e0b004540a0302290f4101085a00030418010320843c031010414a01014100900b800315408403542c4020741000900e1995000e590001080d00f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 462285215 1250 462283965 462283981
    0x801021606060807050108190902151c020c0d05091503130c0602071815030c060909050a0c080403050d0209100818010b060406030b010e040c0e18040201080a0e15 71
    0x55180d1000caa03964100301c000909203a021601c0e40464906031940c503035681d1250400c2500c2031500001b12040e1369614582405030b100c0c8014507503207009000b107040d41e0310130114001c201142c0381042c511100d40100300086d000203020480d440085441d0805680313401c5410000303243c4180d00150b01c900c0da01d01108000030301e0403c070b0340e950540b030003244451380301525550104d86450480c0980702c614500081407407a480a1548003454880888400c840c400c0c0d169603541c460070107280e0010001800807042405180c080388201900034103103c03c1000302c0900c480015000707503001080a000d2007001300c1d21011407103a6404560040b480144130040000180c030f0041c5c0807040590780d04020b68841d1004406249052090320320514000300354500381854503100700c0181940e034590700d040002052030b020441c0c9840c0101451380354079072604280602000180007100300204003187d17001122909200c0541d0300032082d40d800400400c400b00f105562141c02130314052007900301e101d0b1a40300f01308001041c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 462286465 1250 462285215 462285247
    0x714062512052503051b010b0d0c031e0c03021002031b01020a180e0c03041b0303051206040903020c151b010504050d021b090c0f031602010507030618240f0e1605190207080102 77
    0x86c80c4114510b19601036020b080a0ce02c0709085801815029000018005403030002c812245040301441200d15000070807070f030082401c1c1c01360101070180e90003090b865004d5801241c0b2100300f00c60103039912145490280b0300c3e248002c0290440b81c41a0001021809000782110540c203072126842080340b00c0ca50303038a402060ba43c0b29048000f0036a131440301091851801d4050f000070b071601940108900c003403c3c01003004500d10014003018592007003106808000000c0c1d00400c0401e46a40000b941c0c4c42c1034281141040000400700c1c045410402003400c00b090003081e04e454221040d01e81c1d07590356803410290030851003204031007000c200c004001c0040749840c0d80e00d0703441204841c2d8000d2000340c4402c0815000d98000e80101c290042000c203001006040c0c030303800500781d00c8441c0c1c40103044499a9415500304a295001840b10003146041880007252a00304141c00100060a400f8440e8851000a01c1406440041450400c0611080303c1c1c0c180700b001000041d1409000841da20541c0c408644c0b84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 462287715 1250 462286465 462286469
    0x6040e0f030c070e042f042c03041809030507060603080306040b150906030606120106051b070506071b05060d0b030714062512052503051b010b0d0c 65
    0x42d0301c00d400001c580c080046a000d4011903012000d900788808013080070030180c0c00c00b05562058032171030031442c006503520b020740010842c4042107080d800b080650409540d11017800e4181ba2503100700400c112004606100c03810000e01b0310f200084a2890b850f0859141c403407140d019205508290001c4140040c440085010b00c004540030040910400f06010030000b00118075941e440f414040d520303550426500641e401500104403510300005025000307251107088c0c01180000b500440c41403103110007a144144c8210418000b480b441d440d110001e01c40b4071410700010259254126001c072103102040100019281c020134480e1030f4030b940c2818030020a20405c1203846407180400020702c80d41d150b0b5000c040a880a48850b26000401c0d090b80c00ea2191031b0347d0308041041040601c00810072010310203142045a40d626035650300b01c807010025449010001041c030049034140d030b40020b600603007120900001250008608003100124500400444400d40e401c0044000c41c08208111280d40000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 462288965 1250 462287715 462287737
    0x60720060c0322021c020a0911031b030103051b03030c010e0102180f0d080f0d0f09020f0f030601030623090c010801080303040b0c07021f080a0605190b0306040e0f03 73
    0xc101e4a0021148854149504019405c075040d1260a9040e41c4401511190325002030f000381580e0b559030340318804a0f40c9080c0c4281c02c2c1340c008420f2000d00380702d84100c224800d5507060494115415500c17800d4444001e006111780014034a240d0300c00e942c400344103403140c050700380340204119841103500d14003035446003075800d00c004011441109245032649840e110990f01403c1402550304e240e87d807100e5580101903d41e007070340c8103102212902041e401421103004103003601184d480007500c14045181c0352481c01c5480344d5403c4600e0005514001501c5046030380095011030fa504609040280820b00c19401a004c1d00300c4004000946800152119600100fa6a20181a84c1c1c1e81031440d124001035600902c1324402c640440c1015000c040a4120700703000414580d85440320240d902c1040c0f00c419503500110360320008100703104199120302c0000f040d0a89030000c900314114500440f100c854004d5801455020021499a860369844000c00e840408212400f0742e09100c20b040d5a5004414200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 462290215 1250 462288965 462288991
    0xb10060e03011a04022104050718020c1510080d021c080105030d050c1002030f0415050712150b12041707022b080f1c050603060720060c03 61
    0x556060501c01c81160030391410301800303c2c500d24810040030754460f10b6aa00d4045214108a14154503003190f0b0340900d105100401000d460441402c641092170341c141e086d060f105125110420a010400b665601e051182603155980d4442c04c114480c6280d4200c0401031052018119809070002032a20010148499003034002022071807c07145804240a0150190049458204501d0260700a05811060441510203501d60342c00d1007030481e00301301d03041d0840702c1407901031005200396945a8003008151117420311541c81c1014015285104203c11900c400780e503044207910403030030802000043c010700101a640d50442c00410440004240c03003d42d485901e4880643c01c51303602108558601d507000e45001010b125000905244406a80a050055180d010080001841c0c0e200603c5154030000c81542c40c0d09c840d42610321000d4606410780c4d0a5450072080c071140ba030300010a1948000c03145406168007818008042d205040c011b070401107482070741d0920090300c000c40c01651044000f260381c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 462291465 1250 462290215 462290237
    0x170310060e030102040f0e0403031e0506011d010e010e0f0315072705120f010c05251a09032502120a0c0603020c030f04030b0403030510030b0105011b0b1006 69
    0x10f080340315601c940c8200412a050821580400c030520552040c000c1c10000740084140009110b54940504401e040716510010070106d9078000c00306850400b501040a038641c804000082c0c050710512001505000c400380b420b0000341c0d1000d42401021a0103030540e03000682c0560401d105404c1a0f071b0450116842e0040c20710306c200080410b003103404c4407402e500785461511080c8030002c1d0300503840c100f517409503102116a00c13109000301c01803241d00c1d58569590b454442240042901410440400c40204c1c450380000700702e400704000841005083c103a001515034681d960700e18860200504005805030310306250001c0d0380500c1c00308841c029500e680c070750805c0480940e00d58038420700040c03e040b04090f06001c603078402e502420b5250584021a45403040c140402d030482e030029802110901c00f00420801010b500d4000c06400c114a840d0b90300c031203411a40d4680c01070700c0c14000e0504100d038441d0580a0100403020425040750805030700001c50030800d07403603400480103000f0800440d99072810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 462292715 1250 462291465 462291469
    0x50102131a0c030d0c0302090d0b070908010e0604120c15020309010f1107030c050c19080f01180f11060d021801110d0c08040b03070908061e07050304170310060e 71
    0x80b10a2221610055441c00c03c0f004000300003880c941c02c0520030145e00740a48085601c4803101c500704140030700c0240304130f454001d10041160000b50088800c0340d04100301403002d4200041d1180d042503000100310911181407004a80b1040b030f562006d010601c9448070041e031441d01d68000c40c0a422210001d0080c0000005c4030741c1030300c03a010040b09140c4000c04c280070109224160040c4d44510801c1925544c401700c8001031540604001581c200d46070740d00c01088104030410113907450074502402800004100e807201c42604809810242c02c801c4018014001c2003450aa240e6410703000401da030b501c41c5561300c0c3d03080c000d410480030110424608071805030b10350b02034141d2a80b1014210b0040440d4040310004840180142000f110700c010203020101d0540004009540310b20003603a42e0b00070682c0760031445482d101c1c3c0645142112451100c906404903450714800d5406405800c190b42e80c4e4881d440d1005582031380e00c6e51040c2544020060144160303011038902c0c1106d1603559421919000901 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 462293965 1250 462292715 462292717
    0x41b180605070f2307090b0306011203140d020903060403030603020306060a0b190e030f15071b1212090605070311030f0f1803070b060a09020c06060913050102131a 72
    0x3502400f41503145007000d002600300f6814490910961443d0b01031140710405251601542e508116101502c030400c2141e41e0808005107030040a031000e601d40d00300c3c03942c0c40180000b04842203d01c0404000039050400d112260102e0ba49802d0250403640d1914080c01c000340284082d0200300d200340104004111140780c103069620984804044980c0b8058200c03544203143c0510a0030701c018840d450305460038540e028029407002c0c14400f8050410100da10304005220340d0010100814046001810948550644500c0381c00e1548414011441144200180c50301ca0046440c0340070182440d540104101e000e0700214019a079035142409103600c0090b802210b80000c4400705101da40020010340f101d0503500c205900109101c044080d038512a112440c02c6511225050b1809102d0320103103c01800d0000c4240020181120114103240e078500d0546d44490015016031f20403000342001c00c80c0d8bc03051070b552552013580203001715551081076410701920030807403041842d10300c80d0141260310201208 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 462295215 1250 462293965 462293977
    0x120f030510090b030106030605150f0a0605220b16030906050c1b0f0a030c030308010b0901120504030504080d08090d11070905190608100b120c06030402041b180605 72
    0x41c90040c21a030408610500030440f002c1030a03815900e80c440000400c1051040070b0017400900d03140704810201c0303004e02041401210409015500340081007182992060560302c52081d04030140e500103011522a8030480002d40000114070f6001445000303010303001d6200500113100717490f40d6004a40d00c0105036601c2c050709619007030a8110011150107052040b00c14000c0c11002040c260040103042c01060f0b0700807440d0401c440e0303030070103042c10701c2031540142c400d900604041e400d1524105120000800c8000c0c0c1d034030000b0a142d01d40022404050255003914003904c0340c041201c60340031f901c0c04003c116a4040ea2145114001c0c5924410310b44d00c5a411001c480c1103100040c4000b9207011180801000010040030f86240d8a0300121500502805200c0041c02c007080104405044111034804483c04041824403400da010341d5541650804181c8498000044600c1d546940d00d5001203005041003211070f001030500042e9640c0b00c103402592201e10213401c41601c00e402612048140c6140c03180c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 462296465 1250 462295215 462295231
    0xa0501030e10050a11070c06020c03030313080a09170c0405011401080c0a090b040b0a0e0d02032d060a090b0a0e0c040f02070b0411240a05030405030c0604120f0305 72
    0xb0000c801410481d40c000d5504603803401c10000c0c2c00500341500e0103041d00300240440d60704401110030450a54108100031482d4002c4014524600300418003985102c049040101304c01000300d4112032450280030403200901407521030040703000d41075410076100d041c000c441c00c0c40f46180200120303052940301d24041036600181c4800d8410303211644000d00c250003250349d03030040004503040820003103c404050f100800f030b040c2e8529201c615400d0007400200301c40501501079030f0b042408101613600041c2d200c07080001380f281c034203401c1080f00307640841202c1802d032100701d07100b00e005202e00080950b000201c0d07940a1101e140f003d44520700a0029150284001170351036010000780249440c0907406404490510a4018a030000c240d54518041008075800e5409103160050600c26051003c4c80d6400d40385401803120a149a10101c0603480c023400031203108018001c80000c080080c00c20840301c0200065013110402c1c6880d245c40303040000040c0d21100000c00d610361f00390199009000302401a214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 462297715 1250 462296465 462296473
    0xa200702010302090a120309090509010b13021c05090d02060f090a0201081302130b03010f0b0109031104110f0a030c0306150e0114040b03060f030a0b010e0604060b04090b0a0501030e 80
    0x18540045020350411450356a115002c641d0009850000c0560301046511940f11041030500d00b03100c2c1c1c41101e40042c181c51859044c0f41c1405000c3d904c40880014080d1354140060711014a200404400264092003408e01c80c54030f4103002d0704603130002c2c0901d0810f5055086a000b591003205111400703034165040381903a446a0191070041d0b000f802040c0d40000340f201051030304212a000501041c0e142041800002c1c5d40386c1d01c880f51420207001d034407007a8280d014140441c00f0709600007000302a6600c005041c41603105800146940d443e005040b00c091403284083e05c640c3c01c1e00c00704c04030340c0c40703481208040f900c1c1000041da22406401018100c4071107401a40313844514443c103443c80c9107c889918108890100c0300045240791001405c0a420020851a264500901480607281d07800182c1c0b13205c1e5101c12000e800250314803104a0542d14144480d010648480c1c0210b8043e01294001c02d43c25030340803c0c00314048101d54030011403201c04403800203419603140019011250041e4030340f4aa500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 462298965 1250 462297715 462297727
    0x10c050313171b070602060c04090b030309030a031214131203110301060309031803050601230402030f0406051b030a2403080307020601080114130203150f0a20 70
    0x200600c404455a0280b1428000b48003040850b00d041d5100c10100310040042d4810550b04480400014024201c9400208014104400014804e014600c10040380075280c050760f90240d03c060041d1800030b00050704a9070b84003003628002c0d00510701400a0b0003150f22b06080f5003400946500030f18086c0e151100041d14410791600e030428501d00110041c4141034030795600740c0c420401030740190f000f0b0882d0350300000c4141e02840d0007400385100082c1e241950420700400d00c0880c0001c200c1904481d0744840440206105102d540c0165610032200750344903101008002c4c14207420004584524402ca8007000f203a602c01075900103400c0768a0501d0141d00b0b0a200146003000d03e6070203040425810486080e0f04518000110324060b1160021240c441e0013006210b44d1980412071207001d0507160000780040e51180350500c81d01d603070050060b1b04a145246d0b461081d91418030000c4640d15881d0403481032450040c140d40d0441d03d0a0300d0300102d0505c1e05000e0006c0034a9684018132103403018003894a441c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 462300215 1250 462298965 462298981
    0xc12080c0d0908130e060301181101030e2419020c0c06090d0213060302010822030e041d0a1101031512020a1d07080f01031e030302190306050f03010c0503 68
    0x80b04803011100d0480810204003480007507421840180300d402104606854500d040c1801d4940300e560040301244849403100000303a5210b40c4c101c50f22400e00e00040c3c81c070900c2c01e0441c50903410035030750808010000310401c035007131b035500d11107209040310311590360b042c10140b016030102c0c4180081550706400c0390014500b00d2038442c0041c034481000814001003028650006264103282024800500f40e85840410031540c00c503203950742c0030020142d80404081c1d8203010715010705628a00504100c0c80807210042b50780c6030f6000036600341114030903010000070429455510851a407064034000f066801c0c804456121740549100107030164201499149000002d050428440c3d200300e07409501d22070f01154003040c080641129036065611150f03035090251000e80011009000c0401c9599080010b1011680014488251000c44800d0460950711410103c0c028010b00d040700031040c02d8a00102507469240c2c200c41c0580b10100d598400600545082500301c40c207091100c0c0110b802440050004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 462301465 1250 462300215 462300221
    0x6040e07110705030d0201021e090603040b0a020f0307031a041e0b0a030501051f090605060702060307021005010b0c01050f01050f2209030503011e0e190e0d0c12080c0d 74
    0x18070051000c9039191a00c83c0d000038140300c00070000200603940414001d01e41d50551070055200c3c1e041c80c5101c2d1a0154480c0030520074840144060000c07030000000c1500c000c1d07103604035031481c002100000d0303e0b81042c01005010f0103613843d0b4030401000802095245103490700c15001d040c0750000e41400c3c8c020045c0305001c0070304412902c042c2d0140302c00c600040462004c0c000d81c4d00ca100546035424102c03040a010f031442440130f80144043e1490004188240d4491b00300701d41c1c03501c1e0100e94039502c1e41c1e65600304030700d800000152190082d052800000d5141040009001269903c000912190340c5600c04140396003000d2203401e5012a81e0180001c0505006179107544c03401c0d5814103902c0102c20041d0110a5440001d012400a24008010414100c4544100000c0c40025140c030002030700d0907a4405000002900c41c0001c5403241000c11845d0720240d005443e203101c48000d9a0404209030b0001e06080c0301681c003520003000488405500a11405440d4071803080850341504018441144d2002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 462302715 1250 462301465 462301487
    0x2060c1611060c072303280c03051b0d0b0403050702011103030c03160c030c02010e0307090e0d031d0a120e03010e070306060b07030c1b170c0102010b06040e07 70
    0x40e60340308070121940324100103010042072000203240d064580441c101031100751007030301c0c680005c05901c03003102c9641c0842d0451b40a0941070b6021101001c1142414001003e03940c010415240c0d110300004104000c07c0d9414209101c007030704048400804140311904100040c01042e02900200090000f4000c0d805021940c1c010301d402201c24007a0740c03000e4507592040e00c0c403c0f071001000c030401c41503298200c640b04542143e072502240c080c0c0305507005080741c041c0040080c103028201d0040d40c01601c0030451300380240407028060011a80192400791a8104486980e000908220003e01218413a000020801e002c613001000200da954449500d8003603201c44a0b4204120301800303100d241d07000d00403101307502d0311000500001d40c0345152003030072110250320842a43c01c0500c420000300c1d8000204140a0303400c0650504030095401c0c601d0064041a0098492044404a094400803000070b10041080382a0003c018440e035800030400603000ceda100300c40503c3c080c00d000911513803190201c60b00d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 462303965 1250 462302715 462302723
    0x50c1303021e09040501090506070f0e0d020f0301020409051f0608010e070909050c030a1b1b0809030a240603111002150703090c0f03050a1403040308130e0702060c16 73
    0x114030342c4140e002440c0030505460644070b07030391030715186002d000090128503003284071380c108809600a0351001501041e60fa513105440b07040c06203140c80954407201d200c402c040000400071551030741c0b0b824a42c40248000e07a0320504164a00000c100742000c000c07003800c00d81d2081d86030304009a181480401d544a4000c104e1000c2050b110300006440d01907001d070901136007600081c19184d107002c0e0040700459804210040c000c0462a247c4002d540c0c00029290400081d644049826081810032a41611620101c42e8261140c6d442c0c3c0411700600462910f40100001c0d001c0204a1500ca10302d030a0724054000540b1007804c0044516062500100304c107031090660041c0d401300107240b4510f01c0180e80450708840400d88664450701000a50592840500b01d4410f07100020750454031100e90b529a01040103104500000c940b1803d50030030020380e8019588030610341d54039a81c0380f01581c110900c510410000041034004100c88a001154040c4500e03025a4054240810103a50042000503800155 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 462305215 1250 462303965 462304009
    0x1e0a0507020a060e011e1d01020a1502090310020702010909020d0f0e06060307050a08070b0a12060929090c13120b04050d08040302070905061c05010c03050c130302 72
    0x80181c55102c0ca00c4010f110a40300c81074074144010001d40211080c3d10079042e401c11601c000c40c0150741090201d6003031900c0c59829400c030071a650041c5c0c03030002e040d000503203030b10110100c003804200683c0080035042410b4003900c1182c220344050006a0043d140003d000c02c0700303154244255111507014092041803920017140840d40001200203e58101e160000d49811560030042c0b41d00f01001614018601541c001c00107031700d8841c0042d20b0340034034000c0c08800c00000840d01e0000344038036842152405000c50800c0090798074006040104481c030352096054824015a075294403003542c40d10702c000342c0502414a42d81c0c0307215052040358070055014240010003074003c00c92180941c6c0c0d030b4040520940341d0b6025070a15003889850709d00c40301c10034803c00c40e441041000083d4080b4400e42102c204150200d22621041d000400e102514040380d0380d070300c40c4005104e090010541201e81c070f007030a5440807c000d4032010010300302c611400c0f0321002210340080003040181044010b00080074400c07000c4c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 462306465 1250 462305215 462305227
    0xa0c09030807030c020a120803010504050c070c1e0905011214031908011706070518150703031b0305060d17090901080d020c1c020409150204150e03031e0a05 69
    0xc00741d000b881081c0c0009401d66440f10441c100050342d0000781c0602040d07059925416640c6922910050040500036621000401c100171100b1040e15403075544400c951443d1034840c4113803000d10880116100511040d64400942d5462910605042e40d0701c070b5618010307602082c0c031403c2080702d40003d11000c4c0d10040003210103091051804c05092092551445941e51609072a44e40c2c051303c0301c240600b550020002c0c000482d1300030f4126a40320ac1003414401c494585040042c40d8601c1d000d4411841480c0080c41f44201640350740314060055899503030a0050590600c21005c035001203405a421468110204000c50021041c1014040c00122054a441031142c08103291140c2a8402da14540c8000040700e2215010302404400000a60341c02104a0400004c4580c1090420019000f15660407858050200c01144c909088011140a561f070342d03520001401c100300340e43e41e10400111400780080071031401100701c400c030b0883c000301d64841c40070035850a003640d4080d08000c02031040070410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 462307715 1250 462306465 462306473
    0x13020a0e0718060906030e0102031e040f06020304060c031802130923010b121203060d060b03010504050c0a08150f0c250605010929030a020a080115050604030302060a0c0903 76
    0x1040043c2c078903907035089092403400303102a06642da05c440c404a66401030040241c1c1c54144a003001000040c0e01c1100c03030729290350a20300185040d025001d044140000b08201c00c1c40b40c503030490386841c141583e0800691014000789500841e5601000b580028481291600c2c1035040c1c12511880e030080c040c504540f02018400300485801700500b4407503945405d2100d8aa191602100c64139940710400f410868407a60301c29a490310000703090500c100b91903440303041880040ea205541c40c071009402080503080c141070080e500c04100d04d0141c811882c1e0300003c0b80c6080c0c0421481d00c000d1a108800807180c544c68101408158010f00503080c410b8280036140c0c145104041c0950006d190700d0100704064640e081107026244140c00800c00282003c06000d0388241120340c4543c0c000783c04100c003400d005400c000a044c0040200041e5012202820108841e0300660000341110022100e13076003080c0d900c4091158a0041c3c0c80702074090b80044c0c00144040d904c9400100f58a8035616020302d20940342e0380c1e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 462308965 1250 462307715 462307757
    0xa1d0a0b0903191b0f12020402130b2a010c0e040903020a21021506100e0301150b0306030705030f06010603050c0d09050609060105150703050904020409020a0c0b13020a0e07 76
    0x1041c0c030701c030418480300380c0280030034528040a0025803289001450801b03881c241e80440013080240510350000d0300f081d0025088400301d0107054880511503440301c0c07c9000c1c0d083c2d0003440079061004210107500101d109014840d2401500325610b0303200d1850140030812000f85800d03d8190194064180008005030f00c0d040000841d020700b044202c255600b585000380740210304085080007400d24828000c00340e46250003c0103000440c9003d0350110b85c3c40700828054a0300b410000c41c3d500c00c2400c04204651f419010318455001038040b12841030307540c01016960003082800a100d038000c41e005000b064441c0c0c20280e0f00c507880b101c009203405440010705003113400550090b01d142d0802d40910001d081c003800614014001210001d0081c2d02007111590a80f00f40c0c1c0c001400c4c40400135270308407103480740e40507907005140c080e20440d03d45210100203041c0304030b0701d5021100e40409c440081d0b0708a804103143c141013900500509400e0f82403101140404901802c00b000b40081d195581c0305d0142d80325 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 462310215 1250 462308965 462309013
    0x14010f0314072105070f060c060c020106091b030e280c0302030d090503010c02060907090c0216030b06150c0a14010e06010f060e060408030a0c03170a020a1d0a0b0903 73
    0x41d00f0301030f0321240c0c14072606203c000d030001940008150010071881b68030515400100c0d070800000211420f2400c1c050780100455801840043d0a101c0b2054480001c40d280858030f0070f83d52001c0c0f1151032244001c50b128120158688032000b0a20441c1c152601c0a600c0d01c84040e1042190704082512900000d10340f4000301043e8001a04c061410f2003627080c280181c2c00507041900041045081c6001219211026402015040d0f9a2049880c1007203108008110107129002c2007605216240e003400c0203601411128940160340042d80490b80344103d500701d0b01c28084600107402c100c0c0307060741c5030a0801c920b10048252503485ea610890302080500c409402440c0c494102c100c0715181c610098007200590710681d110702c400b4403040095440c08811208490752614020b0690304240c40e0640b1484407101e10b10a28144100810007011340031350061400900d076454400002c020001c9003000700d00040030150704003441550070400341460001074628544000d0596404014185c0315180f000142 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 462311465 1250 462310215 462310259
    0x7020d0614100506070b07030c0306050901030605070221041e0b0c010c0e0609030c0f06130f140a0303210209040c0903060f06150c03021f090614010f031407 69
    0x26810b000800c4800d5407860028001a030304242080c0194440010700c0c03500502c20001d140c2c841014840880c0f0960081000c0e01c0001d200d50721a50312810608002d280803201400544036400280030344000b11070039030b040c10142800080c40c043c1040311403040a01d0700500d458058109650100e640f4000380040c006001c41040001003491a242006141c0000903940764090b540401503021941c80100d0086894101541c1501625118401055043c441c2c100e86521414582d40c0c0841d071000040c4001003260801405100112101d4003044214001c0d84401804580911080001d031b0721700d50601c8004582090005003041c82810101c1c0540750a01102c00c002009003100340200909445003110384003582104000c0f150800d0070420130503c000980b0700a100308640000d0403d44204811000544078a92410708020341400045c0502284403044030043c0c02c01a40d84030010030a00f07107604891000d00b00b0080d19140d0746442d20b14030145541c0714000c1c09214000300d00300000180e552444092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 462312715 1250 462311465 462311501
    0x1e011d0d0f0906140304050c040c0f11031201230a060c06180c211b08060f100512030d1a01110109020102070306020f0714033001090207020d06 63
    0x112200103000c4080c1c0c00200040c41911075003480407980c000307404564500041003551342e0361590b081c4940341500740241c0039405418103c0b01c0e0800369106d00c01000301c07181da072551030848000880c290345a0046061111050303020400400580b51040b0103610034020840d90074604040003000319481c0701d103a4201002003181c5848034810040d262052a0302c0b01c0c0182000d0f54000e089a9030414103586521503180b41c41504044130b0903510b00c120003101c550ba4010302045045052045408042c4110701c5054014090900001c0c16403000500b5107209100340094048040e007040100003100f00c84d00804500ca01c4140255009085d01d445101c103240c2031018030004008001c0b0004018480504840306264108401100141d03000520001580c0e4411805a11040c2d244e02504c010700a082000e083e180781d4205850804c840440284080f030780e10300130319054003080c0d0301d04a03050598500760818441124010045100c00c4c0d0b01800b0624401031041a80c030072142c54440c01d03a4900340e1300d0388042c06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 462313965 1250 462312715 462312733
    0x160c0b0301061701080c01050c030d020c0a0b010501030203060123041d150303160b06011403040609110a2301030e0708060108010606030c020a060e01200706050f091e011d 75
    0x5040064004500c0e04482c031030043d503041404090702d4030f100704032007410700a0108191207065000e00544480b1890890115210301030091420742c0c0d19084003080c2c50740c91540002003080c0d4130034000c8031700c9000c1c103854100780300303400c0f00815040c0021201814010003080c44041841d561400c074910080140d8a820801403c0c510f41c8800c23444c10344140584640e00030000d030400329090307401800b0b10725080f00c0c3c00081907a4580040c3c944001c0070014903405180001004100304066205c3e03e13480d4010a071090152440c401400402c1c40d42c0d0050500c541d030500c0b10322581a04c3c9103200d03118620107240100700a0101680d05107003e0482c2c0150070650401801030020031000d22400c40100060701e01800714541c0702c0c6002e5160100040c0c06080d194235025100c81e200780c01d410200690019040c00d01040c0405a00d81403a03410034070003125a2402c120100300c0a035468131006000303069003000b4004040c44800c81b80343e45d03140a154420155200d281d02a1103820bc203404954241c242c01c00784c03000c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 462315215 1250 462313965 462313967
    0x3d05030f06010c2a030213090b010b0f07151d07080d0207060f0e0409051f0f050f24030604150f2a0201061e2408040602160c0b030106 59
    0x580c005004904011825403080c001c500c0030051030030059a601054030581030300c82e160020500e4641c002a40004c0070304801800003e0940c01036442d1405180401e80903602c407210140030703210300c04602c04420018408103000c2902540322104800800340001032480c413000c8108107402d0302041c44542604010000c00c0680340500001000c2c0c0ca107032015001d002e0920102800d40c082000317004042001602e03071015551a59808000401c2c1c0010407144607620074840d5504c00c1c440c0c100300b151201c1c28103800307081502050190900600c45d40e110f4507429644c90242d10070400c207203568080000c0d2009a4410103850500115018a0003801040304d00340300085072800b5a000c01d0121243c0520301030100042c0985a03890315030312800305803101841099404100d015020a401c550004100c8088054100000181800c215056119001c4003444040000c42d80c0c1d503105500b01021528002c0050006040340d0300810718290810704044180340251a030690201482e08103640d22000000184095 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 462316465 1250 462315215 462315241
    0x9060b0a1e0e18010603060c020f070503060103030309150c0905040b03030a08040311030d24080318220f0c110d120f060506070602070209060d023d0503 67
    0x60141c0340300503141184505040000a1058890602c80352201030124411280d5000c2655190341110024014161642003040c02800300460743c001602c9613404e8500c0001012a03043e00301c0311300034003803c910384c6151026809000d9002040303e6650108201844000143c41180348030020f44d5110803a007801c02041c4001c80e50048001413181d0300c14420301484070f0340143c695510a40c140340104602050180c030500d14001e4800082c241c5040c59040c010300c000221848041590b40b50303d60032016916010140c03a8440d001515580020301030052849041100358203a04200c42c101040041c04c511b1651400c440d0030400c051034994075102c0f80304000d58003c10520603401342c0c50152400740030b4440c000c2d024100c01001d070b5100c1a116546031080008546c4010300a141c050700c820350300c40c4030f46080d01c002e5100070300c100c0c400d2030620045003082c1441c5111806859010345500e80c001425406503110300c0c0c940240948a14484440c10544019041502d001d164240c80d500e40324106070141c0d24203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 462317715 1250 462316465 462316469
    0x405010906030203030d0b12010f05150901080714061201090203100f0501210b03010e070602010c081b0d09232815110a090e060103050c0f0a0203040909060b0a 70
    0x100d14107040051000d80e8000c000c0b91209656440700058146070705010034180b223010b140d201255403034003070041101000c5811580c4586d0200d40200c98031891941001a402c0c0e007805000e502c0e9014510510040c0c45811001c8200c010062006041951000802c1c3c07802c2c03c01d800507503929802006002080003101000f502604052080c07101c41410400002c010a6121010801400704420400000c0382158088289100098000e102c1b0f19811405240d0700c40d00d0f80b04910056103001500b80145100c0d0011034080c54094141c8000c46c03800c0140490b0329081281c0100780c0c00da6a404071800a841c3d10002000d8040c0c24403111504d0152401441c00e001121412051304448a01006a5400740c0160988216030004980e031141010064032002844801c03035420101d100000c49120003a0040171040881d0300d1598403d0a075660310004405031803081d00c0c1029602c40034003a400d1380b060000e0203031081306018030481e401c0950ba19040c40540d1010041a900d0a665a00c40005400e0941714040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 462318965 1250 462317715 462317729
    0x60601020f030f0f0c031303050f0c090f19140a0c09050607030c0507080f0303180f07180b1509010f091a0a0519030b04150305061609170705040501 65
    0xc564007586040075200d200702c04010256210006540c5100b007100e40541d81c0d64106a000c0300c0d2101800441807020b480c240c001a21648503404030451541d400154105444038082c1c6845010340740e294030a2007032040a003003140c1c50519080301903001800340c8509800c50907010024026410301b101b41504440d000001401045924541840700d80c545030100c0d20056171520309403490194504003241442100d070040038060240300d14900c5844800006103000340e04003201411100d1420f40029941e0221070304a4580d60424207040000c071408107440d4030030011610300071a000301d03003a00041480c1c9200c503824185000210306004603582c4903210002a110a080981c1d0103420201c80c0700f62088e8100c0b411500000026520a0440c41502035600d0540100514000000b2041014018101c8409554021841c00030a01c1101c1401d994503400c4a4000c0090026600d40d82120004007040d145800d040c0980c01100080301c85022840d08629003469002e025818106070804c01504d0060b44800c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 462320215 1250 462318965 462318973
    0x5010507032304030803010e07081302030a030e03160305070e0708070c080d0f0203150306090607200a0f050303040c0602010903092c1302090f041a0c190f0206060102 73
    0x240041e07003060161801e10940044900032602c08034903074030144140d0b040101040404000055482c4041405030300484071502c9100280da00c41e20904103850840c1e5004e5856400a4028008a800380d80d1168040001030260344804001503459084402682c0c412078890303122040402101005515040d082280b92908034103e0402c0da400501d800c45041002d0030079800041e1b020070307030000b40c2e0200030385404120b01507440345040080c1103041141c0c159028000d0103940c001030100880400c00d680304440356103c8148000544465181501200c00c41c0c01c25403261030b10310004101c602c000c080f00f09108400031696490a071500f40f4103001594850b0007568100003210340025040002003081c7e81c00003030032548901e074110051024600101014440310701c0181484100c01040e5042d040c0d0074000c0c1c8401082c1d44a00c0320710f185038202114050318200c1d10103080c00101c1445030800d600510450300650400d400301400044d020f0000c890300b00464540403032100419018405158440001d0004d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 462321465 1250 462320215 462320227
    0xd021b03030315010f0203220602010c2318060403050105040312060b0f0d0f0c0504080d1404120c080303190b220c0918060f0f120602030604140709030c050105 70
    0xf0380541c001c070720905105201c5a00d11149208005894002e0342d8502c0c04003122410014815042a03140603600055080c0351440c00d02d58000c64550b007420007003070030390b4007505003a007030030b001c0c90f00107203071700c4400c10041c442d2094642d842d50090030284d4040d90001907a41800c2c42c019001494241d4001252410301100f000400c0784c14003540d0728500152032007541e07240c0401a0500402d8400450b45540c1d140c900c20068040e84140540306803818201110805601c908080c3c947c1d01285241c0b10200c1420070060003900f680d000c650308a684204510580d4503150b4601c2410350700304a40d5a030130400a01041c8007019014002c40008260a07101c0c910010b80c5d5054150420100c1040c5000b03098503a007860004910030005e140050944c10348a03106003003005003507400b03132002c1d110384a48503104110109000c904001003004440101c80c0d08c0050424542d102c0020b5000140129482680c2d009021000c0724a03a61062041442e0f8ad519001e41b4110300e001901c40c030458102c91304001003840b0b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 462322715 1250 462321465 462321481
    0x10315140c040e150d21020f100f02040305030a0302220510030905160f08011a280506190801090e0309090405100603150605040b01090b090a05030d021b030303 70
    0x850782a6000702c150300b112070303076440082c81c182d004040c24503820080b042e0042e8280007035003280c501c83c450080e03290002c1412840040380c8d10300d1809402c410540100c0110b202c218015441104100d51411015003090360721b4032000c5c10340d00004402800300b9000540b14104424000c0d0403285004000b40040300d680c1448081109011985030b503209042c1e680c950740301444010030071110b0b4070710900c40c1c0100d465200c01d072107502c80003203104002c0a5800c00015051117000320b61170100e845006400741250010030805013100ea002105280034411029030302288507100c41d03005110f04201503801110501301c07220000d100c00d105034000c285092900c486400200d4000c0210b4444038003c035140e2800341c0b1682401d604011803000032180e850700e071000000420404418242c003142d0002402c125650342c900500080d160700912446c00107117413490910510000002070044000041c20700c0855139280c0010a203000344000400c40564421250580c8020005c0e40c0354a00040c02e0300070750304505106030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 462323965 1250 462322715 462322717
    0x6080613080c010e0616020c0906180a0204120309050118230a0b182e050f09030d18050402040b03010308030912042918010513030209010315140c 64
    0x200100040c41c00180c88a0341c8509400c415595500c48090b00c085041480340b018030407075000c0300d400250044024160300d80c40c0c040e074014030925002e421015030080e00901d20304035440c010103120500c0d034240b10100d08080c06843d58018a80f103612460001070421001509200c8425500e00346180c14541c140002580c02042540d003803903440c0600c08210107000001d80e5005a904001074110340800d03504140b44201c086140c040b14156420b854a400c20460300101c400c80035060484640241c214480c440d10440040241c02150721f921401e00c900840040c1c20880242031000021700d80c01100108900303c805032200603c41102d0443c6400e140c001501c4050105102c0034040c048040002042c5080c2881269a6803240103510359549456012440c500d4840c2c09078141803074100010061907400d41d0049580391069003030a440c103484041c004603419404003c2c8850004e010002c000010303220180300074080c61083c6a501c658040c2ea03144002140d00c071075107219440d55010240310203031038100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 462325215 1250 462323965 462324001
    0x41b0308030f0f07210e0111030610090e060d1403211003051506030a080403120f0804030c0f020303040b0a020708060601030213140a05180615030615210c0d060806 72
    0x5400718108018245205d004201c50207450515508140d2440052001003004602c95601290800c0d03031a008860102c800802030b010340043c3d0241000451054544080c40ca041e840c0b01c0d6900710f1600742101c0b8a81e0464000740b00381180b0300840c0c0c0900c6081014060819800b400e0041d503001e1030b51654072202e40d50b0034940300000c0c2505405020452644051005400c4c040d0015a02591a640ca185c6600840300300c0412a00190000300d0700003d6512490368140100d415945098615850f52248264601a040c0403a032502c010000061036940c124040c0c1840700c4c654020381001441c1014a50a0582c001c1945042503c10009151200640301c480f0051f15250019404a1488100418410b2021b41c010f80d9202d0401008000f0259421900a01c105800d40c3c11100b143c004d1308100d080b60000381c5590ba0300008206200c0700c074008020141802c1031000210300c081384501d07511419098025200382640303540c00618074000384200e000708030003071001c10b000780310714500352404040e407451071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 462326465 1250 462325215 462325247
    0x31b01032301030503071502090607081c0e03040f17120a03090804090203010513050405031815070308010f12150e03070c2702071208041b0308030f0f07 67
    0x7490240029480580d203031440080d0050021071a58490a00e0f640d030380c001e5003041f509a090410495003c0c02c05000356041c07500068805070408100c1d541c3d0042c0d40c1c1187c2400c5489030321058561012201d54013134007a142d00f03000007965403141003080c0f2045226582d003200c46100d40c084032040008100142000040110054080c4c450a54210840107007040c610054180303800030078041581002903000f5412900d08440070305008801000e403506940044401402e03d400500903000000c82880030f500303803540020901001010115220407407078028190690000d080c020040c003541051200400c0507000e410103619001302c1356900c40010215007180000107503110449500451002c00603645000d40c040704040381c0726110f06030f00c0122098a1130203440c11400410a0b902d0070240d108542105401c808200c40d0042c5030f18040e582130b00c0c054001c40701104003000364002c80c200390b1041c0b0701031449a019180c3da818180044c4044200103007004144401d49400d00602c1604060001000307114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 462327715 1250 462326465 462326471
    0x1308030402180a020d1a0a1703120a15080a0b01150e09150a09020a120515030a030302040501020c0901140d06020d0f060513020a0f030f110a0e0f031b0103 68
    0x200e01c04034071140c001403001d105012000e010b00036280415000b80c01804d010120130800d0101d0810703104050854031030815049031107054140659103080541c10b54409082e0100c0741f4240113844815620082103581d8045140c0da801003001c411044040c550003402c030100149064a420340307940c0b010b014188503109000d00b0a03256414094001c0e0003810307103203800500307c441525003010b0342c6000d102d200700c0e41c511491342c07480e0204005545109480c22040c031595201c01801e0f00350fa0110052502401d1003210507082600c03e54a9a170420803500303014803030b07580035031214600000a03240103510310005115031000001401b110080d11003000825104941405d515811400c194000f8494400c0c207401e000d08010342504a04002d41000007121003e17125889100850311b001c800301d00444580c0c0c03000901c00344c0d113920100d10070b400c8121f11a01c050000039040e4a03030b012050065001c0010900070500f1a480070000785420200020003820030f0700a02844180050f8444405804113645418140c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 462328965 1250 462327715 462327721
    0x20105011a0705011404060b190b070b0c0408030408030c070504050c19120e0f0606041a190509010909020117040b0a0e030d050f1807081b040f240509130803 69
    0x209400c0f00402c40c45c0c070703640007985003018107041d0b0243c000d038030085004200100301600c0140c4855002c1d03086840e481c2000d4102291903461210391680a803c20b0f0010200303220200d507008060005200800320540115650b511100c50581040401d0b8843d500c02e525003401c222410440e10704403030100c01132201c0d60000c8076915009490542c03844212080d4946006000c1031415400180d5001d000781200488250b603403408100810303100c1c0d42c8000601c04018644082031170404d8801440c0c085e11304c184075a06541c030b810100b062036a007640309000d0a03444450043c2556000344005001305425040d402203840e05466001c050400035101c0c8451594aa10380489803c040c1b042c0c8421000d01c0e0400c0c802800d01100c3c00e142101c0070341d0141c6d0b81b04045407a21004020005254088461306030250680030a881c4415040c00071443c400d0380c20644810242090900303502c915032003500e04040c541c11400d160306102d0034900d4035401c0320b0b004400c65024040100c0508500918a6500900e55984c0369 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 462330215 1250 462328965 462328973
    0x31a04080409021c060b0d06170a021519020619020703021213030b0f0615070f030e010504180e0c010c081812030a030e011a0105120408040b0a030f0c020105011a07 72
    0x3a00c042c014032200e02d0101d0101c2c8080c203400047c000b030f1039902428052241c460380c4031040002c15010200301030b0701c800795010050920819907180f440400c03001070300381858000e140500c0c034180006003005800c08000c00100c148601d03040c000800029000b1424018940d8020b5a91145502c201c588002d0101e039000030030209601e00c0001c1d5038407116101d46820078441800c454581550701e039109880604a043c1150828416249565000140c02c0d0760051540c5080c3c0f0521050a00141004000c21000c5005682441d480300341200128001801e0923034a0b88440c140140f21100e5030402c4003680341803011a8540c419200000d156008025520180c4000076001f862948203800040c0004907500c0f99884d0540c0c030064006400c1c4000b44010051003803441700c10b9503e441104d010030000d1110307000620344021010361161096090031300d05a1520b00c0104950094000d5600081d15071000c2c4492101e00e02841070907084074002400340b54104110032124070000045100c003203602007441c40030f00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 462331465 1250 462330215 462330247
    0xe06121008010213081e1005090c100c0201080603210c0106050a030b071d010801030809040609111b03091f170126060124020a0203030a0306031a0408040902 69
    0x1081090000c65842010341c0c9141d901c4c103400c0c4070381d04a81c0200415034040c0301c1d203034403140805400c0030050070504681810601c01440c0280802131036214032401c84906440d00c02717505540408645950410700c546100040c00030302d00038003140c029040b47e0580800d28801070105041c0103403009616403200400301d041d9006042690100780d00202e40b070400802e10101440c12400740305990f179000142c100c0c1c6450600360303d0b29000031600055898004201080700704010b0031300984024008910190355100000030f681450010700140c010000d03104070041d5142075194042d0640e00c01031410801c64800140d100400f000301402210400340103815060701c10030501040030f410407050502941c556010003e480d4024540d140f00c034000403280c0c02140e00019001d4125144e1154040b10702048080000d07802c0c20009949040d0f100381d031850b00063380c080c0f01400700002070f65000610383c4d15508012070420050082c1c002c11240342001d001c08150b0020450702920850326000d40d0760b090440c640c3c046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 462332715 1250 462331465 462331469
    0xd0c0314040e0106081005010206040803070c02030f0f16050306011a040e0a02072a1a0904050103050a05010605120322360209090a1515030c0f0e061210 67
    0xc03032040010003080b070101802880c0d06031a49a80c80401035600e4410611112480d4026240546c2c40a0009400a80b82c0001554000c0030b0b45400c160304892035020034508205a010340c440c0e0380080303280030022602000f120300c03c3c1c0e0b0650003080007280340201190721003806016004820132900040341100340c110046034006c3c50107413002d0741d882c54800c190000079003103607404503a860641c1c020805003014081d6902c202c01c244007154900c907460012000d10084440240c03483e003240a1103420901c1c0d841d0f10480c0d00850040014003200c40c01c03480c080d821220745170040c3d8032400300b9001e40b6003910b40c00401c0e24007a903910007205082c076003c42c2e0303000c40c0c000c0c1c04c0c0d0280c003009403100041012818044005180300f40c0e0004180740d011710140140050303000b101e50041d00824480300203010805181c018902c01e100c801c2140f41c0440c0c40d00381c0c1c141c1800717920022001003519004c41c107050b06c3d4418190300d2019407038981016034000c030000103022403103030032840311341c01c40c0c0d880110701120180140480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 462333965 1250 462332715 462332747
    0x5010908030906010e0a0501060512093306060c070b0f0702091602060f0105060702280e040b090c01050304020f04060e07020d120e150a0f0207060b031b030d0c03 71
    0x80c0300d282480d51265030f07560034050a0400c0c4000350120701d05804a00415050b90665111039050050b4100244034550000301540e81900c20000001601841130f4401001e80703c01014010002c00301c2c40c0101640540582918041c400c200b0802d40951404120101a2602c540017559a01d4859011548500030410003a43c4111090f0510840810781186c0399040082a02904e015903241443d203c00401c2c01d1180c1d60b0424000c01c010750041c6020604043e00d510600c00f801c0203a8111050307034690a82c20b8014100c9405410280024865003040c3e485d070154401004203850316044000030458080036000034040d0f04041c1c000f90307983e40d0715040100030b03000c10034440c829450420802075480c003400300e4030408212080d88105a070b00c40d900179044202c51030303402080104c0c148200d103d800c010040c00c070f0344100d640d02003203000500180001c3c021107009010228800e0170003000c040c142010802202c0411643c10704012561300c0100f41c05103048102c1c20444814015418280d80c120708c1050600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 462335215 1250 462333965 462333967
    0x4050f1909140a050f011413061d0105240a08090109060c020d0e0a0819030512070f030507050a0e060d140c07110a1d180d0c1101090e040f05010908 65
    0x4202d03445052190307071051440303c0060083d07441c2d003220103003800001e0003248042403d0380b00b2018241011007400c5240c1f0040180040c20035510102c034452100300c822454224002c807001000b692800d42508440c000b43d0405a0305101000100c00b0035600c07601c0340960510056070300160180b0000c2d885603030a281c1000050200c072940240c029101c58000e07407988007040d03421101e4405418054001401d6805140c0100005e000340703032848855150321042102045810069544e000c14000807d034050040c540b11540f02000b00c10010b01a2480280080304002040c001c81e044258041420215a502a2090f55561400d00048005001640c90303a0514940c002c1c180321511018200034080140030b0380000d02c01e11003e100300044860356205102c0001e483c0e6602070104410a400f0503044950351450b111500e13600a0b403107080c04000c10034640400c001c1d6509400780016030703050b0314503880c0c00d107080700044d07060450354401031f0703000340000d0300a18088082034200301d0254410050315401500c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 462336465 1250 462335215 462335231
    0x20d120914010c18090207051207050a0203250905060607110f0a0b070c0909080f090a050a06020d110607050a0c0c120b070306060e01120e07030b1f0b04050f1909 71
    0x203480c0c4920b40e810403010783c00294000840301174510a58090f5a0301034094041c038900b045508201e1340001e0f90a4919011b07034040700340103070380801a502d034025004101c641c0500c0c03d2203040030780794015031110500b64107102c20001240d4a50f8201d90400364007084840d14a40b80c000031845991104815a81040b000880481c0d072600d00e402808405104500680c981c0d0f44503800501520103120780208080001d00c072524104240101904900c8001343c4200c04643d52000085d50302d403490762048000d038201012800c2c003640e10000000c4000c201350b000f8495420a0000201903100e400e00750320420800d411401e0030890101c0d411001000051144003190044d03045c100382060f0141d55190209180c40030005a841c040c40020031112416111448020f0b00450310a000d0300c010424070400740204540800040e04103480207003c1c01524868048c1c0c200051410f0401c070003141c000b41c6c1d039082c0510007008141d60381c40301407000e810180c030f501002d180b0f5192485800c02c825040312308020700704066 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 462337715 1250 462336465 462336467
    0x91e1e01080a050c06070c0b0d090602120703050a0b061b03040902220f03080d020c0c030a05010608150c1b0a060f05040605070e0a090c0219050a0b0601020d120914010c 74
    0x10080540240284c9500010b40d0007008030341d01c101c0f440201504d0302600c00700f0070707010108041c0180f204510400701e020222a981c4400300d80c000358071202007a140d007042c061410b605201300c0394002545041040b00684a20004085002e803048144280d0305005010040c030400b402030302c00500c1d0310306044d034955091134801c42342207928444400703099a60360000a400c008079404e00c01126080048540f07800c16235600403000c3e6004034080d10440c4211103070482c05031010000104070b28000e50000445a00300f0403540c4c10f100031803000c4000700f0f6494080c0402a030030b00007242c01c690f5078900e004c440960008006410030040b6540a0a0546007403000c030b03040c07095a04080e21492298001704071071b41d41c100007618100745900717800e034105036030600c10700441c522644130902d4054940101c8400011030a2a4820140d801404070f40381d40018003040c040280240103030f134102009002401c20301c6000b140003800341c0003015003450060345610007030041c0000c80c50303440341c0001d9180007404221840340c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 462338965 1250 462337715 462337723
    0x20d11070b09060c18040204031509060605101d0423010306060f080a030c05070b04030c0e0606090907080c04170105090d1b1b0909150b091e1e0108 65
    0x142500c91000400004842e5880820801c0c40384059840840c280000306802241400c4074508164102d9400c11000c00404c003050101210002a40e0011810301c600c1e2400c0c5058409650045001350720b52003032080056041079408a110f400c1e124010140602c03800040c0141400504000c601d000300c0d0f9800306443c041130b940c141624010750007071240964944055511030b50b00d1007030801036002130749007000103486080307105021401041100d41584d21007403030400f41d82c01684120b40044680780200400303050403819640c484000c80b0058100310035100882c1100740010403501c20070070b0038070020b680002c0090654001d480d980852441c040c09112000d0300038031098a80c81c81501c941054000158071a1101000b03041050604014405071b079900e61034212500105407054850726100400d07008968400c1200740350095681445002885000f4002c82c1c0c81c0307408850003940440100701a10640c203221000308050340c01c140440d5901c00041ca5450541a4461000d90903544000544450001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 462340215 1250 462338965 462338977
    0x60311070b071706010c0b0f071110090b0a0506060306060a050c0307140f060709061b0609080304021e0a030f0f0209010f0f05030a1e1a01030f031e080a020d020d11 72
    0xd5404405413200780c019242d00d45880c10081c103440c036802c0000d0710460315000a5400520b21706140d440030000d886110704110602c0b0880c07082c0c0c1d80d51040303013081c00042c000d441e4015002175000c01c10f07424040c0c0030810030300c001051340c1d006041c0040c03035001051091080301d100056440503641c603800540380c40c0e58200c1b580c001c9000c8c10700c110690b00c20300b00c0c1d01040d1540613800944034045031030315189083d0345e03e103507000c1d45030309004007404501d001c01c01a00807000b015101c2d6610654030319140c410807041000c2071059040140c01c0101150082e1036840c0044c080d00d0300301f80300e11981c19403407904110030603148a000f50040090400000d0030250440b544c010b40d80f04040192440e900c500c1459640e403510403010300409079500d15008444031907444260450f000702c5008184005580c00d145240800303a000b01e66000410f0701d1503003172640c021801c050000074071020001890854100804514014103000040740c0c2c001040110307255658115403481d280c42805000141416954600c150408 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 462341465 1250 462340215 462340247
    0x40b030a09140118261204050d0801140105090d020607050a0201020f0c0904060510050d030519050a0e010e060c0a080306030613030212030604021b03030a060503010213060311070b07 80
    0x2040721105100041c02413004d03502a041d0031502c4131a4984402e0400801e0610a20582103011407402c2c000f5610700041070f41e2500455140c2140c14589090f5207081207103541c0c80108145400148146074001043c00d0300030100b46003d0740c48502d50320002c2c1e1280386410000354020000201c2e181001408210400b02c54002d8007070318107040d4000d80b4992a4280e03a42c0c1950b01c104841c0000300051259032240703400400300000300c0142c03a2200c0118440b11b007501d605601049001c034000e007558143c441c0340340003100c2601c4c019091032a08400a400001c6038400b86050200b4014881000d80340e0702e040c0c1d08502198001c468080d011410f001c12150710a4520900070f00032940059001b04004000c581010f0303043e8000c08803030905141c0500a900060300f00e42d8825001c01c001c41401c4c080410301c2000a00100180d60780f801d204542070b040340e01c80d6100324026401803244052812009a4000449041e406d000c10040034072660748a0324802c468008140300c004805120107140c6c0580b8000700c0c0c00da4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 462342715 1250 462341465 462341483
    0xd05071a190507030c050d051801020c0a1e120518060409060305010501050d020607030804210f1b050c041a30060c070312021b16140f01030c05040b030a09 68
    0x10ba04003101515803651001000c100708004000400407d54000b907485007561000a12241201010500b0385c2d00264203401356501c2200000140701204450219210400c000f500002e4a01e0796807103040d00c58485610148203010a1a941d0103c1112000b902c90500070010342d51643c075400810010100c42c001501c2d290b1914001140a0501200106400781c000703044a080034202c0c1e40c221b42076800103008032904e84040b8640c00c560046500000c000c414503072606084507405142c0100645200d84019030920291112070011a0b000f003164016441e040c1c50100314043d4500754a602100c5800038070f60490307800107180c881c1280f622f50000e00050000147c401c030a20040805035200c100391600038000c0c90400038080002d024800d00c010b100f140b40c42c0941414441c41c40402c120a85151040b503903007008441e4040056012560409001e041d045100d150000001140d020f807003031080b59044c15910211000d809018a003910000d000d41041c690b41d910303103600120081c2840c000110b40301309d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 462343965 1250 462342715 462342721
    0x608151c0303020d110702060405312a091401112413050c010509041806050a05070207060207050d030c0507170c0103060302060d0b2d0a060207080d05071a1905 70
    0x6201c411121069001013230242400d05080c100105280c12514489008103851400c07524003131003507540c005442c00403000003003c3c03850300103400407010984c891541030310b042c003200003000303405c1000b260070788807079410b07840100d46d901005903112100798000c1000e034070542062500610445a481d0a4a48072242e030800a1721031005030841d20032050f40080940c1c00c00c20444160b07500c02c8000d8070064000601c0419909100110341810507030240c01902e82c41d07120401c01009910a00803142c2110312031000f4500b241c50050001d4446c2900e0140e94860100102d0841c00c0c54441c0410011042e08401650b0744031b503460b11690724030308480606480602509054140640c041d205503800c9a1f00540401c2c81e0091421400c002801004103059010200c541d4032550803860260b101c5007508402803406003500581c0030804a000c850b807103001107500566050100240c0800d84040d04016400d10b540c481c0d40e1880c0182a04d26207524884410070b06000300030703400c15a0300420142c04d502800c10001070b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 462345215 1250 462343965 462343991
    0xa0b030c0d0507240504090b01050f07030c020a0e0c09041a040e0706020d2607021501080c0103060e04170304050102160c06030e0601060e010f0c0b0c0903060906010608151c0303020d 80
    0x100403000131000c102c00780820825156280c10221640344145040c502d040000e0300d0155032600020300136800110304c04102011410310713070b61800c041c18942c4144100c1d0310300040070345164032600f05814011900d4030409040720404000303100080d00020800c0c400c6c01175846801c0c1d540c030118410940144541103042c03400a000b45910720552100e0481f140410843c060380074400e001c00b6007010110301c2606004090307041461a08c030302800000b0041c02070100c0d803100050a4454507002040180c85c0c407402e200019691f40701556464803030a005c6a22580c0340c2c10464024001c802810444040307070742c2003034100304c000c40d8294155070680c2c604200030318204403000d035074440c24010040805e0a41100030800d42c0689403031001009207240c000d004494555603580c0c40709041d14840550040480d07074140902d001c0c4003d1360700502c81350050440350304d40500202065805401c3c4484402d44004445c5551581d0304002c00c2224000c090200000103890300400a42c4058160046140761145001d145 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 462346465 1250 462345215 462345269
    0x6090203061807021507180303080105040e070b030a0903050d1404021e0f15130902070302010b1509010e06160506160c1a07050c0706030b010f03060e0a0b030c0d0507 73
    0x70f2401c80c0c0c001d001c85030301600d4081c401040506074005005542c6c600102e0056400e0103038000d14843c4da2290540e503d48400d01c4141da000481c0402c4681181e401030151100c030a0960364865003282010813092243d04050390320b032140c001513814990400c0140a04071811861680c000c1d48291004040030414040d904012108200441e40c01800c03584a0030b424039004080d0400341c860003480c249044081d8160107900340301c0c0d62024803080d80101c0c00d5410300d5020b1142c0201254150341c001c410024588081800784510407a150500503d001d03201388a89401c03080e030395001c02c4028203403810512402c0180e690001111521054a1200c5030402c12a100304841a003080e4001d445240d00755040180040300140140708004101d41803084201c01701d010460300740244016140029070700d600f80001001d040c040107a8005150070280200529240c20194942c010207039000043c54004030350000342402410300107107030b1042450003450203004021031060211640d841c03100c0000c5201c41c4c0d0710f00003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 462347715 1250 462346465 462346471
    0x19033e1c0309050c15090409110307061718120315210c0f0d0b19062301050c1002040b12011d040f0c0b030a0912020a02031f0b04060902030618 63
    0x1043c0c0040d0580055818481c2814070395004428080d8101031401d0302050444400400550702020b5004000c001800c00340900b9000d4082407403c03c544050141c0720348131205014011041e200401e0ec0007110260092000311a08440e0070080ba50368142181c00840c106600c2c02c60303a2240d188000704514000c0e4141d01d29040e03440490140c01482e0200c010009194082c0d045075401c45041c5452030300040c0c1c401c0c41c0074440c4c00000711025030500b40041c070340c1c2141d801c0d42100c14941c170014891000d606c08100107808440091814a81c0c40098021260411810141d041c624a001040108170540400054048482c0d100c101c01c0203a039a441d100c1c0349204a00041c02250300400b030101c1d010410b050795205000b8001d0480740c0d14695180c20084490340102d504914150390789040d60100f14211421700ca040781c00b4402000c2c1c440c1e807500029101e42c8069206c81c40529079004015490509410940d46180010010401e40d070781c9480100c044c0d401101c409204038a07d8161280e2003400820140c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 462348965 1250 462347715 462347723
    0xf070c02090c3a0b0a0305030c28030206011a0706060b04061119080306061615061d0105090702010e01050103080a02060907030b0a110f16020319033e1c0309 69
    0xa0310003940a00d01d0041c22822130840c0c00a600b4030000c00400d00c200010412685884010100849080c00080d14403500b800504041520340727403610082640000d015065a0054101800e0741c1c1c19605040907038820340cfd00c010812820003200152040506014000712051504c80184004025034090b4030f8074002040071242010300350180c0007203540300e00a1039200001a200c14900700f12a07500c0c03e00400442d4085400301d2401c0581002c50819001c0c000c014050300c0c40182d00318449094802022205000d840d000c1c2485000141c0441d00c02d420060450481d00003c0040c3d5031607086c41c940f82e600504440025101d64004207a65540009100c01141c1d08500c600581c0d844490f0248060a104002000301d60720611000602c0c501550040030b85060001d17442a681c81c0c1c51042c076042584964607a100c80100c03481ca1400b0a41189104210a00c1100c940e0003060380002540d100c0e484060f4911070003403c481c2c03034140a200000d04a8030b40c4880c00300c00784901d001c285c0c080b81950b4400c01d0040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 462350215 1250 462348965 462349057
    0x8070203040b0f0927040c1406120c2709011d15060405040501120c170330011d090105011d060f060c0115080c0303030f070c02090c 58
    0x21081400704400b40c215140010140c40b4068404107103040808421034039807031710031250018841049001c0440078010a440c5043c40c6070b407001c20000459500a00c0c9990600003400ca0000769817101000440e46203405c8862800c00c9580b41c201200c030300c2d042008505014103d0980003058404198580e840d080c06055080900c82d030702c0e20b80c2041c510000d07400d002d0304003406200104590781d0f2405110f000c0e00040030395003030340c000d2410320150b00e0303006611003030300d02e94000904c05405d60044121000301d0f14000c010390321032006410703161803c1c6902c0c1d199100d81d480000041014002a24407220406195140c228280c88011049080315000e114030050706901604002100c1403170303429258440c0f4014102c0400c0300e10030012885a5200303418400301c1c0c1c5d55903072440e80c02485640701030b8017400d4524010800351381030501003640c3c0d00c0080c010b01910a4080002a0402e03ca4807007007947c01d5015281c2c6d405400c1190598010341c20603284401035174201c4e030200d5501c1c09044072403000040c41003070750 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 462351465 1250 462350215 462350227
    0x30e0d0c0b1f1a0c120901020c040b0907180e0a2f040510030e01050a022502090402090907031e0606170d0305090109060608030a090b0c030910030b0d060504020108070203040b 77
    0x1d868460f80309040014840042c401304071142d03030900c480c1002c0e00341090601d94800d502c500080c102080d54101610641c0b400e6a032108649503100c00740d03484001c030b040403801c40a925000b1449017210703502c040b0b00364480b9800c000c410492500041c488007040300c100c0c0071106090b00f6000d04000d01d0b00c0d4003117100ba8284130411880c0703441c8a801c4407480b00d03400c0014020a06c90f030101d00351501141d28120701d5400003000181c401192001c50076080300c005a25010121641c0020071f42c040103040a03104d0290a0040760b0654428840c6200440d40110342c0607507407115201c44035652a6240c41510202c1c41c0002c002407540003d0291150400c40401030302c2000c601801c250000c0c07034042d04808a41d91b80702034400008240340708800c09014140c0007581c0751800840c0041c21031601da0850138103a035041c000d0034040c00e00002134a01242e0100c0d2003003402519420308800400300180d14980c85403100c03003144180101903004a020701d000307903900c1045988074001640d0b41d100301d1192100c416020011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 462352715 1250 462351465 462351479
    0x9050322080312070302040806090c0108010605040819050f160801050609060d02101b0b0108010c020d05040920160228170c030a0c060813020604030b07030e0d0c0b1f 73
    0x841c580c00013060600604042d2144211440e0500132140303041e03103901c02440c8640c250b0f000040c0074010645860301910b42418042925258040302050021645403a420320041120600c0b8600e43d5149070421204000d50302007600410000fa40700312402035113040c01194107410220b176414403e8402411103443c04013140d0030311803145441d040610820982014254030102454914080c160099a0355812541032940840c00c40b00c0c06400c40d4159445801c00d03000181d0040c0503202200c4640d000091007402408124003508015050329402d0540041c051009158048202c12141d00070341c0c02c9950b0040025a5480307620129010171071800052208200c140408200e05000500c603105542c8041d580b000480d2501d030041004492130706d9a0780c0e05108640d400124076a00c80c950540740c0c0300b50843c980200340c26101343d02014260070348600000e42000d0107038020011100c4080115080304009080003400071000c41804c03200580640007140c6402003885058482290107004038042a2030051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 462353965 1250 462352715 462352747
    0x12051b0c090f060f0a150e0a0602060c13320415051c120206180c0d03050a030b1f090b030402090109090f05071e08010e0c10030f090503220803 63
    0x405a8044c13010070441515880d100c090300e00500780c3d62416100008042c2d130181210021208080c0510310360813040000c503a0005000d41c00841602c10785d0760303071036401e01032a020380e803103400c41514040c1d9074182d40d04c0e4406200101c0c88440189601c0e0002414103420082a140c00111111001048180500c203a181080c034425900242088030040c4002d603070707681c074060202251143e002d82c21081c2008102e007418172000040d0a1048054841e9030f900750001012079441c8100541007200c04600340c05c0e041d019034014440c64900a000320181c0c03501c04c0c40c002510342c14140850000d55142c0e400507440b580001543c0c0103a03401480c2c0c0c0280d0f0300300800c5400510307645d0000e4a03258840304203c8d021410034000c2c20040c05480c0314290310a0400b04004034540c0040c0e1050340d40b03130300d40340c11548041c0700031405030146441110101052488800d08a0240401c900d0421910b880c180c2c903a410004000010303c0e24030485412085003180b541811104525a88200304054008001c41d01a0226190b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 462355215 1250 462353965 462353971
    0x7030213140720100207050c01081e04141005151c020f06130f080c0d0302060721060b1c09050601061b15290a18020712051b0c090f 58
    0x80c20465001061141c554030300a084c005481c00680d0024150040c00b80500c0000d0f01180e00f800d00c182941044c3c11104c1d031300c0080740c1001d0b42e4603429002280070092038002059a10203078508441c0b0340488017400d4401003000380c80c140c0309040901e00070f4515043c2000c141e070044c2c10040030f09591302090340a215a01404000191b4061410001000c1c01a83c2412403009400317040e500c44480390402c002d0380c0c603194243c00381911403030360f091207080069800281a5070100180c9413480800084c441800316014580408652160070103c0c081010000364025000f04020064044d081814146810f0202c03121100c003e007444e0000c0e8014007410340200d00c0d251a5005045c0540c401ca40c494546590390700d2213288004000d070b1111003404600c2d407030396a04e83c4038200e0301404a5540140c040065059055845007814441c65165248804092581902c0a180c2c001800540d42c07003c8903001020341d4040c080c21f40f08540d0108038181944c40c0050800c0400070040c010381410b46134210070f84d940328401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 462356465 1250 462355215 462355247
    0xb130515030109080c0c03150a020d09050d03020c01050c0301050a170f240f0c04050111030c070905090d03021e0f09040e070603061d0105010f120608070302131407 72
    0x1003003084030652000d01c10a000203004002c0f05443e0660f8204480c20401c14030f01d203602c40d5200070081d40c01101031391840343e04284401d00050ba5140204860800350007200030180081c0581d650010031150180c00900040c000040208050f684244020041c0d00084c0100ca4000c140141c7c1401070780c206031404207441d0f0700302c07044400090480c83d44e64900b40d9070319864070321450322445a00000c000c510030705802021040108210b031405901965140c0a83d00c5040c0c104000d9111803503d0f0b0500707004a900644c403500990f90140c0d20303440c7c00806024207841c5228244111400049010311902c262603112a0070b180d400c03500c5055070424052a082400440d2105008120002031307640c503803044080c1480c5410103804110324100380602154019841001000d42c411205a0514040065030341503840900f04401456507443c811900f030404c0708209074000d4603140022801030000998074045034400c0b180344541c520340c0701c504400c1d10200d040303415854109034041804da5005c0c4004040700051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 462357715 1250 462356465 462356491
    0x150f0402060a0219081c0e0a080d090b010305011a060c03040510090509040303060f1203020709020d0e030f0403050c01050406020d0f12023403080a2003010b0c0c01030b1305 76
    0x480d40420902c0000c40c0032140b2210004c6c0c0e842c0c0608400e125000e00d544d208504100011150645948544807004020084240046c4903d02820075030300c0945003a400070010381c159070b160314115000b041c000903540030000e210902c200240c076004086403045842507002d5804c0c0751a0000380580c158407202d02100303100e5507050100300c645807030714018801c2e0300030b990114180380b0b420030004269400d0742003c80102c2c00c1c9403407000032940000d0aa02107903202000141c8c0c074500b00701c1e01d9000301841da03a401802d010014800209204100250003541c2c0154161440e000100e0b0041d2180d100314420700c40944c200d9070602074078030b000d518000310038113031424003d640200c40c1e655001240c1c00301020400400500d200c060b03400803101e01807480107518018003142003a4030340300030304001d0000b00303900091511417840c41500d070204880010040c1c10920306940b25616003940b01c40580181031802d10901c11246550155882405580d02000c8054410009090349029150151000038030710001c0300c0c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 462358965 1250 462357715 462357733
    0x4060f0203090604030e032103090f0a050307060c0c0b15030a05010501091d0303010b0f070501060e04060903180506031503030712090611281b17150f0402060a02 71
    0x440c00203520031065107020381940d1405203009010040340008180c000e41c40140782e4480d000c0c2440c5020300c6004500c10b82a103a94490210714540088405c4009142c045c80001d03000300a00080a02035a500c0385c0018000381d03204142c200c800788080b81e409000c0604100104514000004106900e05c8014040c0c80d000c0c000794541c942942d01c20391000c4900ca03a903505035001000d003143c000c4420050780c0c003c0d625551601c030034130030503000b03030203500340c1c4184002282c104004095110200a20584018040d01e1a150038210020946114240d01040700d000400340c0741095007000e00c06440000b000c0605584840042d1800038202e030000903007502c4100165800f007000c0720400144452140e230f82146050401d1401400ca0644c41580c08140d400241c192040c5040791000c250040082c1c1c0341e4001856280c06d0400040390070050240c51104003e501142c3c03501c0c01e0130180a07111000c001c40c1c482e40303c011036610712400300700c9030990000e0b00e003000b1800600c1c008009040b42c42e8184100c0c1c01e200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 462360215 1250 462358965 462358991
    0xf1407020f04051f09050c03010324050a0507080114130c1209050106080f0f0703080f070b10061b230a0b0c090306060a051807090f0b090f0d15050406 66
    0x1540a9030086a01204001604030008003d1303038190160000000610640c1400f4500680380c0c001800300610408040011001092042d0b07015030301c1c50001c0c0c1090140741401c0c1e20b00001400301b0743d050ba0024010360000700340c400903403020303540004000e8400d9402e2800000311100402481032084100031b07401c03540500c59a0103009240049010307000006580d450605800d1809410480f04e1070943c01c940c8080002681c0810740c0001c40c1d421039856640d400030390000070300b24818000000d140721006803e00c81340005030564581607550540714032250551031001e034214847c8508005080f0314078030454001c811142518031b99402050f00031500c241c03000d036a4858181c4003c6804980202007c12a4034080c03608000c5107802460507503950b03100c54100000300ea40d421041c07814003010502400800e09140c4140e010f18010a00007105401c2d03e070302c84030150a00e5008075510b40c4030340c02daa008020305e032800c0142031110f654806840f41d010804144040090400200107807807030359403500200564 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 462361465 1250 462360215 462360221
    0x105270d031e03050105090106030504050a0209010305160f0b0a0e03150c18040c1215031209061701152a030909185601060f1407020f04 60
    0x801d1290b166550703210b556500659080814607011810542420010059074071105003690643d01c1c0da2901007010303620340c202075152194400c0d009400030307003010000091100118110341d14401a04000070038075540c1a4100713488555028500d40c8640406c200c0b405d01f03006140c10311440c4000b0b000c3c0c42034004407030420203285004071a00101030100203040c07130f40c04460740d00000c641c0c0f0048074200480511804010900000b0005403514541c0c1c92480740140c4e508070080d0745c001c0d50320842543c00b0349680103000b09601014400c610120301c0803151011013000e2050f525042e6071030520001c0800159240c1107075031402c0c041a0080c110807000d001d000c0c64040c404407041550082c1c80d0804030a10b40b400b420b0482c1c0350081da0403a05034415000e0400621980c0202c401390031151000c0e5400c20b01d9481109002501d5140d00e54184021603503a0070142143c0b003039900103c484544030300181e0b607a0000351165145480500001881d41c14520820003900000c0c040d01400641324804c14062140400c00f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 462362715 1250 462361465 462361489
    0x5090d05190305120c0703020703021003090b010602011d07050f10090b120105010e04230c040f09090318060f0c0c05042a0c031d03030c0303070810050a05010527 71
    0x1840028100e000c072250014845c1c003e0708120026103803028544009469044c9800300901c10390728480680c2a1921903009450500e1f0000300301d450130350b07403558003a008280e41e02c50070301480850068002480d030042085021208041c02c03903c03004002a0800040c000201a460103006262801080e81c10b00000601000709000220580550500740050071110322092800d202e682050440c0442e28204100b0120522800c8003000c1d0344d407a625002e100328050707600201c180c000340690000344c0c42804e800204400d070003a10303003640d8819006a03d004161141c01110003203141c00b520221071922903d40541214002c0c42c401502c02d03150800602641c0d05012244408485440c0c8204016002113200702e0382d0071141440035a21509990181c20b101100111039200300b0402c6054030640c600740b040fa42c04101c40d005507030340ca1030320060140a040041e40ca1011003402c01c2404910350900344098410348405031981401d10054480ca152810307040d00d050710105088400c49d403242c0d2510081189 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 462363965 1250 462362715 462362717
    0xb0f0a170a060e0a0614210f06010f1e03031202120903070201080106030e120c21040305100c050f132103110c150a09030c0e0103021008060105090d051903 68
    0x7903640c5020840311400c0f80c0a0040e030300e114603103003041184502098586d00920404e864007100140200d800d00d141030208140c81c2510b000b107403698104170030045a014141d4218980d80c5401c1c03070302d406820744510031542010704800945482800820f010b44901e070b03964910000301602d0425524036040001c0010f441f0100598400300d400c0341150780003580c07240034000c145010486030b806041d03001d50b60f8a0ba042a8824620000341c502c900310b10500041500e12140c82511404100c0c15420f2400c5500900c000e89143c040c0c80f6400c022011540204581c000d0340b50b854500300060164010b055900c4902d44240c0000161000110700c0c08140104418080100810740305103403230f00b0f0240c4116403001280320560818070810119540700d803240240355080c00c00242c0c480d003070031000792220304640e04094a03106a01c840001c00000d0152828180c1f0b1003540c0250b080102c4c10000c3d00c3c05070003600d049000c100107002a5015052445031000740700c1c040d0049a0b00e020b8100b0b0786908040003214150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 462365215 1250 462363965 462363971
    0xf0a030504051504020901051003060305030307020a0c1a030f0a2a12050402090c0c1207150b040c090b0f041205010624090603020d020c030a0806190b0f0a170a 70
    0x4402c0c0801032049810501c4501141e150a14042c3c0c0001c80329041406041d11800400020f602440d200c0e81c400c2e4003071603118086176900d060144002c0c0d0348101d908001c5500304c45500020450388000502401c084036141c040c81e096480b09a0f15204095000300824100d0ba40e802d0941c0d420106032580001741d2642a12041000580601c01451508081815618a803d01c0240401622200d10065000c1c0c191102161100070303101e10103041c110302c171118031010302020400307805210b4022400311140380c40000801800c14110180070a641852080e50003013100614100082030300d46005200c085401c01030b2901d065150641d000300c030014108140d403180c2d0f6075141440b91603075041400c425050302c80c01d0054444c54405000b0101102400b0700303010035401040000504030107405503082ca200340d0041c0d90b254004000014503020045400c40e2184059100d28811018044450000c3d6144044400d03c1c08034002c60340c00088c1d1050701c881e4100890404182d02081c48400014028074080e2404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 462366465 1250 462365215 462365221
    0x822051b100206160c2f04020a121d06010b04050a24030c0302090a092403120f0c17130501050c120f0d180521122502010f0f1a150f0a0305 61
    0x101b0f804c40150702e031881c0240c1c410464065131f10381240c41c61060380d40484000c40c40d007007010b0085d900e501e06040c010309240320340030011803a5140c290280c026a41c00391605d1b20507a560b0b5200d16145050f0005548a882518a080b50101d01c00c0e0004c80c281f2156080140c6003180083c089444a8819400b000c1240e81d40d180000728201c00510103001b01c410801c24016075070440d1034070341d10390451101d0348017801701514501c5080c6014030450081d141d00084000c2c1c1c0e0fa0207000011030554400c00000420321006e00010541d503010700143c030075800500340200031101c1c03803039034005c1c07a90304c10704101d4180c240034004901007185500446680c51400c1c610340d40d2840484ca17042c0d1078400014803c10020280b85442140406000c050f18412408030003103900c5615400340010040031181c510300310200c403075800d4181880d0150040b0050300c981903010408040e04180460072a0070807030105040c00d00000c046d5006250040d003101c047e007501d02c005031402281480c00e9120b94000050b94002c25121410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 462367715 1250 462366465 462366533
    0xc2f0a05060a020c061c090632011206060803040f080d0c0b0a0b0d0209180c03030310090b060c071e0b0c07060822051b100206160c 58
    0x50801404103944060400a00307010103510348649808070b41c01154041221007104a1589201c400702c0d07a500b50400000089003840000703400e440c101c220001c0c500760480c6583c004a1414541c0341100500340301002e90a160348200a40700c000000e80300360351203490100744140c00f400100001c0070f0348031400030f030185040180ba0030408201050b0060028203419100802c0c0e082001d99401800000e0008a100c2c680307001490f030b0b070190040a5000f8010380100030700989208003100c0310b00c4503c000c031a0310030046800c0560368803080b03440ca4542c147c04035041205072442c0e08401188680244100c1c10418161043ca02c0d1103400e90080e01807031700d107481500b80ea891501803000604a940741507072511407002c80595840722144290b400300914400003d05000b030320000300d4a51000d04001440c401c40c50f050242d92038100301000807582602d80c9111600e490404100a04000f42d81c02406c01d40e500c1800c1d00d102c0c00c21000150061000c00c000440015118201c11000000070a00440040e407a00207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 462368965 1250 462367715 462367729
    0x10306180209013302030d020a03140a090c090b01020a151b0503160509061608090406030503030108010f05040c170a0204020a080702070b041a03040f05060103080c0f0d09060c2f 78
    0x440c4da1400d510750300b592952194044211505074014101c00b603034035041004d08070000c0c910800c547c48040c0c5141d082c080c00444980010400e207001d4030058800c507840e0012141101c080d0005a800750f0301108081c000520405d400f4002001d001500141030079081c6002c0c001c88940001000000380000100001034076806440e050303001061401314105983c01000c210144104c2e948405180c100344c1c540d80030800c844d0b045518241c009082404041e5480c030382980c2e69082070156004950822800e022210400c3c8240c0344074076004160318001e103107462541c1150f42c020401c078250501400c0540707005a01e550008221030407141c0c1d12841540380c404402030800f0702c190803410002008220030004001d0750046503120500c1e06039030036600d0f03ca51904d02280d084041c00140a4043c41000106010501d000f4000c00034880081c3d5461290080c28940c68924408485010483c03049060241511640c144000c003441a00600007500304610401030711050703482ea0900002c3d45542884c03d60404107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 462370215 1250 462368965 462369029
    0x60106020a120e0a0605031b130819030507020d0c05060f040509060d051e160303031413020a230d0606150203120601050f0409050403051e07020901030618020901 71
    0xc0f900d00414441c0c400050780c0130b0b420713100314010810301002045492500c0d8560300d2500d000b0a025943c0d0703c0780540d50b40a0764885210302c01d2a401403c041c900748001c031445107495150301d40d407001d20340461682008070003801aa42914a025114404212521a5802002c48074100d914251326280340c5010004440c0008007414019000303102c4070030001e600000c0483e1001e07070001e13125004105a0915901d0311100300002516010070394800418141c15a0189020181d8880003020594480c10012072026018500940040020804000c031050303803038040032120610f00303071310035031480d15030004090012440041c0d400c15039913034080106403a4010107148035031050014604112500c0120040000b00a01040c1804000100403d40e4042d0000700e0380680001c840420540c203003820000c1841c0c11656160451100b01c0d82c0b16005c10340d640064500c07541e8000c3c442c28890b821035640c030b000b9101411801101982000c003080044c0d581c441101c0c041e100c0e0384003600049101e5220b111500d4403032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 462371465 1250 462370215 462370217
    0x40b130504180b061e06030103080a0305160f030504030c0212010b1201140103020409020d02060d050114011416080d0908120708010305070312021e010b0a05090c04060311040305060106020a12 84
    0x701c0c140009484031018503130090b02103400480c85100c40441040750804030560541c0140004008800c205174240608004005540c04010541e19030022803101c5d9192101100800d68884001d00f80c40d01c2a000303554818402d1800c0324102216502241a4820361050224141d44890300050075041600d030407600c44550308001d01901c00c0c00a01e20317600510601006e0b00880d1a14950341c15500c960301c0d00044103034080c000d0740c1d581c0281500440204400c2c002c040c110382c14112080b800f17601c00c501c450140d01d03032a4111403400f4450309004541107507040007212006010310030048030245500c0b4075043c40380201013041c0c2c0d52042c00400e00c1c110000a00c200c06100e41c580c01800454000a04034060f20781c400c21060115000c0300040e4600072011400c0e10030b60700304900783c0c4600041034009401c0344109450700d12886403a01c04000e041101260a100c5242c03044c88200720141c0f00780c1240d180d03105240c202c6458586c80b504c805042000c260032540c050b038414407400c0d041020b51540410040300b6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 462372715 1250 462371465 462371501
    0x2040507140f07060204031a04060c090308031909060e030903060604061a310e06040e03180d0501050f01050118061b031e1107060206090703080f040b130504 69
    0x400300c072a55540c0182502c40540300000704007007080140541c102c030003460304011815801802e83c2d40b6407441c2070301201c089640078103001d00c80000b14018480c0005032179129072030505541c1d48030941220391541986c0041c04a0316144a400401c680d4800d0303405039001c05010710780c0c0e178021000381403410001904203401140390403000c00c01c06265180e64030000c5108610715945903c010380c901c60080e00d03048001d42c070307800c1302c000140c0141e07103070302d4940448400e000c050505980340e000304011a052800380c4941900f0030003d8895030503007440031240c8104000c081880350074045c1c40d500d0031110100e800515110480005010641c0c02c40100b403108090700f18020005818071200400e014042c1c000140280185070180b0101809400201c0c1340d50b110003440103104107605802445a101545201200d015080c400b20300c551012407124030030b010707200082009520356914403600354448050104128428130021580061160051180b1400350310718403030040c2880b08000440c0c0502c481010401f203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 462373965 1250 462372715 462372737
    0x1d010630030f02150a0504020f04020304050c010e0a35030406020d0f03111305120d0e0f04021c020c0c0901030b0417131212020d0915171302040507 65
    0x901520300121141d040ca4050001e004194081e460107103560b0103403000d00c88900810056801e540d2240d4410781c021121900100780540c1404200d01c4141d80161664104080d566420b500980c0b0790a4a024040c0031007544031381c0d900d070701e4030f521408031601c200074412880c2441400c0708852040b000400c0c1c65014624003031a205000e07550f4030b0802d420310180900c0c1299012094040e03400520307100e6110007260b0707440c01d4a00c0190110101401070600c11546030300c0480a945001402c403502c0d05982d141c3c1c803007041c80007041004d1900c00b00d845592198082112980c103000d900c12008003103901d62009030f268080000f0160400040e441c000b40038500c010010070100d02d40d540703440d401a802c0741e1646030180802032005014894005000115480f94030000381c8940780e01503800480d405200401c03483d1040c64030403600d860f01d80b40300c20001a504030041c440900020a119144000b40c10700318660710300ca4103002082203040f110180d502a251400ba01507040c0390099591141e5140b402504600b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 462375215 1250 462373965 462374039
    0x6050a091a0d060b071703010510080405030c011515020a1109060d0206030108031b0f060402010f0309060606051b010e0706030908090d0c03020319080306131d0106 72
    0x29581d2040020030700140d1400d81c0da920440c001c0316500400203400344045038950300c40c00590b9000c12012200b00551000d01c15001701b0002c1602d040c0c890041406803c02c4126508460131040900b0030380e0103000030405102a10000d210344041c4e8410402d0f00c030665498541c1001d500c41c0c1c0d540c40c91065411040b441e070001032948042c00040002203c41d49039035103404000c100c0135004a1402034100c1400070000c94103450002c080c1c2030b440c003180b820105806240c94800e0b152038688030840c046a10003000300d0010740c000c103124044a003040c07034001340c0c0b00e0098542c10309a622590225010410003c0c0d81e0080c4610b040b40c480306060b0410003808000c0d00515040d9440005100307000407d0b85c0e4000d44000c101d5280300b01d490041001b00040da1013011f500b00260b103a01c5034032040340f01e0710035141c0750030740544001c02181c8801d420800c103074159558182840700d00702074009000b0a242c5d840c0644041600f030020105158001407000054003420f01c01c903040440601410300d11748814660304c4d42d0b140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 462376465 1250 462375215 462375227
    0x2105010f1b02072c091e010518070f050603190504150b0414010e07021212061c0c1406090909010504020f15040b0d1e0b010f0302030408180f04021602040606050a 71
    0x840e041d00c2c981041d502c0d01c5a003400c0c0a5a400690344200d0616001100000c05421560107527944803003c01c00b40b10401042039850846101d4040380d502a820b04120a02d050006103a001070a05805030359501043e070712030122a01207030100c801c0c01c0800324150ba900303514403031101624400d035810400d10030000c070421688001446450300b5001004005203c9500c00d105542c0b1403000c8490141d11b4145441c15868203890840d403c0340a850f4901190304041006d03801c1e002110b0304980403089803810018000700212a8815540d00110104101d00c0c1a440f000d40051051000301c0001400341814410010030804501d040c5200c0c001481041c0800300080c0210340480d0680303d0115503e04101c80c4c84030180818013540d02d004090921182c039046000c1d00032220211091360741c904800c854140c103070101c0c0816134002c2c08900041c002c094640308041502540c428000704080d082c2403c40000806990007441180c3c1103000c41c21001c1c0850601c0c2c05048054a06030400c5418080918001060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 462377715 1250 462376465 462376529
    0x141014090601020309062b02030c0a0807020c12010c030b090705040501030b040608060f09210a03020c0106050a1202040b030c090408032a1809012105010f1b0207 71
    0x4100520360114441e07038001c004450035100050074103607ca607421540072400481c8000248401e0384a000f83c45d03119400741c8202e81c401e041c2c50500038104440c0300402c58030170700000c0c034003015480ba8040c0c2807c40d0341c407444202c4220074180b00205003121160380080a85115440c42409140985c051003401c503041030a07201a01c0b800e10b00040c00c8090100081d0181816030700044181c05030600307014540040c10649881580f065048070015510701e090900002625100d409008009010000704144282c0040208072498000801d60036115000142141c0c2c161303100700440400e0075401c1e01142058008c0d0f4800880407405041c0143c42c1901259420f000200000e000850000008a0342c15a50030032852900140c00341d00c01d901a00110b0500300da010070001c03003032003e803030044506901d480000203060384d440000c286000403040c01c0e81091608031000865045d521400c0000c000c1e034441c45070b2544d144020070701030b240da000610003900342144c50700a003240c040314a100101000c140014010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 462378965 1250 462377715 462377719
    0x30f0614010e13020c031b0f06060d0218090d0905090c0a20030a02100506030105070f050309150903040e1003210903060507021e0708062a0d141014 65
    0x240d050b29040004011155120407142e0461001c1510907894000101600b00801410024040040c00750411f90341d03a840d4070500551940490700144d03ca00305080c074172400903c09080d8480400c140f2221401400c41110442400d0780a100d003040791940c05101000180302c162184441380c145401055074500c9002c1e589000d10901e110401101c81c02001601d00202d25541500d46959020f840252036400180020744258140804200a8230b4180f003041d005d03840c0d86c0c0703401c048154400000d50300c503000205090b440d80640760000a1020b07032450741c0741c8142c5001d0065070f43c5900305803402282075400381040000703061944040c00000c020055148140f58180c6402d1008600401c0072102c110103900010409070804040c086100e80005a000101441580c58440407219100c400d80d5062a4032032007440d0f40c80700001c11104522158542c0540705510944110315400c0080c2400d40e0307021541112003a503491085c6c6c090b4410340000b00f9045440c215040e1186850030340108003118041150078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 462380215 1250 462378965 462378977
    0x9031d010e0310050601091505070b0c0d0e030919260304051012110c030702060d0e030309030a0f020703020a03030806030c0a0f08071205062e15030f061401 69
    0x1440581c011504032409440090844416850400e005000392000381ca1040c045200104042654440004070081d56030b03a6a48241c20040e40d61192210024003074a010040c446c2081190b000807818001c4000c0381c01d000c4000e50351341c111182401415030249003001c000c101c484109100c548182c0c80380310100d8403000c3c0d010851030f1007641858118403c81d0720885d800928040d01e52001c5401c071203001061562070404105060049100542500c01c44030242015002007040400501c0c0c040081c1c91100d102803000141c1c11580003040345154070588034100154800b2070ba6101541c1d22170310030150344419102a01c4a41e00d16804202d1001c82030000409110290380090020307182045010304030710000b407108038903680d950048440c0e480140900400d9020308400440c41110000e9000255070781306000f000d441e654151003441d010041e411f001c001a001820040c0d000c59810030460240078940e94224441203070134801780840d40c040c22140203690900c9400c0100c00d4040c18144404002820701d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 462381465 1250 462380215 462380267
    0x302010f0909050a0603030201150e07120b0301050132060d0c02010b09040615060201110304110a0305010f05070e0d051506010320090f1912110607051b040903 70
    0x1034441d80100e80160710301c0b0b8580b0f401c005032402c15402550489010790000c20a00c0240c10403004001c1d064064641d2411003c1c0228220621890003116440d040d42000107000d80d003040000e0a4407004e0380100c92110031109081180c4161100702c203012400441c86280595102011400c18040d1705003500d156603440c2c01305201c140c002c1d0801694148010009800c5290900d015001013118480e86020300305010f0011a40ca8014030800c03120f0600b0a070280e0460340d9555a52445860010300e064010b00c03062000000281c00f40a02010001c603902c01050314035024100400700324941c60f210340705403002030f40c07000032810100e01200388080d400e0315054140c0d00e010050f0041c00d413280c10109407031050f80300000e20390a0030001e0700314142e08a4640c80744440002c100400c5500c451561000e01d400c1c06400c004090405404585580c451080c5032a140111800135039543c01101007998590000c1210f030185602c002848040582e00311001c1290442c5030302c000300512904081001201e002e141d103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 462382715 1250 462381465 462381467
    0xa0b040602071a0d0510170f07050d02010239060a053901022101080312040c23040c0f0e0108040c090501080709060803250614090f0609010c090302010f 67
    0x84900d01802c02c02d0074405801c0c01d41082d011030700c003442051400c2d03400d00a01f06d0301c4174011605080c00b000c240300404860f42000c0c20030400d9450140200d0562090700940c01c2c0340c200d00f8000b00b004085001103406c480740d210110364222811048180d01c51242000703a0340201b9000000e1b9803400e18001c160304141c580054202d540000300d03407011103070198440c40d81000070405400502c69500c108903075194460b801048600009000c1c02020710350340003407040402d9603004d075a9a0780c1c018014854030207615503401140001c41200c40000540f840351078001500b908180c011a00451894942720100e08607039200100340c1031442e82000d041181e410049810300115030f8010010b056843c10800c42540d5510032503a54004c0c0f4400c50b80144d00701400040c5003140802681e45080d421074a10101401c00c1000440c509844001206c01e01ea6032481c1e0039214bc0011515881411b59034000c15900100340703145481d106008202d42c2c116170400414205071640030309140c0c100da81c2800c00011490f80450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 462383965 1250 462382715 462382717
    0xf030207050a1509061401053106090209040b01080c0d18021905030d0203030609040b0604022a07051e09060612040b040b060414011401050409060e01050a0b040602071a 74
    0x50b09812030410a4001c8220903488020030350300c5803800300045086c980d102c5100342c000b4800c4a07071145000c054100e0151280d042c0040c1c5070076110806014103280060102211410f03040303501c59950105042409007818412841c01d02c0c2d00742802e03240b40c50442c00c50030300c0d441741c40c500c440b41a40700d50300c642001700b0b00e10f0003c480d00e40c0100003030950250507420091082052007440c1c0b0901c200c521040346140088100c90048101034440e8040c0d50b80c0d81c4821036607010260420790010b40c2000034074426100e00c165581a030a9040f40020712048460056141a40d690080b5105804180201e856012144182c0d6842141918a641c01e0750380d400010fa56402903050b602c07a5802d2050412040181e460522481a48030ba0852030300c54851109100464150404010230b000b0314a00511200500242d009500e8205250132854141c842d401101594650f81c0000c0c1c10a010000610403031900e40858030181c03021468244c10b00d490014025035440142c410304410101d000240e11003840800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 462385215 1250 462383965 462383983
    0xf0306030501020f070605070801080303040f030e06030907080706030e070509360d0813030e06040b07050c120c010c0b19020f090111030a14030c25031d010f03020705 73
    0x2500071521103d00d0a46140c281e0302c917010483c1c026140800182c082809480400d0580320007a00441c1955200c2d590b8003d04402400142e0a00030b184004488540c1c07448021403094100401502d08603140009a9203088060b800c400309050030164400304941000420304102e40084540042c1ca40301c00d072001c1c00071812072221a807421281c00d8140c605001642402040c20209400c4580000d40d11404513082c0700c0c2900c0e02c1d0102c02945e1035050101c3d02c40d4010f1858040001d104a2a160f0384444500b5145d00c29142254150020785407040305217480030482c80840c0c0840083c1c071140d02c0302000240000d114a07401402c1040500120702c02d41903501d12440c1c3c1104200c0115551080c102149102d900f02450b03460004503503c2540c90400804420381d400701103203880308520700202145602230707500001e10b941000c030010f11980040d04220b90749007185284c080500d8403c0401814001d0840c802032100040c20940030580b810587d82c482c01c400c2c41c864030703132800503240d03a2107140050500800f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 462386465 1250 462385215 462385223
    0x100b010c061e290103110301030807061e0e070b0708040605030a3207090b311502070b13050105030a0b0a0f091a0609010e0102070306090c0929010f030603 68
    0x5400004003024103141041d1003014a00e07030f00b1001c80303800f004509440105240300031080d001d2004000084040c17014000c4244910302c0480c002c110120911820303050f0080f04020980c42d012102901c510600511014100c4d000401d0b24288682c1ca480780c10f8400c1e485084200900080011a000400e5010080704e456180c000b2000c803070580310800b15024030184200c055880c0c0c20110b01d4450207428110100c5800050403410304084080002d440804501142c00c001c82c41d0354014040203800000030050040040203501801600f00d0007032400380140c20000410100300009040310f500f044865080b200240b804955a54805601c070028060b0243c3c003a0700003a012501140d9191000c414200340c95008000b042030500c0f03180d44030200e20b007000c0000d4000700100400540d95126424400c1c0342d07070701030044032001582d9903280b2040350094074040c7d034060640d5806008550590190340040d00201d030200d440101802094141d6040303800741d06061100002c904400280240c0182c0300035504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 462387715 1250 462386465 462386471
    0x60906070c0803040605030103060605060703020a02010302090d0b010801050417030708040609020d020d05060708060d030806040203040c0f0303050c0c0402030423120a0203130801060b0703030f09080304030203070203100b010c061e 101
    0x45c4030030251198100b80400c4a140d8201040845d9500f030031000c3e1203809030143d00404400300703140c00540c000d40c806a1816045401000000c0c0403509030240070303000b0070390800001120710301030502d541404000710000130f4070303a0200107100805621100c243e4000d03410000000d4603800e641b0004411407965040203402840c29a001000d00c080071520340e100d2402600c901000c0d5a44404100390703582d040c80c0007000b08070761a020419500b0198040e50340316118a0001c9141074568601c00310540320b540c0100c0008000107002e4101140510000300c450000790f80a6045080568452284038062140c0505980d9410b9031a4103c45081104485000004800c9955a20001c0d4000e460b5441032002a4411000b1a0b00150740c03401403140b50100c81400c0401070174541d042c0e40450140181f11140c2d0041b64a440e8641c01107100180214060742c4250020740c2d03244610b2061504018400e4400310300e451803d07800340303c0b59030400c2c5107040aa5004100050b040c402c80d06603030884803880b4403c490149 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 462388965 1250 462387715 462387719
    0x16020312040f0c0b0901090332070f060513060c02010c080a0c17070c0e0a02040f0f06030506090601020d05070201020708060f061201021611030f01050a020d0b040b060906070c080304 80
    0xb0103503455400c00e00560749940010f4540054915a02c40c1c4802030380010591030303040010582003200282e0216500c50301d00001d446079800038a500690f03c40d42a142c0d040314400f008848212207803d8020140c80c2451410f01044500c8070309030000921480e814480d600b0820b404580c8100a0341d05210360142a6036120b100320ba00040c002884020111804204500100140c0f5240400e888550341d0103018242c0160600036004000362000e4050b200d100c2d000e21000c644020301003040c80c0a80720f4003850720b05803851f04400900382e42c00070303100301e008003051000e1024a990100c0c0c40b201c9644581040d656601881c40100e1525450b640280d9042c0034407000d001c61411103a003070501482c011104200c4100b940140a4200d11404500b4900f01003081006000070345c41d50340c28925204010140e840e40d400300c0f0222402e481c01140c020580a41c001481403000d8643d02c00c8810141c001e48080020b2100d0702c012951a11800130660301c544000700c4d242e000c0003090f0a03504050598102aa034440d6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 462390215 1250 462388965 462388973
    0x30c090a200415020604050a030f05040801020c06250f050906090a080102030105040c0503150108100b030f040203010c020c0604030602030a06050d030807021e060604050a06050409050717151602031204 88
    0x2400c035014681c0c40d20000d0040503410f52000a030f5502950b00413014001280c101e41e420340c2d0022190b48014144a820320002600780d030284040c10030780c1c6d5a03c0c0680000c0c13510380040c0c14010030401d490b000c0c1ca0180000740300d00c280e00500c07140e802d030740710b040c40303591081014005a024055007148591000c410780b00401c17001419000b40d03040702c078281c809101207031002c9415649400204c40801c1359000c0200403241640c0b0070307440560080c00e85040004629100c0d000040d9903071046490349641c8200400344001c5040034400d0450102d801d102803c1c0c8000c0b480000342e258845c6200142ca0560044045640d035040f07648580010300c8001c1c5164080c0d900e5181c041c082040491341100540142c0442154040c54040b08102c0182a1030150081d691080100801808081c2030111183d5817214045000c3d160b81c03040c200b105000d10b0007051104c0ca04411080301c1030750303010310030300380d03045010810402c021800b00c90b5041548441e100080d203040c50004c0346107000b5080211440c40c111000c0c40144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 462391465 1250 462390215 462390217
    0x20d0c05120a060b12062706030f0318041112041209080111040e070e03010c020c15040f0614070c060e0315190b040b1f0f0c02030c090a20 61
    0x5126641c1c50300c065036903481c0e0380a0450304203104840000c1802c000350135480700c210108542c000001442c120015030800d0100c00340c1801c82454518020326101030200301d10381084090000b40010004510703107200c01181e45c0c48144201c0c520b074055600c0c3c90004002e45000360036141d00d5400c0c16042d000e02c0c581400c180040d041c008a1a02c0407500700000400d01d040d040c02414408200c00c500310340781502c1d0010900c010400103125404110700d0b20710b10b8000365028050760107020f0302e950040442400400400c1212000c03008c011716a94403c0104000c02c1003d48851000c40d1001d040c01000d02c00703000c0f4501000c5c071405071300808248601201058458101588421402058049401c4400b0507504d8919801055452481c080c1100210442d4030310a038200c074280702c001910104c1d40c1c1d2600e4010520280c02210042d00c0c0da50a040c0c55031900c3e50243e5586d006907180d280200814000b90003003a1030303c43d1800120700a10380c0d1800140e6100194200849019010807007008072a0440c85101e01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 462392715 1250 462391465 462391477
    0x10b0405090309013b0916080f04020607062a05130308091504090c0f0e030c0f040b090c0910170103080a1e020a0b0109060b040b071109040c050f010c05030d0b04020d0c05 75
    0x101b00d80820100c1d05080018000514080e1580c031043d0103034480c45401904a00020004c0b0707030041040140f00c000644500030980628038020391040a191904000b104d1450b2071a088030420a090022200c8c4620718141d40013180d4001c20515642c1100c500807581072121440010200500010000b030382c1c01d104d600a1088449a64800007000c2001e001141c43e042c441d83d031680d01d640051944880c40c41d00981d8243c940c1c4008000160300407580d00481c400700300880e0710100003800407031002b186040502c50414441158034119046403c01503883d50101c0c01800068400040841d00524150140c06808883c20804804481c0c46042e440001d5440348000c0b02181d02506240000480804a0260304191008144600c0c10f04d03040c40411421900405820b85003c01000f0b03024101380c5400140c81c4c084c60191050503070043c00c001c28010140541641281000140140040032540101c01c5c4c0390300c4a540c200204015580400003006070080224030061140f402c0e000d1160035800000400d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 462393965 1250 462392715 462392719
    0xf04050c0a1e1a0307120f0e01021206090702030313050a062a0306150e150301030b16090501080411030c1002010e071428180509010b0405090309013b 66
    0x25107544518003000c0300c074035400041074003043c10700100f0291405080c0310210301200500004105240e5000d89041c0c81c10b03050400d190b0303580082c0d80619413003c0c1c1001e60b480361003900e840581c0d051410f8000d5503444001d114045105031100a041048810701800c50f4207a0006010301500c0c0b4404807180241d036003a501000c000c2d02c2201081c401c00e000f03000348004c6900d4280d48405080b07113030109940e5508800030955010f9500798246031184201c0300518065400303aa0351103564a882601c468992031850030701c5050242e03410341044540c1c1e020307203881d030300c20f0f84008451496104400442c4c585280c8a02c2d00e0351090001804540c03481d41503104440b2821154116406a552410b01c80140a81303c401540c203c4500090012620910440d0044c4030301005a5a41c03200d81d100e044086140c200e403041329250f5182c00c00c3c01070030503090040140c0c1e001e040b0b030f007007000b0700b0441c02d600d0b03403881401071240c10310510b90411000000300504840c06d40d0205410419500300d10307850300d0320365000100d03c24 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 462395215 1250 462393965 462394019
    0x10611010e070510050c0114040c09051306020d1b030209101b08071b0f1a03070e040c140c0c0a06020703050322081504060b01050705060f04050c0a 65
    0x4a51a014041c181c08010a070300509041400c04041c0603603940c000e28150180102040503841d954000d10540000c1c040c0031844412070b0616280c0181d05100341e40c001c400113420401401081d110407111042460303070140005946000700c3c18a00b001d816401907140148400d6840665102d82580041804480844914411200e5868240c1d507041004000f41c145400d862007000006030300c00000c100b214001c28480b0b44040c000000c0107030342a26500411941500120200440c2c2c4840c5550001c450701300d0341c11400c2d4a00640000c10421040751114421512071028a01c070034084c502113400d645e40f02440c2d41ea035402404400369640320000c282400b0304865800040c9161000c204001903903400406141340124080440001c2900490072041c00e4291641c0001d41030001c106850200d0703078035041210145018100745003141c007074624080c1408410455800014000b00b03d4039841000407810200c10b80340c5080040ca03140c4401c0c0c5040e045250900080340c100c02ca540070076041002407541c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 462396465 1250 462395215 462395237
    0x103060b040317070c030f0302030415080105100c030e0303160b01060c0506070e0324070207080105010f060c060f0203040b19090206040504091403030c0d05010f060504030305210a050106 82
    0x20a0081c4203500c00600b80300b01d96511002c070f45a0300401416010701480406011030b0f140d44030a01c110180c6602200075a1001608014280d00d400007020007249a0820b42c40640c9040c02082288034000001020040a603d21104040c0114000d07246c00001800b00da460b140040c90b92900b000d80300c042915400c10083c0005501c6100c0d2140b480c8203540316001d0025501e480d0b030140c800f003c003001040c0d03040c0540c034440310614000025840e181c0001c1e07000c4920340d08005102070f04003012900000303071a0b4107180060081c906006118402c96025203009117440503241045001400c11540b5249003d000200b03000074070101c51781c058021080000c050f2580603143c0c2522086408822000f0b400c954184020080751415038040d049050068038254451000462440c0c11540211000c505002000c542079202007180c2c481d15015051864803000041d0410300094900e004a10000302007080000341003411031402480840c0800c414080808541040b00340500035200074015180010f03150712035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 462397715 1250 462396465 462396479
    0x8030403170114011e0906210c0314360304092a092108070f0516050a080604110109090c030f111201030201050a2f0c12060a09150911010306 62
    0x490b000c1718115210780f007210b89050429100c41820303c291808204d204110031007940e9190013100c000031425600050811034020342c0c160381d8a005081c801101100a00403203440c58040c0c0e08000c072400c88007807501b16031907d032a018a107102d140c1000181905082003402004840c0d1032038071000c00f40a0120810030541032045598401d544030342a640c01c02c0c58071850402d622425030008481c001c4002074602005900c82c5032101c10018000c5405910011807000d524076400000030241c0801c4400340041762414100c96901c02c03001d0000f600c22201c01124101d6a80100d5070710000345009242805509280180600100031600d600f0085c5814920010450002c201c00c0368104201300b11440640d90850300116055001900c0107c1841240125001050101080084500855800c031904e400c5040e41050a0003031148159014074008015940300d5107001c28803650010341e21100003610180c0d8242040e0100c0950301c0a25a41d2400880100303000390500d8011440c40284c0f0309001d061340c1c60350 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 462398965 1250 462397715 462397757
    0x170a050f0d0503041707020907110d0e030c0f0a0e070c0c05011e11120c03030a0e0d02061b0f1903050903192708070e060409030c0803040317011401 65
    0x14000902c0401c0028001541020501015548042d015060043c140d000c03a90900042e2011030204014901020480c0c0c000c02030300b1801c0050307140c0302500301c1403a00829941c00303040549520915400400c0800b684070060000b0042c400f10700c49040c0c60402170b102420110305170a040c0ca10310b4545c2070100705540680f111200010512507000031148200f50110785d0050840340341e40050044c14085840010110040d0500703041d180302841c3c0d42c1c105101d00d1004c46100202c000496013000084000998000c1140d6500071034480c44140303060004c1c00c9044587c811410000080c84010915032902c406001c492600001d80d51410052a00d0303009100e543c90065002c9041c4440c41142c0d0758480910900b01d0324000600c458a07002032654000340d0f13100400c0d03140c02c001e20b150f000507020040403004025841d04003000392020001d280c02514028400c4a4007580901340180c0040480c080610510f106440d503054040641d200703503142c2d0610200441c0f09100d003130000d64030100e2121032002c004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 462400215 1250 462398965 462398983
    0x503071107030b132a14030703031403090c03010c0c060e060402150a210203040201080703021602040b01110105091606090815090307060906050a06140306070810170a050f 75
    0x43c1d0201c542c0e104201a40d96204512003100c042611030104104a00c04841a070780c100440303a22a40e00702d050402c0d00b01c982060005c01031083c3d01080e0100086a0061a052021080300c041c0e03507504d5403801040d51400600d5a030040c1c06620300a08401c1c0c40c1c0d4008070300300c0c1e014810401400f21001411034035603180300684000e9417003290a010300710103d1101004055541c00d5041401e0540c0d000602c01c12500c030300382005862aa00001000110740c6d10403074059201d00303c1c0c01c00711304100b0341c14103c1116041148009020f2030341c415090400b80c0c0610040700e541c000e61802804145804c9a01c2d03a200c0000070160048112681c401051603070192804030700342c413000c030001d0409480d894601030b407480f0050721004840c04100900400300d0601e026110405000324800f2403281061418103040720b1701d6070307c00c80d50308001411205099030301061898011080e894030900301c0c1c5940707401940c010965800301d40b010384c5a03404202c1e83d0001060100d9003e001b802a5803034140c00d40d40c1280c85610b50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 462401465 1250 462400215 462400223
    0xa0c020109030e0f031f0c020f03030405030f03060d0b16080622050714040303020105060a0914041b090c030f0b04051e09150114040e010c0903020d060902030d050307110703 76
    0x522a0b011401d045070107001e0384100070111203890500e1b841b1540d00030300f806808468941c5902c450021a501042100c40d01c02407400107600c2c40ca001d80b01d40c0d441e03014122001c0d11444001022981c02e58596402090362078201d401a00141001c08202d0801048012400d0100d20408000303071062600b10028580049a56103000040001913890341c01490014002c00034400c032250000c450034100c201a00c05180309800010301801d0103020002e400703006501001240c4c2c14841200c40c01034022120316005540885c402c041c020702c1c03c003410340720b944070703000384000500e889400010b103035241e040300703004e00802c0c02c0c00c1100301d1000c404e00080d40c408a5242000816000200444904143c0e0041e0300800380800c2d20222401c6002c51040c0340803c2c0c0c422100d600519000f004249041d10030004144407580003040766484120b40078005145500c8040d00c50740503a400a030034401d468102e2501280d00509440c94141c0c9076801030715075041907810717400040005041030380156002402034203490700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 462402715 1250 462401465 462401477
    0x2040f090b1f020d020c03030f071202010e0d03200c07051201090f0f030216081b030304050414010608180c0402030c0d0618140112030c050f150a0c02010903 69
    0x620140001905600703401d240c00840390640c440301c0302040042101050b507036601411004001d030000a1030100500c9149220750420007114101c40a821f0444103610f03804a69111202452201a801001b0801c0c890945000e29407a0707002e0b05a02da8001c02000956940980c40100b254201e00050f000c0c3c2c00343c416041d488520180900c0c40d184101d00b852009003000403a401129a845200c200307000c09086070201c450340c508004050f0148940c00d611040c10903d064a10303c4c04401c9607980c503d01d20030101c058084a241c49641e2014000c480290002410138000d00030f07056030303402c03240100348154400580403101094000b030a1095143c030b203d01e40c0c80240070481c8180c00f080000d50002d0524840414100204003c281d11409100018600c5481010080060b10742c9c5505959210070044540307284c190060012000c24034100d220103400d440e2080c0d00c9981440d0071464000e544101714071522038140b450b5000c508050340d5610500b5002c000744100741a00718203a00365000101d006001c100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 462403965 1250 462402715 462402719
    0xc090c18030503121315020d110319110c070315060b070b07051303061508010f061d0903070818100c020105031f17010510080712030f09151706030102040f 68
    0x114000e0115040100b9041600d05e5551031740d140c11101d0106440340750150b401141c20500d110b164445c071040080ca40f00c046146185c82494002e120032040d1590b8100b9555841c841760004490040d00c88025540c400c88080b19107070305010400c0461a9006000641080f801061150344041500c44055028907a580261078010003600d80c0e400265103124a9105044004080b07692802540900d00140c2d99030031030f41e07081c206820700b5100300300100309481d0f08241d0200b0a403802c0c2d090101000e00c0913852a0010348807051403904511509030040c0c491400403d403602c0390b4800c21020694800203c0c2e121003043c03841c4505441031070506070041d001c1207082c4005804c2254203140c0026070902c20a8040c001903c900300b500501c2200c03070201200769550000c018a64540200c0c3c000644240d030010024030b454401504030807804480b0050810244022020641d80074200f440c1c00b8240709001c0b041d140c031380c1d4080200460b40301888040e2010707101d00400d00605061003203e0940741c0303201c20406118 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 462405215 1250 462403965 462403987
    0x60d0c030308060409060204060503100b042105032116170f0402130e070f1211100314040b06010f0e0a12050f07090204080607390c090c18030503 64
    0x2c2d90043c80642c009485005074000108503100034000b40800fa155030382c8905007407891035001c848540240b00115000c000c01c2c032103080491002e4140d0410a81c102c43d40c06010b250140c1140100801c0e61741c01902d0354092190383d80e210039054817400c516890700c21043c140704c03812500011902c00a10442c1480e001240890b60140c0c4100c0d44a40060a5000020681d003055012200e90194070031b059017000d00c0a02000d540401d0140040a10f014110354040f683d07212145984030407100315100b10342e00d640f802d079101d0080c0c00c504806004128481100e1a080c205124007140c11550b00f03001072481002c500d001c0d07000c0c1013401840d200103010305002a0030400302c2c58500c2003040c81640c0901c1002c004c01c4000170104080c1e4064060844050303181c1d403418080c1490894090088000d104070320031032450007442070840e001c47c544400000c4c0104030908010716206200c1440244c010040c1c04404217862400390082d131226403141d40c98400e83d0000030501105040c00d4003009102d9042001036100c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 462406465 1250 462405215 462405227
    0xe070e0a0527090c010e06040b0d02070c03080309011407050c0d0809072409050108040503070206090402121501020601050103200d15031406071d04110c0d0314060d0c0303 75
    0xb00d20195040102d0b00c0854142e051481c40031940c3d402c0c42d40c030600d0f02041559200890130080b41054404504107810001078a40d60302501c00d0901c00ea0b0380c0441c40c082440f20208031440110b400a84441c3c0e203050500940380a407018010300c100030b401040c042840144144102d904001d0305c1d5000e0b00c3c1d20032032024100c3d045500a4403c2d5101d00c201203001c0f9140f00b2101030540240c00101c5030310500658200302402c07203000c507408141408000b00030840443c01c0401151021541102c2e00340d510000e43c030015000303001c0c1d200360301d880030804810007810b040058114803020900360211102680d0750401182911415503203807942100b1400d842e020b445064001d064004161180070560710b5090300300c41e2068020303600036079084071030250f40c0360f42c0d40e42800441d4002c00c29203010290705401c16410340c07240d00c0e04000c560007607680d55040ca0000f10400e05035001c20031120181c0d0074402542d0001005006100700c024051040d100118505103064901c207030f685640107250344c49103891a101901c031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 462407715 1250 462406465 462406489
    0xe070b12010311061c09020301021b011e020f040e040f0804081e0f07030b0c041a03011e060e100207030519170a0c120c02030616080901060b09061804150e070e0a05 72
    0x150b40900c48542d281d40800035510840d0709070000040e90045408100002840c2c0c40dc00048662040154640812801040340e054070150300142e0310545962904a980001520f4040c2141e40c0110780850742030004146403820040752013407032115001030383c1d040da22003610008000d4154400a0f007000003401c0d402c129988128220303029424203642e051014859030794240e0407040404000014880c1104403141c0d0228180021003007a110307814844050860703500400c10074405c6000304050182c4074800c1140102442d40a001c1d540019203044401003a0400c0740002c5641c4800d01080380c20030007551080d55001c15070b9a0320880d2014680e20b609001080c501c41c618100160840d5480c05600c04000f450700990784c029000c01c2c1c1d0020101c0c0207264030809407002403c6d90614808004406c449026100b512100b2140355941e422044605450301e43c000341516003090130300f4030700a802c203228408a02154070102c1d41d074400d5603801c20126500c400380801298003072403218041c00141494100341e59 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 462408965 1250 462407715 462407719
    0x606030d1223010602010c270b0304140d02030a03110309070b160b0708060f0108070e04050c16060605090603150c360109170601090e070b12010311061c0902 69
    0x8002da101c00b0142c55410b400d0300040c003d40e440e9098060307415800303220180f50385a0302c80e141d1250b48400f90320b09480070070340c49100c030522404000b01c2c00344180345c07521810540800742100e44103905490042d45076001400e40c00c020034a401c03a0b0b40c08002c085801c0301d12030b04241000d001c155040c00c203100440c0e040349400d540002caa5070382c40e40001d0921981107020f078420b610f0b41c400030b25282041114048031002403604002c1c643c400d10070442d400070281c0703003007440880c0c002c1041d981d0424410128001c91401c4001202d03407546600902c6825408103007640c205589805080e078410090568405101c001c581904030190000341042103800060300800c0c900344110406108203043e6240d84040d00d1100054465903015071040c65a04010880300034100e49000c500058030502156441d001c3c14441e101e44a44c58200c000c00d500418004d5402a004400707080761580c1031420806140002400115694440074202c41d0041c60144180c451506c0004601515086910b1801c005803414400491f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 462410071 1106 462408965 462409001
    0xf0f120308060f210d0908060a0903031503150f051303050313020a0f0801060503030910030b01020c1e01031404020d03180e0a06080606030d12 63
    0x624240c141c01e05521a680e41000705090702118907030a80d002c10900307460202c1030518285200c0c480e0911041300c88019243d50280d070703400030a00030902c055000740002907001c500c2d0f070403050404d84a40ba0105021f01100c03080001c0c00c2c100e801c100e40040c1c2400325903021020500c00c1d1452440c0100c4184183d040001c4800e41004c4102c1014040050000008022128681080d081c259001e002c000b00140d6854a408403103000303000b80722055080c80c4002942d40ba0000c03d640d84030800400c1005900c0f009101034005004c8286441c1c15802404c40040c59541c41c50070140c03040c07100461282d11a18500001011101a10001054110700105000160b00d8810210601c103500d4100745200b0305500040c56548401c0d40e20101d59291035000700241c000705234005008031000e07442125202d0315400205910750043d2030b403040000310f010100040c01201a000314400540b051051 = true := by decide +kernel

theorem cover : BRFrame.Cov 462230215 462410071 := by
  have h0 := BRFrame.cov_init 462230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 462230215 ≤ n) (h2 : n < 462410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
