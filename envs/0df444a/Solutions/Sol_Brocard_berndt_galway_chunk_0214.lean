-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0214
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:30:17.444989+00:00
-- url     : https://prove2.me/submissions/2bd3b3b1-176c-414d-a69b-b1324b95fca8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 38309357 ≤ n < 38489213 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 38310607 1250 38309357 38309363
    0x12060103240204170d030f02160609031e0e031e06060405060402090409150501090209060d0c020102041229010f0303050903240f010501080f0c09120706050c1006060e010c 75
    0x10310b81a42c60060004007400e040c0d01c01180c0d04170303004d60589980c262049045900c0c1804007940362000784d030080755a0717904c5000002c1c0500e50710b03500401032510584980b003109810784995510b8404030300003c0c1252641c0e1024920034411110118284800e07000005500f460380c90051016480710010000038200080280b03400a030709004240e05c50ba55030180c0c2e82c8843c010041364559000d9040344c68141d0341c051b0418080980108030581007612600d0484240b9022032500082060100c0002c0740a4840c80e0701c11041d1b0002003091109002480c50381804805070101000d1403440d41b0b081c00d070160f00e0244034030b1401d07001504040001ca4080c1d0001c04280900406861010322400783c6040c01311000117004c280d01c07400c4401c2141d24080300f1031481c00740c2030900f00300d590351403c031441d034000d1000140420502c00000c40c05c100981c0b2142c20000d140d0a5080585d800d403500c81c8070091250b00322a800d04441d1082000710140c550951060b0f80c01e9400c20741c4c0300ba0190b00c0d442c0042da8100c540100403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 38311857 1250 38310607 38310611
    0x3050d09020f0402031503010609110702130906050a0b010f1701060c02030a050f07030302101e0f0e0a0311100605030a0308040305040e070504050f01020303060a030b191104051206010324 82
    0x2682c243e40c1c0c2d84025071103000360320300018080084400381821175040780c1141d41c0031440c081d41e00e201c02294405851180e0ba04a80c21f02d0005d00c0c0c102148064003c0720700003810141018103014040702250416048074100f030b80e6070070100d0004842141d407254903440e08141002448018480180301744040e610990014048940d2a40e543e541c40740352181b460400d180b19040f9030024000c040d030620000c2e40c880c00c0c14070240091820381551600d00c0048a400e080700c00e6071030640c900f444000b03030450401304000c9400e072303441b0101034107000d00b028900410041301802900002c00c0c03107110f144107803015103001800504c0c103041c036660160381c07100016105074207005060000182074040c40a0365842000c80b640c5241d1550718040901c071540845803505d5040d0b420274003c0101640b80ca80044046940007a180110780d180c841c03203940e581c00d815144100701c600740381200c1a198428001042100c20030360b0380c644255055151161505000e0000031308480f1100d44019074800e140c1401b6480e00702e04100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 38313107 1250 38311857 38311879
    0x150e0f030c01050115080c04050d030e03030d0903030e010e0303060f0f0a06180603060b16110a0b090a14010507080a020118150b060c03070f11040509030d0501060c03050d0902 77
    0x4640c51908041c452601c240e449600621a070580e403c0c001c414600f40e41400c2195040c000340e40c000c18001d038020b103401045c0343c2d28200140b6110300d070b0701a0300100144c152076551603503680c00400380c0031102090b40800e080c0900b030340403400f05214209600588502540c11034403940c08011303807526541191640301205d88680507096440800000091045483d001c8a5416a10b041d099a5800d9400082454505482000324040100c11281c601e50328500c000f128200c80e1074224450b0300c506030f0040e013000d0810404984506030500400714100704840a101d01c654615102e1400813034282c60340e0018009200180c0024440380152082ca03800c4e000100c3c1703a0018584107821145c900c1401e4545110345100401000c0031841010240c1805036041072038030000d000b00c036980f441501c40040c20b01c4503111084d42481007240b034800100e00001c0041c881410b0404c1e64039586e0704540080301d41c4031b180c0000010500c2c052021004a036915480d92401d00d030000c0c0e8503000819000304103036040607907000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 38314357 1250 38313107 38313133
    0x606240702060706110403050123130507030503040b0a020709020a0212070f060f0b04051510050c0319020d081003030c2d0302010c09080c03030d180c0906090c0c150e 73
    0x14810b095284007040a880711f1640c109542501d400780c0c100c04c00c1c90848e242155050041c14140c992010241683c0581d0000e28505180340c00c00c164009801070002180102e00040740100401c50801d01d6800c032400d03e03403240c801200b28031850307520b9805a44100c000c1c16104030707500094811036020b4098050405140e440790310950304400c1241c0b202560b100301860443c0f8042c81690380042181c50881c4848040394081030a503a0205245801d000b0045110103210004004581c3c0221921106000d502d11601c000fa6a5103c400042c0000c1165140000c4c10707140c4841034481200c0d0035a9814202e04503640702d0902d50030b1841c114402c0b04892001d02025501680513450615100e80c0c00082d00c4c3c0c91240f0000c1014070381d03400ca0348454000362006001c03658004141d680d510308800000940380340d489074011116a030208005c000b940107000010380c40301680d002404031510307600c081c020304800383c408454a130355410700201503000020b102c282d2424954010f003c042400021203000001c007039 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 38315607 1250 38314357 38314361
    0x310b0a02040f150c1b03050f03040f08210d090221240406020a1701060306090c0309030f08060112060e010315050603030a0e19060e030606240702060706 67
    0x25006128250002000c200390300b048030780003006011a103801401410540340080880305450001340a5824a140c101c4454161080e0000115401411280042c800110580e140d40051140620903901c0440004051101040b4407003001061001000040e9036007464003055080707540614a0720b555000e901d40140c0398000390b40f180c0e455240c902c0c4e003118440c100c1989015404404007040710080f030f4001c5400c446080b1a02d801550101001d41c0740d00702448201e8135502040345442c400116000000b80311a0141c1c0010280c50500038140011480302e5000e40c1911815603000700062001500c1c42c41b000e03c82c0f07582a80251051401240702c040c0b04a44909450081d0461110402d020b401081007040349017540400d00c1c0c06040606c018603200000039224011212000c1c18003500f820b0261050740c800000101c034080403135181c0203468981d08010004084134226a00a106a201003040c91400c1d0071061031180108614404066046c0ba074100da641080b04100e800c04018861000081c200e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 38316857 1250 38315607 38315611
    0x6090602030a020324010203090105090d06090813091401121401020d0b0a09090c0e07050918060118030b0a0c1101060e09060c07020603061c0507080105061305310b 72
    0x940b00250700e03400c000389014100107801d4500551900c0d0b45034200d445980100039985000f0007420700d551a0200344000c0745070340e840040c0050409260a0504003040700f044013900c038200640d00c0c0c09400617100c0851004880c0c00701e00701c1c9288981e02004009242c402180b05c00b04c0d41c13140303115000025000859a00707a8116080705031140f41c5803c5d420400e401c0c404642e1002f8410340030b0901c6050040e07100c0044004050140841c030022010000e0f0204d4041c100711100e280014240c0100e128250803500190601903402500181c0c24040c410b48180c01040c00c10300307880c0c03c4580c034a02074031002c03600002016401c0d81c0c14203000584c0c00389154210300f07101c0d01c1d00801c05154900300c5481c4c5200454146040205a1407010030184068030242c0c844906a80e809103064408800041601c0c401c51034503003120b08014642d200b603800206514038190040c80c010682541d2141012181c0314082050302c10454070000c1d4180011036020070aa0400042000d540c0702002c20302d0080540c0e140c484c400c00701 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 38318107 1250 38316857 38316871
    0x20f010603080c0f070e070c14060a0f05060301090209060906030a050f01090b0f09070302060f04171c0c02012c0a08061005100509040507110a060501140306060307030308040609060203 81
    0x306404083e81c10138400da0300c50101500142c642a03080010300303400580042e10700c200304916180f1400c1040309058034100802900421502c1618140d03000f503000d031031790408034001141450302084d142c2c141400b0b07441c05507234014a0998155107500610103410001004c184d8540f196200e0070000c40d02c240b0800703802c000c81900100381c3e032810342000700f02080d01904d40d45020030110104103081c000800c559042d20707030403100c841d501c8a42e07000352100c034052074201c012080d0301500e101700300c140005010707104000d40c0f003400010b041c9645829218017121850181c04901e82c20f0f041070105001c61400c24003102040700618032140840d0124004c00c01580010005a004509000401c882503584e0300c020308080740c8900217018402c0c4010100c0c05003444042c001c136207c4c2d002c201051b00801d01c940b003168444044131640441d80c00c041c0c0103804203104440b8000c2070700c12000300e42e0a0104401d40b01c0c03032014000300744c580c2c40d50350200c90044004200392042da0341d8001e4840000c81c0d42c0000c5001b012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 38319357 1250 38318107 38318123
    0x6060d021c051305060a020d0b100519090518040204141305060105030601050618030c1002010609060504110f070512030703050402011101150504020702040b0d060903090b040605040b03040201020f010603 89
    0x42400c001c80465202030180c01444280c52080380c0040c800091031640010350400140e100c0c0b0040c019980039040402c68103078030412101c0006c0c10140d12601400c0708400340300d4120780c01d0903070000c1aa490526801003541110b04c1c0b4007401d2100491600541c0c01c248090800140c001181b682c1e038072103580a8458002c054806c0c0c04002c18040200003460141100314060105035161100050b9203102d211000c9010340301e0008146019602409501494180540b222403440705002d0001c1c000c2445000d541c3d04146003e074040b58504080c4518070100c44040c0b0140d10342801074150500941181d10115540e101d0032140800306032503030000d507002d02825100800c65007031a1001612210441c81c40301410782c5031200100c510b00316881001e04807075090350016990002c070b00110703001e011200c407a2904a40624041e008000e4960300140c3e00c1402030f521700220381d407034100d0410f0910407032045500184d0284400d1080e00007001c010f681003403050048411015034504402e003500d0b0350741d00a840c0d01c0d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 38320607 1250 38319357 38319397
    0x20041205070617040b15030d0203030a060e010f03080903100f0b090a020a0c020906030a0501020705030c0106150c06110d0c02010507030b01091a130803030c0403170412030806060d02 80
    0x704a494060641424100000e400300110350b90404002800a0203140c1010042022a520080c207011052800b60680d00c1030390310074602035600c3d0b1040e00c21400d12890600300043d5207512007a801e060740d8610440f2200745280d621210300a8006880301541809582070481002e0640d10500710070710500800454ac9a072490304009901c2e50091400144a00400c42da032001a80403a403018265070403076900e01152074800100e460030b201090020a65031001a8003070500100001a0400c4c3c00f08000902140b5214001042c01908905180e004188103600080018003940c02040f550f00f6803594042c104403800c1c0c03484054500e15103940c00036035900c07010310003d5589030041d03d00c200d0003800d02c40c0b81c4525110846030342001c0480300c0203402c40d000c500d2000c07420762402d99100400780c0000b180c1d120b05042941c002035602511040300d2624000000300101c1c0743c4042501d04844082e40802d100400545040c0d404010051685501200c10008031100c400c0602c003078541680205403050002d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 38321857 1250 38320607 38320613
    0x50d03030c08010e070c060507030209030f0703050f03091e0d0c030f03080606030c1204020d06020705060f070206010b0a0c0c0e13021503040206040308180a060c03080a06060f03200412 81
    0x5442d040c1c1019800a104c0b07001c02490640004403100700750b070700c00c50001e0395030f9400c0d104800902070010429414000c409104280f1407000403108144c074082c2090b10052410000c0d455641e04c139002e420741c0c102c070802418000e220700f0060102d081c0480a009280c00d5a03181d580d024003400c0a8100b100c0782c02903da000c0b000d05034804803507a0301620070790300307545076080111440c0c0990141030700042224040000007821900c07902c061001e0320381e01410a5444e14103d01d4110b031904400c4500c010f8078407403000056019840000da0604949841203018541b65100b44216075040822106a400e454907000014002e6114085a445004140e00b5070345001442c0c0b04108415030014a01c15175040c0a100303000140c2e03202d208a50841c2e501c10042a41c6e0b10a041401c400c94080a03800c55011469a0300065060340003003030319080511aa8603856599202c00240003112440c1c081c81000400c060400fa003441e000b41c0c059803019402c0000160040c2c00a002c9100c1d40c4d00c542c01401d14460840340150070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 38323107 1250 38321857 38321867
    0x50a120813052e02040306020a0f05070209180c09010e090705040207080a200d09061b0c050108060a09020c031905030106050a0810170a1e0b010509070306050d03030c 73
    0x41c401c09039104901c402038459aa0b0740c41401c0358110403c000520100320300c19480e01c0810041c40c1c03010259210355490401030002e41056030b4420104400940d03080030b030380c0b158044408859009100031805e03200d503c0c242c03010707021703d2803202c1c0148160a0b0008190ba14425820f00910013089018401e152944d500c5090035529440617000d0307030040c0300520004000c0c2007079580c0f00c2102e16108041c9071803490316140070304d00403e040106016806015503241c0d1701c680d07000151081900c1c0d25002c2107080306000c2818288103400741001d001c1d100144915803086082030b400c26401840502e40a4031903900340102c0e80f002d600103180c1e42c000905400348051a1080c00d48503009424281d003190b02d03006018065105243c4002c0400050300009000300b401034100b60090b003203e1101c952092600401c1a641e040c20080640310500b1210348000c400c42200c0810f14803a620040c00b407840c0c0d00e01b00038480c000704042d0502d820716854410118003034440700400501d032030096034007182050149102a107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 38324357 1250 38323107 38323111
    0x40f0203070605070f11030304120309060e120a1101180603060f060c1a040224030709080607050405130e060c0a0f08010b07080901140f0d0b090105090c0a0c050a1208 73
    0x14400f013032214602090740103103d890941c1c0c003c4c07100002c0030b1070000024290b116582180444102c0340b807141083c1540056141d00361045521448203212420040046100310100c92101581c4081504400500c00e640f1178440d000d0103043c040d410100d840e080f8045448942c1120f000250b58042c1004482460b001c54002000c0504011740304c0851502d03602100c0c0110080c554101ca0780307c01041c02c5403140740b440a4844d080705c0b0400700f60b074504003c10807550310698103080001c500f82ca02007040d010104625024003101e8a407546018605020311466246080d03000013411366400c0b0038800944d0901140c1d04c581065616155030b00242d090142c10065140c082400f000b24070001402140c103424111407140d0b8003e00d07403503255a0343c480103d940112254405803445d00c0401c1e000918050030000d030000b2480d00405002941220b0f0510200000901c100c40c1d1040d080000b25200b020310b80c00a007030300780441c5014034034400b2135166940b4101c05200c00301c03030f2524512100c440041c0d110150603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 38325607 1250 38324357 38324369
    0xc06030603030301060c0c0305060103080a02010506030106150e010314090105040317040f03050c160905010801060b0f160c090c0203030604060e09060c0307051e0a080618010b030604020909040f020307 88
    0x5815400e011021076a41d0005004490601000b4484181405018283c4c08001c2d0362100450b003e4bd80c480c03900c3d040603004292600c01540c244408160589018015503050301c90101a001504500960403034030303185003200300c1d818503a442c0d540b8242a02c80b442c81a200d10f28041c008546428680343c024a0600c071694941510030540b402c0c480050128008078030a01d070113180854546240d2049a4209a00024030a10001300d5600024410303070f41d40c002c14100c480f42002007001d6981d0f6851481280b0a95400180c98002044921024071030505505130840c01a0031442109880d64a400c0441e1000c0700c5007000361b8804020001709242a000f400c000d81911a0207110ba410030055199075014040c0c8070b4403641c400800018541440780c41940c1418144001000003038100c200b444015511029580002441d228000f41c0c0c2401c109140e2006d01c10541e029091582c45d10100395510b800c050b00b084c0e442902005228820341e0b40d0000d00740258000d0030143e06013401841010700e443c08540c000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 38326857 1250 38325607 38325619
    0x302030c01080108030409021b1c140703050f070c12080301050a17030306010311130f0306060b0301050102100f020d11120907140105160c0305030705011406060409020a0903020616050c 81
    0x1071220309004800d6901f2125250030260b140d02150f80803480700411181c1c6a00b89126a400f84030000304e4044802c24032146c103464030810007405480040084c8200500036001c50300811000702d0030713620000200496405a619840c03080d4070b039622403410752521102500d0304c00b40800103200e140b42481142e4000d00151602c044200002034070140c91780002003585051545e10403410400c80510700481300c0f41c1c04041044241541c499071400b2084139517000031703110f01d0325024021034003c0c10001140d06a46050b001003040c4884003a028000d8400d070111140000c0d000e009900d251000c07030062000c0c1c808180341d0107444450301000002c100c07200900004091740945000c005001c01208110342050081c41c000ba540c8650302d100803900c2c01d5203803008020042100c0c000040c08804006400c0c15032060009100380940c05610302d034044015a0b06a070300c200204810000c5800690042140d00310605000000c3c0c0d076130741c00040306c030340100b0b0102c100c8090514405003084403e022071480d00c0c80807030f10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 38328107 1250 38326857 38326859
    0x80f070f090e060f0415030b06030a0201080c1605060a020a181815080d270501050307030509010f05040507060207060503010f0e040c08010e010b041103070206040803060a081203010302030c010801 86
    0x402030441c07103184142c0750381480c0400401d420362100c19805519260150052128207a01a034031701c00d02c20755100c151108002c00000c80c0703c80c9400300341c0809068050750740c058961601c0040540541c08200006841c0d42c00c6030702d10380001ca0a200e603510415000a0040e120900f0a00c0641400c075000004800caa180c903000b40004024500c06001100c0c1002000a010420003843d00d405040340d001181c1521504004804065001012241d40d04540101262107120980341da54810f100f80103040c0440c03014400940d02911075441154484210800801c20107201d100480841d50140c1e415101500448014082036804100c00c60040c0305030f1414500e5585031107101a111241c41c0102c55003451004041010320040803131000141c0710050081040d40c4803003851600030142d14110340c2c0103d0510352185403082d10740702900d01c81c0e446500600030b00e0b80c0d60b9503041c0107540024611684102c403103102207010642048600c40449141c100700703549504500405107000c0105045c64104000000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 38329357 1250 38328107 38328137
    0x101a100f0831060504030e0d03020a0201030216020d03080103021005040503190201050906040608060a050904020904020d05120c0303011701050103210302071707060f0513030e06040305060403080f07 87
    0x42c0c2c00b011600b00b1040114050b4607641c00000c000c0c0d000e00d91810890007210900c189940301900591181d1a0b8814200c00c420511145884240000e000768210070308040255020b6001403164520f40002c1e50142840d1341d0003c1e614594640301074000810100050045040842480314662081d0422a00f0700d4034000000740e698100d81c0c06200907192003980c05045901a4040e0b070555600141201d8455469a030000c3c8491000c9482c54881c013030f840c00000c0d090904c52541d902a0b44c0240c400011961150248000b0015442044680b0311800d4600801aa070100c00703041c0d1140c950019503983d500d0002001c2014000c2d5007072a01992600e001000010155804040d243c00010750280040c050010268028014010b0140140320f880c1e40441c2c01c1002d81c0010105c0d1440303854108541103c6010240031110101c0c1d0283c0000c0f1000701c5000401e002d00802d0b807105800816403031a00d901c0350b0b14181401c1e4203076401c0700815017010034444c0d5001210039640c0e02443c50300c0e003c210724840c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 38330607 1250 38329357 38329367
    0x70605040b0901180f020a08030406051c0b090c031e0c0901020f0c0603060d0c0b0d06030311070323030717120f0708070e06070501140601021e0304030b0603101a100f 73
    0x151300400f909404c01c0f801c0119200c121410004082050a482e1070b1076982c02c001d4800d605c10a41510003802c0310001c5420310801c0d100314444608060407190301c6a803480e14036a11680702070071000d104490302c6003000400010040c0d4900c0340071800e0905403a1500c1000281c50f00c030114aa901c0c0304d40001311401042e0721010141e0703500c07507403c48002c403400c106400c0004003a5907035000107000d00343c0060075012114480e080303042124801c0d62800c040400c0b2100d003a8888060b40002401ea0202c2c080780600c030340c90718032201d400001c4202541e04d405031325941c05442e020040d8205290038004502c03000707152540c4038441e901c03004200701d004082c68105002001804000c041c2c50502030701c0246030b8101c3d140c001c20f80b181254024003c0204030a40505c25200e410111031682c0180310390b129142c403851185181a107107004c0800198109403d650b103520b8007030002003103d50148a001281c0c094801e55001e64a04a490481000c20a1500e181408006144403001500f40101c2d008141c05040e481 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 38331857 1250 38330607 38330651
    0x606090b061602010e0604080f03030118050f192408120406020606040510031a01080705010e030a120c1a060a060f021b010e040207060b040c020c03030307051c02070605040b0901 78
    0x9103000404601c40c000083c0c45070089411040235441481d00c0d81e00301a00010040d41078032410752290900d05450170200382543e00c04c44880f41e0144d24540494548000d81c0845900c4003408140400d41c0e000008100f03480b6101a0300c617640d07400e0700903020040c1d408203115484e805252000100d24003420140702956a81e40a0f000d24001c994400002e2940303003071161594040d56001c4007123140c1a05a5800403001e0381c085c007450580380a0201300194660150310382c0c401d18440a0058091403005488400301e03c1d504541980502074646031b08030000e480c0482e8120806a0500324181d0b50500030300b880085c124541012007070041100d8021451030300080c6102080d450351021038100745054004030358442819020a401034000b140c0c100c100038983c0c01c51143d2a205440400c1401068081240c3d1800d4800e1090f400d42c0080010600e458800c034000d10b400d02c62421311480c425104405c480032640000e405484031070343d8005000c10081c00291954020f02010000c0c014042d102c1c468418420503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 38333107 1250 38331857 38331859
    0x60307050708040b07030201022113030305040c1509090c080f0a0903030b060d0b030105090607050a11010e10060e280209010c0206030a0e061303050405130e07030606090b061602 78
    0x81100301c1080404011180500740604101d9180d10491a02038080d400c030701292050444400038918201c80c54400c50b07441181c00142035000303100d4a403001e800504000c2c0051b0340c144032180000c190311502251442000c5069950610b0140c90b1088050444d9803c400c08010800b501083c05102c01041c1521034004000d804000f501090b00c1c0b90035801040060030361364002002280c0900d0740304140e0302c01801d4201c268001d100556031a550326864080440b046d502194050046c059800d1040c085040d140c076425000180b0f0442030705401d890807182400c51106680c1340c030402c1c0a810f2252000d203821403020032801a401503001c004128890016401c40907003a40400c030095541c2c49001031080c2076401a00031a5a41014000a07000e003482040703104251103220041100d4045440098442e1605030303464605080c100341c01c0061840005206c000c55545074030011800710f50501c442401140308bc48001800742c6082d14103003c1c2d0342c201900b144550310500004409a022038003041e901a4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 38334357 1250 38333107 38333117
    0xc030f0a0b01140d0e01060303050c0f0304120602031f0306060306060501020a030e0103020d060302150904050c07030e040b06040302090a0c090b040303050706150e010f090f0b01021f020d1a0a080606060307 90
    0x844d2071076100007032070503100d4201c09608000c07001080c560880b0080c80145a00f200380c8071400d00c500d0500c0c1e902c2c0b08511802c144404850f0091002c40c026902858014001d28103241c0114456014102ea40c0314a400c1910a5a40c4941c10810401e05200309001040203001a145c0304000e9140500884840c2400d2410306400040d80a042d04107540004007440d40144000c05511090a05000b00c0c1c01502015001300d291101151001d80081d00340c03110030780c0c90765402c44054140002d0102a00c24074207043e0b002003007407102000590710084114424090350b500000c00c8400003900030006009940b020120001c00c000c01d1000c41d500104450800790403480c040b407088407001e44013400c455258803034150407900c4400403a030f0420701c950b01380480313461302d41c01d2006030030031540301e8212050007007042d002d80c0c0a0b043d001081d1804113645040c4080d0300a005090960310744800080e19602803943e403803241045c0e5030b000346243c03d030083d2000e085d0354401403856180110200f4524440540f0b180700b030003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 38335607 1250 38334357 38334367
    0x5040302010b03010903020102040305062815031202030a0e010e010c0b0907030609080408010507030209090105010f030e0607090302090a05040b01121401020a0509131a0103020a170c030f0a0b0114 86
    0x54000d4202c454450005402000650840e08000303000b9041400110382c41d004500100c0d024500c422120011401030001d805000c0c01c1c1036800800030b100b040c03504d01c01c0803a601d074008082085032541e00d000e080d154010755074602c2d00004c014014454100c15606000302418080b01e00d9070f10010700d00c0c42c40e602c480c4000c1e054440060040c40c0c03004590005106509002c445401c000302c44010707004a0305030100030300042e00c4828040e41a40950700744960050328000040020f513101c0d40013090b00c14031a04000035040380b800b2180b4103204003110f0940c08546038010410860a02420560380301083c42c204109900f07041c1e583e61410342c01072150140d802d80e00c2c030300201440308061a40c44213a007940000c42d43c0310580e40018005401c0078090603c0388103003a59918988556001d000f10354540003202c1c0c110110070000540080d008000c0c04020405040390b5031247c0b00022400c20301400c0101442900e900e030070582c02c0315460740281400343e018104155242c40d81d07040100c038400c034002c034041d1039260 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 38336857 1250 38335607 38335613
    0x160308031609080303072a050c15120c091329180403120509010e070302060f0405220507020d0e060a030f0f0515030318040203090a0c080607030b0907050a030504 71
    0x720b071290403c20b11400000140141703140c000c4416034410070482401120740c02c8041c9801c0301c9000c81000941903410182451074103103010410300e001032800030071140c104980003002c0c03981002d044842c500040400645001b403450b0034180b0348407003400400d0600c000352080301c50b05000d034010078034503821624080c403400f869901c4a035082e401c4c3e402c0e030104a03641d00e41403c0060913503220840d0444a14540408155440011300503120441c65800041110b039246074288000c07a4400d84403d41e41d01e0382484041056aa05e03020162042ca0307620307c00c0084d0f158550380300119403018068101390b510003071b011402d298004100c1301c60b925045650980b60701980c0420f070060300041c5440f520042c0360500d003030412a8113502417802050300249148407800c950b424180e42c1c0c8503002280224100c19a80c45c8040d1804d41c0007107600100003c15580c0b1401540c1d10031845d0641034001921030340045080042d200da05108080e07103030004030344141003414511002340c207910030110300710109900c80b0001030034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 38338107 1250 38336857 38336867
    0x10201020417070608011505030f060a050d030302030915100e0c1303031809150902070521180904031b0f021c0b0903190c06090b0a09051603080316 65
    0x5041041d8942c2c103218441c0100354461409010360000701d0400c20000c64030905e9030000148034000c41d26142e142d52600503080c8400d080050100d9809203054002040c2074542c03500e400602c901c030b500c00ad600c0c0d09080711554181740303030400c1d01d207000d1222000b00110014841b10442c111514000d860b2800d84503060541d0796481a0440034079040142017002040580c41441024210b01040300304030082d8664811070300b540c0001006400c50040000c1c2407201080990080000c90301c141c04031101c04085101c0100c00078090b9400c9514035001040e0641c07640f201a0200c2541d00c2c0894074103c0601d8959005080454040f103142580c09403100d4007020446070048400d00c0c560000d01b28134480014080f1405e00ca540e05408440480e013180106141210020599100b085540c444401140c0e20b808110b0381010780590580c0c0c00e545a400303540103c0c00f501401c0740034507409000410344100d281411440e0107100d0200e00d910300c502540400100e10180c040d070f9042141d420406588011007242254 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 38339357 1250 38338107 38338109
    0x603060e0411360411220e0f0a0305040e01170706030218031501051c021005090d0606081b060a09030201120e0303090c030c01020f060402040903030e0607021f110702040b0102010204 80
    0xa41e00e05150268401d0f0200c200326644281d20502ca5800005520414811079420390244903030400400e00861504150a4001c808030059503400c81e0040100a82158581000000241e011440004090000e0072069001c41d000d00023911041c101c0390813000c051903407000c9500c6034070209a13000c1249105000008003041c42040024102c44240c00e0ba111014200042841258421404010010041996401d001c1e0103550001d0410344110990041034455901149940e039000840e074101c07000107030007440303603d000d41351040c000c1079100c181e008002c1c162101302c1841403003010b050141c2c4070705590180310001a2070382031821a82c0e900701003122002414050078042200e02000c410814840c1000034400d4010b00300301d040b6036100c00344800698035103041c1e40460195800c042c00003805070800d03030407580c6864801d1600113501031420020714203020301942c0c41c60041e08101d180c00503035030300011644035942c94840e0402410400084030340c00d1f4410980028002d5442d08407103000e81c0e00039030607030b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 38340607 1250 38339357 38339419
    0xa050403060c09090605180105090406021b0a0b01050d051c0203040b0403150f0203010b07080a050702090115090602030f07030c05010f0204030b091002030114010c2a0603060e0411 79
    0xb209607800740c030015203051014060501c21602d80b1100040f9864400320400c4c1159880c641e840c000c2e401d050a0044001005005849503602001000c04402101400a9608100001503c840da500b07203000e48078024103910446c820110b0b40000000310b0800b040300044030a0707854403004041a0701c0b0003a42180150f070300c4058000c0c00410004140924401d401c01c480008800400107044034170030345d004038007080c0100142307444213128a20028180380001c11018041d41055800c0100f550b00007984503200360130041419052456148600ba009156640640824005982800075205a0314040e00440002804000d8030391040d8050160030b6005015488880c0b00a43d900c588a0521a0b41402d0968850f5614498040500e03017441c124800d0b40d050381d8602d0100030b41c020208004581c01048904256540c0d040303045402d1041113940050250008000c0365240380525240026044402c0c540c440001400f00d2820800000c0102c0c0086100c040d04881051a0f010000b03560689007583e60054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 38341857 1250 38340607 38340611
    0x601020a0611090301110a09050108040c0504060b04150e03121318090201091413050a02090a0303080a0606030b0609060c0313120204060603140a020c032b05010509040b0a020a05040306 81
    0x1460015042c0c401000d4000041d070081c030110603030f5800c1c2066446520100390005101007000d00c02984925005900540a00700f0074814a4030360000800700c841ea940486a50303100002d0801800040780038940d62104503013089490b48118002203516503000211042800c50006541e00e0003644480e1500017614801c500141c09001e010744039002130240e10810307030104004200010350703d45015210740030440007401c41229a1103107142003020705000741c094802c198003441445000d440741c4c4000703001036020b0350f40c2c0c01040c00d004801900b01c0e04140c00071001c050500c1040403142d150a8101c0d0a5100165203841e651080c86a00d90300714001c0801000380c20380b030000c00180840700003026401e518001ca800300807240eaa6070003602100d41c3c060000b41c010384620005100b52580f40c0c05400d00300141400c2da490403207540c1c409803c500309054543c801e4980000c1c907852445003441658007510080c0c441041d40d0405440d41d081968008144000790307500000c5140940e4030541c10b4400941c0d000c841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 38343107 1250 38341857 38341871
    0xc0f0c01050f09070807090903140a0f110c09010e0c0910020a02040501091404020409020a09060303050d0f02030f04060203040c03020901090504050d021b060f0f12190c12050601020a06 81
    0x19501804094030b8040766407a501c0042050148003181c0c01c2c040b101080010100303540b030000300ea8043c4c0512401902400318000c0c0450103c10b0070300003400170180d2581c914800c2030103d80302910307104a104403141658094136081c141515100b61f01415660720203e111491742d03582205111074800c1211040d044048094600606500000c810210ba8805c4800348040c0e80c8a980132000c4544c9a503580580c420714101280140c1065444080780701d0015000040c00340c4c841201c40c00340c0318603a000702e000400c0003540341000c4042d0f10412881260080d0306504d903080c03400030a08200b0001d0320207800c8a0b4000b003c1820030842043c008010b6902400000c2c141d81c0d2007a80c5402828110360540d078500407902d44010807840460000c010b03040450740200b51601138401d22140350000c50340501e900d1001c0050840c000031910150100201500000130310b0320300050f40c079000c00060124542d07030509000000b101e05420100c003c440c00e8403100009256922100100d02e015078031100584000d1602c20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 38344357 1250 38343107 38343127
    0xa02130b191a03130206090414070c06110c0a0215071502120f0603060106180f09020405030708031c0203370c0c0f030807180e01061b05070e0c0f 64
    0x2609400c803211410025080321204040312502c0c40104c03a0442c904070001d84a0340146041005000180c0c8044c00c009038011048101c450130301420b441050100d50b00c00f5180e4104140c2c0d0041c2050001030110990400543e00096031b82c0c1e41d20100024401c070059040311690101c4041560180b41d013040c0e840050f01c1d4913100140c004c0d0300c054603010888000c1c1c800954911848042607008400c0680100b18980c03824804403450101131071042200b94408200141c103201300700192002c3c044c039100051303440345040300301440c00f54240d0009007250000d00c540b00c140504e102070120324104c01c81015030307030303030340c2d406424103403084404512040380c815550031941101740648003584400f8a034420440c1e40b40c05074050300e4038403007000010044c008840721039000030b1055103099080003c1d070900440c0c03084016105941c242c0c894028050842c01c0d900100314031503100b6005551580610201c0c0007001b03850b118591503010b103000d2841d1707808000000c19041c2003e5800c480f4614101d0f03010310b403030b9080e6030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 38345607 1250 38344357 38344399
    0x20c19060537020c010b030109050309040615020a030f0c0602070c0e1503030f070302010b06030405010c0305060105161b0b0d05160201050705031305070e090607090906080a02130b 79
    0xd24400c041089001c02c00200d8580681c4110810030a02216500d200c00824000040e5215000c0300c1c00039500c42e88803110b607072005d01a0700034161280c0080e40c1c80d01044000d01c0300b00d66080c0d00680024440014010100f50045030720102c940d01486e01b58140061100261201e0000910041189100007030f00028007054101c81c070160303994000b45201c3c40c3c46100e205080780c141e03503c901781d042d001080303040040d107800710050007028480d000105040c408200065156001142c0a5800ea5115080c9000195151080a03400320003401c0c00d6080545650001d402042c861034002d1440d650b00c01211b11061141d40b200c0000c2400c001e400791b84180b805180f601804054565051b03803100c000c03410302002e0060243e2032044405a0301c80341190340c3d0004690011150980581d01401031141c0131034001d004488803841820048014078890410a50007400c3d61026482012158a04901880500b002003001d00000c0d404440140b5420b110111410041ca00c506803117030710140507484188200502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 38346857 1250 38345607 38345611
    0x6090c12020301060503010605031b030c0d0302030c240402010518060c0307050601050303030402010804080a0c020402070605090d080403050d02090109050a03141b0307091109130e0d0309080d020c190605 89
    0x30b400a200b500c5e41c92080c10300b40c40711800f525038185c02102030000300183c40d03280d240303038000010100e4080703003440e40105011805142d001c1d80141c01c005002c1980680410080685105141506000e1510b16a0004481802810003410004000b907090702800c01890030a4141200130052643e580d5602d242c140d5980c0041030464039070068600024503490040290fa101c0c507010303150b182050366070b656000032079480b0102d49400e004a145541c07000d61036030b101502006202d03410000703160814000b41c40c0ba00700030001d8401004002810400000da026056a041202c182d5003da124461b40c0d0040c0c81c034080c0c5802481d00300f8000203000052196a0447c504404400400c0d150116a076140002001d0036001500d42c2680c0107820810000722954040070b86400743c1070f8407a081002410004003041c00300e0381d00c0c80d40a0707103809003840c000b0343c1800802a01c00e12070038100005185940c0f102d1482c024040210070070342d40402c01481c4ca01c0f0034045086101280049041c61161500d8180c00400007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 38348107 1250 38346857 38346859
    0x1c03090c15020d02060f060d0203070305030d0906050609070e041508031c0c020712030c060b060c01050402040c051c0b1206010609060f0e030616050405030d030f0b09060a03080706090c1202 83
    0x7010240201c0704d001041ca940184c00c840b4145031260307280380c28000c00060b0100c0c2260076206105c00040810418409420504641c240200c0d211141d410010159203001e01910f1041c403802042c000d2482d006051031511110a03180840c411100c0c45480416040d03030b80c05186640800261006030004402d400c204c9100b040c0700c1007252030340354a822070740d610050003203610100c0d5a00950000ca400380902c40a4184900004550a40880081b40058000300c00c070461aa45820a010842c6450b0003555a0580180313001d0f410441150050800c0041c055451070740140e4494000d03405440b6200e1000c59012500d0413142d455a58040041441b03105205240001c0ca807da03c03401c40700e00c100c00b000300741c070300050052580e03403254200088802402c241100c28480108000901030314184203a21200c80d864600040031030054060406a65035203d0440c03144403140100801541c80141000644c1d801100b01a2520304524000c0c2c003d000f1240c0150152419440000300300740f003d031020781850300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 38349357 1250 38348107 38348113
    0xd060e010609090302030a080a110a020c10180e0a0902090f040b0f0f191d0c0103061406031306091a04030e010c05030f090d0f080301051806031c03090c1502 69
    0x240d200042d1084039110580140160002c00c003540000b0310407000340e50400850000060101c00c00b55038940d85502030320006025070086819101146800039401203003510f42d00345140c1d5008415190540e082c018020b0080001592020030003880c465440380000590140840850341003a4a900c1100c0004580454800540c1d400042c0644c4920701d4141c0a142a005145140e40300e4100c0e50f00c00a1510050302002a6138007000c480b10030095000746402c651003005058404074400005040d18019040040d00d150201c00441c6543c03901d90849a0010140034894a078100302d00d001c202a00249a024002c40703410750607040c401008940c030741d0040340300e501c0f440d07000c4000c200150f0b84a000658003514541048c084c1c4550000700c0c000034a08090700808070207030402c2659070300120f030400c0d4800303a03001000407005100ba41407401c50303000180f0340e4800c0c031105071501d140000da031a0041012400301440d0364092044942c002e07084518003560003403a0020032a202c55642ca00c2c8102c000b800c0300144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 38350607 1250 38349357 38349359
    0x406030e0f0a030503040212010b031606020106080f0705010509011206080303060a080604020108070f050f0c0c0a080304030b070e04020903151906032a261002090607060e0c0d060e0106 81
    0x202001440b001d4403030b85511a0303411a62141c00300042d030342d9065900741e520f5484465041e56686c003403240e0003200b041920001d06480c00d1890080c01c4424903000390750700390b01c080305600c2041c40005680e401c4900c00d182880e540c032040e800407240351424000400703110b81000b10216040c1c10100181d44204816a0064031550307403580502e644072804e40300070340414051b50100f0500c912400c0205041c109504000d4903110304411141400d50020801c03000341d07045441031161034070704100ca0b04014103070480298186810344e102c2d001c90030000343c9403e0611881e00c5004980341c580390190b44445034014240c0d0b01d20306200160070030764041241c5102290100d04d42101c440c103224420038040d01c1d004030140103500f902c180318180c0040010400840507102c064000785081441e08440b8115414499045007000120501d5107401045950149420700501c0070701400d890b0030b001d0701c0c3e5082c1c100c030021505070b0820040c1414211869415030700314007030550a8051140a4101c032202c046000002c01c005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 38351857 1250 38350607 38350633
    0x170703240311040906020912030403050f060115080919050102030a0507050c0307033e060703050408090d150e0309010e0616030c05010b0306010612050f0c0327030406030e 75
    0x34105001c010110710410b0461071880c10140c1c00200300c0b034071031040146005250070018007190104d840410b11540001000c1c0304209090103400c0059221400602e403d5041c040c4075145c00b09051591400c0081c1c000024681d07035000c21104101284404110200e844203007440d9010350300489014407528142000302e10040e00c01c4048820281401d0701840c14141981c4e002c5400f0a81c3e00d61040a9480c40802c071070303054072940d11842c03031107030307113204d015091008a0344c2c80781418401484801418501810031020640f50f80440d06188004c03a10304407a07034145d00d058584590400b1011000ca403406e0820b0400e1072000000b007148070000d8035a480c09007801e604102c054450346444003c8002d01450110000b40079004d00c80c1500d10820011030304522074000710f854a4800d91084002420304846809441074a01c5110340061880b030040340b46141c0280940454070028100c4549000184100c8003001c0e02d003002c10205110000543c0d83e226a5500020040c1011045001c1d55010b459402002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 38353107 1250 38351857 38351921
    0xb030a0b030a0809131104090203060a08010e0a1205070501060806191b050a120212040b070c0309050f010201020423040606111b12010e01050a0b01030b0a090c170703 73
    0x30b6981c00400c280c44e00c1040800e0150b000c00070511070f0f03c2d040c1c544001d0a0002d02000190002c0d00000f000180c483c907000007000741c2c69003e980700000030303450145041c240c21004103074040400d80181c00300380018480d9004565500c07403100080e2955203030407804240244003040d00e034003a4000241e8801440c0d481c040e11000c94181180201c52a10360380c812141103405000640105246828204421440310081405136403000307480e400854003910410040241040f60660040114a8580800081340d0f030098405c91050244c139200b0300349103450b20460384c405d40469015000c1002c00c0508403250842000010300501c00e190b00c111b05080c004215180b1602003a4a51800000200030194404060045260024a071607400410308120380d440740009000348405d034006100009110b01e08480ca880445010310700e4a81014203000d1542d0341ea07510001004162225034400203080c408819058078191f03084464200d80c441c204081224541d015446003a84078080351400464844145031142 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 38354357 1250 38353107 38353123
    0x1908010b0a020a120302131502010f02090d0303050c090a240309030f0c020103181a06030c0f040f0212040b010303090b0901050304030509040902130b1201060819050a020a0b030a0b03 80
    0x10050f448031003107a0102d40403029860400505060040c40c10144000d4981c941000e0b40101400e4207402c0b11240700c3c140d0904c1a5a10540740c0c00003141001c000f180010702140c951540503040507140d2011a088071100d00071a0750000000f40340c040c40903900e290040310140403840c1c1e6141c4141c07400c96481c03500c0c00781c01110f68007685270ba00c40603c20300c407690903a10749141c03071006d0b410107542c0d038582c00b0100142c0a81a601d940604100c0c1c2d44030075034101101e204040107003a203000e0781042c22513a0080e25580020560703d41d0032940401c2c80c1c00c4246940c1d000f40103c020444408a00d6000d210511191040e0b140c180c901075a0f801b001c80352619000c00980c071401c0186030000d4001c00c00100031a100b4006031800707883c002c0012038032038083d40000da81d080907081961040350740d481012149180100b010b10f0000c8082000340515490304445545540301c240d0071652031070b038851500041040501089014582c001c1040e21030b2a25131004010580007128000002450881c0c0305495180001e6892 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 38355607 1250 38354357 38354377
    0x111030c04120c03050d082403071809080301030b040b070309050616180801021b06040203060103030c05030c01060914010504090b07030c020705030f0a03030605180604021308031908010b 82
    0x2071400d40350084110220410301c2003510810341d162404000517105100781c2c4150b1905e941e80c01018200702854038002030200003e00401d482d202c1c543c9240d0345021902c80300310340601361480001100d00703e41c10081c20000000802c100d00c0003001004200ca00394610b8012b44c041d0782d9500c0155510f44098049030695180580320b90b10800001c0c1a40166501004552131140f520404411102c00c03c1088540140c0017000302da500850002c81c074038145040b16860a01c081c00502c1142040d8022039200d2806010150400c8a4400d906091000401c02c4908840604000300000c5ea504c0707440310024050042030b40804040360000258a141c24094000740a0700300394202c403940c071800c005a00a1911482240540c000c403100000d0300d87d010301019504000500c0909030074500c910340101100c140e0f4209070320560045020801c0e10401c400e0655102c90b0607180140d0740c1c9044a0b0410642d016503001c0d8525200000f002401d041034450010081001c0d80c4840000340d0b2101080d07005805458108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 38356857 1250 38355607 38355631
    0x2070512010207121416020d050d03140601170a050901140408070b01090e030a200a08031e0702030a1b060501060c0b0a0209011403060d120906110c010504060e0a05040f0e011103 78
    0x30703609006c9400d03414411038401041b40000c0380507030b51001c0c01c2c030510380303809004030b41e0758400702d0300354110190b00c40e61080091034a0340381408001c02c1240020806816104003544d504005002c00307200754461010100c54042c200030f5803816182100071544040f900b1035200184600000302e00080f40169142101d9181c055814512011400c9171103100c041c50f0010500800e511586a041040c010b281c000c1c1d0096080347ea0301e151200301c035504044030881c0d000c2c0b5901c0900c20000d84542c04001d5a156130054900300102d0040c03c0c000c15070400c2c0102020303242c5441c03c000013480540156603245804d100380450201591070008403c01c0b4014502894081031702c054001c02119100c40c000c0d540190300070b142000c0011540c980001040b030b00348401012803443c01c000e0060942000b440707190a54030b80700600d01a40c9910008129025074880c0105200000807900195900c040403c000f4200c054400c0201c011a82c8a00010b480f500464480070b519200c0365408400200c0c04a920030035081ca04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 38358107 1250 38356857 38356867
    0x6090f0509011e0302060301080a031e091a210405100b1c02030102040b0a170906010305070e09210a030b1e09040201020f0109050a020f09061f020705120102071214 72
    0x1020001d4407107103c3c01e040d0820340040400141d030307440301650181c0710020061940000514001e4152001c403500c9a0301c3c0d202c2c1b5a41c08074403e07070100d5a03034141d031f05c000e214035100c41c09040039641c030f4041c003464604170384100070000308885c80b00c80c0140c0c4528002c000f21442c400001e039401c8210344c3d20050054001c242e42a510b00c090710089200089644040c000601d825914807030202990012001c0d40000b60540040030711201031548c040ba00070741d410b4050101c80d499a903a2942c0c90440b4071860803240404000a01005000d0156081ca00c121600251000d60461201e6011f90320001c0800d02007403918050217594280f404602d08424034081562074007122540800241c1349004000b01e04501c100410761404034428040e80080300e1080c401825901500d1040203003520200c82e6850254607402d00b004160744e5640031100407440074007110b03007000b21080c0e012400c060554000b0381d00540c0f03240c03c008804005500800e12140901c440710300c3d00030401012101c184449480b039000480c1840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 38359357 1250 38358107 38358119
    0x7080412051b03161416050d0201200c0310060501080606160804030c03020307060806030307030c1106120f0603030306060a030b011808011415060a0c020f120706090f050901 76
    0x40240b00354141554441d40c540381e030b079880c1455584640c0903021403160740c1c0f51060401c005070602d040440d080c80040c1ca840c0c0401c802e1141e0000241c400c0d903102c0e07903039501c0d02c60070745e402240b541040401038044101885400320340e80359900d03003e0340d19a000384500f01030000e144001e88584416594141c1d038100701c50f01d40004000003508504040d0380c61192443c00c03500000c130840d000300004c500c1041a580c807145180101800c0040360350000c4d00f4008110100181a500881100d007a00d903d4104203800e01460308203400400c1d0040c02c1580c0082c00010113001000c800c0d000584180d8083c0b280b03140702d64812040c15143c0c0010785141d80c01c044240403105131140690414512540d0624000d8140202882c50407480c201c240d100c1c2519946d14a00301e01d80c4542c0d07401e45980720303074103100365608030074801e001c65182e00c01c0f000510300f007126075881d007002c55407144d48a11001c20024413aa04110b49481c070340361202c86910481b0086911014001030140c0c8000300c42007202c90080a00701d00c0e80c42c2c28 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 38360607 1250 38359357 38359367
    0x6040605100503040503131e080304060509190f080a20030703080f09130f0b01020705061b010608120a090e010302010504090b030316030503190614040902030f060a0506010807080412 80
    0x41e00c105c0d0725000c24410b24041240070710b8500003d00d030703500700c0240540c1c0542190414405a821010003a0407c00c0144402d5400000b01d940090080e01d0403c02c002c88000c0d040c0c03401343e84d6049045504001a40090003003400113000e44014010040c0200816031031010b20f43d903440b6110640d4040d002600c0806c003050040d00544000500d1140345071820204800140e01e6903903004c07101d0861a983c5034540c4290400344181c0c000d4110070b000900d50b03281454002402c500400c10407070b07840c058821195140040a410102c01800d06800f144c480ea54220181d07186900700071104000a00c600e140002c480001c0b00310302e4100c0340c060b124689040e06107034940700a840702a840355018070081007226402c00610b001003004901940e40c4580302e00b13000c80c2c102c8070610b842074108d007c6e609120b0306003d041402c16010f03040400c101c030000744000481c80483e091100141b80454140140300800100044035040184580401d0741d03880d00942da07198090f40c004405860180490600d82c403040c219034019 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 38361857 1250 38360607 38360611
    0x5030f07050423160306080c1e0312042606010e0408030604110a1106090a150f1103010b07021f020a0611040f0902091915030506040b04020406020a0201020606040605100503 76
    0x1034020f4040102101c203010700641030b03440c1041310000384c8048000a52502c02c903c0031308810b5015160303603c00c040029440b403a8551001000e840c94044900055408124500001044400c0c82d44c0762566000d514071810b005001c1c07105181d007000940f0441000c042071507810f0754141209596a07480b41e44402006800051030190881e940700070200446188030050141d20141d41d582802540a015a85003060b41c094804042603000e10402d8000410070103081c10030000c02c1c90002003001d810111840034161640542509200000000c10741c04051801001140d0003500c4e20100150100e00c03c08590f21805414401604581301000010b0820303003010402104ca241418241501c441d200b41c80381000f030340300c0b40695600150003402414084c61441c11064100e20800800b07242005460206140c082030404040e900e00025409a945138082455000c026004644075520340303401958643d2000e0040c1d0141c41108005001460140261000d03600c019042552021888000351426000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 38363107 1250 38361857 38361881
    0x423070308161401020306130c0c1506091805060601051c05040201110105090a02190303051918060806030c0f03030a05090409060212060a09020a091202010c0215031005030f070504 79
    0x1001c0b49840214034605020f0410900c0c40d8001603507410103204100704031000d40e2050048500300141114045c1e04814050b40094000f0207200d5010245410580200015004211f0207468200d041d80d40c006180c1b10140b609103d0303000c0b5051500c4120054400c0e0151408a01c0041310b14080720700340a505802054100d441070400d0100000d01010302820358000b101c1c10380486c1d1000f2489010361900d0020154001e4080c0000c0410506545000b0310a00c984000260070107460138200340e00c648510000d51900110b100c0d060800d0b0f45801c0014455401900c1c2d02e84a88240165207c05161519001a403904018000e624005040c0000e41d03082d00002c2c4400c1d8440d1740c402200c004281240000d000d10032403041400b029260400c200500c4006507040916607038410300081c0e4400d5001207880080e03a212a051160b6180b50f48012600ca012a543c0290407807409100401034800b103401550099070070b9170354800b0b501c0c2c40382d05045c0d0311140c10410f0f201035480090100010b0901b03038040304080034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 38364357 1250 38363107 38363137
    0x2010e040911030c09011401030e16030308010608070206070c020909070504090c03030206070503040302070e04080405041e0608010b09010b1308030c0d080703050609040b0a0e010e060423070308 85
    0x84080000c0e04403505418181e9a86411240400e100e00c0c06102c407001d00b0700308407401030b4694184003982c014000080c600c2410b0503030b41d0762021000c81042001919040158580d1060341341c0740e140c0209145000c0c1b00d418085024180440c45c0d00c4e0012503203034400c41c006d0361401f02860040d000c0020516003d0a031007100d00640d4408100d40d2194001d07801402c3c004d50105840c1031462900034607040c2d00405000403c04180305000009601185140c00c0310841400c0c20850340751030401d40018800c90740a103500510300742c03130f01c3c0e4a105002525403004c0da01500070130025030b4800030503098414102c1d0903030b40b240506006100315140030000e4154400c8030948440615100c0300c1003031031944410007400d1035500c03950219a070b895001e050306034456841d1400f0701040c01d04501003000110081d20080225038168000b900740001940184c082c8440d200084c070880260006d140d031220300542e000e94000b260b03c1c40b9a0303450f01452000d007009503105002000814516210413549421100034003070500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 38365607 1250 38364357 38364377
    0xb01080402010c111201140f010605040e0405120a020f1e0d030e0f03040f030b07051908150901060c03090e04050c01050a0507020619111b040f15120209090316030c0201 74
    0x61034100e00854145c890300000200c140011040c06901c0d0380040c0070005003c40340c0014082c0c0b942c408295012510924000389450b2514600300b41031070740c031800c940f11881c0081210202640d00107100c1070b00c1e44106080d86d4060100c0a1595030320720150340714580780c1d40309594080d84980319600c96034101603900d0640c0e0b140d80d42d4044541c10b40d0b009a01c0721201410403481401030103004007605404c4005814214581928540074040b581c0e002c004803800d102403640014600c070003180d00c1c0c04503070700001c200d0040d075a1038240181010b140c0c800241d00064548402181800101e0a407a01854200000300081208080111100d80c0015080c400304003044c0407090040c1c64180150042e044640e803000d9071070507120300081c2403040b4040110072f25445080e220300915445004100001016100410b0120f2001c3d0300380c02416512580b29052460444001460510000f001c00d69510842e8001096101c84a250b0759074040c1e1903414031413a181240c1240060701801040c0052031043c148034800c0d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 38366857 1250 38365607 38365609
    0x30806061b060403112812050904090c06030e0a0206040512070801140a0506010201180b0604020c06010305030705120711090406060801020c0610050103090818030703020d050a03030f0b01080402010c11 88
    0x35006682c210045043c0c405c056a00b01810b1160f650701c0d40c001c0d500c612200c00340412082018161000140102c2110800c4400b001d01c607100321004a800500188000c000605d040b8521200d14440c050000c1c0c40c1421401c04503134040355844186800a10480c2000c3c00e00c010010760443c28100350030700703105215001481100a00440c008040c2d440c902400c18079080307a0060030707030384001c0000b03045902d800c122414600030442b074540c40540045050700155036003400b040091140d82d5028409101e44000001005000801408080d01c0307901900c60319051401d5411260151410082c0320f5005456400c80d103040c09408540d21a009600c04140103568031040c1c1e0880c1e00001030b48050313410400c10020300b800c0e40c01e100c0c0c00400080c1790070020b40d6940d85802055002e103c03481060304001d00c1c1c00752070381d56041000304040d540092a803c005805850103960303601e07250700101d000c44d040021583d02d4034414840e28802c001d060b100d484650766503a004507210300103508115450f01100f07c1081e01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 38368107 1250 38366857 38366863
    0x70504050d0c0602010b01170403030506030102160b2409040f0305070204090b0907080d02070e04021f05031e0402090a150312020312180a02240a031a0409030806061b 73
    0x300500402c4180d41d468103004000382540c07034204130681402104204070140500454085a109406250000da035803100c100090191240610307074900c190080c2640e034203115228000c81c2c0038207800496082d2401000321502c4403c5030041d40d069004140e00002008642030098a00100348030b480d101780303001c401d0760000301114001740c015540c883d9000100040c0742801c0104602500c08032000740b05440140400a42c0d407003060054800004103140031504640303c100c0c507040780007804001240340540800700181160070842d4a158000a60803241c10398108400d070050041d90080d000130001d030f5528501d100076040440071440380043c5c2c058000042000c0964000d01003491380c3c040d6684a448100c00e00001c079001c5c0040640340642103000b101c00380c0c0080d41c0d0740440e905880a20461100d01c7c2d591402480000161085d05d90009440c680a60f1591085201000d41d680e049000000c0fa0b00380003c943d0340c00f80040110302c001021036004d181c11005440c2c81c0760201410340b5090501c031801c0d41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 38369357 1250 38368107 38368129
    0x9010b0102030a21110a03140c0912030d05070302030f0a060305030703030507050702100203030108010c26180708070603060e0601120f02040f090506040c1107050d030e0409030e0a08010605010c06020307050405 92
    0x1517a002140142c95954103000d0030500206544411a4034142004541d03050b2045001b85445241c2812946403030010500079107000d040030402c04c01092404010107006544111020004400c00b44001090110640f08a0054940100095090035450390b020360060002800c29002d00900740100c000595900001141d0403045a01840d02c1c0d5141440607420756a10800010911100704083c440f0b40802442102e41c000e80007044078041c0d210401c2c1c2503044051400c4503034007801840c17402f1805950020b100412200141c0d002c2204c0d42c0d90381c00440c04040c4c2a0707116030009007500201d14019802d904116001c0f0b1000740c1c0189055a14001c0d6001843d140e0301a080c080c2c2c84100b08840e614007480b03070554201e85814021402104c0090385078442c0294080d5502ca010240340030400e03d44680c04a40a0080c007a10402580c00c4905000d81481061200c45100c0c0c2101070001c90307201010b01815041341c1c0107855150075140140e40b00c2000c0d4000800410070000c0034800080c00750345080743c0d60 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 38370607 1250 38369357 38369381
    0x303060302010e041415060903030a0810091b0804020a0503070609050901080102070209040f030c0f05100606030c120b040f0504081b0a020105120405070b0f1209010b0102030a21 78
    0x406619600c000341c8001480c19041d44182d01e00303002d102560510240041c1e20080c0200c0c1d428244003000700281c1c00f4064101016050b02c0080391b030740c1e0b4050b00b0114150180e0300890401c44c54076590b003100c50a0390714851819403902c10b281c4210051314000c075901500188001c01141d0346903117540100c1c0c508801c6500000c000380700800f040040741818806207001d00b03c09070081d45040244d4010039240c14000c0c0c002400300b05d1012001d0203051003080c4003044030380c0c400303103104950b02d407410825a5244558240b04031940b903c900012181c1c02840340040c010015103803034980da000c803020038000b040b000306951b41140e00e918169030300d444240702e00d03885644034503201c589a6420728806d002404c40420f848880394801642a0003603a0800103403065080440b016810341e55840c03a00720300b00945039100308103030003010035006040b4a0390409009085e604000074041992200a07103400d8559030110540135030400c21803140c5031803254030041d0b0b9640204102c0d0541c0e40c9812120b41c12201050148 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 38371857 1250 38370607 38370611
    0x21f0e060a180b04080a080d0209040f05010503011505010f0509030f0313030c09090f020d050a12020c0f01080f042a0303090e0604090b06060918190606050a08010303030b0105160303 80
    0x4500b030840d5096080d8003810f000401c4034102414680030607a6204000f03c041c02030140854043c480036082d40484610020241052040d00981d00b00800030b0070007801a1071180d420500807101c000004011401202c030169540209010414019141d5034040303c3c01917014010019440d40101041000b020403448140c130340c0c900310f45141002ca0524030f241c0c0001114604040c503503c003003101d0403810068030b41c0481d0803240c540040d15000b840c14003c55002020404144a100380d0a84c011400b60150b05065031000d020910b01c50044841c0d40b4211454541c5020f03030004200422403091414031845a102100c0f0009480c0700e00208040ea040d82c01100081c100c044e0900c00030701050300107a00101c0558050120701002d603204420040c00801b02e0b8080d590206a0950903542d508140c5500038222048040c01d081500341080140184000f00c064541000000100c0c18850030031554604129500d821159085581c210003500c1150101030420034140014a44244a141352400d454826140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 38373107 1250 38371857 38371877
    0x901090c1d090703050d030c0306081009030305060303040b0d090203160b030405010c0912110102011e020d050108060c031303020a020604090905120307051b07031e03080f04021f0e060a 81
    0x11104241d24000c01c0034080381c1000408000103040044c08a2104a42c1d043c0411342584c002c2c42103004181c40e41c02801244280046641c80c4403007984800c2c06036000e170f60140599030b28041031540e06c0c4128030032400303000000c01078201c03d480960f110403130301d6100030280c1d00c6a55010300b10300b018100c02d400c102220a8000184003c0002c240b10341c4c420540c040c14106011440d10501014554014401412191040340200c940341c5c401e42c800701400710000382402c000e001c00500c4030025002562070500d05450400082021080000d64900c00c440d045001855595608803110341e0380c2103103000700c0c19841059a80001a40d50070041c0024018104002a100c00d8900700145042c08202c11051201810018040f610358001d04444200705031100a40b440c0a100072032604e091087e50000d450740541c000088203000c1814452910749000750b850002c2c176103da1226510b0307800d0039a0000e5100500c403101c0000700b01c820030010002680c03414042c0c8e0305040003002c0361407170b4007025a07100042d41c03c01d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 38374357 1250 38373107 38373149
    0x19030b090609010b0a0312030f02030c0408100e0619020c12070516080c1905030106080c030708010c080f090a170901020d0809061b04080703030507030f0e0a0504050901090c 76
    0x401d0703403000b1180002e00c403005181e000714130209510701000d0070007010420b1a5034143d000e41c002d000d0f414140d103400c6589140c01c1090f046650083e000d19030440c0a04100848004524040d036090600c058020340b04603158448640030040f0196042c000d129000c0c020030072220400d002e1004880c610220443e901c031003916200d4100f03843da100c40314000007440300c14000041c00007440d034014130b070681e40b008241a201d080000c0c0142e8580c44a9815801c000010451a81c045405504c075002503049401c2207454441040c02c0c2c46d105010031001590300030001d140e104110100c00e403c0010b040036148144d046403503000c000000512000c07040100041c000d4541d5030304000c11007284a4074545480c0c107090190115442e090040c0c014a0381c40b0b902c940480352060000b040300e0080804404441e0300c1ca99034a000342c07581d0400541a40491001c0c1c09090314140544051041100300500e58042541000308000050101810160700c565980000c0d00000c0d5582035a200a0206541183c1d1250300400f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 38375607 1250 38374357 38374363
    0x60a080a12030605120a021003090501050c0703030606050301060509190801020310030b01060203040e0a02030a0e0d0807030605090402010e040f1113080606040e030307030b0303090414090c040204050a05040b19030b09 95
    0x41e10030703401a2440366440940310317000f00703034450095811500c0445046081008901411400b10040e040f03500e4101407101102d07682004161844c0b00e61414003c25542d14000c0d40c1c0e6010134840d03000840c40401c02c8030700700d00c1c101740004140003401503c0501c050701d82c8a40e908a0b0000c40b5403e1101451682c24003e000200b040c1c0c0b4014400f502c015407400c0d00307020207034207410740c080e00b0f40c020b554010022031280b144d41e8106c035902c0484142200c0b0b0141d0f6102c8000c082c50400d4481c0d2020a260803400314141c2403c0b4001d52242e03806864004d42581c0030300c00d12005041d52401015400d9888140358440c562103001401c0303155415255041c3c0702d080101e2542404005441e0b107214902d085030304c82c5a01408000e403940a4118140041c81c280d1640109007544100c45101e0341c0b01d46000342081d20106808481806401ca28044a03d03101c2001d080c0b004900ca0f5000d0141d1100fa0b400003004186401e812604003808003a2a0481411805c0e07040e610b0316219070003c84228406900f0014012010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 38376857 1250 38375607 38375609
    0x30a02071109010b0a0513170d080f0402060307080a06050a1e0506030f130501060b0f030f0601080103020a1802040308070f1a0c0d090819020d020d0207080304060305060a080a120306 80
    0x4072440b002c80c1d4905010455240b0a406141c4140310700840c3c3c90815940fa520100018001010311040b000c2e40c603a40c564662101580c1d0f000401c0040780807401c0480302416540c400c0d98044e00c12861511281d0040d40c080c203009000c140001e40384e450100b9142c8401700701c03a000f0801412048080c843c0e44012203101c0210307030880c0707020711424810804003203050107086411510401c4099101401400c025000d840160040480c0410000d90a100d0000c0704000f035219001009042c5501d4031400011940240c081c400650301030082c1100b40030842011402c061501c100036001480c150ba0baa51b01c0d003481d00540e00950701b800d00d043d40b020a0121040e003284007100940c020000031318000c50780552602a401151034820340e142c108c00308010006003203035a41c6072602e83c185038021880e20000d5a07a180c5419400050080c10382c407041c4039000044030002d0318101c03005141400d085c540d040f801480c005058680c84941200001440b40051003001c86843c01002501c0c9201250040501541d9003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 38378107 1250 38376857 38376859
    0xf05040c03050912091503010e01090506040c0f030509070e09010504030e03071a090a0506030f011a0c03090d05031210050a060c1a0403120c05030a0b1002061b0708030a020711 77
    0x41400b00440c0f554046082d0707480202d041d00140c0c03150700e03035004079240c0b0720020b1200100000010001ca45ca02001400c241240c0986600703004580d9140c00b0310094810800115003c40c0d0b0008559010600a0b0011503101c00c142d008c50360845d0741c0361840d401c801030079140494241d664030284810f042d804510410000c805070300600001d4548805500ca40c6400c10b40400c1c0c51401280128131035031211410030042c0401800744c3e8072030619035032100e0311075000c0c40307084070f0382000007c018900c0301c0710410b42d0100144107010f941400d40042c1070100f10005076104a4080c00200801401842c3d21000310b802400c882c6118204d003420b20007030094443c05604070100780500004003100107030311b40320b10100007841101500040c0c0c9a0749400d0341c19540b141a0a92100d04142c140041c45500801951041c5006c0ca000d101c112094800c0c031006000249000005810580c00201194848200c01d40b03581200c4c072900f441c01026481e48182500196400d4092540000700d2005200d0728402d03250305160 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 38379357 1250 38378107 38378111
    0x9010608010e0c0f07050c010207050114070f02030102071209081b0a090b03070f120203070b090d0b13060504060c020606041b0e030111040312110d020d080c130f05040c03 75
    0x10410001a080c90414462044800326403000105441820390640c1d503080b030b401d40e207140c0361003e0385005525082140c020b64014802e4540c0010b90398400d2601c00c140007090f4000380c1c0740500b5038454501003208203001746d03003642d0200040c00024a03000c2040d214842c0c44d80e40c5014450800010500f004061120300505150565030300600c2d9541109100440322800c00c0007a0600910f030101c2d06049a65016101010b82440c0008500850440c4c44800d5442141550072860300c600d0402e031310b400340c85280703500321030407017480c0000512000040f0342040980031001c01c603e003107541e00829910b0889049494549480c174204c0b486804103e103e400000c2281c06000311031203441d11140c444244c860020800c280d083c09a46240c030294490780031201481d5050399201d44a0a0a90030048000c480700d000610080e00e90000110214400e1001c40e069405415210a403210840301101c0142c02d15031030f0034080060002d400740445a03800280366020304062002c0c034100801003168491028101814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 38380607 1250 38379357 38379359
    0x1605010203030a0506180106200109050d080c040905040c0906060509010f0e06070b040b161403010909030e1306060e03190b091203070302032d0402090405190305070c050901 76
    0x103a00802501d41c0701900c210002840d0741c4500009682c210400b00e401100f00b42080003060869000c00002d04404660f801c1d0303464075540512003400c0725000d0782c000d451604402c24112102d403203568240e401c08110b605207801c0c681c5030040c400807520256000c0340c81e0340da0320f401002035403a18082c0800600282c00e06508020301800040d204500019480d02040541e008082d036076920b0304190b50740d094004812040343c0ca400d10f8a01c00400d8142c2d40942e00083c040c01c3c60b20440c2c031441e5400c010a42c02d00986d8116442c2c0b01e051400707005051012818001380c510508195210b08010358030410f0584004100300d440c140001c0d20361171070450700c0b0780240c100101c04c1c0c01104920049205966209045400c0384c0e032469403950400c20070a00c4c0d64940100003041c452020341c10340140d80144900c02042c60f810144002040d500c0e02c0b42c8140414071610317140003901500d40080b48581c064060420740c0c20481d8440e40100360307000c81e0042100850300208919060140041102001e020241d4080c0c01355 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 38381857 1250 38380607 38380609
    0x3041203020106050402120a0b0102030412030203070501051005060d0b0409120507030914060a0e0d0503070f050705031605040c030b03010c02030d050c0403030206010308310905070305010f120f05060f04051605 92
    0x1f4400a00d805080f81d01d40c40c40100d00e900c00c1007251300405829080911590182c41d009480303910000c029070b8250b003401c0104082c2d290080c00e1034101c48004150178540300150b6480006004100c1100d0b0b0301c140c0d01c404140200707903008401202c0540c19035445076610f600e0325005e01103d00d590042d0303603003076200a001000c0d0f0700c41104442681c5e2240c14017060380c0d200e210001d00e55055103103004001d804003046030b134204240383c111002c0301449102a00d00c01038540b030a066a503c0c2d0300396107440302c000c252002c001d5800d00c0d6000030034034280d926000c1a2035607220007103425203541041401c01a40009000c918200452003400e4104442001d41da15003072860b24000d550304418040a03151580010710150b90a1285098251408001c681400301c0d0001c004005d500340542c0c03096583c21402c080004a0080c442e205403410780d0100d0002c40c103001d06121a22284428144045500c2d004140301c02c80407440070000f4a1040201d000c1d5010545400e281035030034000394040c0e041c0144000c480900c61 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 38383107 1250 38381857 38381887
    0x31a060604120203010b120715050309060708090a0b01060807030c0201091a06010903060c0c02090a0506030a170c0f0303070207050603040c05010c0f0b040605040204062106050a02090303041203020106050402 91
    0x40707030303021070703903100151030300c3c00000c0c01002d2804001ea4001d80c0c50840c0348220300042604802c03102070300b0302c00302041c040350804e40b041d10084070b280d07000c1c2d003040d000119030340e00904102e030700300c0790b01d004a404440c000e60b54112626000e030464404110748100300541c07103503d8054205403003070340d1000f80210717038650351400d10115035001500c01036850320000451030391244444c20000d40d0010340034001400e0603003020f4820316061200303030f004101000000b00a45407902440c0c0c06070700060002c01014843e600c8005580108080503404214108295002d61204115501e01e0415180c0503560301d0802c1b602c00391611005500550240d80d081c010440443c00000068080b1202030074069030180d09417515492403503200340000c0050423494140002d002107036001602c5184242c400300485030301c0f0352415480710740c1d240c031031140300c2411000500061640c0c1c0049400054005016003000b00a60010741540c100f07400c0444403200e420795420504d17030309014001c020901510218034101e0307480f1180c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 38384357 1250 38383107 38383109
    0x10522031409010c020d0303020918041131051501090e07051303060903020d080907052101020904140a0606080708061207050411130b0313032003070c031a060604 71
    0x1d503150007040d401a140d000d000b120000f154010401000d0441c01e19000d130094104003500c502982d00034088164849a000616003d6a0000c5e00122107103152000c00c514070070301403a61640e152207112204510303c0340658010704262000c602040e14030b464a41580e000904d1340303950b4100202c08030f003080080340c042980358102c041450540da0780c0701b00d4507500d002c1d103ca07503100402d840e20300000a41855030100d005580040541e0b1074454030f445040e9000c2d510380ca0342c041c0d1540301e0140c40c0c40001403813800000c0007550f4001c03000982006600b80010301198074003100b40d01122071000810582c0110380c400c41c4081c1100342007a8515085c1520028a900401041e03079000c0c1d605051601c1611004000c0030009040042052105413800c1100b11203507001000d0f500d411303165416000c02c1c1c4548680680b48540e1305030b028030244010b2900c0465900d075200c408440c121810307480501c6021428401407601c40d00466031f0340c4005146103404101103001c1003506544c0401712040c8510356442c481128 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 38385607 1250 38384357 38384387
    0xc080c040f05060a060c05070315060e0709060504060c020f120c1306030f0b040503190519090305060406051b0d0218010804110411041e0311010801060c15020f070501052203 76
    0x68148201b9280c84c1d403400d607450f000503045c0c00201c0300c072513000d10540c2c020300e042c0e80502054401a84540c00700340d800400a010f8640460401d100600101d0b00c146690701103180000c10307031118810813401182601066009002c440c1d000744e46c0585407418543c115010308402500104010b038030f0b5460b01203696a00c03034402002070000d03501050920100700281c0d030340202030f002036103155804548007529a038031050038140d00030784101342100c1c094029500c600440790481c01a000d660344690350702009007402040c00400002c42c6e41d4150840740340c0000391041010380200183d0b1007229911980c0b5003400800281d04100d44402004001080001c03081d800748815140890380c0c0812140c0c408140c02150450b1401009552401c6880f80366030b020042268000d00c030311313901842d0800c011030703800b5000d010b10400304545450440000352850100000001c14071401810280b10000907056980711820035501c50f03450710284400e80c1019075141811310114880c5000050b03c66401425003038400d10b00c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 38386857 1250 38385607 38385617
    0x7030b0604020c10050f010f030503190c05070f03060501050a23062b05010605120114040603020918010e060702120d0b030604050d090f050109210c080c040f05060a06 73
    0x821850744072501036424507003120381601c00e0340041c49401030007400200c680c44001c050500c0001401105002e0003000d598129010718900382d9007121211000141401400402c124030500d440498420b2000b6000b130b095981a0030705051071400c201003034883c1a0001031003007002ca0740411012071864210407800080c00e6182150751903041c0058414050000a142c10020001c07200c01040d00344c00c20065000b10081c42045166290142202d050086241300d4000d0300314038006100c0240340d01c8683c01e891b18003c3c8007160329500c070340c045905110150342c0d0200001d1070101140124100f0b01414058002c4940201418509600000d556164442c140c84c1ca661000805094079191608000e01c004006022149a0f0502e4a08985d0b141d079500150030004441b0440420890304240f4081c080301d5050b034940c402c1904201000311606a210b1600c40704e1072a496084000601c210140c200910b22400901480405801070100741c0d0020703c0c19203141480c08080003031582e1140b5010301922280e2400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 38388107 1250 38386857 38386861
    0x812040b04051009050301051006140405100c0c0308190e2b060b0a0303020d02150c0d0e011409030408070e010e040605040c091404020a050906090a020901020109080d060e0c0c07030b 80
    0x140d038201c110345c002da9055401e110070483c88046400c0070004450f075030740e51642d0480a81c0d010220500490048960003017084c401001c0c150301c600c101d5401c03240100001c039841940d0340d0744c420706035010705641c150340e042102c01883c1250308180014900d0906584002c0951005c40c04003c011030580c18588071200d013a0f05035001c0c00751540c04000c0d117507806003005400ca07459050280d80c13515040301090052040f510240c0b049540c0b40105805004603612407814486445808005130040e010700b210950758a14490391604001251a8010149080516601c50801510a0070403070690480d000000c04400100000201e50a1081c1d009030090740c002460386491504448050081d40700000d0103080480000c2f002088200d110b00a500c200c4200300c0d030640e00d000340407000d042103030060f60140039040018407640054006051000052000003038600741135075021801e800138005d04103c00d40d1100140010100c44e00c0e0305400507040081c2e00c0c185868104101d680307400d1400014003200803040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 38389357 1250 38388107 38388139
    0xc06050a0f120227150403080306011407060c081801060806040204020f04080d080a0c0804050c040905011506021005071407032106080a050607031802150405190812040b0405 76
    0xc150340381c4e9010340310307654540c82074103c0c0464404c081408081c031484090f9007410707002c0580c41c203ca007221b500c03500b05411541c814005640b80b1f9440e5803050040b0904005080001d25544518165000d0b1900c070740c402d03402c0009100c4110f5200c0c0305c41c1c0401c1d0307141880c2407003180d0300040c940740c3c8954110b901603a10300c20184c65425601995124007014428a0300c0c50800a8200408074450403a20204010200144000301c590300410b036000b8055800003c85011241426000b0b240705500072400454855480e55075841e45100951060005811446d007081e00c003111400783c540c210030f15140035001041c90481186491080e404028140901e003507a200942142c800310004a0091070b008024480c2d0710000030f5140d0711440c03412107486c0501c000040c0400d000b881081030911403000070007a003103456801d00607841c80c0f1895103a1608824000050282d40c0c007008040b990a02c041041c1c0b581c0d15141d100c0c1e10b000c0c055820b44904200901c018000505040181c83c210b0320122030042c3d200c00c4600c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 38390607 1250 38389357 38389361
    0xa0f020a0801061214060709060320160201020c03010b090f1f03060219020105010e010b0d020903030d140c0c030f0f09030a06020c1207080415021203090a0c06050a0f12 74
    0x2522203010780d402c12000084640b4070150b075180e654083e20b1091400410080600d894007000c039844000701703004034010705c0b01600c00d41c440e02c4060402d55600641c003101e5902440c40d900441e0020014400c0d030f4800300c04650b41441009010316054009020f440c4407403001418204c8000e00c044544080d40000600c1086e554007040f101c220303100c80b8aa1541d8032410410085d43c4184c44907182c10348010f07000480103205120f5581200c0d0070303107503916190742040b84025480e80911004c1a06640911015620760307001e0004080300c40b0f1030035000411400491106044c3c0400803c802280002486059940c18010084131040c007081511190780d109420441105401603004807034061003030104440070080540e0003040d400301448200c400c2d5845c0c2d0f2044130020f104816008180310010f10080080c614110b00b21070725802c407801510001001080702d801103420850707a0191661250010009200c3c08201c1c04018140a24003149011012b05c805040828084429030400054181c90f940041305a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 38391857 1250 38390607 38390609
    0x20102030d06030506040c06080f1807180e010617030f030a0603080a021b04060302010e04020702010302071703040201030b010509010215090309060a0504080708072103030908070f140304080a0f020a 87
    0x19110400c8890740341c1c213019a4444c0e08403030403180003480420202d00c05005620799842510604104186561458908a801003003c58449810f100340d00f404902001d0386035041c1540e459601c0000782e0b04400403445400c0d60900c0c3e000060104e10b038080442400c0c0003108441d0b800ca00c003800540c3e6501c881d21110700802c0203030b1000e080d2100c0460903c030001d0303001c164410200d5100d521040508010000c0000319052444002d020880d243c0d032030100c504064000d41035007401410010b06200f500e480c2c82142070f56080402d0380c13044002040108541c0c141c481c01e1541d10003881d000d800e107940400080d6682014034091000382c00c03446c0000d211160200122680d119000c1c1005403a0045084040c120760441d00400b8002e0103424404181d40c0700028a14081315a1002c1512036610441840e0f88018000b10040d010561968850b0300407505180c0240041881070760090700c51015405d00010f04500206000000c1d002004200070705000050312044840c1c104030b0700e003c032402c40d20001d103c01d551 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 38393107 1250 38391857 38391877
    0x309060705010c18060e0918070303050406110a020906060304140d0306060806030a0302030a1b020d0c0e0604050c1e0d05071110020408031207020a0606081f060803030c0702010203 79
    0x100160240401006401a10078180c45861300b03031109146044c188101103c90240200041c0001010840b920344001e0098204980340c40c084d02061403800a1410000346070000c0e00402c00c0003c0800840ea800307101708880d01c0c14000a0640042194001070000030045c1c541e40c1b24402c04000716003070150038040d681540202c0b8044900d8042d10346400f0303002c0c02087c072845012600c0e01d00019420305000c601030b00d8107a4958013031807030f142c0c410740140d03440d00c01455010640d01138240310000580300c00590580c0c2d14050307414001000d191503460052900010f16181c02075090070305008602c503005058503402c8000111440500c960001401503c1c024020072000d0241003005005104e81c010403120340702e400010a8030500000a0f0100c4182e10031481003980507441002800c030340786848081c0c9500b040d2548140c1d0002c0d841c0f5191001610090b4104644540207043d00c400c1c0c001c4120000040c0c0c03107013000e0600c80e42e480e01c0740094403408014100121500c0019215007168424001c540303c0c494 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 38394357 1250 38393107 38393119
    0xa0b0618010e180f01060f0f56031b0a020a0201030b0102120711030d05070b0609070933020c060d020901030204030506040506011404091e14190c060c0201020304090e0309 75
    0xa5075a180c40082051071249240d803801d83c1c08042040311040d503240c0d0115043c901d03649d000340311640070281034518528444022031540c881c0c001440600000d1810040c96101d0602d03100d0a0200032040c2e80304844007000440e010411807218900d4001c0382d494402502420700084543d20200180d0400c180f5072125102e800c00014403408000795401c207400c0261f0305400b21030000c003280c81d054480d031180020240c100801e020004501d0302d04040c400b58070807800d20342900e80c190303607010584841805132520b0815410480340c0740005000001c8034503c00410348003c100c60044000414154800c00e9000341020340c00040102041c0d020b5011580115400b500310b0340d43c1d01d00f5041035900c440003070042c2076242036044003603009440c0a000e21840a608409501b0700d802d000f0b000307628600304228044500c09143d44140910017018000040750300426a8a54013007a9149000c080c8820541c01c01c20034081550100c0004d03036400020340f02903503941000000c18101d911061803035809150440340e4002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 38395607 1250 38394357 38394359
    0x10c02010f210207110405131b03020d080d110f040603050604020c0706120f02040f05060903011b020d020606181f0b0d0204050418020102031603050c0a0b0618010e180f0106 76
    0x25650f6006080d2030b070041502040c80c03205c0200700015504295001c42030040c0301c20001c00400d1440a580400510305200c560106a0701c0e1302040b03c04041680603601100041410340c0314130b80303d0250b034071003800301d00380781c1c3c98200c60124070001c60041e402802c00b059039400000381d603601c50368100c0f1080da582c401100c00296940700000d100c107030000a003800301350600d0389217028036501d4000d0b1000d881520070540040e03420700060003c1c80e004844a02e03850345d2a28516160403c05c020344030341d015041c1e0f018090358121000301034a42400605407a01940c14400c5c24006052103204854200010a03000300358401e8a40c0c010207000e13081e0700b103e5a10800042c034002031480f245d00920071074405075800d212a1003e112940743c800000d823000303030240c1c00c10004003886035035034264480c5040c0b007401e00360b0900040342c0382c00c1e160007803c1d8400c4611051a40900076136281c0134003000403031800080001c00e9981440a036014024025010644620642940d210506d070709109062504045c074008002007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 38396857 1250 38395607 38395667
    0xc0803040c080f01060506090603060103020d0f1a010804050d08040f0b0709050405011509030206030601050408070305070e09030703020a0821070c14030f0306150403020a08030d05060f010c02010f 86
    0x84241d803003007699612400d20324885040060007010204c5d000186031a0500040b081030003900c1c1c0c8008e005504140c0e00700200b1075580a03c0c0300d0144c481009100008442c00c2407201c005031100c5182c0024148a080380420000800000d0071404c054a00c2c40c10070402d44641c0b42c46000c2c0c8180b548010241c80d905020015410390001061089070000c650601699030f8848558049482c5407003e03000103030b0700000c1480542040d100071a0004018504280b900c2da031060001d00313085440e08200c4180d00031800401044802200494200f6500e501451404505543c0655a46240540100f8617280415800040d600b41c1420491003540008540e40d0341c070341040010711000894104482880c1c06400400d403205000003990b901c54001d51040340746444010030032001074034440c80c03019004403c00c408001a00c6461504000f000404000d603190300c02c0e40107400a85400404907030181c44208400001c0340e0b4011075003c0072503020308284410300c40c3e844003280c584490b070280f40018051315001c4154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 38398107 1250 38396857 38396873
    0x7050a0506041b051f021207080405040c0509060d090f0b1303120c0e010e030c270c070b010306020d1401120302060c04050303071e021306090f0506010203030c07030c080304 76
    0x8030754403482c803003040c0c100000303c0c2514600081c0925904109000d50080c14480900c05d071000442d540d00480d000c0c0d08a8020300c01d01a800014200e800d40b1004c1000c129130b05050152810400d460b0a00c00e082400500100300c02c0d018052070f945002e500c5503440b40521a500741c603410010703001440d2010380d103400c10144110b48040c401c00c80001c0c2c0360085003026075a843c401c0b0300c0a01030569900d6000341c0c010300119544103107070b260160306024407030900c2d00385d603103120350071607120803807086040d24400222822070846401404010011820094140094040c051540c1504d5001c0300060702d5280100700c0310000c1103ca4000307100d010804001141c0401f4882107070000310b00c40d0b1f003201c60036603840c1c516503624069803180070f42540c8180254000180c04a640d60601d44080441c2641103519400051800941d03292240d8000da64440a0001e069103006420312068040c60a121078141400001d680c0d22004150108040e00814281c04152090071590301c020703000114070b610f80c01d103801c003150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 38399357 1250 38398107 38398111
    0x408031204060b21061b0405040e030d0507092903010e04030c050d2312060d03050d0c03020901030e0303071706120304090b09010e19090c080d0306030201030b030a0c091107050a0506 80
    0x2083d8851007002944180b0006d1a1040116804d080e4906141c90b200a0001820301000003400c540030030300180030603045a00c100c40c400c81c80fa40e220729000c1d117000110b20300810300d0040743c810a10080c0c103021461030342c0003c4a0440c0d0240e20140d56654980c2170407500810b0f5141c000301207016140950391107550010841026001071103000030300c5070511406900d64070038260b4580903030901c0d4001603d01e14108050303c0d2042e000341002031400541d09855001c41c0c1d05000004042a0b0108078028039590500c550000142240300461850902c0f15010b071031000b60b44004460070300201c2c00101c45413110482c45007403501900407281c50b02d4890704144040c054520440e13000f1681900000740b442d1408030007501800d6411701001580201442c0c4501520b5000c00a5404001258002502c40c00400c000c0c546404d89079400945541180300042c240c41c0c085011034820360007103200c113010806106849048036020100010005102520041e01d07000c0c40b0000b0300140034a48190301031040200b0064 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 38400607 1250 38399357 38399419
    0x81e01061d120703050d21050a18060c0206010e0403020c1201020c010e01050f0c190f02011814010f06050a12050106030c0b0409050603120901050c0c030d03020c0c060408031204060b 80
    0x20510582a0713022207c52003180e6603082c2c2c1615140306030b1000c03007481d888260440b09006000c80e400e03034045051029200d0184080707607086d070703582c4100c01c0d0b03140d040c00702d03901500000032420241d09050300c000f582c40040d18501441500ca050700070340a10404d42c1142e840c6084540240607502098021a000f48402c851036100d500c071410014584400c007104a41005190b8021003201845012080310504901d403e00e0307003550740e99404001c0908a103d000d0a4183c40340200c071404055451a00b801e5641c0480050103403030500d142444159580240101501d000d40c01c0c0e410305035164200203014100952029101d20072100010420075980b50062069407004007041c4110746a81061540e140c2482441d180354160500c42103805601c9000280310b081031080807118a584036500090819500c4511000481d900103984171099100b8046060803501c1202c500e42850310f01164103440b803098243c1c156010288000107003c06c212070b40400c0e5903407030141c015040045d003100c800c101c3c842200c03401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 38401857 1250 38400607 38400613
    0x6110c0c0607051f020409090f11010c030e13140115090f0503060411041506050a0f020f030306101101020703050a09050301021c1505120d081e01061d12070305 70
    0x1003003a092400c100d0740c00707660103002459994030340d0702c031501380051201c0240007182c0c082000040c1441d41d4090b41c01400e00461040c0c2d403010092900844607082c000016040c00644c00300e42d008a500144d85941c00407056800c0b021200403020309000400710000032440c19041c5c45e00100322083d400080070f69647d100e4981c29a09901e0340803900550407113214070b6502d580301c0800503000500041d0071007240e41002c0c0c40810442e800310650000c03d0805c0d0000c40000b0002301d01c04041d6980020441c0e05960580051301c0030480480d145030720780c44010080d90144280c00d000b010154440e08180104040c980001c54641a903803800401030380c030604500d00020105200031075580340600c2150712480440d4941c001700c1c080340d0700c100007820740c02c1c0d1019080d185a410004103030312401060002071441d00c000e05400d06c0e4019002d0074410010741030710340c000d503441030b12031882c103a040c02d040c103580007400d0505c880700c40100d01a0310303445000c0e000d0350403c00f040ca17002000007000071900d00381e030b1080c019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 38403107 1250 38401857 38401873
    0x28051303080c0c03160819081f0f0317070b0c03010501080a06050102031e0f040303170f0702031c0b060a050a0306140d020607020a030b010803070b0106050a0503060405100306110c 79
    0x114003103a00a206107803143c2d070030820580944c44948461181161312440416083c10111a140c1c1141607d01a803080030a96840c1042010419261036141209000315400d440030304018649550025a000080c44070b00382580340440d1b002c058003624075459101800c52a02d01c1e00010f143c441c1e17003003842110701050518022030203100c0030303004007015070341c06900442c01c04101140b03160b80c00c0001c851401c0400300401c16504018106802000030398000d489001c03410b014103032a80204000246002e50410f01c042c1405003503540071045034280008118485c1d601d00c001201c10008040c3d00307032450343c031007030004400486940100150040e0000343d101001010380e01e001b0075004a604148059103e0710071000900186050405071101500282080b50342649aa403464510342080e044a40d01e41e0021400a08100705a0907440c05842e82e03252490920f503a4004c05003141c00094100d62081f5203900003c2c1e1180d100488010003103130040d40602c0855480104548640d0040303240000301d00800d05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 38404357 1250 38403107 38403121
    0x60f0207051b04181b0b030a0b0a0806060a05090a0213030b090f120d020a05130906080d0216030803070c0245040303020a022406040c172805130308 65
    0x801c442c0001c403605035203040070f06180d481702000d0244006100101d90b40341d01c003059002240001e1440780650303500001c0c86502840800c2440400f6074852135880c3c2c04030301000b01d0f903280c0300d4800e8100e0700d0641d04440e0340d444100028029020341c00e001031070100240e1000042c030100482072805203443d24143c840040c21000d49944a420100040601503c1000b43c100140f015034000e0103200c24500e407590405000a05a03050380c0155407001031080c0d2541c1c402d01c298007003889800c402880a00082c2450303d8044807040001ca82c80c440945414130100000e12842d0042140da01555030040000b0004000300c85013452020714050074120100c200b11124542e4002c00380402d41c0300c52038980321030640d6603c1e502100039501c04d48800045025040c01441d00c1e40580e4515034290b2000111081ca528009003480b08a81d5401d01000420214403210410110300c81e80058106a282c6102d00884c01010320101002d03400044d01d2540503e07200070071105081206078102403c2c80707560b4a11698407180d0f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 38405607 1250 38404357 38404361
    0x60f050a05010e130b0c13080a033908070506070c14010c0804110d0b0f0f07030606051c02090a080105010e0c03040206040905070e04050705030601020f19030c060f0207051b04 77
    0x200c0a07030074084002c507010045800d00d0141a4091b0829803600c0c070b003408004001c004000c0340e610142030350744038114040c1096040407003403081e4100762201c149104d005111200400703a80c030700107103005c01c0402c03600000d01c010241114051a0860221400ca00708004001c000440c5004203641c1122140e1a0224224041c007513070161444980d590181e0381c4a54035003400100180350702550110116104000098040c11014414650b46090f0700852900340c42051981d98021320401c201460843e0034440c00e0b4010f02035400c020b041c0000b01e000c0b007448400a000902c075640040303911500e20880055503403015040796042e6058005041c1c04ea0720f07404160030381da0001307403002540544248028071042036640d010942c001010314100d22114039007030214084403015500c0c24000350b07000080144e00d58040040035440d1031100f006046e4007409040440d00c4e100c0705a0001c0c1044526000c078010300015400241c02840c000404541d40c07034452401940d01c40c0d41c0180d0008041060480b1801450300e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 38406857 1250 38405607 38405611
    0x90105040312050d06083c060c07120306030201080403050304110a090209151810021c0c03020d0c02091902070203030417160f0501030e01090b0901050919080f07050a060f050a05010e 80
    0x280801c107280d4040001f0900800d10502c0401020703ca17a01085000b00004014013409440b0180600b644c070394207410a1110a0241d03115441818201081000141d0348401d621340e00c2901031600c07036102c0d00c5928101c00400d1010800b03990118202c040800c0b560081c0d40100060041260303103c0010030010700c1c0c10854045d0510740000c010301040001402d080c0380402d00321030308262066030048821804a0440049005085c40001c0c020082131000c040e010042201c43c5015814400034641c2c10392700113440c5c0c1a0041810543d040610b030118010300b07603034040d034201c5176000701901d8880341c84080e100c0e03c400500c10107140310700c07036107815181c00c225410107642500d10012503800141d040c40019006420341d2030540a040d9a20859440820103200c00c490027045140000b04260914003101460000c188003000c00c08a0f01c000303d031000a00d24411240d401d150b10740702c2c07074684003941880d47c108413555402501e650b0030050701110010b40d540c40760703210b054892802c128076600d9080c628150001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 38408107 1250 38406857 38406883
    0x302061806010807090c020a0b250203030f0703020a0309020603040501050a050c16060b062107030b040e0304030f02011b140105070f020606041d01020703020615060306090408090105040312050d0608 87
    0x10507802884074080c103800806040180e40100e41c8c00229507501d0074101402194040042c0b0008890007604200c14a008180018030388021800c50501c41d05015040178003034140700074940d0000e400107005001c2e401002800d034000b02000c1d220319260a00c0d5028000c1103a642c1400e034a00320000341c84040803000d8a1700301000c050040d45c2c02c10310b603507080000c280d43c04a050784101c060048004454030347c810004004000c40c04210b5904040101a05460845203070910603400e00e00c1c80f401c8444000140e400700d9400c950100c16000f0280016581884905101e51014004100304d00030310241459041500501c070f002040199603000c0c0440c0e51900c840f0740344005070041da01080d12890160802d000c8d42e03a10b0340800d040b000274880507600726030254200304c02507080b00b4100640030400c9410300300350200690758980f451400e00c000030755a590052004084100108001419904c03c0003903d0140d0383c480d414076008204148042d116800c5030b41107007050b0341881c2d00440d0380040450780c0c600030700c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 38409357 1250 38408107 38408113
    0x609030c1205070e0103030e030105010602190b061503040c1a0306060a03050a06050303131404090210050c010905010212010311030f030a030f090c0b030708010b0a050304030806030a0f03020618060108 88
    0x304000c0020401ca50140c030650321807081c2c05000c542c80741c040e0200c60007503120b41c40380c40035041070505141c00c0da48168022000d541120421820140e40f0300000c1d55200e52042d05403030b040e41c070701000a40c00b109034204005481c1002c41040708201105001e241a0b4030710050140314078401c0c014002c294481240c2042d0800070500c4250403080c0a500495000790407402c0c0400c0d203d485401081c85c41d004140c98480000d854441001452464141d030800172000f51020f01c103036801038011585080f0003444580c1042000240400320350000e41c443d66849a010009542e1a002c040d800d8408071402c1c0070680340391280242104440c9000508070500d0b80480c0055420220703008402e400a1480168405031a81c85104a07800101a1800d0074040d03d03c03c3c4030300e40c803414403100003810048143c1206d02c60000401150071241e030014192913000d50315280540303e0b50340c2d2401107414000d4440300101440d9250344000105600400c50b03c2c49400480c642d2068200011a0580c0d110b2080c071401000ba0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 38410607 1250 38409357 38409359
    0x506070303020702010e0d030504170307050706050703120509010c0f020303070c032a0c08011104030b160c05060a06030209090d090b030603031312112209050f03071b0609030c 77
    0x28042e4019100782401414000d07a4520000c010400c0402000d20450000d14001001e002c0740800003046501404203c3c000c5060602c035075201c07035961041d0300a00003880400f00700764041502c9a04d02c0004070806110510485c1869524540030b081401090b80c0422500114090420f1000050380d211f6201d9035203000b45094281c038240d6000900da0f1703200c1d69402000d100340010764840e035564820030b403040641030019458021003034210f801020400403501740800040001ca4410407101c2d801c05050f0a548070310141e1f41506070f6640500d80300c02401070041204015a6110607807180c400c0b01e00a403500089540c81d1503400c0d07160941e41c840e040105803900c030309001681480c0082c43c0e002e40050110380c540700c000400403060100c5640170822401c180d503425030802403880c4910390580c2c0b040c1e440080c54403018807018030300c018800001030550307070343d2100b101440340c100b009114000c0201c0c1585d540d4221418480e4070b1a610390403a2004082000002422521550b188403c40307411100c104109 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 38411857 1250 38410607 38410613
    0x60105030a050606161a0601050301030b04080307020a0c08010911010e100320130f06051804050907090501060905010306120201170a0b041a040e0616030902030a060f0e060a06050607 80
    0x1e10b4003500c820f800941c18041000c6803a03070f403c0904c500c240514090000c286890f01d203140f107000000e1403681000018001000040c03140070381d15410941c404c541700c2e100d40da00e078801c07840c0c01c52101d0301824a805e050300000d8086c0040d401940c0240c0a104070b05507642c2860019904041c8000d4500d4200392f8184611168074440c0d804190240300500001d41030700200055040180c0150058580d0040c5106041028440315004807004200e6410140c1c1072601000340d05210320100e00780d05014070b03196130020340348260a0040c2e00103070100800400c407550b142c0400904504245c0150703400300e840d0290108003081b144440d506400d50581d070b10409804000b800207220301c009892205941e4490b0321042240c4e440d4003402c0d0700d0b04001c00c0e298008601e0071003040b00391141c0124401c1580c0141040c40440c0124100ca82d07001e0000d07090210700624244042803400c40c270000040c04091030011107102c90b8286800002c00c0d01c0307012045605580303a54000a04549461080e190705c0301042080c0000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 38413107 1250 38411857 38411861
    0x1020d0f03090803010e070f030c0207260d0203031501410409020901120516050a050d0213030c060801140d080906120402040606090501020a02060d1d070305060609060105030a 77
    0x80900c03031401191007034030b554a541c402e0b0003c0c2c002c0003002c000e410400040e07507440b4844d0160782c03141d440d042c4003141103d0701c0070392142d2590260386800400e62800610314144480455911203100040390000c8918120080d182d070010346006a5580740701804912643c480d200c40035040e1940d04404c910345195446040d49280191101c02c01e8203020fa45541e1813003500340c050001800c007104096940c02105e00010300e038807058580420b46a250909104c01040c00d1510070190508905240340d982d14000c00076100d038060782a801040c28000106141c042c10b00d8400c240c2103e02c107a0000d0b04036a00c1e060242d402c034400b409105020704901c1c404040d50700c0d081004050f164002e5580516040d94240469810303401101241003001c039800601c021400c051140800034051840c01e8103d0740d0030000000d480300200702000c1c3c032501003c503950020074400c0d4800566000f00450340021002d15124054440810744820340d1580a200c00080c0f0381c0c1050990300e403160390169074031450355075100d02d8140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 38414357 1250 38413107 38413127
    0x302130b03120a03020304030215041a070e270112030f0309020604050904050105040209060f03150903040504090f1b0e0c1c050703020c0606041a01050d0b03030403140114040201020d 80
    0x2078075100d0722245215a400d08002070610754030310703503001d81e50380b40504010f403500384c8510030150900415000c100c0070500c0c0303440d2500c1401040810480f2a241d06a00712070540c81d0060355648903024068440304100d012616205100783c03413038020b0b1304c1c0c5e070f8a50036101c48112155024001c9500024418800ca11030340c0000900ca02c000c0c107039403e094440002c1075501c40c0441d0121030b10381d034030b5003448150700c0e200202d00e81c8690111100b09a2030340c3c0388003007074a620b13111a0b8105200807120214071480c1080c015940a400b01410070054079180d07081461411141c220140c403d002200181450725000d40090025610700b861044543d80f114070720061240c0c012500e01025070b0104800c0403060103030740507250040c3c48076a005a2111504c01501e420004060001482507141c00e005e407034003500b0340c2e074a1030b0b50302c2003428000c0d2148200301c00c0201915100200c41c1d458003000401108001d02442680d440c1c41c45d01d0004c00c0110081d00c01d9400040341030f20003a002da4096101c1d502c401e4421803a01c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 38415607 1250 38414357 38414359
    0x60d080409050a02041412070519050409030f170906010311030a0501050106050c1002090307030b040c17100b091e09030408010203010b0705010b0a03080d0218030f060406060f0302130b 81
    0x1034642503440040404580094510201c0d260f00040c04110311440030104103500c40303048a05140701c0b82003640d441c0d0f0f558424429540910a690b002075a00e21403007031094010100a4400d1184548034540200317048100c0c142d141c00304201c0e8065418001c2e8a0329010312030401d034402040183d08648a05040c1008040c031b01c2d80c54030a1481001c0000c1003801901c1c0205002e0b01c5031512854002d668a041103032860340c00b0359081c07050000050360356001500c102104e4000c11902c81c00e0711a4201140ba61030f440d00242d25001c00c1d103001c006e440030b0002d5910820380204004100918185042110412055550002c03031040f00d80c4e0081c0084040c1e181d0350b00007001c0350413a494555180c00403400da8001340e0189180b8600400d090b030501c88203020361b002140080328640c038240d00395501c8c0c0c441070041140000d9061380c08111140c44900001199038004001000c407098008019802ca031381d15001c42d0102c6026061100000d111040b61090343c0035030798010140e603410380d94505400000c1030810841 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 38416857 1250 38415607 38415623
    0x120b0a0f181103060c120105040b150a02030904150308091e0414040209070203030c03130303061809120302030903121f0e0702010c08220302010605120a030801050303070209060d 78
    0x340005030408150081c510b12445209030301648803030806007030180080c8844411403003085640c607141c0803465142d05459007210001002c900701c8012400c3c2c400d082414004101c400511351100c0e980001c043c044190040b50207000321103003c403100c10303150828800102080e030f003408035074100d2401d10119054007284005444500a6000025082e140c815400c0c01004102d48284411f500301101001c0d40400c03107000852031414105d503540940d21000300907142c2203003107450701800c040c4281c01000040c03800141000c002d02c03410702c84000400d16618121600344541142001c0a8064000d4030f100d50381d000051401c00c41420300440c1300d00c000415103030b40071070903603414443c0f8801c030b80240b406080303010503000b1146000c020107030854050040840900c031550041000c04040c1054203080c0f000307000022644200580340a902500c100d80100e9406226070f4255151584005082d604d028020741e40c1d9409070340c1e94401c0c15160b102d000400782d084041080007070300504000d40c1d04485680304100d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 38418107 1250 38416857 38416871
    0x10c03030b040513060e07030201080c0c010906060e0603010f0c0f030213030501060602030c06070207030b040201110309120f100504080708090a090e030403030e12100b04020d020705010501050a120b0a0f 89
    0xd001c071501282d152105802a500d014184170151250140f450381a1004000305821500060700d0044001c040181000e40007403000e0401e482900103982d0300358854014094240ca900c4001d24001040314024069864210741e860701124900501a80307100a44448101d001150000c0300a584070118888c0b440310b288a0000001e002481880001e140c558086c64a8500082c1040c0c10f141014080c003085501c100c0040c0b0220320038481c0785402641c242040044580c04141860444c041d446085a01107240c80b00e10103550300c013203444c81100e600d08040c0e0381d1529080304207400701c0303505031006081c260090200030b00092080d0010942c03444001d061103800380d600d22110b0151741c2c1e40c8400c10701c02d4101280410405401481c20180c00c00101c480e034003002104048980c0d1074070340e00d000c0b01203541c40302a6082d60b5291541103840c0da01d41940195074a508908000d4045c04081c4542d034041e41281c02c0000b0400d0a07804841c01c030b5680312014268030345500d901480540301c405040164246d541070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 38419357 1250 38418107 38418109
    0x70207120501020409050c0406050a030902041b1107060207060203030115021903031406060304020d030e0103060810022a120c070e0405010906050105030102030601050901180f1d060d02010509010c03030b 89
    0x24505081c8103100241c2c0d070314100010042510005000d00490180a000c00c2c0300e060740290a07110102c40c1440d00240602c102e000003000341c21901d00103c110510030700700c0d10600394460b05214100c61003034101d03041c80f580c0e010304130303520840c6101d180d0041e0420f00c01480b481c1c0540300d480c0e46060051044400402e0310f05c841d50803480b401c01d07049000c00d0741d828812000002807000143d01c488120b45031419454035030041a441050204c00404200400600701100c0c3c1c004d074404405440a00102c502c2500c80041c21002940219010f0800340c2c2450540d400000c6c0d4010350690554004004d0b02c04075102d07210150071500400c04403240d900131074402281c0c265000000b80e12070390080c800450b040750241814421100b040e0030107030082e40100304019959820008460480c1c0b800e18000c000c00d404c200d000707804403400390490313581c0c240780250026004401440054044180040b540c0c220386403402004000b00c1000c000034003141080c08424403c0d030003034807130001c1280a810007140d0501204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 38420607 1250 38419357 38419379
    0x1a180a1d060115020a0305030703090611030117060f0403020d0503040305090d1a070c0305091c02090f0702060702070317160203010914070506070b01090c1103070320010507080601030203070207 85
    0x1000e44049a4450001040042e1400140441610280c0040c0420b81031540300200306100013090a820b140d10354945c1700410406501c0280710305040c0a0164036961103c184008803403440107141003070f1040301c1c0407441c0300503000d15080c021031b816001401d501119032400d4826810041064090150501440000d80c5800a481c81082e1169041201d59003e4142c1c800b00f0640103090b400803c20200d04010020390004112040b20f20102c4212159041c225600642c440c81d99000075008041ca40910044c1c2050142c040c1c02a0321030380a4900e80d903602c2d141266101550301c400303415003460240082d03a07403544100406c01001d09001c0e03d89180c0d0503401107402c0d982c0c005001c440122803803883c480018018000d07400a0501100d800d1320300006502c448495610600a031b0034001d50b101c00045035a4052814243d6190f06c81c0c081d40e031580007500700507003510ba40c55034500d011714141c07408500d00081032280da4840d0302552184411501c03440d0044000707410041c8010154440c2d5000400c0e00c0d0480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 38421857 1250 38420607 38420651
    0x160605070207031a0a06090b0a0504020c030d06030602030f01050d03080402210a2301020403030e12071e080c0103020f07060509030d09080d0e0111041a07020a06020d02011a180a 78
    0x204c11550030604100300d40f082261107650240280d940f40803034541c01c0c0e0766030042c4c3c5011600704176000342c0c0f2058682c11144c15407142d40201342c40240f40110000c10000280c0285208910946407079410ba80daa80a0002d400710002c00180000d80400c0040c006190070310b6080c5a200c240c411070080023040c0303000c0c20b20b48031103507800f41e42040d04440c40c00d1690301c5840b04041034000b070100a5081600d1070750098001c81800160900c203010090038903107002d80412500c0020241e60b007030b801030440340d030700440700c0200940901001409004100340c419402802102c01100c1d001c034102d0319000702078a5601c02410054a03d400701d01042140c43c101240c180100702009004803101503441c94611450b40440b2120203145036147d051003103c00c045148441600c04843c0c1440c02841d2180801d03103481d4041c1b0070401c0096125464400c04650543e0001b080d6980b90305a40081044003544040460b0400d5084007190b40310405418540e0720b0b04480410b943c02241c1c00502043c50101110840b222006c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 38423107 1250 38421857 38421893
    0x2070615080c090105121911040921020a02090105060a031103100602070509090601030311030c030a0903060b0405010b090111100504051c0819051302030a030f1416060507020703 78
    0x1d4486440b0b0710340001018010f06040b11416548580c9002e06910780c9201d62480c103c1400c03810418060210002415003189802042000142c1c011b01d070000c0c1a800b201048200508034108000c1d42c03a000007000401c0e55001030640f003941e880d210420203c2ea206c0c103122410151565030b40022a00540040c0d402a40c8440c2e04041c103500b4940028a00003080d840780303210b100040b081c0070341344070085035583c1901d40500d8407200c100e41c50301d5441d246111703c0c4911242c0e4440052142ea40c2e0703038860711210969100d0b520a020340181801003000782d80c4d0038010300c1000d0f2001c2280780219030092801403c03e240b910142c8074140b0044c6101401c660045800307650b5074000d6108101c2400600412098100582c100b403101400e100f00d0040341645071f0074641d10b00b20b13030fa8000708003600c49040c124284182d00404030781120f0040d1400515202c074080b00540443c4010f11949070003075030b800c19151010100395544a0411403502c03480080c084c06050360b8198003900001001146070900c65800b8904 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 38424357 1250 38423107 38423113
    0x60b13020405151e13031a0f010509070e040c0207050a0306060305010b0d0f03031a030607020f010c090b07080901031407020a1a01050d121e020a1203060501020607030207061508 78
    0x8a000c051001c282a003016044442004002005012907140f00b5800410300100e00301c2c4c2c40c5c000c5043c4403401450507403c058107040900c125800c1d004502e101140c420490101d2007070030f41e40c0e210144043d2440a480c84004600c4101c400111400c007684a80b0b04090944100c401c841c0c0d50b50042406803143d0f820645021761599001d01c14000d003409042010101590810b80b00b41e00c0d600c1e10344414034a5040102059103480840e0308807081a5810000004024140c0700c3d1402c0c9007102950301c000c0c04c1810801542000450b440603401594003c0440d800c1c9000180740111b0340d03440101d160300015195040c950b80e2601241c601280b040e07098820062034009004e401601e042c611441e55800c009200402e0380c2800503c025119200818040d1760710115241c01104c2024003943daa003403043c04c1c030041280002148144550005a00040074090075500c201c24162103411015620301e80102d602590100002c90031103486940141035450045200140203214001c42d00f010750181c0d80b101c56a58 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 38425607 1250 38424357 38424359
    0xa0506010e040c1e0306020a170105060f0a0810080a03050403051912080702010902270112030f120e03040e0402090f01030b01140102030c070602070602160e040807060b130204 77
    0x404014060151004041c244400d01d02a0746410030b1440c103014400c45901c8500c424080f0700300e209000340185170700000954880b0000c0d40d0040480c01d0f02012040d6156004000050710b0400070201d4150b550b40c10400b6140c24052076060b202e102001c0d100d10211003c1c1000001e1403481400f0f41c00900e4429503542e51b44070318509103245003600510415503a102e08a407440b00143e4030038058051000d1034240311384142e69032042a40144010040a0340100c1d400c0c4107441030b000103013000401088641100000341c2d0725800ca00828003540180280403500448070358814074024011940d0290041001242c04448008501d0a503007065020000480a403000c4c80704602d0440c1c103c82c0e00041c0b051240d0565032440d2100c04401d94103200d500619001000ca0001e40d9100740100c0315184130302c6086403803183d510440256514003903c030340d00040c007030904c0b80790f4081501c1030880102c820a0003411020744942c1ca82006d281e000080458805580c0c0d007526000d503c50103d01a030004d0010b20041c0c0303031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 38426857 1250 38425607 38425613
    0x9080307140d0e010912030201090c0b0301090f02030609041112010603050d2709020f090301110408010b090403020705100c050f0703120203070506010b090a080a0f03030c091d09031603020a 83
    0x202041c1c42042040c0303d0038103101092a40c3c0030901804884100c1c9540e20303c003d40d401c069004012114014021904160303001c5040c100c81c000460403507508250030003000b21201022001c9001c1920243c1d07010102e03202040210f900c00c0d40c102c0003004010b0003056a02c080480c0341e0b01311002e40c1d01c00c455035040718442c0c2107090b400c001c0e0215804040707014140c11426481002e0240324090044080e01a070110b100c10f80040c0340b4007500d004010140082040202c2150b8000954005100d0714005600340000400396080100102d8003130b0364550001e10005003024100090108656a240200810152a40c0100342c081001441c11030394180a1f200b0365045050010410b0040450307141554401c014080001d03800081050464000c0d411035511044800f001403170b60b4946034401e6030700c1c1c840c0240030404e000b8110044100030b807098400300034070b4415520550340b1130f940b880703000740148000750110303004110560340c03640c407003482d0069914103e0003944450614900f0071087c0d005030b000d200c61000b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 38428107 1250 38426857 38426863
    0x70c020f01080403021011040b0c0a05010b0103020906071113020301090c110609121602040c050310090b06030f10030b070905210604023307060507030605030309060a0908030714 78
    0x315028a846541441c040c1c5029558010a180001e41c160390340c0c1c503901505c5602025180503010f034980895603610321700c01e200e60721017010708244e8640d481d0043d404450340c024400c441100c18045c16160820000e500d032100c1e00c00403046026000b55900c1c10903441e5807024402103000c0c0c018058005048010300f01e008041070080706001d011030788400d040c0801803c000a091a842210703070030003503a81002000c100c088248002d80250054101301c0c1101d940c03074000001c1c512400b080015051010f0313903a4500c00c1a0394103103102c3c135004034003080400c04240c00401c0302c1d40c0c4512031a508041d11666580d80d2740a038801140d83d803000550500052080c0d10780340107035140c01c0d800c03010450019540125059110480600000e2098211080c1482c014549000803880d14007421031400814050300174516495219180464080b840c1400041c82e0600038030642040d40c401800850a05d07001005001c0c65511028002c4107005800340e0010303454004000800d401340c420200016000c0c082070005107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 38429357 1250 38428107 38428129
    0x1b020d020d0207090b0f03031305032104230306041101031505100503091203160f020f0c01030f1d0f0c090c1c0209100306030b07020304211406070c02 66
    0x11500456250010a603001038448203843c04c4480000e10700804200044038202010080f581500000c244001c0301c080b030502080448a05500340c40144545c90702c5a450304442d551240c030814003e01007840720030002d0200d00042103080030035070002c0030344400003858400c088408991103080c0300a0a601075a05000301e0b40400207582c04403405904003000140c8040200501e0b4040107404000941094805c100f101644007900891990b2401c00e100c2102c503000c1410105008248845101c1c44248d100003191080c100102c2c018004c6181e018004602401042d03000e0a00315071501921340c0072004c14242d1241d0040600003c00003800340410160500d030004030618400c859140402c081940400c0403180014003145d00c0c04596104010318100030700591040b2900110545041026550140c0c0450b0641c0d0054042d0061580c40c85030403a9244994020020507800c1c008040a400c04519642c40c0c2482c4501201c2c0900c24009024520b054070840d058000035007021280d00a605000c1101a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 38430607 1250 38429357 38429383
    0x7090b070b1009090c0b0708070804090605010e090702030d0903020111160b0c0a020d030203130c0b0702040608030301180b04020904050f10050406050603060d050a050d05070c080105040c030807030c02041b02 91
    0x1c000c84105807075403a015017451007000c10404000880100700000d45003210350726075111040984407a00ca850080051001e8041c841c0840d02e410400e0314185031461b80c0034030901e040d078019860101d00c4407000000c1c05a107002102035648a03070059007140152406031031200e07010400300294100d5801e100c14506c502a2070310141070400c0102080c00c59011494841000c00350030302596070b442c1d1a414400c481071064000d4550f80c4030744170103c2c500312100000c1803414000c40d010b02180351255080d540f284800e1007a00ca03400e00300040045028465040100316141c028001414030306c8140101701030f60421181040c4079001c070300801200038034407070400c40074007410390b010404c190600c80440d44338030000d481c040c807904000e4803540070080100899891a0760240607200d2040c50f50070054181c1d00301240c110f5440e2030f600004034480905200b058469900914290030705442e41d100c400469102c650241c0030420858101005a12140100040000115501e4901099840000f410400040f02c0c0c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 38431857 1250 38430607 38430611
    0xb0402041202060a0c0b040804060f020708280606080c010f02010b030607211b0e0f0a030b0705190507110405040f06020a030204090f020d14070903030807090b070b1009 74
    0x1e00203181e0100001c8507003981a40c01950b1900303102425a83c5182e81e00c0000c0680300c0300c0c0c0411007009803220141084550b01e0700c44146806541c40d0603601c07a034580c0258034817035021a064117400315000794074602c000c2c00e01404c01144002c985801081d1000c5800c07118103503000d0600c00f415945d022340020505d000754130007004000000000680c40340c40240c840020007072800300c0c0443e40e54101c1880f071300750317444031100f001904950400460000d001c0784040e0b01040c0002031101c51404c105280c8482d13200010309034031802741955120342e415100a80704004224041c040d1100c3d26124140041d500c01c1c0c140c845540303d491038035240d00512519010300b4004c13030801d010b0000117072400d243c9079140e41c0d1099000d038444480701c1c0124028003441d80300609050401c144170007084c98940c028440070038141024480010440391000d01014252405000500c4503c002c00c086407140340c6558100c042450601240707076803903411034030326000b0f98000e8400c000a24180f00008484100031300c0101a00203003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 38433107 1250 38431857 38431859
    0x120209060c011a06040f0603050c0f0309070e0a060e0f09010204030212060f180a0f0809030d0504090b0d03120e07050607080307030615020a0809030a06020c060a0e0313090c020a020303041502010b040204 89
    0x1c03c91440986c0d102e120141511100454604c0030440165001403180c0044240c5916108025a640f03d40910901c2c461101c141d02180e110368543c0603000548442c0c1d078054a13540c6070000009940c070001045407a045d54244004001a0b80301c503055294804040014552030a12008070442c2d03c1020708002d010040002c074401c41001c020601d603d0302034210071140103000017814a4101c0303205c1d20150a41c0740c011145101c5038180c000700580169803521400300003000d0242c06203c0841d500c224050041115418507182c90807203504070381c1d40410b1003010b55091a83d14004a110f5402541003241d110501000700864143c0c540702c0c0800509007540d04c054114040c000c0a9100c900014000d01401c500045080d03142d202004205149644074204541c0c80d1074106003070342c03032711410b80d40d1300350840c2854200488508000207031396061024102c454281c40c42d00d0402401040365011403425402104a180c0260b5401c1c000781c00100524101c50f4030410b413424000742120305800c4103910407441404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 38434357 1250 38433107 38433119
    0x1c0305030f0903072406090c1d090c071509020409030804050d030b0603010504020a0e09090307020909010603110d030c05100c0e090c0f090604150309030f050309060601120209060c011a0604 83
    0x10781015100b950017505000c070000201c1036010741119046540a58100003000e000e2643c0680c2c0304020310139200300c4807400306042d802c00200c0746003501d85840940c4144042c10200d117824202640c065031304000080c607640540c2c003281c183c0300810030a9021803e24420002030100501c0381d810054210316003040b442043c44c000488070302060090038042d0b40e011400300340150145000782d070350703000041171603089160114000b540d030380c06130504030300648003400400c0580d0814000c1c1c1d01540c0d4460500c2c62490041020b101841c0b890703100035800c00c0646035010f4003080040c0700c020982401004007041c0c880740c201028090165525045025501e107004010380d810070703c4291140c5d4862840c856968240705400202c10740190780141504030300035102203807681d4165008200745440391f1030300005142c100c4000d030388900088600c00321076086100020040d6110b00041045103003000001800d0400050120340741e038110603c1d0080e035a54410060403c0d0324140721008200e1403c4411a1034181012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 38435607 1250 38434357 38434373
    0x10b0a0f03020306040e120c071e031101090312080109050c0c300316020105070c0f020907021f060f080105040f03080907030803070e0f190b0304021c0305030f090307 73
    0x18048000c042c0d0110106010b41d8698104513056181e00c400c41d940d02010402d00e003129400440980c010340b0070090300141401d02000000a0450540003021a041ca103032241c858441d02d9030407650411100345004030010b401c0103054401800f01d1751b03c02c891581000000021618050300c0e01d8440340d002d10035810103203c00501201250314040b5030071006034551300d01950341c040c4102e8441400c0c0b000b01c1000b01c143c0400b0208074880400d9070090180b0f0b15907040c1903440a01105024090b50b16490109000d0300380407440315001000b0348100d411b0206000c02035222440e01d481500529611040104001c0d161441c200c030103046024020005420165291140c3c9a0080d00043c2403100110024900300c80c14490040110303040601190b0300d18210000900d048112501180b05d207007d080300030b0b11828050001580d1003400d0960101150070f00c01071070038680005004a0f4088844160694042e01031444d0009480c8262145526418040e00d42e407440c150050001006a005102400104d081307a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 38436857 1250 38435607 38435627
    0xb060904090804050306070f020c0a0b0409020711060f0c010614010c0b040501060e04140607180b0d1b09030c090203040c18021215010e0a030b06060a020f0601060c0308010b0a 77
    0x11a0001081071071031800d549a8000c6500c000d42c94000e103000c02005541000e05d041c503005143d400d540714080c418080200c44080c5006a40920390180018807080c482580240703540f50240f440f03401c0c840800e00c002400780c0e10609040d80740090120b59065a05401d00542001d007c8440803041000488400200070546541001d0520040000401c050040c01c1d40400080d015070086001c2d0341c5410b0500860b0f5802c01030660b511480343d41300050f160381c41840c00c407801c40714001903001c1051a180103198140c015000c4050403d40e43d02c107461084a114140c2c441204883c4c490a011a243d41865100c0243c540d01c21000c1c10300410401001541c7e0362070031001e480940021000200c01e8019820007400b030481800c50390410f82082c003140305804d24002544004c00da0b540800740510304140602201c00b44001801400300070f02060130f603d401400340080d0161403040b0360540300008881858290b0a074041400700d000e840006040c50f51266140d80074014682440d8039264290704010542480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 38438107 1250 38436857 38436859
    0x915031209030c0f0a0305060106080609010902090d03080a110313110109060225090e0105090d14030a0c0212071214040e06041a1201060510030b010804030e0d06050108010507030c030b0609 83
    0xd012804c0700030341d14014042c02468228040752010340e103420004c0c01a0701d00b5a4494400c652200001517054154021182080005400110410401c1c5e9040d03422038801b0304160160b039140da0441d5100c800c081c010350310404002c000b0041207011414a08c1c800c1b100c11007102d042001b5000140700098001070113000f01360441050508c0605840907003284017000b41c008011031410038000e20080c5405420160288140000b0f40e040c14074418002d0794409005002d09200480c2440040c2d107280080d400b080c442c01e01030064555025150f10307441c0d072562100c10700305d90649410306a000155801641e180341040b105207820f00d083c0c1001501e00c0040002000203100d1030300c03452a42801401038408022910303020340428008415545071502030305c03441c06510301990100b080d111161344240501e062421040e16418415103840d1011142864124401600400b4191110001800034403c3c14000c04c01c1c400005541d04000d00020140c520078104d5a041508201e0340b65801e50b0b4540441e007071044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 38439357 1250 38438107 38438119
    0x3100509010620100e030d0f0c1202090409120203030103110d21020c10090e0c07020d02060c0a0c0306090b060307060f030b12010504080a120e03030406020c0c0915031209030c 77
    0x49007045041c0342013400d064146031142400c4007951040790010150903950711900043c03100c041144c203104122840500400e00240d001c115500680905900600d010300300030344041400e0442340c5034141e03503040d0340c2030b01170059200000400038800000308500d00441e044170102c100c3c08a580b94012000009000c804607002d0814040c420b40703008120201c42d46c0e502515000c58590090806003c0011521a1f4029203440340005003035039800303408032502c590b401000703100711103666000c1c405075402c1844a10740c01e21030030070035401080c1c2c1c440c0f22000a5104a0700402d410107680341640380c501c0080d007814000e612070401030044682015015150504610b00010b0a039809000520700d1a07407c4c0d541520303546060144020f101d40a002000c2040f01c070b40f03980083c400d580301054102c40841c0749001051300140041800500c5580040080c1080e41c021542c06000c0f20002035020f81047d50f040c0450440c0341400031041c1018006c005084288541c00d50901030f0010100340c64000030a601d40c170483e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 38440607 1250 38439357 38439407
    0x3020c0d1101091202010f0b0301051312050f0c011506170f090a020904050309040b011407080d020909091b04020a020613030c050304090f1103040f02090a020d020c03031005090106 79
    0x307003095001000c1c1c2d6400c035501d1003900c1400000a8020280d150b54080060705201a03625941814000d00d805100e00801401c0802c03405c0e203450f50200c42c11041501006000c01c4182e00740740100c40940039a4007036000005000301549100c64100343e05510403c103100d600500d01403050014400e059002c003071012031002917510000030301d0801c0024a802544240008184030a009001010b458102c10540e020400c0c1d40a603001521508480303c000b44041038100b00490008000d036014024017413841c040035080c0010400050303a4107074120381d106688d40c080c403075011011800c0c03108400450020784045180601030394009444541c000c007041d00294a95904108251061900041154100c02901c2e2035a844200403000381180103030040c0c1144c141007a03c808074105008590040da4004200e8404480c4e544c2441140034000707080c800495800d0000060904a80c0010050030071503802840c0d83c2d01e0000b1000d5001c140310b4006600594504006014940d00104240b41108031054145210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 38441857 1250 38440607 38440637
    0x1e1805060f0f010e03010207080d050105060408030a0509010203070c0303020d08010e0c1204020f09040506040506010e010605040e04020d050601060201021c050103050706140c0115061d030c0d050a0206071109010603020c0d 97
    0xc1c0041c62601903100003001c1c014406818003a001f16419188188032f10799a807400c0280720b0145009182c0142c00812201804600840080c44000c506006680c01e15080e6100c0d0461000f50b0f40c4180c0140e080020507017051070307210303000c18054540008003010b103051620709603802d4018400e403141000e20241c08942956240d0145a0030118010039540c25460140342050300c2d00c0e0192000c0382c0703034400c2000200b412001c86403640d060320000d1342c6907070800e803034604070103031000d406801a0b8200104801c1c45011480c00d200b058007900c00e54002580d2001d0030051000d204608500b4448034030320f030a005100140003c00d11200300c0d00585001d0f04551401e0603904803910511506580561030000c40810b2040150002400ca9a1544600c1070008165005400444402c1f49094bc16000350030321070b41624200c500543c40381d00a03021945002d0f02e81c1e001c00d64551181c6c0c425611a14408402105803034041009800f43c14146000d50400948071406681c6a030240c510000303002c0b24940030301c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 38443107 1250 38441857 38441867
    0x91006030e070b0f041a030402090a1e0c0801050312040e06060919030303050403110a03020703080a11060a06170304030f0f0204020904020307030b04060909030c020411041e1805060f0f01 82
    0x41d0100780c005a54550300030a801038150303c581b0946610034401140c26550101c5201030f248501c1e0050003141c1c0340c4e40c40017905001841c64840807548444c011389d460840b0301a51281d05a151010340721440e2075414a010036143c9401c50403104a100320403c014060150209035482d002035040c0c808a4070384c180300d0002450b0381c0c107000c3d5510a104407000d0000615038140c215900441c02916119901d0410004541d240c1000c05409000b680c00741c0307404c200141d50000103080c017100d41d01d01040c182620701200c5007000c200751152507003030307440300300c24030150601d414052080140d0800941c9000d145070798169103c49401710141aa0003000103074815034440b50129141c101006000310354a160207403014000780102001300b0f000714601000400c1c110058854070160540644525034603030700b01c1d820000a00b03001c00403121501001c2c80001150000b0100204c03014038201c801c00042410100e119016140001c0041030a40c103000500030151201c2d0503828042c0c00a40d9400c14229844d001611 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 38444357 1250 38443107 38443109
    0xf09040b0d0803040b06060304120e0f03070602070e0604020304210201090204020c0a0303050a050c0403060b06040801050903040305011401061b02010c080307110106050f100c030c0b0c070b06091006030e07 90
    0x1c0c0001004400300c040206600c020b41c81107105128640032920350b581031240310701080301c0c0140b1014103001c1840000d402010841e901c014001d000c126808084c41c00b00b0300f40095035111030b001d41d10910007031203911a55a40a90300c0b10094030110b0651038551218132502d09a00105080010945892802c15101390009450b480e00a0000c0d03665594203500b182d83da6210751400d0740007a2422020030500c00c031a0050074001d40285441c20709081c2561640c0c002804a070b04000d5214800300000540c0010a00505225074050310295464a1860810900356400b032030000c0000942c1e4001448065004000c05040302c40f04000445460a24030058a40811090029110750700c04401c1110b400c0c6d011040c003a02c00100f10080c000e803503482e41400390340d501210029912600c840c05e1446020b104003480030806000f40340c41d86c00c965240d110003800308010b0700c4540340684001195002c1c010700c0b807044c503007204080c0d429104510b886007464881141c140260810107031290740070382e00d0720820407003c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 38445607 1250 38444357 38444359
    0x1002070e0115080601170705090427021509010207031103010212010807060201140618041a0106021501050111070308031e1005030708031206040903050705160302030f120f09040b 78
    0x8541e58582c66020080101002648001400000000c006510907080400102c0710000302030341d29210082c0a032500c0e00300046094100b552240c24904101203a100603001c04503034940320072500300c00e00500503038285560038038407205e60800c00441c250b41d00084213000c60360420010440035440300300007800391252112a1b4050144140042410000404d0420885449400806c6072004654518514140031941d81d079003c00a228210b918a07400050140e11511804c95201030030f8141150003806142a04580b0051340700c8500a0814041c0301240ca014081c242003d116444c400050b040c7e903070106000003052124040003144143c11082c1143c010b086044404a01c1481c00f0a1504001030709031103840d00c40d214250700005d41c400c02108a40342419078801d01c54859071100280320103007110b814103e081150400005e40801d5007130040c2007010b071120011303801992560041514080f181410360456401c00d880031081d101c0d5190440b00c181e102030302000c0d00e500340c1900040082141181803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 38446857 1250 38445607 38445629
    0x6020a03050906330f0603070507033011090a031a010906050604030303090804050d030305250f0305041b030b0108210d091b1203030e03070201050306100207 69
    0x100260680641185102d149000102d0b20181d540003e8840c9242d400072040403540d0414407406044481603400101d150405001c4585010800300400c4490740211003000002e50301249000805901540230b0503c40341c002481c100380c29000d00c20303158209240500e01d5070365039a000c0c141c10844101c0160380e8000002040c00614541e80d04040c4e51020041c0d01800074101050000b02c4c089800780300b52026920041e00e01401c0c01d080d82d030140c005180f030200c107564410007444002107640d5241d5011014901c01c3e80d0100f654108402c0400108911403c3c00344801600e06164030744e5507010407154480d40c03c81c5000718940e183c41c1881605034401c084c0c01880712500e140301000380a030107942c1324101c030289011100c002c9480b40840c2401c2d01003080c124000402000240ea5038841394111602e1540680f5505401c0d400c8280b030a080d4444551005911650b600c3c516010305425124001221102030701451074515181d000a15501c00200913a201300c044000300c616451003001a040902401d20300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 38448107 1250 38446857 38446867
    0x1050a0e1210050906042d08181003090201020c060d1d0102070c080703030503011511061603060801020306130504030c050d05040509061c080c0a0f1415101404090602 73
    0x281c41d84810740b6050403010203007072038082941c04000040766841140c01c01907018048080540096500b0241c3c03880c03100001400002c00702269035a4000c0040180011100190944d0700c0c0501c842c1c282600841002d052404100d000944d07004224400088030032940d040c2d80f60030195160004040e5a080c016070030000e8060010341d02c40c150300030a0710724050443c00109503a03840032a592054580801000a0000d20042140c0c41c5668508201000141052002019000a03051a010301142d98410449900807108403250305071240030090074902c0001d526500e0920045001203000781442d45200380c0e540001030a240c4900c9100007090789c80800e4454240c14408000c2c202e070894081c02e03100d01030840c0410700703d10741421b0701c3d5030b00340c40300903804501c4109441d1440075400090402c1c0c001d0040211000c0024003d0348500c180c584200301351803d0310407103507030f10746000ca0840003552680031790010701c10085449049403046035100f00401145a8a03c0045009040480e000600e09070021031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 38449357 1250 38448107 38448139
    0x4061205010b091003030e06091219020a060e06030103020d03031107060506090606120f040501060b04030b010f080a051906110d02030403080f0705090904020609060703020303010f1d0601050a0e 85
    0x3141c2d501c02401c960401180e122001c00c440300c0f41d102c0c1710082c0490664001641c1c036080c120f02074400002c000b405142030007202c107400303820004484007422485100b514500c0440c54862070050282515240c48110090325002040e8607100c103000181c0700307107d5202c402c0b040501c640c01811200500c00e21241c4c46603202d2030400080c1c9000e0701c40501c84c071100400120300381401c41c2607501140001010383e4603900c400c00c2d8265030080160003030f201135494000c08030343d46c07240c400100000d51003120813040340c1d0f243c90541d411070328040c0c0020405800980c8808013007500054191914400240200007a03140c910784040182200890320741c04a402088400302140c043c2c1c055440f0300c1c040e40f50140c0d0341d9036040c01107032500d60071a41c16010138401d016400c000e0402e081c1d6542d00500c00740801e80751040d80d000244068015080490041c0c3c000801440354141658114000702006a4008070700b01c49401c140c10401c1004000b40d040010109006d42514442e000d2401c41c1c08000d00101d5441542c51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 38450607 1250 38449357 38449361
    0x40f0e090d0311030a090212060c0c160f06050f040504050705041401080601080112020103090611070c080606090705220902130501050c0309040207080715050f06190905060406120501 80
    0x4600c00c203980141800024090701a005031111060241849851036a07880800801000280804e80e08403841104001c45101e0400c0407a0044011000c4c2a480d40c1004200e01d00d44041041400114504094204001c1041888840c143c03138581c2051500e4000c95030080106005a60101d50703c24144001d0025854104004100750f42c010990481c0080d600001034582500644030382d0300180e10f1400401c12a0700c10407415008a10515001c611110342d40c0700c0400b42d80c0000ca400350300401c00980e1000f00600584201c0c0100722035000b501151030400c000a800000082c0034009000c000110f00002da00c50f201102c5104400c00e203086030503612012124000d41000c0c414241c0300740d18040c0031039298010340646030311542d21401035150003e0407043c000030b500031090880323052800340410000910905000300300c80c4806080043d0383d00c3c4c40701d60300b0000c0802610031400b40c0c03040144c05a0030720b480d03c01c020031b5442c400d101160030f84541001c50001d00b850ba0155522800c5248150108003040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 38451857 1250 38450607 38450611
    0x506070e041113170109051e010509060106050a030b04110c1e19080702180f071b080702010804021c05100501080f0a0b04110607030e10020c10050f040f0e 68
    0x41d60100031525000d9030380704262042002460989440c003004000000d0600a100031078070101c4004039104031580d8405103845282c942261220300c050040c80c50420092190a41c4410058000d00040d49422005851480350004d060101622810841007945a07034121040410014543c556200010f241442c1c03911403903120940200620842c140e0401400a00f4103c07100d070400b02100584616982c0c408180d20002e02241c02008041030300c1026200d03680a540300e00e10100e00c6214618103034500400641c0c50025074110000c00300e841c2e0000c01c56000a40d141c07a0350a080092a0b5221400003940e1242a1071015400b0103a01a070320081203000315a52031b403000700d03d50610281e40c0320050f26417211781d4005040d808d0f520408810002c078448031103154100e401002681202c1c0c140c637011440341d0740003070f01c2038010600310300c0101c0c0542042c1450201c1180c052001c0c1050304000b000040aa540742c807951f408014011611808494400089034000c207441034600c8400340d61151406595001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 38453107 1250 38451857 38451859
    0xd020f07020924030601050102031c270b0109020a09150306031407050f030606100f050702040c030501150c05060a1a0a27020f0406050c010e0a030503061302090a0905060d0506070e 79
    0x800f000380b016402d00280c2503058072416005141854101079101c0610500d11161064503502c0d44852401ca6940008149541025a042c412941c0890411080740d11069201440144c8100719a0764810352000c00d003c280c070302074083d040d10040080000c40242141d500054402d8030311004500c800310000411004842d030598421044010110402d529904e088541a810401001c0440d52203403080180c8000c07401c06080490900007a81c020408840d00f507014000420340d140014080d0041c07010000d0030081c928540910040825565a03444003809400d4080161325604210740e0741c02d0140815001c42d101516148003242d681e0841a600180c071000383c01010110900c44000800034022104442110807009291915082e000c482940c807c0c909802c46542e07c1d03489031001c0c1c4c014840443e401d80a40d03203894030380c03c0010401c1000a2551802441c40c3e104021111407602c039403401c078003195540040054039170b40e960045801c5080b202d40080c8035004103070030406521b820084c6400d070403070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 38454357 1250 38453107 38453161
    0x3020a020907030b180c0a030c111006031a0601090b030a0f1a0103060618030210050d140601030516090510050702090108030309060c0901200708010c081b0a050d020f070209 76
    0x59011044a440b5030a8981c2c080c01b41003082405641400b0303030441d0004464615000390740175a02d1040504218200c080c0110050321a03400304140b00000c050710030004211035008805040180019004c000c2600c40d50310115004000140e1035040380d400049007042e450b000380900e12018400ca40701c5911041c4035404a440d20b940843c1691041000b01007041c0e90807006a110380c219001c104e07400c281c01e154402001420000f00d400f400c0039010311140c00c81c075040c0200540c03d01d50b0001d425540014800c09d10f09000c0010326000c264024180c5040303840c199242002c01603a1481101c0c58418200c0181d0408210000015445400402544510003e40036641030f511415400c280340c0c8504000d07940050014440040150003400d058910349114070215001e80c1c1e5104040c900b510f10303000c80000410010401c01082000f0310500040503046000380b686801e02086000d402c600070200d0000450f03902080d1501c3e00e100003c00c503608203400503d080418500841031250f41081444040d008039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 38455607 1250 38454357 38454379
    0x18021308070501051606020d09050d090602160603020c0705060c0601030302070b040b0306060c0f07140a0b0f030c0711061c1a0a060f09050907170718090903020a020907030b 76
    0x1100400d0301402c1d02d605948003032800c0c1c140520b050102d0820070098a0f11a0b080081ca02d41c03200904c14098128410b802400908003c0c860141002e5145e51189080d50015200012070700b040f00d21100648621b030500603140c4010350040d51801400d0341050ba001540010300d030810311400141e01b41201c0c480e600b222035044e00c030300001003540110f20030a142c440c0144046940c5140040242808018400444d51200b1f80103504a00d00310b03040e030248118092090800d008d40c11701b0b0f800749014052508200307141025444800c0d00c0303440b00038100e10292402203140300411032014080c00004800915007a101c21a0314800601244a241c1c00764480385000000c90740f03860075846820181c0001400c1400c114644041610400ea51450708010092102c101003995960b10103218020302140e41d41c000c1c110308030a181c003040b00001e000031090055030601d5800d1560a204c42c6803e0f556074807030100309030505140a0f46450041d6100a60280140c0f08101b5401e078560320007080d03590101d841907804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 38456857 1250 38455607 38455619
    0xf0e0307050304150c080406080c220602010f0b0a030201030b03150a0209040b010309020d06050a02070c0b03060910081209060c15040c12020a03020f03070b03040302010b090a0e030a1107180213 85
    0x80d0f02d48070001000c506c0140420800240a040100e80c80070b034091001d4035000030b0711290f0b914810b110002801380300640505109e01c0b58240700b04101c00101c41800c000880d1044009030501f81140b20080c10140c542c1c0d14802d2989007030042c440085802041040c03542170025103200a5000001240e000b0f500d04800700d8480d40c8a80600754019402074001101c40d619900c460700a0b010042c030040006400f0003020300000d01440c074500080855507500e5440b03060840400c004404090704d8a130094910035418042c0c0380010bd00185901060703080c480d0760301c00d0300000c0340c0c8a00408987e290a805a4400395215950b26201c041c4558031031408244003d0321090700c08000009040041c0d00f00384050800c0c03006081141c0000ca0642004046a9440e5941d803001030196000f1901140140d448001815050400e101095008003400d10240401c400320381240b5030320b004031090401002000350f80f03001e00c44020b1101c503000d010b9149415207004082c50344070010350320241d20034010100441f000524 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 38458107 1250 38456857 38456867
    0x304050c0105030606270a0303260105031203070201090c030b06030606060a020309130207020405011211060313080904140903070b090c010806061b060a06051206010e0a0f0e030705030415 82
    0x11440000300140c0c1040e1500042c48900240b001c682e02c4400d00c02d400411042c2d070303840c42c41e00055100e60f03244c1810f0380a100e2b905074003103000441741506c144803400600555801064400c95560290b8109449580b003e1049015120080b8040d10103900319034080f0038045040002c0340315403802c0d01214520340304c1d441800124442c0028102c01038005104028161a007603e0b1103842103030445016007807008580000b01140c0080e440001c48051560303c1b0806c20404515031050748000310f6055081d4a040c21144540c0100d0200040c004c4000280202680e592540b200300b800001840c04813007460700444040d0b03254032005064603560103150002c1c0d002c010018880e45c0c9064107030740f211140d4403002c05010458009003105c0d0010403100701a1420480d0400c0b50358460f0407a0355020918503c2c04052181e21b642c01900708030942c00c05001030101c5400c036502c4c903403c03072244d040c0000c00c207004405c4000140707484031079119507010004012090002c004041c0c820b803441c1f200c0d01c0080307015104081d55 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 38459357 1250 38458107 38458111
    0xc02061014010210020f0c0d03020408030712110a0c05030c090108070506033301120b0306040b10080a06091209030f060c05040e09010903080a06120f0305090d0501020304050c010503 80
    0xd18038014003014000404070615200325008103004840c000d0008500b40b0041e42c004000b4411000300100f80d014a07500200001c2c9582022401c04519141c1070082079900c030701c00e4000207051103101c0301e94180440c1c4a0080404001c6003941070b41c01624480ca4616512400c5100c1c141c4030348508680124130f0b1600050340ca04840fa0b2070024000e0500d48028050a80c2008082851101c00a103401400c1c44000280c0c1c4a0043c1040700701e00154601000540440441e0650031000c601d05620008036031000101c0d59000307074200c485065940c1e68514409003c080c10b41000405008580070881089103a170440b201462060b15091109540542c0840c3c4001091001a00601e48108044040340c10396106461350495442c01514182d114000d10f1000c0c4426601c131807050395a801a5806c2c1503001c0662504001841c1041c84403601c0c048100300b5032113001c240036002c00f4000d290b0307104140c0070b4130450b07402840c00361144038110b0076410514000e4000b2501904c840c0125901071038079620800c1124 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 38460607 1250 38459357 38459371
    0x4050c0f0702040c0509060c0a0506011505031503071703090f060a0f050304110411120a06050a06050d1b0908100b060712111204031a01030f24020d0605040c0206 71
    0x25040c10442d4081001402c0c3c048404814408104046201c9403a564003c00d000d400200082a10012914000e4a41070050f4410120040e100700e0340a08c140d40b003812660090400b900002042c444240080e080018a912548140c0c4890051882680c008006082d90400880d03100d010742804074140f20782c502c41c450422000556881c541d804050040307000d1074000e40140c5003000400d9025000c5012035071400c031902c04d10440400d000301e4411101029641c008a004010b01c989440d01d400306444801c10700549062142c003168114a06107558003c400d6400d24100c1c0d000c105203468005015501103004100042c042d03003038040c1031119207010324207144801500140c54140b068484000601c4101c0c150000c224644034103840f80720b4100303c0d1a81400c0702c42c03001c80d40c603840c5d03180080480900c0b00207000c0d000707448001003010078840218400c1542c0c000303422070300020300180b0303d5040500c980042d4025510108201500c00081c2d804941504d1040c4e80400c008440d030401030f42d403403004494031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 38461857 1250 38460607 38460637
    0x9020708070b0a020f030c030103050f070311010e13050a0e07060f05180415090b1309020d0b09070801050c040e090615040e030c01020f07030e0a031703180a050105010504050c 77
    0x200107144400b0840d4001c09640b00182080c2c4001c20850081c0d0080d0346480000d5408070040c0b0170703c4400d11810702441c0316640201240d510303540d1100510400e0030b01d407a040c40107854010185880b075080e40c081d05182e07610300300210700c0c2003211440244070010407401c042c0302e2004041036442c05405018142c070f4558a842d420102c00e0348000c1403171100000c031142c00544910b000c6804000b01c03015032002e05a90500412080814810321051030510395000c402c645c207148910001da103a4140481c8501d80102c940943c6030f83d000740d81c52511030300341d001003000d40c40c00c000c001c40c82610f200540103645201040c0d1040e0b4940f48507a6039901029a450703826240c140402541320315282e84149004502c80c1d0503282001c000802c02801c98009100c038900110340000d10408050703003e2801c140340307071080b102ca88101d4111b07190042e140010109802ca40140040030412404000c5506032003450803000f240c0003540c00d0319240740641402e10650380254205000705220030010001da0f0b00c1c0d440a41c0e90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 38463107 1250 38461857 38461867
    0x1120305030a0207020402040b07051e011406190305070e0f07052503090f030c08070503071a030405120408030a080a020901021002090a0f1d0604051003060b0f042409020708 76
    0x2910080d408542d040341c6c001d40c02c101c005080d0f54444054224680a2030182044e11031002007181410011070000d000381e454400c9010003511000da071290025425682082d9600041d007210851803600e400282051207980700c00100c0c1c0808100071031089114100e40100e0b40c032101801da6242c0501d620604402e1400607460b0b96401403c224420554001c0c40e00703c02140d070700d071850028105550000d881303543d0f44110a101000082280c00000e04090b8000c3c01241d00d00100c1c40307113000007100c0c1d48448000000c0805c051050410400c007100c2c002014140d0b17202c2d44da01076030341d4070350082003014080780107040050034038446442990300308041030f005018208005c4000100a6220350986584020148400701e254400368952902503c05504809141c000e625004107659500401c0203200303905000810640401c050048021240d21410116a00c9a440006013107281042212500b10f1b01d807014003200d8100c184104a000c0680251811615444041010680c803a07007601506580c07003048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 38464357 1250 38463107 38463121
    0x190b0f0d02120a08040603020405030111040605070305030c0705011404060b010815060a1205010603091403040f0509040809040c021e0703020307030b060102070314010504021008060d120e0315010e0112030503 91
    0x40000c0d9402c01c28007541c281c9842603a030b180b016000354025100003940441d080c880342c2824441d08003080003c4041c18103240ca44413000f009072150a10080400c0008008a41c483d4105400c7e50703130165000d07000b84030408a043d00118840801c03141502ca0303500b8608c01c1c0b0340d0f6500481100d4018a00c1e066007010030f160000c2840b8080d84a502c40c3c10402000080040840d0028441c030741c02303407002e6640030503d0085802c00030007820803504140b003541c000b080100003c40c49032500c0d104558052f514098141d403107061031811805500c5410303410609128800701102da01095007580b03420200000020750342010b004a0341d51901d07003c02505503001d8002800494800340c0c010742d00c408140b0403100c1c0203441c4e5a86a00e0308501003100c44882e0744034400c0c0011841c1c28450358110a42c68030700110145046030025220010f444c0001c4c0c50030120281040c00d8034441c940c1d2245018000e000c4503424003020b140b016034120300f40f040400072594003001054075040540844407a0350155115402c1d40c6400f9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 38465607 1250 38464357 38464369
    0xc0703120c02100519050702061302011803080d06080d0306050904020405040c181515020a0b0406022110050d0b01091a0d0809030c04021e030402040e06190b0f0d02 72
    0x1c500154414070102800016807400380c0c2c0d1042840b05010407030800c002180b0016210080d10b180d0030b540100c4c0c2005146079988501c149400e03024a421040103040c000310300d10000c225000500030a030001400342031728152b50840402c8a420204070303650203106400440488009002d100d5004c020500400c01507d0b2940090f90454056117020840b113603946811584200300300312100481c0d03220040002081d048140713800003441445905180e00000701c200944550029500800030110703800030034103000c0f60f507065940c40d681e5070008005e40c003040242c005000c0f0080f240c400700401c0d2500b0224550a00600d00d0305510380c4815800480d034240000e5038041c0074501121f000c4403080351400c80060761a5450f8044217400362180135a00c9080030107160070325084c01e02c1d841c011030040003035a039400601490071882c0c0c41240041c0f40c59032117610010f0f01401e4500d20030300c200d119900601100c04540301e860144000e107614200000d01d0710300d0070b000007600c020103030320343c081c10720000000035007814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 38466857 1250 38465607 38465621
    0x3030904050a0e07031a01060f0c0201030c0e1003020d0e19081803031204050105100f0b0904110d02091c050606010f120507020618070308031b0403060204030f03080c070312 76
    0x204030200b0340d40f41005045250005683c03040d1002c00741c540402c1101e40d0030300c42c2a030240c440c1d454180c1e00c000345500301401c50203e0b12070084c1016a50850b440c805031160301305802500c0004d01c0c0496810b00c0c01002400ba411013444000d5030b0789403141c4072810380c0c40000c2140001200484810148001c1d80fa00340711500041c1c914403400c6100c10b0202c0b1155001e01c014844c00b8a0150000a40e0a2600b8040e0031078100a160844030442044140560413600790f40744200d41a000306c45585804c5100454040c203000404503c07028800310300e42c041083e0b103070040e11403060141d590380c03d65844000c0c1d1148003440c030302016040390451004a440c551042c5052b810451281c100360110042217400301045031b10855083c0010b8101200307100c926031010900007501d0507080c00800303003c2d0464560f01c141c1d100c080c11245000004c0c1c1c040c052284042c2c03090f10b00941d040441103444a549051640c6880500d100440001e0600c1000a060702111016500001e40503a0380000480d41d00b90f28400820403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 38468107 1250 38466857 38466871
    0x10e030f0102030103060204150503070c0b06030f0a0b0108061308070303050a1e0606020c1017040201020c0901030809010f0302040602060a150b0a0201020903060604020a081b04090c020f0c040b0303090405 90
    0x5040240c0e449410900041d402184030311001652240f504c0300b08000700f0441d08038001005800c20a0041681d0b200d10740c0c200c2c4076080500c1d410b4646690000030300d0814640d4960141d0302480112409004100c4d40440c101d1762120f080c0c0d4060750300c2816050014280d5840102400414004440402d02c20f42c0000e501c51b000030070004050065412a0800041d02d150694007251141d1090000540c148042031044500b510310860b111702d02c0780080c1171110752600780c0c010220f8180009095a01c00c0141c6903608402800d4004256161304114480794445404140468014184d40c5401c9100c2e20843e001c980e2140c0c003508042d1103070240000500132004154600b00290700c00400c3d5403800900030135a0300d019400060303441461100b814208640141042d01c9688103005946200307030030400d0f455104118049424129884281c142900e000d980c20424416142404a01503036400080300c00000d14400c00305c41101080008000564918802c060b42540050082012500341900144d0304151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 38469357 1250 38468107 38468113
    0x919020705010b06180f01030203060604030204020702030309060a02030c01110a08070e010c14012003091e011104060c02130e10110918010501080a05040b0c030601020102130b040602101a010e03 85
    0x380090000b42c6541000c0d0f5050421030345c0031408101c502d0601c01070045d0132002c2c2000e40c2540303080c2d0001070b2a030090f4130001c0e0241d500000d4100071942d003031088030041c4800420b86034485518031030080d80c82d0440549501d480d07180c109004201545581980c3e0914001d507101c144568520380e088803840c5000d60313500e0500091091100018903941c0c410708400300850300000703001c5403100764048429071040041941841c20028000b18000105150302220116151034001e50a03c003050ba00500b400c9c01c1d20903c005022401051070360780b03c081e6000c0075000f104e540f41c0d480240c03d40c040c11226180701803007855218001200d42d00c800c80c1c00002070605007000090030201d000c40821202e0611010b4685000400f1005008540e00040600d07080103410f0350030061890583c1d10601034401c050030f402e1050078040005440340c0c0c0300750111107001140201c41030800d580d40c4036225160304030303018800240c011044441c00b02100e5118444041e60810721030003413154614019603000b04d44503121034040c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 38470607 1250 38469357 38469371
    0x3060721020a031b0807021608070306021606020301030623060d141f0203010510020f301b060703020a080f0705070503040803030402010315080d030e1c0203030402030c091902070501 80
    0x401c00e105020380d00c4d064172151090324060303600a080c800040140407140c0040d5900f03100b5400001246010780c0e900000040c0e80700540d4001e00c0d01c246c51b03c2d4000f001d41d030000001204214094002c0030900d840300000140c0c00c4c01c0c802200d9204902100c0031504805c1868400000c40c1c080150341c00700007011b00c141c8000d90890050104c1d20608029040e001d0790b00040100b140342054840c80301c001c1e510b440a03100e03200c120400941c45045014020240095401c501c2d0515519040c03042c982030b11501c0b050790344070106800444143d5041c4245000e03030181100181c41c4500a00031224080056900c480b280e5561881c847c0d58000c5c040c00440c10420284a0300000034403c0001340041c0c0340c0c9000a542b68a01440014155015982105284100307104100141e06000070f501e4641225401c01240035040c014007149080d5090340a0441e28007040c8100100c190003100075130085009609442800603508244055510151564400c00700380700500368206132107601030180039120344001707d420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 38471857 1250 38470607 38470631
    0xd0f020c010f061707030f0803060301060b042903010f03030333081002040f0b0d29010306050a0f06050f0412080301090c09180e010603060207080903060721020a03 72
    0x11100b07010a1152265146030901c114210140710303450180112008020b00d504540c0e50820500e8000340c0108900d40100c00316041e82c0d170a4200c00b000c0c04207e40099110b6655040e074808111000000c240c0c1c4189028080420340410b80403241640c05030a60480780b64550395084008201103031014098082d00c154407448043d0180840e00c141140b2071000c407803a42050341c140d0411035003d0605c030354984100010040300c01c00ca21308004441d20308411a80354090041c0c0c41015024a240300d2003008130001da0b0140d92443ca64910422282c00c1ea01007014a45031410301141d51210b0150311449001e400c020883e06100c5c02c0100701d030403082e8071030360b00700b990300c0d02c82e079420071400101180c02060100061001c0c110b035100d03404841040303181c03030402c0c83e142100f100c040044e042d81410321140c5801c2c1c0c0c9080140c00350880d200960b07200c44210354540b4942403000e003075007201c030406100b405081e021070b02c550b1080f0308407001d443c0904802c00540c441511380303800a601800150061507142e40c08000b039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 38473107 1250 38471857 38471861
    0x5030d06030503090102060106020114180a050601030b0a06060c0503070221060109021b010207200301060e100501020706110c06030a111c0b0111070b0307030612031106010b0702060d0f020c01 84
    0x1140b06200443d1a40500c41c00a03041481c140c00c80c0b070440e85042c0000d260003e90b144055000401d48040d80300c5000441000c0e400c04c44118405080c2c0d01c0b41900001c108103082803824407901c1020000c10841b62103010844160144d0080030300a03500078407032a405458180010300008001c0c411300c10700300b040400c0160600d04242c3c0f0140c0d40f95408a00b0500554100540400d41c00d5000000c610706031142d5524180240769041d81c00800904000d00c00b0700c0c3d04c0c2540100c001d41881000d2030740d107181441401c000e070f0000d40180381c0140140d400c0014814007401e5445004181c84001e020903045075000d010003908002e200c0542d5507110501c07050480b4080d4000c006420b50b40c207018040c1400c810340a4252880c0288243c1001080781005201e40808500c400c240c80c1c094001a9403a15258011000340141e81c02201c2c00100307031186241016003208205210f540e00e14292403803a81e0368031007010207000b00c04c0c000e50440070802132401070002c1e0713a019a10782c2036500001030070305403000b040c182 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 38474357 1250 38473107 38473109
    0x50403020d1106070f060c030f1103041103030f0c160501020609030d0203070912030305060a0e06030c0103090f0512130803090a060509012c0306090c0612180a0b0106110c011b05030d06 81
    0x41d425603503165035000c2e141d00d405150612042c03a01d0178410b044150b00c402b8014400104083c050800a41705100c49a400703008031024040400d0305140c4412901075620303113417001e61401030a0751011110001d0b0755400410305d03a100c1d28054003d1410204032281c400003a61000f001001044040d140104441ca0b11005944019020741c0e4001050b2400c01c0c24080002500d4010340038600c500400c000c00c5607000241d42070525002c4ca40400c0b610440d2400340d01d00d00d60440000c005c2c5c01840c244c880a008602d01812400d070481d001480da881d510305c6040e13124401ca842c041d0300013120340c500303000311030064009001c04003040c0740c44000c01da84081c8039500c0b410322950021115400450100691078200300b035a4000d4422800303003801c60010070000321284030f10600071005820708000141101c065030b0091064070f03458010b4501d0341c0351610317080d45290300c01d00a2a02140d40c0384403106400f80002400d205201e41030311389500c5250041d0010350081c031501011a0944000c0181d440300001d84e0203250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 38475607 1250 38474357 38474363
    0x30206040312030b030a08030610031103070305041205090307030f14010c020606030d0503010e01060c150c021f1401091517010f050f0f040803100e0411040b01050403020d1106070f 79
    0x140c820b28034410020282d5003406001840303584000004008140b8180480b80c11000856154010800442d407e6005e4419903a0860794a50040208a04c56416410803442948249030035400e4031060403003504d00307004010011f50140e000b01424800a04403a400714403050291000600101b2a900c3c0d60342541d85440c944001030b0005011302045007001c208400d07280480d401c1060844d1305103e4407110401c814030500b01000303424612102848140c4064414541c112001884881e20500d00a992071000c5980112041c861480401390642c861261409207a860354102c0c0c4103034a8203100d02c0c0035240741d0210503504082420000713020241c40c009004039144003000410f0110007580c4542c00c540d4014800c0081c03075084000c00101c480790b20104c0780c1c4030b58003800d800e8498903030740340a258842164210400280c901d9080c081481101102c04140c107100321000e02641c2c00d00c1004580d180a0343c84000e4010410400000000d0040001194904c5024240508140aa4582d1010b07121003400039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 38476857 1250 38475607 38475623
    0x50d03031107030c0c0b070b0a0510030b01270603020904030c020301020904060e01051e01120c0905090f0a0c030e0a02120f031c0c0305151c02041e0b040b0102150408040302060403 79
    0x801304202219410703900a00881d1061400e061041c2c4a488c0d8018000f42035071002991040080c01048810001c0405141c00c031b04800d40030741e100ca1011180c2130b103250041208922810003445c600c01c050258400b9241d004e06204180d0b111540c2c15aa00020a00c0881e8155020f0081ca406c2d5243c603c03800005000d41d6100c01040d5141801340900e494228101c401a041c6401e5034110598120b0074000f9080310b91140002d805140c888112402941500860743c04aa92030a0141403480b0307402c0940141009601000f07224400c54017a01250100020700480740c2064001c50f0143c50524140402c44400d41c00354ac401498401d0310b00e044d03601100e034820080d400760f00994040b001c240700700c4403101c14504080046082401942d51518152980c4510070310400090340300d41e022513091180d003103034081c100707000a030000f48c142d140318296440480140c030302d0300304c0b610011701d0075001d4112405010703009000a010700c403d0507119558001e10613981003d08000000050716a480280000e500400007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 38478107 1250 38476857 38476877
    0x90c1a0901080c0a0f081e0703020c160503060a02090402040e0109050f07020d02070b0307110d030e1009020a0b03060105040305160e07020307052505040e1014010b0301050d0303110703 81
    0xd4045000a042d9822026052002043c40d90b004135142100305c00d1403c00c082d459448030300145500101100c01d08190003d90705010842ea0903030003910420003e03009950b1283d10b4031104428103141481030030341c150300190205140401e5540100760300c080c054005482d00d40c41d0f80307010701e0350743c802ea00c048c8296513560108180c5440d040002c0d508001c2d903201030b000407000440000d50340c0681c2c0c00b404501c04400800f164102c2c0c000c442801001001c9001d0700c038160300d555030150084c80c00040001c020701422030b460395078100600c038520200e0350060070500464189030070f03011184c02c0280701c68140001048080003040c0b003000003400c00366040d58110502c0341401c4244a2800780500711802399441404001c00180303011071490b002180301c1251884100342a060040b040304268000c541003898007a00b640b0000e00462606108221134109110980c003001d82040d01ea0400d21070011240010300060080746460440009214040d00d8045010a01020b0300380c032650000d6022402301b088040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 38479357 1250 38478107 38478109
    0x10e0409050c1807080f180a05060103020108010603020f041202121b0a05010504060c020f0102010b120709050708131401020f0f09030601080606061b120403050f070b0a09030204090c1a09 82
    0x180c24940c03160040aa83e8181001c1002070000b40307029010a0f0900003070000254401107100d50490341c1031960044480e04080c40c149107803190400e000603400101660008105107000b4000c98881603400da00044c0b40c24903041401a145501e81004c0380c0c070551841c514650488108003160a450350340e840100b00030340b10010440b44801e16840706051040030f0104129a0342c01950201030a030f010703036400101502a000403030061403014000d95100a030041c407044200400a17081c0265800150100060344a61005440f064411031b0092003101200c00d030500041d141240f50441c03040301000140c102952200b601d4181e40014840016400000c40d100b901e40c5400c001031130040070440082c110501f00280451807610604030054482401013124042200080001e10b2810201805164940e80c40c1d1900c151914400203221a0b10f10408078042884c9660100711004a041c0c2e8403002c09491541e400e10000e408024015199014044000100c03c4460410a01d10342080701e1191790700d001440c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 38480607 1250 38479357 38479369
    0x90d09050d0c090504060902040e030c010b030105012403021204030e040b0406030809060a0504030203010e25050102030403060c1e031e06030c090519090b0106110f0601050609010e0409050c 83
    0x1600c124480e0026a03103080106601008060946024083c041400e0783c1e076041c13010242864440007504140b400c038103051140300c0800580341c2c8545045c0240800b00c010030405081c0c074028081c074101c041819406516001c64240c0c404601d2007241805414407050018000103842c0440b010380110341c1f00c2100000c00c1c5420311072610143d01c00c0718100846419501c0c0d92401d4061114068054100014146002401217040d50000d503402002806088481e518103509d46050700c141c41d03046c83c00000c0c1d14082061603e0010b0540c0c2c0180e0045040920f9a03c0d200c4c0034141d509840810f00004100d4803181031003062840038003044036100895030540407004021000031440c50703940260b00d00070b001c1c80082e02c500d8580048403403c800105050b22140c0c0f01140e440d03000b50301d81024030300e041610800c1120a500c080c0c1250360740c0d1104402690a41d16080c1c80b41d44540014046d608a1001031142c0e1412202400d0540010f24100d891002102d0200b0102c80702c00f1000c1d2040d1340f1480c501c61082c41d100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 38481857 1250 38480607 38480609
    0x415270c020303010314190303150f0308070209070c17090d1208040b0108030703050f1e040801051005090f3d0503060112020604060e061201091b030b0a0302010c0c080303090d09 78
    0xc2402487c101031911154207040045000040426880700403600000c580c02481e80040c0c42c100909405041c0c3d203160104060b0300001080b8020010701d80084c80d03140c052004c404050ba00b00060704d04528100301105401e501841c6d81c00c2c6d212400400140104889141544050002d038440c0700b45810281445049400141c0c0100600e51041203c00d0001c1ea010301a1480354103007400f030640702c500100e140e008000c146e41c1d80315503070303040450006001c4005421690003406d0b10b680038455680c40e0030038004011000c45203148402c031a00c001c28203400004801c20303c0840f5218407244003222082502d10340da507501440d841c4006140c00306109074541407042500501200d018070f001300286a010501f20301a5106202c2480000088071201c2d460316002c450b025210300c80c41903490740e11390300e86100903c01200041803005140403d003094070701074440c0c6081132600405417800145550700442e10102c8039078040b502aa09034000148038003003080a503002d4000c9030060300510500c124010140c003e6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 38483107 1250 38481857 38481893
    0x207050a05060a050c030c030708070308090105060108160c021e0a051207061407021003020301060f080105061617130501020f03030712230a0209010306050415270c0203030103 77
    0x5440410005542e511003118000b4400b402c02c140c0792200322120703500710301134250010b6035400001198020400c0d040b005020040c4a525140349a41b2580c05d03031400c03034104859035070100d04040007250010000520304600e90410f031400d520b050405a0104103620700d036101800d884c44118980910318030b0710350781542c0079110940c0d08080c2100850400e40e5190845c0c407580c8148403c01c00c940d4128007000c001c450030315030090001040c29003501ca00400961003489034000103030400540c48002c522034055181261401440a070418140c1340100010f04440b100031207442d815001e0001e03603c0541005040c080c07800c1800503035003038a0200061b080010210510b84c81c0e810401c20030a100d5081519440d1194031030800143d41c0184c584001d14020320300c0428100e4600000030000d80d004550004c1105600c00c8c1d03010302c0300700e90b10024001515000c032000d191508001801340401c020a80101001010684848034403044984540088841c16150400103800c000018014004280112680b80341c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 38484357 1250 38483107 38483119
    0x910030605120a020607030c051507050706060b03090c1c0615082e3209010b030c030a15140c0403060b0f0f0d02010207090c02100b0105040f1215020c0a0201020705 72
    0xa0b07134001011407040d841c0084c1030002800000701844030030086484214101c901105c46420088000b4080e034019410403900346040000c04900c0301200b0040e00e014510141c001c0a0000da0322080007101501d13401405800c455615895000c9030440c004c4c0c4410b07070504050300d1012801c110301d690600076652090304200e280e40c142c841e0000711030f0031007944840140ca000101c1c0c42c01032003040b0250004201030f141040d00c004290700f4550348504d10340c3c0180c440300001c0141f21601e00505444480e841c1086902d5001483d0f1200454090a01441001480e50002555894144c0320380000b2038142d03000a81108041001d02c01c102441c4108064a031049905100c0340c22680e00140441e0039404805001d894801a940704590003080408041d0048400078000200010300003941c03039030340d880da4903103003400d041540302c21b54003030001c840540f25051685146030381000740c18080407411000071a05000d42420400e61750480740701030218003100c403019007101d02940c0002450002a600442e1140d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 38485607 1250 38484357 38484373
    0x80405130b010503011203020705120c0103150f031b0305070b0c060a090210050d090c060f0e100207060809030f070b0f06030d1b050106080601060203030105130204050a050607020402091003060512 86
    0x303a04241034034111007001c1c5513846542c46c245412410030300c0f158006500071420301c0782400800f1022490707005120702aa0100000d498a0b80f40107107a40c81407045030440c810288040c0007144054070490806919004040c080c0c95495546518015a03030340912644136010510301c510000c184065a00410307940d0081c480441560001110f85001c01c0114041c4100003610303189910040d0841c9402c1c98024240d0100e25940304000b44c0a03602c241c1c15403000481450496004e403824440145000c4950fa004045090800e501580c2482020b4401d088a1209201600c03220a03040000d111451040c281c0400c1c909043d524207104a0020f0407180c402d401c046070804c10b1903401140020340d0300b40c44180701c001f09000c0c01d1007401803d25801c850181d015800001c51100e400100440c100c40341074604900104080011000300d02450084660102e0409000c000c0d17031900801030441980000c0005103481d0404000454900c041e0300c29101081c1c44000410041c50300014200c600513116024000300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 38486857 1250 38485607 38485609
    0x40201020c040e19110f010c0b04020f0a12080d06090c0804120923010e09090c06211501020715120f1506112404060f0b04020403080405130b 62
    0x4044000c105030140f5030b07903481016808810003101d08003100d100e100008035041402c2083d540361000342d17094024100c0e0b040b150704da0b51040d2080c2c9030aa400c15007101e600e459070360070040c5001914684540c01403840101041000500f5829081207214040c1d0560311616003044409540d81c80d44140c00b071618000c281c004180c0c001423010b80c05503009102cac805200c000c150503142440e1075000182c00700054860701049244003840001c82e0442603c800000f101c030708080101c1032600b2140440c098021541e0751001c1e0030f00101038014032458144186410000700030000b0000d40455004039070b910042e41d062550758060080700050302885840403400c072947c440140858403480c02101000381d40f08039001154921358490f1508501c41e202e9410241d0303487d07000400080928000400398058240300c4c0742a07074908d826201c200c90300b05031085016a150345a80c0006d12420488100039902d502c11071a2580d900e100500184d4820080b0603211402c1c401401351383c004501c85141e20500c0c250800103070f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 38488107 1250 38486857 38486863
    0x70b030c0319020c030f09031b10081e040b060f0108070203090904020406050303040810060b0405010e0d0501150b070c0b0c1c03060302060313060b090601080c07021809030a1704020102 81
    0x48561506000840005401642c00007403180300010340c2c0c42c0c040850800040c002030402090662001c90403242e0140104282155550001c4950340c0e00c12014810701030094021203100b9030010f0003901d030051604030100008103205040760708a0740709859401700100c62034000300d400da1030300c1c082ca0302030104c0c98142c001964034031410140a114040050000d021595150403071405040007074256034982d9a1803058540ea13000b0488407a20b82400c12401190140107042603c08449059503011a00b40d01c420512440018031442500d0310754032030084158039000d141035107004007424481ca42d5540d010341003034600040b141d0405440d942c070030400381d08544000a115102d03070a924622510003a1042420b070000c010b241d02c02500400044100300e001854800503050060040c10280200c080361000c0200642080341e00e64040b82614000c1443c0780180406040d50610191001c003102c134000040240201c011280000c00b9400040c82103840c1e9440001d41811f0000708240003540c0c2801da0010352 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 38489213 1106 38488107 38488111
    0x1903030807080912040303030207060f060f080f0a050604020f01020a06050703020304120201180b0901020909090c0111120906030c0d15030c060c0305070803060301140a02030603070b030c03 83
    0x81c150b88013040881400400807102c42c070b881d045580a400175000804140c1d241e5541d0b5514a4007544188200e01c040c5c24800c072101e94907490214510b10384005051681055041001d41c0b200103400040c40c40d4001b58103c074021b40b4901c042004030320304003200a0142189042c401440341c1681c00d54011402203005440d910001c40f04030bc0309900761181090031010304803140380f07120007161224005542140b81e10002616002c241c00008100780c0703098801541c1504005501c0c101d5607000388051100350411005070120500d0440c46050038094520351902400c000400141c0400001045a0840000b14410400b5108121541403402c009002c2160548d6483c000810241d00070b8030605910f80d450f60b80e5600e40710a541d01c90302f2640000e031600d5019902c4d08648000305884802442c4940c02c428030040e10ba01d044002c040c80d048890f802a10070107000c0041c0040c00c05100100e80d = true := by decide +kernel

theorem cover : BRFrame.Cov 38309357 38489213 := by
  have h0 := BRFrame.cov_init 38309357
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38309357 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 38309357 ≤ n) (h2 : n < 38489213) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
