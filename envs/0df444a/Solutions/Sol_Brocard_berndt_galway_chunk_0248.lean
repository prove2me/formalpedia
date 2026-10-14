-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0248
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:43:27.782522+00:00
-- url     : https://prove2.me/submissions/c2953e6b-f83e-4d43-a502-5672b4d0264a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 44424464 ≤ n < 44604320 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 44425714 1250 44424464 44424467
    0x30f200709150b040504050903070b090106030201200606040b19080312060d08040506070f0f0b01030c090b0114091207030c0509070503040b1302040e1005100608060a0e070c02040203090d 82
    0x4082c1c512684000e100402403c00d10080c4941c00740d4410103200e580c40714080b400841052080300c0d075071038005c1c161050510341484a14041c24883c44203d000801d580f260010302007050400c80c405901c144003401054943c541044060208155402c0c0d00007804200c00710225202d0071400001e05002c0091903c0b01c06010248a03036400080c60240510301d130390340c1040000c3d050300c00c0310309464040310070989070030060522510340701c211500180200c108146001c00d0100c10300c5240d040343e02c0760500c80341d02074440034018150f43d0350030000303030110703410710441414501c001014280d81007010300180519003290300d02c603103070100690083e41c440011740002d105906101c0d4490b903000c0040e0401c01d286041940c2d50b5444010024425261030b00f1011034a011980c50743c1195040c1e8161300219076400c0c600080d04001460180d82c200c4202e0010400000c2c164003c1485c50f12030400146641a050310300406a036081800410b61400c120800034044010f035142d102650080310341c0e10091041100c007000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 44426964 1250 44425714 44425721
    0x3120606020c03030406120b130b1e01091404020c0d1107050105071106030603070b0a020c010908060402010c081804020f0c0c090606030a0f090501020703051e0f07030f200709 77
    0x101030115000002030b0855501c00004a8040b136000e8a8072641ca00725007003000b00100f0140422540c051240200c407103045140d50010700031540d007111a0b4102484494040301c00840300048a804a00c44130340400c44503080342c0144000d18800740c00545000d02826955051601802004011071120ba1003880c44c41d200f000480c014090a007450342c54040d83e41c031021400e0010358120b41c40340000000040054070103000d44401020300140145c0c81e91519007000c0c1d120804441500e0018506442c0014803000c005032050050790107849043c01c2070120b85566125034020707200f81d81c3d40900006040910b49841c40100b1040c044a00c11030f031200c50800c002401c00318810151032042d10000c0511005603600b8045036008004510000384201155000350b001e00002940504103500c0403030004103041d00200107210010303160402101d42c40c00c68403840306c0e5004070160880a00001e2240c000000c0c000c000a007a0741c1c0e503d041288076607005007046031100070510322000e69034004281c00c0009118502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 44428214 1250 44426964 44426969
    0x20706030501030308150111060c1c0204030803010e100f0608010f0e0f0a0c090302040203100e060901030803130f05030d0c030e03040302132c01051605090d121803031206 75
    0x1405000a503d0f41c1c4004240c100003a0034085600e5980d5003020103680150521031061101c44242c80c40d0707240500c2e0003643c0c0d4112480000ca485034400e42e130203241000d4422501a60380c0101c18500316400d00e2442d0102c4c0300018140340c6070308071800011071946042c48440c4014405a620f40d0302c20f6050ac5c000d1400300003e94401500e0100540c140710700740c41d084244a40c404480b4100040001c40184110b600e242c19500103034105e031000061103031580798034030110700384c41000ca80890952118400d0000884091001804040090000c40c3c540050070b0703610342589004481281c0140c0003519440c2c10340c1d0260300d03ca8841981d0790b104001c0550580940380c4503e03042c0000d1820207103590080f0325010b507005c82c07010800399918280001641680e560b128420700c00c000d502c0c021240c0e2982c0d54000c4c038003507074104140509540c4261702c2a01c21011200440d02c041c4c48521801c03000d0f5158006030741c01300104010301c00e03041203ca500d4065003803254000c41c081e03901c40b880740078449501700072208280c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 44429464 1250 44428214 44428217
    0x60303030c090e0f0c041502010603060b06030405061f0f0905040204050a0b0a0612060906080d1e05040b0d060801020d1a0603070f0807090f0e0a1406030c010c2d03020706 75
    0x1d0408200566482c1c600f1540300800010030011507079824001c428901c2650007094050710824043c1131910341c1503010006481c400c40003000200000e900b00042030004440040007580300e640003402c601e10040340c100c00031980b0401d4400c001c0d103a1048031984841e070341000300ca580d0390b10204070a40c03405020f41c94100c0d100748400c10086400c0300120b040d28499014100500034401401b42c0c4200d0755901460043c180d50604100700b035203a50341e40340ca80c0700352042080003030074504800750310000c240395465054400e40c5507145000d14000d89202145c10a02122203400d40c2d9442c005a01e10083c00180000440c0d00c2e03000510000700d841d1320b812103045030b0b452030040d00c6c01c0c000c0007080c54001021400b5015181484d030715940c0c4d80603080720b224102d9084884c0803100600c001402d83c6030b264626000d402580d400b8041e858505111501c0302108903091540350340007005240482d40200c18907880b0394000e0030035408640c4034203d00246c42c0481d40d14030a020190129050500d58144541005800d45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 44430714 1250 44429464 44429477
    0x1a04110418020906040b0a0510110706030b0d0f0503160b090d05030405030f03180a0813050102030a0c0204050702010f051603060b03192a1106010503070308121302060d060303030c 79
    0x141c02181100d08018035481c02951b41e500e002c070711591408078480050500402c4003d24120400313008282c0c1900c4c84e50301d81648907601001c10220300a00460030b1103800a02405120304458407006403c1d400d0480c192000c0c0001c00c02e0008100a450310001d819000b101d20030381c20301700b40c81d69602d0300115080c0c140c00c11100f40144800900080b040711115050710101c00c2c1c0341d8403091154a4040c10110050035170344a400f0905042181250283c40c0c010006a400f82c049550341005980340e100310300a80c800203012110900c0145803d5100c01c0c0c0003d424400000e00010040b4900304403401a03a9807400c1c1c9103200840000b0300e60501900c00034000e2020141c1c154209405980300400b0369003d0a004540c4910702e0081110044080921014218801c510060100c1c000940540501300300702c80799004070380c004030f0141070005010048aa101009603d819044241160406000b41522804000035685000542d490b403000d000800b0310000c000584600e50300c0d000e0201e5a50441c240c044c0042c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 44431964 1250 44430714 44430761
    0x80106110f03030c0903070b0a0f0305181c0302040b0f07020f10120203041a2d01121103010e070b0a08060d02090601050702040b04150806011d06010c1a041104 70
    0x1010043d00d40001503151069202c0244a0010f070410400c1d41144040c41004036649428a038000c13030441404603036031400c12081c0c4907196018104a000d10744d41c00703503038030044076100007069902c0800034002051800500303054039181007c2c460703405404486d0384002e0100b49281540340402c10303129980003c950750f8072401546d060140030401030004102c0392a5021002505001000107961080b81c00881c075003410303151803000d8501c0031451035a001403044902141f02c48200813050280d050382d900355055649040d1513034402c6415010310003400d400d5521454020741c031400c100006005448085451511003400540c0101034084c002c20003032007995240804009030f102e9162854018400b813074603e40c1d48400340040b90103040842402e40d00103240c04e912203d0740c161961108241e8812070250f40d00ca0b643c80c49022140a410008031154100c02d43c08500d031507000311520141d0320f04c1508405400c00c0d84400a001032801118291242c00c00c1402d028a146024484c0540c60b402480c690491042c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 44433214 1250 44431964 44431993
    0x8091501030818040c03020417210c0a0506010909050609010b06040501030209030312010b0a0e030c06090f0d05010903051c0e0604020906010c20041407080f0601140a08010611 77
    0x1418071019005a5000441e40e5500d0003440068030b4449010704284481078071400d00400079807151003101c1036984164240c04080030040b40e0040321442984214541400000143ca81507120300a0500e41c0d105944000001500074000c0074001c3c0000341c8006140351450400608040c2c3c0203148210a0349400b05044c480d940301d8058809941d020700e00162a18000d0003c240b0350b00c03500240781c2282c200f9800000d40d80038404001c0068913060340c0d03218a40b80580c42899564500030b03503c039030b01c804207000c11070031410710b66050054008010120390400d03c072a01e07114211650b0b5841600006c80000f803030141a184082103031103598000001300b005a0005070f01c107071108400782c4028855603440c00841d005a108032081d11015403c08404140d510080800e01180108645820300031804d007034410610588854040f40b0809094650a850796550b08100510400052141c5c0c18081c240c4c9041c0d40c480c00840240c0040045c40c0c0319900194182803010b0442000c103414440d8580c441c50b41d00ba40030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 44434464 1250 44433214 44433253
    0x50c180106081e090106060e0103110f090f09090d0305010e0603030d0b0f1e04050606070b041e0b0f090606030f10050414010c27120209040204090c14010809 69
    0x12040d0785049911900d075114001481d0020948200c5402e03c480f007444603010041d0b00400403585140c8450b0b4041d00810300560685012000c00954000140881100550300c40300409410f100181115660540c640025001c0700003550b408041d0780c0010880c1400b030382c240c46918050240010b04001c5880c0c220006980c034810451364841c0030b615180440c1c4103888406d5034203100b84004180514003039507041c10003580200d03c80500c0c81303035041c600451040d04105c4100d54506400c2101c03083c1c50755950310703003101c42904842035492282c91000440c0c08079000c000003038000d05102c0c81c0c42001c1d051640a4034589075024229a2284d000300c0c900200c14a00056200034264401401086642d681d00f060300b240b08150340d04058035420403030040d0340c540d8040d802040c004401d00d00c1c50305100c2034050303a00714040d6038004c04581c00000d00b10440946066080d140e80715100230004205103200c0c0d035540c0e6100c01c05a114040b400781d040310302500c0b5a04606280c1d8811038400c001c144c440303645108100c0302c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 44435714 1250 44434464 44434469
    0x8060906010507031404090f05010f0f0e1009060306050f1806010504090c080109030e01091a0301050108040f140601171b09090a0b010e010504060909030807141c0504050c1801 77
    0x1441000201070041601400007001c51502c1030350204d49403a5141e01040180c2303203807422400c50324070300b00000c40c000301006680015a542000001c04450801e142041101000381c80b034501c070080403038001681039070340c00341001861146a000c034013818043d1076480340c03440c0500704500c0c1c41264481c4640c02e00000032418116001181c02003051000360070980d201ca0030a8019400950070401e036102410781005811001000c2a680d00c02481e0b524032804194650300141203070488000c00040080e51b128804494200307018004801d1400d1b070310341e0f0b019101c44558008004980203000100590387c141e11021041d4a45413014264207034440c1060740c401c105001c0013900c03503a450700c081071000408224100d80140e000c6c0c038459055841c0e5250103640c010074801c4030311540c181040881c145c100d5029104e0010313410703250030b1800d841d110015105007010b0341144480e00300a1003004c02403481c1e25081c1c031200075403c0c4005400c2c145424080c6c2440c50040c14240604070301c4c94842146041c54114604 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 44436964 1250 44435714 44435717
    0xc010e060d1404050105060f0303070b0408090a05030118110a08030702120a0b0a09050c04020c0309090613020a05090f040c08041205070c030803071205090307021302040b04030309150806090601 85
    0x5039841d480660000405054612000355090101000200b000540c0018011103003140c0641c28580e0501c01c02d80c1d01c0c440c2a00c010030a050030000705000a9000020700344012004052445082d00c03640800e00b115600c3c01c450031025030307050100042c01768a000c0070909003000d81d034002402e41081c0c82d660396486040402070140b5280f030000c1154141c00c0c071030f0207100b950025840300e56050030044036010b40100c071000d880501230107042e00c0d0107291070300c221111460950051410b0407007001c00c0082c400401441075400916002c00c3c6100c44503644000d10704c0000b0b40e291136442d03000400034003c082c02040c8049005619010420b441d258200c1d0701d031988640e0081c481c19a080c0c00d040304032002c0c0503012008080907000e01d4048100408035020f507125015075512041d100c0302c120500c030242e8000752005d100740c2d00108000f502504181030401038611508038054603080d916090240c0c01e43c407552003500061542e58003404010100e00c42d401c0460f040f03250481d07032800c180c80041e0503c42d02400103030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 44438214 1250 44436964 44436967
    0x201150b0f0f0c0a0507050f100f12020c1e0102040b09060d0608070b090117011a070302030403081303020a14030303070503130b0106030b0111010e12070c0b040f0e06030c010e06 78
    0x740c054004204958880840d18400d60f10740001a00316941e51000000c2115540075140340403619061140d412452003100034000b01d40d06d0003680c2d0507074940d1b0380903240c002040030070034000ca0307a0045070008000842c02d84000784601811600b464601c00b40f90317088014664010441001100c04001c26107100440423105540d580e885005144001c016a80c05901d25001d2404000351035512403025020886003a02d40c1d06215030f00e100c01405030b91090182d041103d600000a0b2075000034030000d00840b0341b1034011603251a4582d00e81010396004000f4044031070412a60a1046080c4910001c00070403009019001c180c1600c40001c0e22408014444010008040300140001d244c440c81c81c41c0c01a000300700da0b00385584802004002c5d011b02c002041c0450ba0040d1b0141070010148280740c0407003a010007400c44c0c400c0704400520b56a110900c143e926100010002c28a85206801400100703050190100340d6490000c2d4103005800051010744650020410804e80740d07040b41904030b12002c122a00ca = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 44439464 1250 44438214 44438227
    0x150c04030b070210060906030204060929040b0a172a09070e040903022a010206010302040b010314010e040302070f050907270303080411060403030f03020a09050607060911010201150b 80
    0x32071400c038007070106244c92401d1102c0005c2c0041d5541c40303003003541d009a03400d110403511621220207641070403040b07082e2000c503110000c04400d00d80d5807045030602d0080000c01c01a080200003024680c003600400b20342c1292181c0d04090440401000b84440b4002da0000110030503500404040b1130900e10b00380c0144603a5001501503407041080c20301e5040024020860394840d814000c0d510300003a40301014120400c450310908101009a0000b8400141c0c01001b050307003550f0900002d0003120710030b07605054850480d02e00540900c0011406050640f4007031800d4501420300914140c00c95010000b2800c01c40c7c814000350720fa0100c1582d11461506000034401e40c0b03e04294100d0792540d000c802c8949400501004060b800540180254040d0424508600d2514100079291043d48002004504101e07941c0303a98601980103040041a1420070048403582c0b080030a255030300c110021108503982c0d0f65040108110012511840074080c402000380304441c09125460502602502441c80f00102e1030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 44440714 1250 44439464 44439467
    0x4090519020f03241309020d0c2d12080304030908010c030207051002030906010e0c0d0603030f020f010903050409020c01020f040b09010f0e1e040e01051503150c04030b07 75
    0x1180d4018800a208550b504603070b0b149007440390404d68030501c0100c0703208104402580881c035620083c210041907004100360000b04800109040304080360002c43c600346141c0416290010f42c0b000740000f40395402c20107044222011a803003640314410342d14900c03131020f000382c0400c001c1109180b42e101c0c41e002d1b565112070800f45c40c0100f05078000000d83d0f00b4418000c0180c0d40c9034003e0f0150b2403040040700e1403070240798030f400242d0004560314040b0b90310950040100c81800c480f02a0070041d020f0500d80380c071030240140da003600c04a40055012a4903050040f00499040000440c0c0c3d0070340c48004c201c5156696002001ea200c0d1340305d02c1200503004108218143c0081d0304075049444600071b4150f0b219030355200c80c0f2141d0451245a8049501076001c3ca2005000340c0703040c03841c4e40d0001c05a1101640c80b10240b1a82c4030b1060742c807504541d40c1c00385c0c1da103411400d1040c01d02803000b02111102d503181a4080516000c0341901014072007100b00c0c02c0c050a08000415902901c2c0c5c4001a101e80c0e41d6407980 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 44441964 1250 44440714 44440741
    0x403020c0406080c011403010321050708030c120a090507050411040e13020a0f0b0901050f161a0c0a020615030f070e01030605010501050703051903021611090912040905 74
    0x245951082c0b400600054800c070004807074501e21401c1c0c0315a010401d02240c02043d50109100241c1512200c062021711521007800780507422186042c61402d003056038407a045c06810803606044003020000c0c182000b5040b12002e00e90140c8101000c0c042e010040d030b1040d4407010f2510070503000781d07140c40b806840f46d00320303405843c040c149200902c0e040e07141030b409903544800303070b03c40030380c09468103a101240c1140418110360680d203c41100918003440c00c03004440c1648021000c80ca111400e22180c04100410303d0a80801401a0342010880c070b680030a0030035461001e020701c0d412200801402101700d40104820350700000c0c801440c40800d4040000c01e060101d040c04010082c0070360400030504210113403d081c1601e015503000c11881c0e80381d0303005446512840074040d0100740103010320401c190389150080e4000e4401d10b8094140b001030105c00029010000d011207244440b82122070040c01c110361585c4e80421044001e0040c0a8034110b2003003a0f11482c01348018107511800085c510058550 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 44443214 1250 44441964 44441983
    0x90f060c031206130b0306010303140d020a020c041505130f0f110307032912010e060901021c050c030408031308030a061e060f1101060312021c05040806070305040302 73
    0x3019603658807052aa1650100d42c121076091003a18040a0b1a40b10b4802d0700c81c4c0c840c41a00a0300922030369095480584884200045140c0b1240b41000351801620490000c0c14050050740c0003089549582010482640c8030008120074101221034104105d82d0f58003040e40c4100c50130f840015002c1142581240501516080c6460b51403e0000a151982c0d913040214402c0346a0b030b50802002d01e06c074440740f008003400ca002840d014030700b064046151604c906c100540415103000040c84d4142c00c0c0c8002e041100898400049035404112404210f1110f10380c0030b44010b00007001c004610f403c0c9800300ca02e00025101519014003c0000364880161300002d500ea04d421027285522454401a0000540214000d0000d21402036028545100303c4820303207002c0d82c2084e00c0321405203040b860105e85003101011203603619920f903040000401d807885010001000c4560182080307502c2941d844108000e07075140031042240c10002040b050001103500e42e040045131401148540b16410308901d003a8581 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 44444464 1250 44443214 44443237
    0x5070503010204031b090c12020309100903080601020d080105090106200313090f020304030c0209060d02060403051c18050904020d0b0a050106080a0212010909020604030b01080102040504051b090f06 87
    0x300841808100441c1117101d0118500003c2c0f15a15002e4100503203030342c140600e010405581c219903078105150050f681c001821000c841011612510803010b80340c41070b106502140110090080d1541c0c14001d800700d42040d410800625458400400c8001d54148154810843c103182011700711b4100010b032904400414044940382c100000c0090141a481d208401c0050b06d000d002c040c21483d00d000396403145070140c86800070400c09400340301802ca40241083e60100e0020340a80044c1e0750500500b014500500051500a20002c3c03501a200c007000905410700008a0a40f210004514103500c03c3d81c4059549045603100c80c800321391801c0309224004c0c819565602085409200c55100074104d80060ba11100580c564112100491280d802601603820043c00103204041194100340754162000e02900e207010382c0c0e9203d10880309003e810626046c0d4000908100d145458000c8541102100441c3c284055002400d15141d1143d44601802100300814801d001d68038001903440c0b04070780 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 44445714 1250 44444464 44444467
    0x15040f1205090406050108010305031204020f03240709150f0504050a08010e0601050a0f03020d0512030903040e0f01050604030b0a0e010e0c01180b0304080c010908130602060601021c0c050705030102 87
    0x2000703403407608145080b601441c0740007400a4950304c50802141200d1300680035520f8024103d03440c0c020090020016a0406203090300006107440402242c03100510194209561008440003121001e50140c081810090002030902140c00a800c0f40248a40c1b00e080080c060140c08000359413501441c1c0c0101d5001d07600700d40000e49903206402c510010762102d81540d045a8a890030030100d02c3d06400744940e10344803904c0520041c10000e000e4010107005400712035540303282182140082d1700407170b0050016040401d040100c441904102d03a00300d41100d800420960429011078501d000e20b10020b400303041440086004403055070700004900011800900000030403602c026070310b079800c88030580050310801e00400c0210040d600c02041e00d60b039032a81d915540300c0c1d40b50030000e6040304000c000f040d543c0c2c2c400e0134001201900105042103040c52030242d0b40c0c2c5080070180c00c00c20000c0c1401d055400c03104a410002c00c48051a00c0c2d840e10500b0b041c14203807040e040c01890140150003a0fa0958030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 44446964 1250 44445714 44445743
    0x60f11030108011b02060a0c02010e0610030203060702010603020907050306011803140d080103080d11041806051305090d081005030615030613030914061c05060f0d020315040f 77
    0x111500a41c1a500140c1c000c0c40402038100700340c004d0010500c0c2c114016001100410680102038201c07030201d052a100101e191001200700d1400d201003600c15000180e0112010400c504041c82a564024020700082005610f150007040d0390740401810701c010007400000043c1c10341e00030f03581c015043d1908034a0f21324140d142e01e00030340701c551207411102d014801d550b03510032420303c50507000341602d80c81204903090081014206028100f145019444107034203000c04106d0104102c110002030340340b0745010a40d1890700042c80480110100c82058850401d020005a00d038001198020152035117442440e60f6180e10210700304402a4106640c1805941d091005000192119412580d41207080c0c45440d151151110300320504c0660080c081050000300f004145004220007210050240c22140f43c21a0252448801005003010f039200316a50000d000d06410310004c070124100c0b0944440c00500c00d0781d000684d4400c10540b0034626203880d500010100308000c02d007040030701c1d88078205005400c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 44448214 1250 44446964 44446991
    0xc0a080604110304060e2109090406020f070c03030801060c02010c0b04051e0609010c0e03070e0703110417010f020f070b040213090308010602120f0d1a09010609090e030705031204060f 81
    0x1d11b104d1104492054000e070f00110401001804000c0b841c02c030b4128501400d1000703101d0740d600014802c0c0e0303241c2c0e070911040140c070940c04001c0c40040d102d00650a081815840e0103441c011307060700700004000040402c40e005036006040018140e81110015100399134903d000c92520029102d405603010b50044090301c02240016054061038002d002441132180c410403c03501c005100414582c19032011300108550a55400308603005281c0c2d18011407a054040a40b510742d900c03503030209920040402190303c03d91428403c400415800040c00d5181800707015503d0308134042c10002814020304200801c0c115030310800e49000702c000410061004d04440d05025012110900c6004098001c84008810b00c003880d104481070036451074415802d21034020b2441004041c0c13410000ca8600541c4076042060340c900d00014008c22032503841c0c0855a00380a41300c016114012122035481d841400400c1c005240070090360055040a80b2002c0303d070390755040440c050907084240039100703840c2c21031020290 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 44449464 1250 44448214 44448221
    0xd020a050432040320010b0d0804090509010903140a020304030605010e060913150b01110616120614040b010903080d050403030b0603060f10050d06180b0105030c0a08060411030406 79
    0x1000030031009128584440410002e41c001100c0040c00104008500280c003c0c0b00034110030030741802800018451003410102e2021f0844483c20b0b1030f28540800c0400c0b4020280c003e20360700074989002400301c0d04003a41c02424035000a5041c1030030b17035400320384181c44601c03c00c1031754010358012109101c02e5030f4518140b4101c900690b00e03d030154002000103011140700710101a0090352110101d001040d0a10500b80244048440141088a02e0702e210350484410002180501209544000004c0180001400d40542560342803122400c00d0003c1103858151400031001c1c110541e4041040c28200c401210040c2d900c2d000248a1100441c103042160f1455104601c541d10a8030100410000d007410402c2c7c0d1b010864086034030440e074100c131040c94107181c10400d030041c2c1d15007032050030942c4100301c8400ba41c0094201c1524184561440082003020b03010f00c41030f840c400c0c00e01c9441d500f0301034004400b0340301e0151501c0c244215100819001d1300d45521207040c80c1000c40e180b03900c90400d4500304015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 44450714 1250 44449464 44449511
    0x60b0103050c0406050f07020d0f030e0405062d0102070f0308090f0f090403120b0301020403032105010f090504170d02030a05090f031c0b0d03080403091d04020d020a0504 75
    0xa49407000060115200070102d40580d02c41c1d803613140c201280700030f0440312070307100810803a00610180c42d40000210007000d820300c000c0c86501e9226003000312000703110032200020a01403081010852424001500155468010340e00034610740c99649902d00507480c00e1030b03641c808820b03081001d4000060180c01c01c0684000c00c1d003200e4001c84a480e07401000845080f000c808c43d4420851404940001e0140c2000340007199288000324060161100007030898100e6403056022400060950041490181c000e2007400124801046039504050750440901c00c207004554015680d000170605102c800d04140008080d100b452079a1140300d00c90403006504140c4849001c1400c0ca030101d00c001d00041500e88100d006c0c80000c50400b058010f001e41941c5da00240c07400703d0f039600c00106020f501c80064806009009458460190034107140042040030700b070784100300b43c201d40c45942008001002e400b94200e03030112028603040f0a5400040c00e80b4400d42e01030b83d0702c0b40c43d00341e07082203e40b1201d03840790a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 44451964 1250 44450714 44450717
    0x80307030f0809030306061603021e010b040f090b0f0910060303090602100b060f0a180303020601051504050a180e1005070210050606030c030c040906060309060501060c1104020c0f0703060b01 84
    0x2651140b246030307640c0740002d54659a1101c0148100c4852042680c4002980340c002c0c8100c42c0002410003201c0c08905070082f078010320b651030301005c0141d42001d000c5c0700c000052911007040040c0d9291101940d000c4094100410b8801c0100070512203075041000409041901104011643e0b0383d24002c2c10f6030119114102c09030180b4005498480300511038142e0b1100d0150800f858140104481c8406078004c1003c4018001404891224220b08122031000b96121350002d0141e541020100a1401120b81042200c503008000900442d00c941c01f0f4041111201190001180e1038005030202611501c91a80880c0c0320300b4250002e1880c0580207113024040d242c0940d1524010b6500310700940c0c9003100c03c0ca4204e0b000300007107002200c0c01c400469020010504072414941c5030b08151042c0c4d402a8401400a91105880000e0000510469004000500300201031185a55541000c66002d409681c403440c0e0124400241c0310044c04091403980039041602d510343c1d2689061801440c0202c00a130 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 44453214 1250 44451964 44451977
    0xf0803060109090f15050315041112030408031e07051c0e06030f070e01030603031b0305070c030501020a0311190c050f010c0915020d080406090c18050603011119030207020a080307030f 81
    0x409060201d41c8c1215980c0004c20050b035a9244c0d200e1b62940703c0038031203580d000304070361081401d0170302c040c8007070009400190003039039450910110040300d10400c0d0480c40440d810800c20000051800201004080220000ca00340000c0060080c2d4403510b1860000b50441000000c2003001c420301105c244c032409041d200c0da1044512040110200c4482d800010301280564900961450040c0c003184d0b411842460034500d424115910400503203060390003150300e81c1d00450104417154160054110554481c40883c0c280790040041841c641c004c110389109110040c0089010b111043c00b09880742c004640003071000d00012180180319041c60f100d0300105509811003003031810f02c041003181703448840e5514400d064841d6141e050084c00c0c440004c50f40301e01a1100021a2030010309200b2900c00115400101071500300289401e643e500140710582030b0007000b0359580f0941045d099000626289401a280d01c000e10110700500800c0e0007580c8180b00109010081590182c00d140f8603200558860 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 44454464 1250 44453214 44453219
    0x3020d02011b03091b030b091209090f040c050a0609140303130512011e0c11010c091a0c0703082106030a0807050309040c0e040c0206040f0803060109090f15 69
    0x4a00702c481181040030707425202115100814440d4001d40003150050181880130300c84140c014920b405507a004407050f101200400400030400c0c0903900c9000218600c90340750006000008002d1000180020017141e4220082800d0015030403041014000142119800382c1d00c954010300f07201041c0c42440c05500d107800c6a082c20307003004003d54000713051050150440e40e017481d04010004080f260003414030b668550303180070b800d82c0303008000c00080b00c072440014540c0010700004101c003400c1c40445080340e043c0940c82e9210380d40162007400b120a500f03a41c0d0740300061028070604600c03c0c008201c00c14030802030301205020562008000e40d80d04c800324542440000c0d1502c500e00d810840c0c2c9164503820510801011543c540020b04c03a640c0700f5025640340c0741301c4000003400c03258864000000107000c0c1c0415286030615118005000c43c0c240003c0c5810700d0f090340c80701541c01f00d10350000c001420100c04640c1d04d901548a40c0058107400a00740040c00421400302c00500e040e0070304941126548100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 44455714 1250 44454464 44454467
    0xd0b0406050907030e030f0a1e020d080a020903030403020613050a080a030c030c020f0907080103030f0e031c0306081207050105160c0f02120703060e07050a0f0e090309120a03020d 79
    0x105000c4800240032034002c1c3d40e410605070001d140209800505000c00c11043d00b8110b070180c0206511410b0340c4602c0d0b19003608041c00041001c1c10b6110000750b46c848011400081e40080701c00d90300035603450002d66200500c0011030306500a5600094022401140d2403c0b00d11810852000f940d0381600d26103a083d079070702c44043c0d0b900e0003414054003007183c0103030080202c0d11078416503040d2030028002800341ca01d8800410390384441100d241002400d080010b04c2003541c000d140000b0180546482000c0145c1c2ca40003a407505900c24100001480070b4401c00e285c00e010b034010750300030a505070a40d81441d0030090310702101e6015500c122065440c0c040000d81c40c1d46002620810f1001c10350300e6038425021031307450070101c0b0031180302640d20001182414482000030028040518850480841c0d40480f545c402440c00c68680c014030b200d0042c0e02001e06c00c0d2032000f11101d040721800c8003921803e03101c03010243d0071482090f4400390000c400c00050324800034000790f03d1109620a0303007107480e041c4001d02c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 44456964 1250 44455714 44455721
    0x90405070e0d08090a030803130302010506060a0219140105010611120a0503010e090721020a05030d0804020d030e030316020f0118090c02100c02070608010e0c070b07050913020d0b04 80
    0x39602e901c00c50074000900410008400b0306802140a0300d5640c03c640c80351110030081d007084030300c4260b01c400103020f107080603428040c583d00908240c91081c205030b01400d0203511001070f1001c1081091405410100f841280c03d042c901c61f0141c1c9000b000035513122000101408400c0015420703030301c00d2008100255040c0c5085810003803495444504503401c150b00307600e888001402c2031801d403103203030030101d00e40102d18100307000e202c8591160140303400c2500c1400011026580403d100e9005000c4250030660005138482d8000d5044900500480c800e01e820380303120a446103a00e401d4807000c500c800c1500c1c183c43d01101c50034000c070360000724076664800456605d6504030010301181c10700681044a0f60072904054040311050068659400944e4002400c4400c01c80010740147e1004004020454008000b50301400115040351071a150215401940e031141c01070041c08401d42000140b950745c0f0403c2039620000c2c0080040e0300000308101030402035009651100c03091071820640c03150174a882e20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 44458214 1250 44456964 44456987
    0x9060c04060f08040206071203150506040e0103030c030c120207051206060102071a0906030a050a05090f0d08060103060e0709030506130f080f040b070b0f011502060414030d060303020309040507 85
    0x20344000a0241e051011503080740f014100720303005402402004002944400820610b1605075800565080c2c07260b60180741011540c403140c02074808210a1104071500c5807100c0c1541e826040030700c0340c00700900d0115000d414181010b090480781030341d14106150701140315000c4604c103c890070b14055011000544442d03040d9041809039010002c1044050400c05030200f8140400050070704000f001004a0115401166102022595802042543c0c0c0c000c1c440c040c0c20101c1c2d00c0c01000705540044030340da0707a0315400e9441313018401e01c00e00145040e803007a0040310181100f1001101c481c140f610010382031850b1808201c41500070080000c1101540e008800b6816821080050301c03061143c403180c101e5803110001a070000406c000c00308246a080300203050700e07031041302d0714011460400e81e2601c2166040e0484210402c1185201808590006103607401980109607180040580788146145100c2c01e440c443c0500c1c1424000400d264011002d0114040e00391fa003400660f9402d90129024014070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 44459464 1250 44458214 44458217
    0x801050306040b091f02040503070e010e04060e03040f0602100606081603090812070c0507080a0807080a020c03061302010e061e03150307030809100e0f0d08070206030403020609060c0406 82
    0x407800680803a00156003140c2040d100c0003a2403020320103000c108070340820507054209080d000181081a070400300031040c0100421041100ba41d41000d5507964070600c050409080305446210201042d00c0500480d070080c580501c1e20700d174440ea0707140c0c00307911450b550b4261140980780400c0020501c0c0500401031142e020b100804542000c288405c0e002400d810f030302600d12600070302203000c1800c0c88801d04e60043c07070a510b4880444150b460301500e400403d81010041c0e8014908a07400905000151201990b1100300baa88500e5080022454807001590b19541032080c2018060614542003100754468000c2e030780c4044520b182010b004041c855819040729014204101c1d41501481101658012240c540d10302601c1d0b0b90f000000e407030086160026541c6145c0050111040d29020a920240c11a00e00345090000d00345000110002c48110900c2e004000c018816010860940700f103031b924a40c01050320781c03a42050309000b55165821100c001c0d85110300c0e0301250040300307440d003524101e601d41d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 44460714 1250 44459464 44459473
    0x110f03031e160801051e0907050301080f07050603070e0103150e09010b0301110d0903090e09010516030b0f0103020d020d05010e070801230d02010e031b010306090b01090b13080304150f08010503 85
    0x2d01052094018120802d81c6c0c00d8012045084015941e0003286801000107a6407991294105081203042c440030040030300e85948815010040d03611400103480d8008450b04200d030918072113a005801900c017030400c212503181c2800b030215000d03000d058030303a01803c1c615008120006100050608036806c2c44c1102100c40418008064041055000528164401d103840059076503240048c41403206d00b903481d0041c070394480c0c1c100070200302c442da0840c002d41441e103801c0c407a040d40c03c00490140d45060400c1c0b41095000070340c411803016a601101c5404502c0c4d201000b0079a5140000421444140e071100001143c0c58000640c06c600d1504402207004050f002000102040041020281403004100d06000f50b107400c1121660341800301c0400c0344014208500e4600c1241c00050445001c0d4121459543c40c0c851401c0e41641c0c002c0e07800040d00c817602c84d02561211180110b4903159002d9100f07601c64480054081040c0320b00301c2078201714200c613440e910903d5811a4003500c488109018890300b5501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 44461964 1250 44460714 44460719
    0x80703051005040203010b0303070510200714030f0a0207030b0601030203100b13051c02031509101107060c020304080c01032318030c070f0504060305030a110f03031e160801 76
    0x7541d50050350420b1006000103808001040424216000110180d40e41c0d0001603102940e1005402160048031904550b8595495542a10300d858091900050306440c01c070001091600000c0044035900320064091320340700c6c11440e0000799200c0440c0011900002c000010500da54000c0c02503d02030240070010408242c201450f40410380c02141114a510701c09240000351034982104c050f0803003640c0b15007900480301500506187c1001d010b0300e6003403e504074041003403040c40031800825001c07000002154001c1070880100720f90155600c05845d0500d00024910302d690000000c2080711816810780d20405c0440c0e00540c22601c8030070715818404a203c40c0c2d08241019001002da12610b0058640300c44c080340c401d4146035402c0b42084151503440608180a05440c0721001d400a1404a4080c08501d04581d1120780b6805940050018482c0202d02c10351814024840480e0f07566009044907201e10b0100c2e40010400410b510306200b94046001148119000c4034066044c0d01d210344078440c9503403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 44463214 1250 44461964 44461993
    0x9080607140f040518150117190915060e01060302041a0304020d0f1103010b06090a090e07080a060c030c02031303080a0c050a080403031107030c05060306060d0e0a050708070305 78
    0x2e01a06105034405000c21012940c0d96451500401c0142980054000351405400454205040315030f00c40c1800941d80000e640d6070390280125500c49a1240c44030265018000104090301440b840182650b000101a03a600c2d44183e01000455070f00c15030104041e680da070340540481c461030007070220989401941142800d0700c64000d6402c1403026000c001070f05800d17111042c800c101e44200701d0b101c21440341810610f03e402d0060501c0414101c070501c0c9441b281c4400124100d8043c401c81081030f8403a408240c110038140850001084c0c100143c0e590344195180c540000d1540d602000d01080c5441c0070180c4c0b40344000103071560b000e0300e08107520f80746003540c51324001608555203807420080c007106400c0000d0000e000d201c48a41c0314000c1592114194a005815098211080340c00c0354401d90b01000803030303181d5160780300f12481030360a240d0702e03110180441c80c0c03407140310b0381074024074144422142d2801002490150390b5000c6c0d41038890040d119000b094545d1740c1840094002d80c0300300722404040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 44464464 1250 44463214 44463217
    0x1b0803010605210a0e0c0604060801091a06030702030406020610050d0311070902220b0c03030a1e0222060302040f172112010806010e0a02160203061302010908060714 73
    0x100301c281050310812140c583c0040d080c0030b0449010b041191a4040c40c9403000c02005904048042142c4070b40c20b05040003001010b0310360501c5614501c0b0703200e05078a2003e18180e003003241000700180541c0d640746030580e4081d41c1da9019210702d000611940300001c070080d1500e103030b5400f5140005c06901d00134440b034034111400080d652140d02140203105001411044920040c840c04042020008100c00881300d40798007140c1d290302c000e001d40810001e40c01103240c04021658060301d01c03030300096494107000c070600503e2031040c00e20200c0340c80007904801c2842c0da04494060115000046880c1a4840728204c1c2640243d100d140702d24400c46505204d440001c00c0710500b41d0300800100c03584203401d5000150081030601e80d03114046800138440740c0105110403050b025003000b500902c0c042d407502e00d00c0d102484004055041440e40410240d41300a4180340c81c1170060740040c1214007609052841513003000002d17100320b02242000c0d9000919160100d02e1a1040315035458035000c0e00c0e83e0f03a207864a01e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 44465714 1250 44464464 44464477
    0x105010c03050a090b0a0207030308010e130209040510060b0903010b150901030902010e04110405150c0a02090601170f150a14012105010612110705060c13120605071b0803010605 78
    0x41c040403110210301c800000e0080c2081d56080d50088c030000d4510700740605070980680014403203130300000420840c401c0743c501d002d20151381910f8040f680e546906207a03081003690030303070340304183d04044001130f502c0c1078140500f003101c0c0704800800401c0110410050103010449450600c40c006000b140241c3d80607500848142d4011704141c5085211500000c046402c103240c181c03104480410184010708101c00804d042c420020549450710116020303465603004d40c104028410107140c4001001c0b81d106003007071720b0b5038407855200030101c2c02e10700c41c02c1d880d0400031280c082410300d0f03d444412030342c5084041d0701c0840300e030f1458002009290343c0c01115600c549004040d64000e11080018001c440c0380714590003001c0aaa503680024103c1100005440085c411660004801c0c08030030049803000c03800b51341141440c0b440d103a82c1e218a0070500c10003506607001c114000c00c501e407483c092140c0b0790401b903c035410f942ea40c101d01c001400707020681940d42c0000031b41600b2043c0010302c10349004400038000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 44466964 1250 44465714 44465717
    0x60c021f090509090304060f05040303120b01050c030c060a0c0c080d050901020909070c03020d081510110a061a04020310060c080721020105010806070c0f110301060b03040c0803030105010c03050a 86
    0x7031503103480104030100b0013135034540c0c00c0c1e5100007810407507142d1029540c1d8003c049407820030301e0503282d924020140914545480040b0341e807440b80c0100f980c0114100d070104000902640d4440043c903c44036150b540440c0c191013594105144805524803d08030400030741d500040780750034000e00781c0c0c1460007801e004028601304e41d03003002074100300ea0300c072a0128030884072940c2d200e1003415145002030514500803854414031003c0002d210030042c0e0700840d0b00c1013001c161040706584d0320424080b244005400d07101c44039805030f9800f40c4140107181c0c0080e44035202002441401c1165501030004911040700c003010019071000342030203d180700d45100c40030035005080031401c1007072640f00d240242c654104104810706001091070006502030094a004140b60005000103280400c8098030382c1c20b02007001098000882098000c02c050030b050f001500034040c00030030000b070702d400c10b01d0811350003502c040c2d03450314880900081412002040307078107a500603585d611355000560350640d490380010042c1740 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 44468214 1250 44466964 44466977
    0x703050c1002070516090b060306090417040f0905150a05060d060302031506010201140105010f0f0201060b031302011b02010c08070f02130506040b0a03170a02030c06040318060c021f 80
    0x122603514600243c03502038001d0f009056069140c10004604800a600440d41c15007000d40543e556941c90b82529030182d002d6807280d03803d55642c03410b01c0c000c02c10b01c450b051401801040202e10304048010700400d541c1018810440e5807210842100c6407002d000080c0d5004040c440f050025080070400760000192205000c0341a540300c1c6e0002e0f0070000c4540550503000e90302c0c41001025a0309000e48071084c81520101492541010002084001000d112400380150440e0324803207140300354004001480440d04294581c10409101c0301c100406010a0b8001160074a140c44007000c0d42542500895058403600d5840309555a01850707504950400d40b200d214120100700580c88200120541003040781001034107181200801c0219003090110500031048410284009a00f020450317079004440f82c031054613055500c070100d246105909207400903010b01c1003031104064021030648044801e0103142c44134903485e0502140c55018444004c1c3d4041c03454800000300c880880c00d1036596504528007107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 44469464 1250 44468214 44468233
    0x50906031b0c0322090516031a04062301051801120902030f06061201021c0506190609080d0f050306040c230c1209060706020d140103030507030f02070501050703050c 73
    0x54259005130740c03440b800300c4c005504101003040101d800c0b00500360f60f143c2040542024508002d1000301c2c041070100741070340d461000c41100044000d540c00a07100130030070301c003440e20b54a64610b001c449502104c0032030103a400441003507007d00150f95001940d48940d1261b42c80c50300c011142c01c0343d542128807446690700c00304030268400340702d10441e000328a401400700303050040500c1110f064074240c200d12a441405241070200f602020a041002a004040749945a0400003100c40a5501d1180c991000440e80015241d1700a03a071401120302410a8a07202205040240d076005400300d4140300050007000050b86038903042c2c0c012054003100f4074200c0107146800b04c0c0840c80100760f80320075a04a102080c0b00c1002000bc00030f041d01908000302c9071303040216040200b040342c011004024441500030840d180d080c001c0e94408900d0400b0b0102c0208156500e00b0081c000c1d601141c0140c0c0000d011700b41186103680002026411204107a5816207031403515101151b90fa00301c7c030442a064000d10054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 44470714 1250 44469464 44469487
    0x5160f051b0c0102070f14060906090d0f0303050a02160305070f050607050408070b0a0807080a090b0a1d010905060112051f0c0f080601090e040f0210030b030c01050906031b 76
    0x50600c01c0d4403a800070201e400c8500c00180c505015130384221980b0b84604400e200d80081342d82d58260721442139800c952148204000100c050242c14070b00760308904409070820500001031880e44585001341c0742080240c41b0b096040003644038441d031200100342031030a2100064803400040c04028010595000200350036034406d410260306981100020750b01241c148011071080c80400010500c650034185050700819002e400601c001b0659003d000c0c1d4800003d11b41611030f0001100703981e2000c0c402c0020300d41380032a40f00600d0b034195981c00c1c11860924112895105104248141e9004002412a41e107440c040b60b800100d5070340c0446643c000c5841c0180c0c1071982e00c181030101042c41d68041008800e401c0e004109080d49501001000711075400e2000c16604004080c068501ca072009614503662401c0c401031661120300c000307400a81007500707942c16984c95840352031706031030131030545034a121074400454040c060700c8080b81d40103c0420100b481d016543c40712070100d541454641d81401004200f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 44471964 1250 44470714 44470747
    0x4020105030c13080d0f020708060a0203070c0602040603020315040e06040204020a0306030204051e0c250206040510030f0f060b030c09040b06030a0903090504050403050d0504030311041403010c0305160f05 90
    0xe40c811940d002e05c0d07a402c462620b0003805248020480d035440c1c00115542c40308050a0080340c240d000010075590b510655210f07007002c1c2c2000e4103564a5076503190080003540116000c03000715123400c84402c0c051070030303015990307481e450f06008240507121a02004025070140303c3d03042c10b041e91100e0001c0184c540b801160302c501c101008103416410880c02500d0001c400030025803a08108000071542480442e02011808810501c498020385180c808600d05224942081c1d60140c2030510703840080d98187c11629118210480c107000d0140c0f500040001d03502c050080c121500c0c810700004401c00c0d02c41000c1d00c07080e00000c1020410000c0d420100e0200da100384d45000e40305484507050401d0680109400c1d009180c1035a0402041c07805440c0200180104291300c45001e03124804070341814841e03001300c4000034500302c0c115642c945d1400000114011235840500035400c181c0112030041c0a8800d00384100101c0c45100405d441d050310072503844901c181c1c0d400c1803220901400301054600030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 44473214 1250 44471964 44471969
    0x50703020415260f011703120f041b080307030819060e04060b010c0209040b0403021c03090b10030f020d080d020f04050f0a23010c050a05030405010f03021204020105030c13 76
    0x102c80b11900c03d00b40e41d54000c0c601c802d4001c080300b441102c0c11300034820680012181103403c42e80c030001d40200d00c00403003030961080c54130b004020301c9001e003130200a07508803080c1340c09107102e52000d0200355440300c070440701c0f80c2040c440c1d5401604144000d50109000e0708816a12044107041c00d4240c8084003000c0c1c0464403141c003c002d1560070ba104000400c60350384950281130000b42890303502c0030443e90008110303480042004120240a102140400d402003100400c074031008a6001e0781d0782c41070a070040c01407074040e8007039408003038000100e0307508078400b0005006e80380c00c8403540c0303400d05548d0244112000b485104407480030081200428860061014284010391420040eaa9518206c00c101e200391400c5159071050010610400c25002c0c2180b5900100780b26186401c681d443c24030058994940c108005000c0740161500c48040143c08001803065032401d8840e9808a003140004404074050b440c00410300d860000d000c680558000c3e005580e002c8110202a450810301072840703140313199242d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 44474464 1250 44473214 44473217
    0x70213110306120105060f01050a020307050604050d090e010b0a050c160b07020405060f0906041d100c09080706020d030513080d1d0c060415020a080309100c090810050703020415 78
    0x11090002c549020181020400c1120009021a00300303a0001010311081c2e02c0240e0601c0380000700107901600900c240d0301501c1d0410140c070080d24090a02c4c0351a440070a4030040040e03480342c0049011100d050045040c0d0319030300754207401c2c00c4030700364240c5055002c6401d445d0a0312500c100c40d10764214655210f005841c0384041d4503143c000c1481030200380c807405803502c3d100c4d4030f0302e001c481c8180d00d07000722496000707004a4005c20b050703001135114100030780800220580390040c0e0b80328180c0c444864121b070402060725524154041d9407094165200d0b07465000d0f000050b000105030b0030b142c510076000701c0d4008a0b0300810b001c01d001580ea5040c040e90000d580800c2640d00c50b110007103a4408070044a030040d400b0720181107114030080000301a846a401600c1030781c56201c03501c0c1d1101348204036420b40c0035880148240c0d2824500380c12959000c0118218810328186841d199105109038114000c950300540248010720380e00e1010701c090030009040d035003003690901c00090b11550401284c06042020b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 44475714 1250 44474464 44474467
    0x6010509070c14071d01080d080a02090402040e09070807060906081f080a1103070f090e0304090203090a0606120305030a0b010c06060902091504050a0e09010f0203040614100b0306040207021311 85
    0x5e203030480e450a03c18030508507101e01503000401c20008003040341071300c9001620b000c103c207913514514a4001d01861241c15041440460701245d480101040c281c0a08000d00c22115901d0351030104995820307a80c01240c0001e05030300d00800465014064582c2c000c00100803481e00505950f56100303585440313030f01882c0907034001da0102044c45034040c1e285424041c1503000e0403100d400c082040c4104a05032141e41c5505940b142c0038481d183c0140240d5000d4401c889080d0354a08282c10429520100c4100a440c024540000060000030031840b10085c242d06450b4203080d0354401d2448030082c15109060b9061000e031002800010342d10348a0318024048003000141c4868aa200b44035855403650701d100002c40c010841031080e0b9440c80300c144100c1d1080142400c50b0b0f901c2c16402800750940d0428441c4540c00441804208020354220b40c031480440b40661445a50f480050850410035101d5041040020000700c0c01605040d00104a10340c00904040c5000102812100c01c580d0305050b1858031180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 44476964 1250 44475714 44475719
    0x50904090c0e1006050406140c0703060e060c0703170a0e060109020307090b04050612040302030d02041412061e06030c0603090c01021207030f05130b0703020a0203060c0c06010509070c1407 83
    0x107002c46603007200265011042d82070800f44050100d219500410060110051000041c0140582115500b1004e0001e4a03280c0366030b0300c1d229001c1d1400e106012014042c02002035441c040301016100c00c0d54040e81d54081c00100b2400c204031002010f00341010030b41d11001070b0000748000b0000c190082202150060380c9180400b0000c000703407210f030420600c0e00c02c204800c100c10f595202c140d58000e602c01c500484551201c1c5000d0785541f013248115803c5900200b00042d43c094240c864030803015064030141c1da20101005c01d551500012207446040500c0340c0d110742140a00002c2d80e40c1d101c880a0111180c07100b109000401c550402c581c4000d2076841801d1509041d607050025500c003d40140205045c824180e901401100080051030200607001c038149441c1c840c0c041207200203100a0f40b019a40d61250b0034000e4484610f4441a80a446540007003010102d110040341c85140040015241d0782e400d010800c040640d02a01803404c100440d84900c02068552000c80c002e155420002e1101c1403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 44478214 1250 44476964 44476979
    0x7050604033f0e060406091502120a0f0e01020705030414030312180712050309090601090503031b1507020604260d18060c0203040e0105030105100b0703050904090c 72
    0x3501d50309505141201010152520000c2c241c060700b00000c0703600e01c80c21480c45030608005040b4006410210b205107030900c01444880e41c000010103004a00801400c8420341d601d500341d00c00c058810039404108800120751000135072001c241da000d40f2a0210b0600101c4800310300360b8000481c151030541000070208044410400b0015034204107a018505007050314041e404441e000070645050241005d500040241044c40000c1c007403c00d0b80521041000b15040041d50f9800840c040c038001e0a0400100d1305a42c0034020200071a02c0c018015454800ba107007881031000b8a207c416a400e06c52600c5610a07a180c1803903032482001d03254000d1900786440d06010f0f10055040e00b1201108100d02c5c0b1038030b102803690003202d00e110030019011464800f01003041807440304160010b4440c074602000703540e000307601000810803242c1071140348009036282d00c201801c0399820790f440c825054900c0020469800c410b000b40c400f890003414818100320b04140806d00303542e95444d0847d5180c0720747c81e0910104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 44479464 1250 44478214 44478227
    0x120501080f120304030e0a031401050a050114060c031209010903020607180303030b0d0b090303060307170d030c1101020c0a152c10061715070504060c02040906020705060403 76
    0x10080c920007054907407254040e9540b288141004004401c038004001000d25004011102c04036501408000c1100c0d0b0700e0410441c00c030305001c0288002c0d424040410341c1c01c041401094141d5001541180c04904648208202e0b03070312070122000c041c002070000c213001e45082d844980c42080400c00100d010f180c0ca103002810032500030025014000300f5401c200c0342c01c0d00c10740204140e80d4142400500c05a400000540d6038440c2e40e0f00034691903035401000b402000201c06940150025021100200d8480ea0130090075000c001030709003d40d008820081407140710381c20a00303410199003003d55030784985860143c00da1b0f202d20629138250307100264980810000d0900c0c240300e00000401003007403600040454466491005480380d002c0120a81c182e9840c03010b21034000d428809a800b0000b8564035102c00b42440100c0722003c00f0350045000110040e10310500c1c25108800d2641c0d1680b130181009000d030380c01d000802041c2d8006076103d07143c50005500f8402401183d0080300103042a00c1c1c98034009224 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 44480714 1250 44479464 44479469
    0xb03070519080a0c29070b1005030102070f03080c0a02030d050a1e0501080d030b0d030c141b091003050312090102040e07080a05090d0210020306040207050a0305040906080309091f050301020406120501 88
    0x4046030380c440f01030b035211644151001b581d480035000d9969102c00702101034a030a1500415855440016908204143d1200d0050424805d444450103650741c103500f13215a0050944841c0942c0040020380004c502c0d07544040d40c03166807494001107128645101079264010080700a814554404c018032079100c0820000d1445c00f02407809001d030071110b20108004411901e001810b000c440c800e81c20412000500c0c1c0562403e0b018103c40ca41660405083c220a0750240c1e61030050710004080341001c40c444402c6001c0d241c00c480154600141400c201d0107096008203213000303955081c40701042d0100b80154190050425955283c11802c00a110904440010b0b090907003561207203d01c0303a091a0041003060318003185400041c0c681d6119404203001e481026001080c07030050711080c03410141c005001d40280c0300e000078204480c5846100055a03803040050007984460f002c0005107003c80c504c0b40000e18407003050003a4244540d12300c040303426600150403190108849500307001c0340303d2503841207500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 44481964 1250 44480714 44480759
    0x108060601050a08070e061606060806060906100509030303070509120106030c0b0d0b0603070215090705031b031f0605010f020a0c050d08190503190b03070519080a0c 73
    0x25080a0300080d00520501290300d0a0004040000b4002801051360100b6003801030b0144e5501c078044014a100440494401c981d1585002c5010176001c200040c220f04c58640544007880d20b0322100100040140c4a41a07201040b40c10031802c102500c0910245004003407070b80303070a40c6680848040001a061700303c0701140f203a150403030400216070020300d1601101c0801807182d64a40e00c0610780000782c13a4901c0c0c03a41c0c01840c000184242c1a82c00035030850f490b003501720400300300c3c0c4420905903200c00151094903410f074040311103040326400800c5107003201d54004080fa000010290140c40100000b2441205026611032080110b5604040002500042c0c4e101502c006452030380d8161801c0c21900030301d070003034602010380010010000116035480c80c0c0300300e82d010b484404080c0281541c1c0121058112002c200031540150016402910b2081d1001405860040c0c2403005101c3c0024842c0018072400800d418000b0354401c0a10400317032458041c222040c902420405c10155200a28000c0003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 44483214 1250 44481964 44481973
    0x30506091303050d02090d080403050105010512060c0313050d0306030b070201020715020f090a0308030a0612150509160816060e0a1401140a0815010906020a02040b0a080601031a0108 80
    0x41c908a400c1c031524206945402c1c01a140d561303104c1c02c003000f0f009800e05640c0107000010302100340174802c805441164030410007800540c0c0c8410500115419042400100e40d0021740070504406186029683c0a03c408503101f207034030402d40701c551030034103050390010100b0758440c000d0050154905030242e00c0f8140c1d000030342c58035000380d4840c05480d0740407070040260741d400300d41906010504421501e60010080030160761300d07141d0408030345540c4103583d4020f01c03519000001403600da0a011500700316030800b2543c2c0e4041580101c00000e0324006200d02e45a00510910f80d40c05500d1449203005407900070001c050a5140512905009469800c00b206010b04030741189070543d1031810880c00d4900e0108420280c40f200c0005a0b403200d460080c2c40303e40c0380046000303c00c082c0c3c002000f034821400d0801c0c443d80302c2d0602e4010740303401d0503a000d41e1b0700607000090030a02608140d004841680005401680b00f03aa5804015041050030303001190080f00344ca403205104a104020706001d042405c0151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 44484464 1250 44483214 44483221
    0xf1805150c160f1b080f010b09010608040201030b09132a061206030c06080402010f170105060c070504020a030c020601150c02010f020f0d11010e03070f0f080705010c090603050609 79
    0x104030900620151640d0120800000002c101d40755452100c3d0690160801e080715119204c1c0b402180d11901406078180700d54041843c54010500610040e400060040c49459007010b804940703600000300142e040c541c95511303640382da444041c0c00c54841e5680741507000401c41c40b49010000310502110104021301540c90301c41c1c0b014035006c28482114074030308100d1081c1e0a202c5850014261a80c0050446900000002516030b0400e001c00c0c03085200b40c2e40d40c8825513081c802503030760608406c525100c01e10010010b008508102c001400007020000440307500c0703070341d41d00001e05984c485000400005c0d2540c60248045030100240d6000d4903049515030300700592a680142862100e9102904110424116491403402400b86030008a003510580b8101402d1000151031040d941d05040d445620301628901081c002200ba50503183d888000590f01d000076842d01520010194401e4880540400400000801c01d1064208031503103519030005807445c25074040d0031a5801403c0d6070042d5404000c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 44485714 1250 44484464 44484481
    0x60303190306090c140d0e0a0b04110112090c05060a090806161803050a060c0306030209090a0c0609060905150c060f0402040f09120f11070f1703070f0f0302010f180515 74
    0x6031500e40c49803c2d800507180007d540701d9031401e9400800500b0043d007071000d03c000c0c01914042c00c00c00c100280ca907061100007151200c4222203079030601a09100800006004525010f0014400c10304c00d450658200c1d51680d0042e814a481600d1401048075075004224860780c100c03640c11260030345030040e0b4804500e1074403526140e00c100c1400420081d5900e081580c0b40c0c1c02580000d01454019003101c00728504401c0341c41d0ba560400100380e43c40d800310000028110b20800d203250a8401c03c1d602c85052500e020140810750344001860f5020781028000d90080364000c02c040ca204083c0d600c00140d4a0419005002c110f070041004420309609204110010540319403400c00b600d0003d2030320580c0310b0000c0000711604034401ca0a8040d0340111030000401c07500c01901e09040c5ca690b54001103c205526901550320701c1020b0004104510f040d030001c3c045418010131880b414003070f0001041c0360710b00d01101d004481290800b050000d00036040a0180107003000081049450201c42aa071800c05001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 44486964 1250 44485714 44485717
    0x80c0123030618010e070305090613030e06040b0f07120f091e0503060c0a030b180105010c050102130f06122c01020705100903020d020c100305060303190306090c14 72
    0xd014003054400404108582ca40c0e2036410442202100c2500751541c4482e010700040b00255102d0300000e0814010480d40e00c404600c02d40101300000c64002004541c3d58203580302c0501d40762955000409220006603404c801c0700030702c03482c02d41c2e080c42c03030b5182d100d4544109507500c80c0307181030108240204051905500100d00b50103641c80b80360803140c05010311800d0820741c141e0790400380d0940580b10501003145011000b80c0f02c000d840d40ca080c0803180f0301d2001d01006140850b80c200500d2003010042040394003e10710311103514012000546015441c2c1e04a000100942d032029605121101d8104819640030564080034180c101c0c050111107506a8a95a032941b0901d0248c0c0e00d40769005c10004017102541140c075042e5008040e0b8401b6008052100002c0a5189056000d40181d0202044031403010400d0607032000010b04003030100303180200071001880c1c000c00c05d0350144010441c6440e9140f42d0030b0540c1996101ea6808140c00703080c41003035804d4415150008040c81012501d40782c42104080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 44488214 1250 44486964 44487017
    0x60105060d0b040f0501090f050402090103020f0607060509030301050111031c020c07050d0c0503060106210b010903050312070f020c0d060905071206060515070201050d0e0f030d06080c01 82
    0xe585507120700c114098203009104081d0443d5105140000c085034600c00e6400513030407145030010801154107048407000585204540080d40100024014001840c1009100c20201c5003d007050381803041e00d5440390201d40050312403c3c2146d00210041026603403248e0704102e16021f0310040c5080c0080900c42c2d42d00e140300006c840f51201d402040004100d0002c002c1c2c10004e040007001a84028102d061044581d2407a01400380240aa035001083c0f482c05448240c00f080303052080c5940a200040e80761000b403c004607254100540002c0010214008201402c2e0100c2088008190750a11600140c940805500d88006540000105100c1c5c4d943d51228002c089410003001310300030903140b4010381080c1064102c000418214100d00c400d20259074001410b41f4001e5030b15150740320441030002414040d240b130003400600100305140985403941c0182e0014000b04003268200780d1850522415a046440f09016441d525541000a440100a495080c0000303080c108062040303295000e40540215 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 44489464 1250 44488214 44488219
    0xa120309110d0503130b09040f0b01020d08091608030c071a1605010f051e0105030a020a1e0b0c0a02010318020102030a080709030c0303120c110309010e040b0301050406150e0108060105 81
    0x18002c81d0034080240110703244440030740300701d0308103503200c141d100d80d0780d04010f8420340101d03c0c001e0b111010741842d108107070200310141c0091000081006040320b90402c0203001c049580103a03202003103403180c0d503807520001d06841c80140d515140160081d5141101d1940052800f00b01840d14a43c1d601c03400c0e00320b800203586100420842005401c19074050321109200240040c601810410360288841e2034005152540980e41ca803640d8441c02c1680e5000c0304000a036000922401c100400e00001c0030030b499a00c45655407619281c1c0e83d812a0784c0d46d400070f6402c01c4807900328603550000c6613030612039550264807004501c005105d480d00001d540b030198500b000b050001c108080b843c00c5020302a0700d0001e650180170741c003241381c0f289002440196013640804515052850000640f40510a1240081e032038200070f60411141c017004550340703d003103000180c010355941000c28040e2801e02915104900410010030700c8081c20320901d4000d0119030104081003d40001440040030100c3e0301411503008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 44490714 1250 44489464 44489479
    0xe120a030b040623100915030b010e03010504080d060f030b130c08160e0c0304030c020411090a0305030901080f0448050406120f080a09080304080a12030911 69
    0x70034080781c010080c0390024a03c8410506080248810034100509108401c1c3c0e0b41074800701c45070f001030394030054030300400c0403100301e200000c0d85030b6120b540040e040220516120000300700013400b1a08440c01510306407911400094085090515402848014442d204107604401c0c6540ca03a2600050050210440c0c1141c10207048184040540d00070081c2a07000c0c2582c691421011400210048500c500c00781e04100390b00199005140b94140c2e803007160562905103000c03007103900304401082c0c40340382110440301c18400e89207144c035940580c802861003900115640c440b00c0001400041c801400d90004502d90b80070440010300b22903003131429201c403030307411083c0803000003080380b008062210140004501e0042c0351500a01d0b915404220346082e20100076050711401101ca0a1703480b4040a4404000076021030300061901000380094241c0d40390540c00345840e685514290740c01035009115603401900742c00c00b40003000d010b80c5c2d01c000941c14100300c03c01440d980e410b540c80300c1c1e20030389101e40c61 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 44491964 1250 44490714 44490731
    0x9010b06040518060a080601080a260d110f0d020c160302010912052109040501211e06061502010f051605090102011d0d1e020c0607080906030f0105040e120a03 70
    0x1a902908809000c4050a47d25a5a151003c455983e1040f1005a40805405a00c01422252100c045003600c1a0313641551500140c1d0030002e000d400e9002540c01e111208100705551580d8201c003a01a8505000002da9641400305001d0320f070546070580d05101c140e00c0101000183e030084440c00494800100030b0741c20841c0b605041d0304000d403620742c2a48020300c412500d00354001d40001401300380c80c116810001a40c136001c110b000b610403030103400368040042e014030340400e01c4d000b013014071307000340b60301f43e9900400135611581643c0050b40702c80541014126018104c2c0c1d0203000d800866240140100035a180c00d18100103a10a00c07903450050100c001002802c0741d20039003000070038080d4040201710750b000101c1a19940d0500d0071003180020714601c006020b070400710700c4000201109a005002c400d0319002000f4041d072107280e04480310301041207142c600742c032550b02540c4558070b0f40c90500b58540c540414441604c1201028071000c0d0424400c03c640940c50005039080b259151400160303069 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 44493214 1250 44491964 44491969
    0x705091f0e040308090f0a24061701060305070b030702030a050c010209040e1e030711011827240317040509040b06010e01020d09050d0c091409010b0604051806 70
    0xc03440d0046240481001c0c100814180c02c6104540a10000c0381180c0c942041c0702d20389501d41c0b00c044001001c0c2d02d0302281c110200440c0a02c000c841c180440e03000694296142820340c0c100c0201c3c140c8079483c0e5100c24040061007020f01c2090700801441c80518a0361801190003034803441510003030b10a102000c1003916105000750305aa2811002a00c1004001d0310a0700d556901c40100c00c2c041d15402c14040e450b407005201105540c0c1c0c50340c2c40195021840e0001c0c0c01520000b1110940307102492010300f000a50b116022914550002d41400050780e00c80d140446078240d486a050880e0500d102d529047d141480074044941100cac0c000070440200c01c040e00f40c050880c8525070046505c01d000506020030701101d0341080b80034583c00d8807501c0c4810508801a0b032070b507150444407030104041032010002820b1010424500c07030310130806884002c0c0c035507018008482c050107140c0f8280804104000c0201e00c00d200c0d05484da0000c803000d1707040134035140020b00c070388102c130203030090820400e0080f60f403d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 44494464 1250 44493214 44493271
    0x1505120a060e04030309020f01031a0603040201050c0d090602070b04050306040b190f0e1506060406030e160602010c08070315230a0b0717120105010503060d020a0602031209070509 79
    0x107042c0281d044140d0704060a00402425190070140e200781e050b00d580c104258041e00c80d058080c0e541c2c5009055075404981042460b0700000e02c2030f07040c003904202c400300d0407100f44030754004642c0070f4507000d00030350510310003c0c0341141035002011401c0c410401403056990000f1010382c000c3d889404a205a61607a426103602089198004038603070074101154500c0c10720750800e51607031920703604442c0c40080d6200000181802502c00c1034000200308011700c1990321903084039607105d032001e0890b4600203280e03201d041e100c06290310000045c1d42d11660341c10901d5200c0030541c0c01c40124030703003030140d200f240460b01c9501c0311622400300020b81d00503072001d01c07810045005806503001000044081d64400a0310220b500c03c46040380c41c3d182c11500c0c031101c295940d00b81d80f082001402c000032560308000040d43c03903902c06000107501503280d100d16401a038031a00014040c003c20341c050340c3c944003012140c1402a801a204a6040c1c014100503c0380d1344031415400e9001500003030400c0b00d000c1d1a011203049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 44495714 1250 44494464 44494469
    0xc020604081621051c05070c02120124090513020a06030921050a02120403030504050f010e130b1c020d020d03051201060309140609070303030509010608030304060c03061505120a06 79
    0x111519254070801604100034009420216407000805d00e1800d1031002100c0040300c4120120300040d00c0f250140c1000500b41804800b10000000c08008100110f18404c096080f005400100f83d1014050110303140a110740002c01120403888018441d0700103503200d02c241c0901402c06948031000410700418507110903818941002d8103401c0c810461000300598442080d29016209426000001402020480c3c040700d8160303480e50704160034030080100c804003a4030400d04021150581e90001d40d181003c6090410303141d10001810491001448403240c80e50382030a03001c1c0c400c03e4106015840d2948102e107556030403201c00803460103d2030256440d029404180c020400040c0010540c2c80e0150301c5001d501d03004d8036503511200a14004242d9441040b104080b0702d8111007020400207000341c04c0540c00c007800d04000702d200b90f11002d1091171030b00120b1701a03d41c1501c50700940480c0b901480762002411092480b030740f80700008000a016803164006071700684081c10300254a181007544100302 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 44496964 1250 44495714 44495753
    0x6040b0409050307020a080706020a060b12030a031b090b09040b030102131223030d0f06120b010f090204270603020d0b06090106050a0c08070204060801021605010c0206040816 77
    0x10a03110b400c06039030300d41040c40124001c0d2110100440c551780d0010341c0c00c0884e0825801011142c42580d12840a0070403105260b810101c1d206e513412041d8000c0c030180900c84140c1e03500040030034070741044103000d440111b81c15060001d03084d01400080f0b54101186e00454054601040e0344140c0c0c0003203402842040c03880038070000e40d4400480d5044032004452510760003640e2203180004413071000100408119840281d90384100802c01480b220f40c2c100051321110000b0001c0e02603501c030303803400000550080498000070074400520003a8541e01d02e0001400e910401141000c2c01d04910400d10aa110144034401d87d030801c1c0890031917260307000342010b15405054442d0b003034114a42241c100300c0540d030707840c400d00000002080843c4503400381c403055a10361742c4071920844551104200f9038000c9030142c0e0032030f4940c2c801060f0750a03740020704114070004411020b1a6880c10074500710303000d8880203000c540002c0244008140030346e081d20304015202582ca4983d65a47c80c1c5140300e4840c00c0600003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 44498214 1250 44496964 44496971
    0x309030f03100311060909150f0a0b040501020105090d0903150e150412020a020102061b070506070203040303180b03070806060702030d030203070909090b2e08030405130203150906040b04 82
    0x401c040b03800390b0031044910460812507141d90319002c01003e0302645d0f1400d50400c0100c0001048c0720f413003400703000a0110140005110803942004160741e401c458001d010b283c040003800b000702f564240320b1190300c0820b0401030112440418001400030380c4500c00544904500303140c1e4244041c051740185001c180aa0403a44070403a003803201019a0300407a0161103410500100b516020300105852104550503400b82c0000d40c0d8600780c0e8151411921000b0b01c825506209280010ba810001c01d4096441500150748035442c6180050100d03296044000526100300c0f030401007203404c0c0050302e81181755030500300e50b41e603115400700c1c419005101d030184d07051041b401110032158041c1c1c002c501814644d41c0c1c1021035502c07108180241c6d0208400202030114030300000b1112800d0000408104519031047c84070801c900202da040854940c10001c102d80000500304030501e040c080d410426091100294190b1424a0310b009c082003240265602424a0703400041c081d564542c4481010700d002003042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 44499464 1250 44498214 44498221
    0xa0602030627011a09030607140903070e010806010b25080d1b030e150105060d23010612050606071101052502040501090603150207030c0b070c060b04020412080309030f03 75
    0x7000403828400c200e441410400080784c01c00c0c8440c11035026041c054010308490f02d402c2030455250150002e49102c1e081c0501c6200603c4d5070510104000b0041d800003100c072075040c22261810400184c1c003007480c1c01420030801b140d50b500b0210380ca40280011080f82840000c604004c9041c0c17090024a11701203280c07040003510320f0002000c44c4882d05590350104035510110f180655101c0b011401031607420003840040180749001c00040905041e107200200741851000c00c2d086581c0e0604400300d1465440304010b111440c0c0c0014800110b80303040b103050149040070300106d40070380700b403140c0074210096140c41003581d64044d104882d0144410100130011580060b0a0381da030b440543d404a128070700b040000584c4900d0340c003840301920780001004001d08440416200203602c000c00072020b1021504401c00451402c9420601c15800d80d02c072a140c5080c1403900804440301d0111251044d48148403d000140c91005400141ca51100f01560f580e142d460300140b0394044c41207a201190000803c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 44500714 1250 44499464 44499529
    0x20a08010c0e0406060504030206030c040306110c010b03070e041506180b0109050301060803040501050d06120f050105060915010c0317011706090705150307031b030203090f0c030a06020306 83
    0x30304003901c020340e900c1c031950b100d4400700300c00d8589910520000900a22061001d898013100440e00030302c1c40800705103016520f59803107080e103e001e1101100701c1004200040206020700543c90b480380101c0140500b03604042e0b00b0440b6010180028041295044080800300300540c403003006420030307a81c10b41c412410b044404001e40700074070809000400004000a00342414010801940c444001545c2440d0501c401160941c02001e14400720755110040090340d451650032190159000700c2c10003500410030f0820760300396500038220741c0c007440c0c2520411500084144805c00454424604102004118101211b05280000c034402000003006d00008607407240b0b00f01000100400001e41b20360356181c0984a4885c0c0341c0744600b541002c0710700c8002d82c0c800d0301035000715800a56410000b46030f5500000c21001040c00390079080100b60f0000500c2036044042194200750085000248400c103449000309407650030441c00240b240c1d4021012901c103907240342c800c0e56005100084180c52031f684000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 44501964 1250 44500714 44500721
    0x20702131805010f1a1f0c02010c0b01031a01120506010e090c09010b0304030206010b19051c1a030f0703050a0204020a030914010203070306090204030f020d020609040e070f05040c0c140703020a0801 87
    0x189903d1170740c40c136a2034100c2410100c00c80c0ca0742c03aa41a4880400c02e04000701654100e43c04d482c100d04100590341035100060403840003901950003450300a80e0340355400544852683e06802c006810041c1000c49000684002a46415101303552216185500c07080c00c0c0e1850406120034140e48005840c002085100a2501851046000b5801c27036243d40d07a110034803981440340c07200402c01007643e800742018a5008800401814014464907e4104084880b0004440d01c11400c8003080660b1104000395107010400400340c48102409050b4192a40d500c01d5a03818160344024061034000c0b441040043c042d501018516130464260340f03000100c411000d00039402102ca40740400d1074a600030500b140325209032000e80e03030700a10320004c44200d5000c20820060031503049900800c00c00a007100390703c590217a942021085c000800d8818149003a0014104450308224003e5150a40100d91103901c560514804ca8003c0b20380406c00103008080e909000301d40d0000382d0080424440015030040561 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 44503214 1250 44501964 44501981
    0x506221205100f020a08040f080f0a020607090806070e04110403020306070503070206010e0402010e0d1104020c03121509061905030105071706090402100e0307030203100b01080109020702131805010f 87
    0x40b041100c8041d540b40f0b43c04030b00075040303035000045954000500181059500040c170314000e0141c00e0400318901545180b40d844004000f0041c1c10180034001d6480d000302040300603150346070140400f440c01007030003003442442d2018140f14035110703407446a02ca8007440889002d95009004c1c2c0300d80b40b510f14405000c9900581d11000184241800011346880c0345040f81d010300d42c1652403000c510b0458040041802e00d080741030b2a0740c0c0d444000c503e40b585e520710050170030b900c00b00007071134480b44500480005600d009091600002c0c09a6180ca12a694951200c5c0d01950880c0d4050781c207544003c120f0030141064001540562914050200f0700e0b030020f03c010100514403806040e907a4844090200d011429a4025003050b0040c1c1c0560f00d280c00b9014030800440c014040360050355498001170325191508502840e06aa00c44c0003074002d5902040541c007600d11400150b2410300700b03070b002c40c0d81c010600740940d508555a0a038030580080d1381000d00f1710300740c00000074003500c480501044018210071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 44504464 1250 44503214 44503243
    0xd0507030305030723030609150a290c0c040e0a060504030e100509030604020123040b030709080d1205040816140c01030b0a09050907030f03050c12040506221205 71
    0x2c1c1c0c170b031500300e42034950710460b449032005d40782541c031a2010301441c43c40140441d04400c80c0140f98501c1c54407114030600003444c076444549070108102800e017810b482c812541d036141e0601000841d18072100058a00b10002c4c09440010707000000c00780e01401c0c1010608000d043d51704000900082c1684041501c182d0301088914040505081034181c0d01e81c030504e510715030141c0001000070701545c0a610780d4100041c0c001d00d1410020429607480000b607004de00202030344079011042c0b014155002a03054007920010006064280289030083c0000402c1c540c05503110742c0790300025003003003140020369004600401001e280c500315441e0070411004040d60804091103000840d8196610030b0244030b80f0545e000e0b014651403404d000049020344401441103003944146d2000100260b090b070540c89045000b9a6601c2c0c403441d00784070a9040456802160191150912090002da0354503c1241c01d808000d80196045e6101084c0c81004460309070311000c6d0081d81c1795a550140000400d10780c900f078104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 44505714 1250 44504464 44504477
    0x110f0d0906030204120b0a110a03090501060602070e0a050702031c09111c08030606120705030405060601050f040b0a031b0302040305190f1203020c1903081e13020d05070303050307 79
    0x100c4030708900300c0c0603520070700030040b17100c0c41c05001150320750380750300c0e00080d0519001c6903461072040896001e50052000c04006550342180b8402d100c0203100d0310025113032510141135030b0343c6001c03804402c4180140021103030590310004544a24006c004482d0303504000c0a028164403603440c40c40300106201c0000f600e5222030129a807800745441081307034110500f080f8800c00344240039262a81541c00080006810400070403040d5045104112201d10a400503a50183eaa00e00b5241090a010002d4911418040c0c1441001c43c1069620300303840999243c80d040548480d40903408501800c50702c481510085990720010031a01c5e4181c0080c01901c0c00b440460f403c0c0079100c0c00c06610501c120f41b0103801e1a40d0070016400044103521900c049049034507016043c07a0004512a0a1840b40d1120010349880c3c20341407010181c101d9000703903001d1680690340d4581c403255010030803142401002c02c9410b0000e01ca0301400c540d10782c3c44c000301054101048802c0b2940702d00d4090000c0c3e000751074800120f500c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 44506964 1250 44505714 44505719
    0x603120314060306010b09011b060209130507020309040203040f020904120f05040b0d05040507210201080601032903070306050a05010f080a05030715110a020706030b03010212130201110f0d09 84
    0x3003a901e40d01034070000d001855281c3c41c040003541c658000301101410007031981d81c806401030200c900e00c103446018060040e61806600c1c200500805036544917580da07820401004061500401a140141e4050fa0050b07640d69452030032802c036000a5000079841a0b540043c441807140244503800b1000d00d45c0c540b542458500c3d44180c1d524016071040c90000d041c10040600861000c0d0001c03908940702d101151030154031040310910248101c0e544a00610740b001400701550307400201c9030b412120030309042065840082e9500d040301000c030181035a06050039850440b0380c40c01c001d44401190000e00400450800e0b007207550190000380300700b00441d00030b55800b042008000c00c0d042c00c0c1c0c60f4484000c0d850043c09950306041d080d0b070800c0c402c0b001030b910703200607100c1c1b80c014009150122107075003d0a2454100000541141d0300c0152490181c0c1c814030048103000c1c40c44074280d4020345203078078030000a54540b00407141895514080c1604c1e000340b411180c040d8800281c0011440031035154403072002c0c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 44508214 1250 44506964 44506991
    0x604060609060b04090c02010608030d0e07060c030c0605250804020306060102060f01090e010b040606050a08010b0c0c06160609030914090c030a020c0c101d09060a0312030b0406031203 81
    0x10b0a90003035100c0c1c1042000200f11060a503402101400341031f00000c03a4030759071a0382550568209e00107030101540c41c0c010001d140502804080080d0015003401e00059495840040083c00d0301c01d00100103075618000320f5103040396419600406000310b03940b14010b000c500001089501d00343d0702203002c0c0c0304a0000c43c02c80c1d0b00104801b442840c0007400d29001d42e180c4400240070303204242100c5c15655940106140c3c5403501d0061030302421440d16400d40d00c0d00c08440007014500142c0c0030a415100500c404a0b5284004c902c1007885807084461f05c0d06c2d040340c503600150a10400e44024001441c0248504c02c064001043c501140d919110b1407034022401f1003804021101140c00d03141083c410000900000050b902070080190044100d420310001c083c0495406000075100e6800305540301650f200204562540f09801441901d40001030300304800829101d844501008100b000c01c5120603031715602c258003001414200800034040e80c1e81ea0704000450300800301e280070000c0d007815081007020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 44509464 1250 44508214 44508221
    0x90302271801050a11121008060c0a0f0c05030a050705010f020c070602120a0203030417090a060905030d02010b10030c17010306061701050603070620031215090103050a020402090409140604060609 86
    0x5d481d00031a10728203803d042c405001500000c00c2c7e01004020804041030220080242c20310900b0396015140d5600c1001c10042e1150b0304c81c022a1003040030315000702c0002940802503c0404240d410880c1d2140d001d89000f40c05000b000a0b0300d820b062010801c03a401c0c540014000c02201d1103602500d0400d4010681c03075409100b2032400c100540e1040021800046090881080c2d135040d42443c1810080e061000a030000c180c2d42c403403c00610302d8a000e0155240030702042901e215103000820501c00300c440824a00f09044068009055a40c080203907064000d8180280b00d1b401c5603250219980c5916040c0b000740701a001c0d00b5028a40390103800382c5c1c500144034590080304020000d11900d4a400c104444824000b03a0340e0b41504030400c0000511a41000a02200010003a0b540150300e44651100000b490444075180306030292001000070400c0426442c031b4150b01614090303a101c0300400400e0190000071300040001c00d2a174038074a07a5460229040c0e00452248506216036540d54442c02c4c1134 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 44510714 1250 44509464 44509481
    0x12050f030c1306170f0c040506032505120c0c2d010b0d0b0f0a02090a03060603051207080f0711090108160f080c01030e010e12031603050106090302271801050a 70
    0x40e07013401020410384103219208aa000520580b0645020303202c402041d40740d0026034080340035a1071a6208001c546107410ad46038903012929215042c5078419134072100f1014081d04c1003610140c0001d43d080120720520105811114403241e1074010001811220200d42103002c1401c240d5290440340b005074a4020002d18801e50018a601c07a640c941030704a07184003802900b6001c01caa03080000b0862900e402003000001c601641c0c00190313003071850904c142400c0036290502e810742c6081103034400240151068603a40402d0041e85a1103a040f4906540d44808901800c0e501c40c141e40700016544100080d00c9a20b5001101441d464540d1101d15204c0007007903000b080c4c01070700b16030035000b4254420707030001039404544400402e0251940496904210040001208180d0000308008180301c00d408844000c0055140802c80ca40c580342c0f000300400d00ba0301000340701e01020b403640003580c144510b00f0b41000a00000ba0600c03820321521544003224960040c40340b41d42080000340342c114092060401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 44511964 1250 44510714 44510747
    0x180d093201030e011401080307020112020a05160f051209010e030106060905040908070605010b03010302030d0203070b010e040203150a050709050f060f131a0304031706030a12050f030c1306 83
    0xc40c90840150090000d0444000103903580703c064001c80054403404e14000c2511030007456445c4840e0000400303140c141096003141c0303401000300325850355110040f00e0b2240c4d01c2c000b1941c5541c001d4500307404941d4080502800030f209000b00313040c5a0141c0307002050594826200d00f0110b20010060500b81d440510441011643c052420001810170345c0040c00d109210b2544680750005580c1d5600445200ba0028018031101100600c1141000c101e061141107490004600340740d210b84c0d8201882c0701c140a00ca204c030011901203400c54508100a40c00340190310081c5500d40340c40c0c90a04020801101c101c1c000408801c000a4241462036021000e400082c16080c5003015202c62103400ba803180202c2d1030400259100003410003c00820170701d51342c08501156540f4146030500601c1000d01d018620326150100080c01010356000402c2220554403034210808144c1704a020340d143c0c0201000c00e00344040000c200805121908000d103503a0181c102c01041598559804035050119600c0209 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 44513214 1250 44511964 44512049
    0x507020c030d05160606080303011a12070c030519020c0306062d030a08070501060303030b060a0f0807020127140d021902040b0d030315080102031e180d09 68
    0x714402d0f00180b9000c0c0380901062803840081e5a0b030710031120144d00c40103454101000500c808031081c1c0c9a142034045420000b810120560345c1c0d13850b4500c001e4400030610000c00034600070035000304180d501d6002401c44e08012001c4000b401ba459480a02190344a8010080080c0c06c901c1c21669441b1a228000c1c0003d10701d0503807080d804052580440440d9261058481440000344900028943c062048001049041c07851901905035100b4480c0c0c40d1140800703201d03400b01ca562002c40d408401800b40781541d0756488025041c0d004140e44c409021b001030300500301c1c3c00500f018220071145580700b000300e45001030b45a03526544480041c030058006030044010401d040c06a2000d101c0c0d502d00043c0300180680c800400990304004d02d00c0201c0103c4d85995420030030704007031500d5070001c0c090300000751f14500e0140440d02d0300305070110400d50506000004a812054202c1d6060303c2d51403504201c030a160303144403000c1c0480ca11362003821408001000b00109005e4800030300f1004092103444030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 44514464 1250 44513214 44513233
    0x307060311091203070f031101110f030406051b0301080705010206090a2a0801181b0803091c0209010e19140f220309090c05040302090f060109030b190507020c03 71
    0x50942c61009400f644420f03c80c40d000710300442d00700190288030b40c035190700d2000b0030004e03642036800c00a55032254400c148040c41ea40d0b0118005c59a02c980e000c1e2000800303950300b40c1d460151450303041c2c000d185040c01000110300300380001205001d035402602110030710b507960a446aa2002d09440043c019071840807a40305a002c0d030b259240302c0c0d40000b50350803a05900c0d0003c1a08403110340540303140900109010100f8003000000022402c80201d4000c03a105051045180c0d6034400e22000d140201448107501000049a045000e2501d500402518480d40d540400c0c5a05c00419109584417040c107500504130303004944540e090725110303c40c544900340d07940014913228090007026100e2084041980160403075080d424001d406220383c40d420155030509001808035964485040300780102044140056078481c10030a81c4481d00c07010455450b40e40e040121604000350340020141803400c8123000010703034813062036010034440710403c0140ba5264942283c0d2580e40c00c4526070142c0120001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 44515714 1250 44514464 44514469
    0x403080702100210020c1e030711010806040b030115050406050616080906040503150403020601080304080601050d03170708010e150907180b16051204050102030a081017010902030706031109 83
    0xd0103103042c420700666403e540c03030704007013002d80c1e00914040426801200c4100d0b20b094014810111516a80000f181401d070103550355100688044a03150500140741c001500d903035a550045226100c0203002408001c1b80d0034284070030b550305070151900c95800d054000c2403034201401591402031015400c030140c25140d440380302d080c0d4410440c013508000c040201007841d490820084c0100a40001022040d19081c03c00905000040c0c1002c01d554104000c1000120742c001801810b4407800c5650302c1515900780f6041c1e030045103540705e11012204c0601003100c1c0b00e800c802003c1c12a2000c4024a0032651080084501b014ad003044880e4001c0801c1d0105803460700c10001d60040c1c20801c0b50081f2255218200303e405a080001421080013240e03401004000007071028040080e81280c0d1355041505100001c2d489000d11408902001031820000d14400030030140c5100900c400c80d482d981148450b00faa901801400c0c0081e0f000e88900e40b0000b5202c0e1183c4903407401c82a00b00503480c1044080b608 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 44516964 1250 44515714 44515729
    0x301180b0402040f141503010c0207030312060e0106020a030e060702010c150b21070e01050306130302010b0d06020903012d0c0306050315010305070b0309060117030d090c05040f020403080702 84
    0x1c2603030095079074442005142c0203446141160039521105038420b14040f5034000b81c44020400391402039042c000c614810507000508030f01601d61606224200507030821880008100c42c0d40040700320200700c00001380c46a000b180010496000356151403c0d44c0c0c031441402003038030814070004c1c0050032680c000300200e00c0c545264180c0003550b150105d003142c0185c0c000780200c10325141d501c1c000d818070340f150002c0020400c4100018014107000b080c80790715000c002a15058024901201912400c241e201014802c0d440341070f5000009007500504502410644007d400131560706020398078058011040f000b1400802c2800c00300711000d03450344407138007201101800c1b5840f401801e01d600c035080800c5a80d4140851090018400380302c2c903c070341c518105245821425848580c40080810a004049001080c3c0905480c541c50030384001c030044029240c074503c24103003d0100745291044d840100010340305030704100d54048909018030382c6119950022880789200081800d0340c10410031006081206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 44518214 1250 44516964 44516971
    0x9060311030622050406021308060105060301030b06030f060c0d1d070311030111030103060f110403030e060a0c15050406050907080c1903150203040c0e060315041b0b03010806060301180b 82
    0xb040a801c10743c0140d5101581c0058a0448030300d60040f619107540325403e2050001041d203080101100c1d450704021560602c01800042c0040f554900011304c50b840c00c00000020031400c004681c05440c24003a8816260024604218040c0c10300480000d0100e4030481100151601005004981d01d940d80d04a41710032540c03001c40d01552142c007940130211030345010f5402980107030004a06000801c0b84c0404480300003802005410082c0f205201090740041c0c2081d41c080305860055079400c228100b680d181441480041ca11800c0c03000c125a00382d05500038030b016a101d42070522054030340c9a806501c1c0c501d036004010055000f4460f040b91850078107102c868031200b1801e0504210b890f40c480c403210310300d0403e86403441030b000810703c4208040300b00702c040141014111910281001c4000940390300341c25052200f0b071510341000c6024000014101030500030103181d401c0300240d8421200001d60400d104810312030181c0c50002f055401c06014480205c1c03040d501400703404100e503803515071b07a0300040e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 44519464 1250 44518214 44518249
    0x714100e030606010e04060812190302030912030408040b0403140601080f0a0f080f0403080a020c031f0507030f0c020d03180803160c050703061b0c0c120206070b0106030c090603110306 81
    0x80ca400030b0361013010f1003203040c03901c0803043c141d2ba10170401050050702c0801401c043d040510400c2006003103c80403558140c14600c880c10142d698480d41841609405940c0080c110314500280000420091468002e000c401c0d840680d00301d41e0342c949450303444000901803000c281c0c2110036400d0028150030b09005c2410722800303400d030030306814100364040c94100e60811120050b001071107415441d01080008880c45045004003030210b001d4060805842400195000c190303210000f0902c071038000e82262200d01a0680c0c00c005403a0721080082d03490805203162008245081480d845150703031208224202d5401505a41c0380d40c8800b0351a410a8821030f0301c0304200f012200c5481d00048044c45464000c50154001050181200310817454400042ca03560301031203c6040c040e40050f40d03005240b02114040141c00102c1c000d14004102580f2654400924050310b9034008100389405078040441e00c011640c8140c0c0e03158036a0741c150200e0b001d043e2001a2000203000084543c03401d40207038400400d82 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 44520714 1250 44519464 44519471
    0x4060315120c05120102030105130903030b04090602031005010806030d0e01020f0d0201051005030c01020a060b0301060306020d09050105070c0506060d02060403050115090506010201060e0a0903110714100e030606010e04 96
    0x54100301581410014811907285542c42d6003080305184c01c424007424811500d00071841c5525040000707d401c442041050a00d41e142c80080c02458020340c0505201d0401a0051060708228507000d40203600031902c04946c603240107000300d59548501f542c68801c46014000344102d21020314140d41c014100c2807850304600c60003007610303010303141407089d404e100b10907070008241401d0541b440080342e80140c101501035400481c0b42d400e2a80d0004549100981040000074405175210101e40504415000600303a9400000c40d01c2400d00140d210040f1a4010002008240c40c1d001d8100c2d0aa4211003000e0800c0d4080d1001c03480300d00d40300901c404580e100620b20782c0b5055496440c0d0b03095940750850b54400c0b15130828200840e80003400b44990004003440200411400d00020080c40003003d428401442e9075214004101801140e54502c9e8108001c00c94491036994090000c400203005181c502500c19039140c8014036010b5040c04a080074018080c0100742d4401004503284070f100c40209900a0710b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 44521964 1250 44520714 44520719
    0x20403080f07030305062707020f0307081201050901051503090106260d110a0602090607020303120108070e281506030903090f0b040b0a0507020a0e060414060604060315 74
    0x24524010190079148481150301d92009050250031510002e04041c00350008030490740c071940b00144484694144082150042d03112494200c3c500103001600e100c480c80005413810034461208042c00c91071800b134240e070840c3d0303880304140103038040700384a410741250411022940c0e0b408410081e50380081c120000081965480c424001480031a09582c0a042c09600400300d0496007030018002180b10350501c2500709034046003d5503a4004c1d580050031095000c16001c2c00c0f961404125896550000c007140d032542c54203000e0481c518800c2c0700e14081d61043e03190000300c10b10b000d102c1c035200399440380c8600600070050980314030f100310190340d042e102c940d503181001812540b00540b001400107542c0000d180c200d180b5000c5d15040d032a4006810b458850203041040d11280011281510110101541c4801c031042050f15140201c0340001c1d8484000c00011440840c3c0060080c411241200d0a00c03850b56030346451140100142c81041c1c1001c0200424412240241c12024000c00e40e07103e082600e66 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 44523214 1250 44521964 44521973
    0x10b0d0e070b040b0a14040f05030606040911010e120d030e07150504051005160809120a02030703060905031308030306010e1807030203060f0315070e010512060d21021c02030a12090501020403 84
    0x501503006a186e1040e4448c00f4416030030100704150f8058410b68041003050010740303400c081602e902c0b80f4141044031400007032400d0b8a41c100020b094010400445c0c1018001c054040c0c0901944102040688592000000d421036824a00d0710304903085d4888510f450b003080c00744a491001c0c12170340c10600008021200c0c00101022034500881e006800c5030340c95641440400c082c007018004412060b03032042c280d00c00941d80c081103090072031703a00c400c000544022610f803460850143d034060110600c1c05120010304000040000c0d8810361782680c0c1d40301c5120701d00080114200c0c0405010303505101050010b43c44601030360096400c40381c001c0882d080400c8005c00203240c240c919400c1035800d00004107012846400841e00b40b0394040908110342041c2092902100948004001610940d02c111b05a000c0c0626190f04a41181c820807804d5002d802d0300304080d6546406580a15400034441009540076102009940d0344001550ba8a422050105084400b80c0a4817106071001d5508010000028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 44524464 1250 44523214 44523217
    0x506030901060305010c17011806120b0702070b0a0807030c0207170a060c03060810020702040f0e1b042c070803070c0e0105061e0a020f06010b0d0e070b040b0a14 71
    0x204954800407079074030f0031894118291411944504144030581600300010700a050060741907409100c600040c0d81805500f01001c0d1200c0e62001d0318003c2c400c0400028070401050740b9100304501d030210380e5580d6413000310380c01074031844840800148100b40410304451294014445140c0d4a2044500d52501c5520003c89201d0100c445d041a611000107242040054020020201e0607402d041081c0c0303182c01c864540380c28a40741c0c0d880c080c035400100c50003103540315032080302c086902c0002044030846d0144099601d2200800f0030b54016202c0c0980245480d1901031003000a00725024501c90300c0148400e842144400c907041c080c1e9006084001c5060081000034240250080046004461800b00c0e0340040803c181c0059004a40030806a1b0402c50b0440c1d1105036040700f03002055450410b43d90813030900209508030784070303805000000101e844081000e461074810034442000003005240b18143e490255200b1001071401c14001000000480c0340501410305681c100900c000310760010b4a40746 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 44525714 1250 44524464 44524471
    0x30e0a12120b040204030503040e091f270503091c05100203010e01080a020306070c030e0d0305041d040b01030209060607060e010525140c01060f090905060615070f060204050603 78
    0x40d12410600c031041c8071501641034088401e5404602c2c281c00c6440709500c81c030070781c082c09001c0640f40010844103d01007180c843d00101142a100300c14212580000103000511040700c0d10407022109510401e40c3c2a0b50300c1400d40e4000000e619028194050100010100ca0380146204118500300d0120f0001c1c848890f090301200d00040c1d07258180101010110390607040041703298442e085600041c1c5000031030680103141c9091a01d40b01101d45030445884402c04140380d0044940c2d1200e00801d60401d000e0003d031170500d02e440503203070308800a02904842c00c0314040d107580d030704000400140c140300e0f01464211601812451030101c0c141c5400096901180d21114182e65501c00c00050800f458071020444a03100d4043e010700030f07042401015841100c00b105080c500019035004012425880b0800510404103900f00b0700d5500d006c0503000307010001040c0c602d80141c0300050940c4c6000c1c42500303034a0902c1000d0781e0820324039466050015003481821034580b5820840841c03150f4030140650312 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 44526964 1250 44525714 44525717
    0x30f031009050f0c070303050a02160b01030201020607030e03030a020702010c0f110f0607050c0f0a1a09040e0610060f030b0901030b090715090504090807080f07060608060412030e0a12 81
    0x1039189007642520884030b0052002c41c1142554040c003103024040c1c8216a00383d5003501e004036042d01d6290100c0001d2080c81081c00d012152403075040e08006081480381d04036030003602902c00d00d41d9008016000d4034524885e1b000140c008100049810600e98082c1013407500600d40020605041d9407604500200c2e181e00703a9910300f0041001d01d0518105102082d850310544e00241086115034450b6034600b80c1c018070600c5120901c1c3e4411094680000388402040c44210f190f50080c441c1c94075030307920fa0005150f54000c40c14200881280b0300c0006032140142000440c0003801441c1120440b18842c0102a0b0001c154840048000c1c640d01c070900b40380030718040c490b5a601c90801010841c40c1c0902d55102101c14200b2b81102d10300c00c1d0700801c0201c1201e200741c03030204804440d49001e0a141c82000d10050080a01150221102a503d8054a0b010348a8581000f00c1c548400c0d1850ba0b0b88800c4400400044501d09280e49140c803035048081c000742050308480c600d1804d40c1c2c40284541082c2201c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 44528214 1250 44526964 44526991
    0x150903200402040b130902090f040518011d0c0f180c07050109080301060206060d051b06040b0d06060f080402030a03120b0306010608090c01080408040618080102030405010b0a0b03061f02030f03 85
    0x45c081c01070204440041000c140b003140f0304420701020561201810300c040d40300c1c81d9208001500d614015202880d1010844000c00ca40c0900c0c0d40c05001c240b25005200c061441007107555074039420840080303003810500510050405107144410030011500a122100c800818020310700000e82c24020507201d140705900090301d80d03050000c02032a0103001400340c2c3c4582c2d03441d6401c601090300411110402001c02004041403044000800e942e40b01d164080c100c2410000380000110a05511540644880c0d83d50a050002d00220455108034240c07000b95240d0001264980040e0054045048039201c1c98408121050741c00c00080c1403039001d030302900100d0382450400860607814452100c00001c02d0900d240a41802e44403200d4601450151209005c001600100f80000d0350800c031000b003143d0b6000395070340d250500c0c065028201d107103405d5000f00454407002c03800d09400000e07288180380140840c902c541e00d0000d880c920140b032481da0400d40c04100010126091800b0080d0b20400380303024020b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 44529464 1250 44528214 44528227
    0x706030f0f02030f0c0a050c060f090f0a05100902130905070302041b0203030105090a060f0f050a0e07022a031902030610060203030c070201090e010303020f07150903200402040b 78
    0x10251a0180301041c0d065204004001040325a01c00742d82d0000c0311103040c02d454801d884019144e40c80783c1040703869144502800c000001181d0251640b040c645203068400d9104031310040c1d5901c440b680c4008207280c11200624a1082c40d5a00207590b450004104050307401c10100744c6c0b07048804003201500d035900310507410b105508150181e40902c2c000091910009100e0b02e000940300d0006018491148400301e0108041c0344a0f034000318064645454110b924a50b00c3c06401c030307803d0103403042d5402400092000940e032141020864494001038001d003126542c00700b40316494107002200c080204101008090854500704410f810345e00e000e0b9021a01c20302c5900402d854604002c20340942c108144c0b80c01d00c0701c1540841900d0700003030380c140e0058841402d88010f0780c5c014440d41202e01e902610707000000a0560000d0070907000b440c0c4d0b80c242c030709290b11414035180c0001c2c00320303102e00880c041c0481040081c512000d881b0b9100d003003110060309010b03900002400e9a000f907002055400380810271 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 44530714 1250 44529464 44529491
    0x60c0c0a0b090d03050304020d080c0a03020d180b0703020715030c0210110a230d020325090614040503070f0e090601050a03021c1703371805070603 65
    0x1500040a0007810000c5400000302440c820f50001002c0007000b10100e02103450310f800420410350300c1110680c079114403c400568170383c1c0b01101a0300610401c010340c0c50180c022812140035086400c485c1903002c0c01c0c03d059050700d0380980004c90441c1304820001608038601403d2420b100d040d681e010a2480c40e46200a00e0442098007045401d0710f0100390007a5848070b54100e030708880d00e43c01c118000729820303090300070a401098032443d00664000b0b4120344113003155008611500003c8071a4007000750800d031654008070301e0302d010700105461050a0240e98041c20702004540e004501440c54035440e400072a051040c594002c0442102c6070105000300310800004a51091444000300f500e50701d08030028540e07140600c0007901072003c426000c08a041d1200c40100065000a060b403103540400f260481e0a80c030031228076003a070400d200b02900030301e8995a60041403070800701e20540403070104800b60003441940341c4502c01c00303a11040900090303001d03c4020014886520005046510141c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 44531964 1250 44530714 44530729
    0x1050a060809030306010c0311060705070303060e13060213051504060906051207050a27180b01051b070e0901020d050606090d030c060b120f07060215010303031109060c0c 75
    0x44401d00c62a2001c10010b2007000054950042d4246403240c006511800d054624102c0400f0140a6020300c404000020390043d0083c50990711a6404000007070382d58100c60081c240030b5450f000740d201d840a0b00c402061090700a0200c5000b41080202003594410000c0e541c5100c00c0c03030300c01050710042020070145401c40c83c103400030550f60030700e1450442002d0156950440040100d0184a4003003105c030700480c450b6000c1c2051a00c0c030401400c140240c4a41ea0351008450700c5402081200b1346011103840115001d25888224103846890816511000d4103d9000c0780030090041340c0300d14480000c0c2035082c4c1c8a0540515504000165100724080007601501c60040040b401180201b0000845d92904101511926007629000900c001704c0d2a142c40a00718002036503502010140b00700105100c0400d150005104c03180456064687d1244280c0e21011940080d044080c0c0750001040840d000b504191020f1406903403042c9070000490001e20036801c1054517007440e038407001d03001d20941070000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 44533214 1250 44531964 44531969
    0x60206040212010605091303031d0a05010e120901110f0604240501060c0204240f080c04060608010b030a0603050a210809100b0411070803041203060f03030305041103010c0801050a 79
    0x41c001e1061500702404030300500406080c1e0801f2041300c40d00e41c0149442548a21800d80c1100c800c9110115070b42886aa90448454240c50355480d11088840c9101c2c0007a40056610700c04803440d04102c41c00005540b20030b018804031503280104035903080e00140c05e201040c803d034071403401d00da51210010458a0202c07850703d06540c40516100040c4600c5800c03403580c00c03032154101c401043c800000e109003141410780c9003040c19a240e24180100f54000c051034908241c40a20080f13410441104042105880880c40f841004c03c041c00014040402c0850080d0713441448900042101543e0b580c4161400700e40380801d0714042c1103140027156444034040c40040f0a4124548480c2e43e080c0f00d0f0183e80c0b00c001d0318403144c011640d55207a002c180d0300c2d42c3d00000d0100c10044d002c2600c0d04e2850810b00c0603a071044504850201c03400d41c039041d02c01d01138032035482611503206120f0f0000741150f071300760001c1c203000d0020f88080806016030301a60350300340224030900b9055541d8003071551424040c4034481803640c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 44534464 1250 44533214 44533249
    0x714031209010c05180f0301140a0f05010f060c0503070503030103080403020a050603070f05160506010f060206070c030203090103050606120a060e181005070e030f01060608060105070b0f0a0f02040602060402 91
    0x240052210390340142030310300100d05194200343c6100d170940003421903030742c4600042d055400c0148140c0000041100e0034813030501c104090240340403822950080364003d01560f5041d02e03540009001452040b044402c495118004803480d04911f511102d107990401d078003c4910a00001e024401c60810204200042030145c41d41800c0d402c0403140503002c50280b5070418108200880d80d42602d840080c11450309070341010075030f109541c48c1d170707050381341004180102e030094400d400c04210b500e07200f03074150a40e0b180c156005d1410040244011000303028080d03c610f0307201710180301581da00f00d041e40d651801406010300000d40300386002c4041c11070000050100c400340300d40b0342c0446038494003c50b04403140065590002104c0e40c03050010303940c61240c5280660584190a11051a58030561000c029125a1b44412440b9900c40b40110b40b40d114114000f132046414201166010304091000c40d00410b0103800032406420302100034040b600700b544000700603071051040c4025824118654400c19052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 44535714 1250 44534464 44534471
    0x1a0405070909020310200a0203031602070609030308100b160302010f05060105070b1003060c09080714010f121b02030702010e18070507080903010203040b04021206010f0b070305071403120901 84
    0x4640010b0340b82d01140940000494135400c1d15141e50006602e51904201c1c006d4030680c6600480b41c0c000e550b50821641441c0f4081c3d15401400c43c0c600004402c4100c507801c0c0e403460340050560340c00711031041003c1c0c41d414845415040c08030704004241d02a00940e0051045448070b40d1041c10b00909540b40c0d0403000046620b00428403410303991000441c0d0009070440e02d040e0054854187c640c841400c00d0b03001074491450030380e0b948405070340044060200d07110041101c1c405602c03445804c0014282c2036410b40030a400d0810101594040c00700b5414a104620307000900355118600010049a040b050a00603000080d10742c046680240c0079200115043d01c5095405424540031402c00b60301900d41030501001103880400c004510003180d100b820090300a54482c04d01e1b1a201c500b2110076141244209414150b0302905040010350504880403050420071039031400c4561b1059034402042901046000c02244002c00c0902006540254000c17000b1075403040c5404a1040b2180d018083c1c403510b034103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 44536964 1250 44535714 44535731
    0x3031b021207050a0b070905191212020a1a09101b05030c04090608030d0b060705061b12011401090503030f07080306130c080f070309021507020a031a04050709 70
    0xc0c0020141c61501442400640e111090b00f40545031030a80c000050004550000700101981c0c8802140c046070000d4480c082c0440842451000d40d002ca40140b4070200001c04501c030200b810445021003050307141c01981d94140705d5803105112501da00d10a0019802c1540074031400060400c00f417003050285010030040e03002c10b01c0c2d03100d10190750748509004100c0044046541c8690340012580102540c003400c20036190354020840d10381e0840b007508a5060704e0000c859459040410444103990381c484090001b42c0d44460503110850850b120004220b03005001c43c01d908021b5010781c074040e0142c0f05100b070600400c9000100112a190030682c001c0d007060007050217a40300e003c190740d010365010000c1502c80c4d4414022480e0000400804010300c2d04001001880c40d82003004640140401e03a4501d401d951b03406000d80a40e0110000250802c0c001603200c10b11008590240008601c005c086403d000e0352500d901c594804078100400403a513142d0309000800c102006800000c0620f100240310804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 44538214 1250 44536964 44536967
    0xd0501091509080306040c030b031603031803030c02090a1b050c060702150109050c1303060902090604060506040612140106020609060603150109020703090e010603020d050906040206090d08041a0703031b 89
    0x3921203806a9111400c81c1c7c0d540f4002d40040012800c06012104007800b038120b90030b00c009040c4000c0c0c01141d41c092a21a8081c004c814420030f1b40c0e0142c40300f801d2803c0d0340d802d01c0b014150051016100a607a90442d8140c0c0a00450700c003c4c2401d070f6170740e0503180c3e1a03150849040420140c9004150340c801108420400820076510341120955500000d0b0b03590b441da5007502c288208100c4140300040800080300700403066124545550003619000340720381d6010240422039040340035030f40c1c0c8450700740001c0000034802c0b44010414640f00c000800c48161104441e0f17081402a081070002d078210500704004581d04006a96210100b14010f200c00c00c4051208581e0f80c0c2c0c18000d007009160001103a8052501038a146801081d9003040550250395070310000307000b90040c500c090860b86c20800400d40c8042d0010b40d5a00494000300110f1a0070404410040441245501215a0f82d070502c000960080e101e51200c47d0709880741c000a655007a14a00103040f6445042d0181c10f0202c81c0b8070320700748279 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 44539464 1250 44538214 44538217
    0x90a0e0a02010804050c060304030306182a0c080403060b030f030f030103030f020f0a030e03010605010201090c05190b04030308071e0905061c0e030c0f03040602030a030b0d020d050109150908 84
    0xc540a007000380c410744807420201d061042121001d500044000103001c01c250341a03202e20708640e0540c1c0c084071580ca83d009400d040d2405d00c1d00ca91201c000b000810032a544c6012007040c07510005083c24103031800c940e960580140c00a41c0240e40c543e07910002002281014030101e1408225040658034041020614041320701040c00040c1c100b24802c0e0707849101c40e0081101240d0300741c41c2412152071610620700100407420103900b00d070095080c000c2c001000c0d40140110b0fa44540c1c000507032084203040400703201807040503040900c0b505071aaa400140c0d641d14500800107035010750f560001d189044003003e4640441c6104a0350b00d03038498110758401c50b603c00182010381c0c1c41107842568480038500110000a00f204203034200505d0914100484640000100800d010b040706a500341e2130102c0e140d6848c0e00503481003d0143c0c00030000d03581e4052080c1d000c0e80c5040e80c010074a407200c41144d00490300711224404100d03803c0c0e56810b190024400600508403191f02c030303060700b8080b042d407075a544041c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 44540714 1250 44539464 44539483
    0xb070515011d060103020d05040c080d0c0c18180303050703061d0f0901021b0604051c0210021309050703140a05011203030b060409090b0403030c02030a08061207080714090a0e 77
    0xe003030004280613038481e070112030f100540c1500070702040c00e040c10039110192551048445520514890100c02130061311000b114941101405e07090915001d184510140b1100c0c07800d040550f100310001d039494022074030381c044038026a40022103241100018085410070b8002c03c01134000390140103100c01c550450079034082074109a00c0c01ca86c44000401d03029000300c11015418150042c42c3d40c02c007280000c0c07403520850141003110610804241d1181c1c400f100d4139019001604000d000800c840c001c6e400621f011140300084040031540d60709160101e0300d05440500c0025200e0b04e00c06e0709003110310758060700000100701c104015413401c80c28003180300060100030185600c610003e90603594001c00d81d0010024681c040c000c040551a24a10301c01d070854048010910301303019006164800815282c0f80003003515000420b4691204002c614407060800c100148610b0002144400c0180100030090a40f100010040d20101c0e0411030400401803555290515080404002e58400904400c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 44541964 1250 44540714 44540759
    0x304110613030803162003160512030f0708070f0e040f02090904050703020111210906130603020c01060603051e09070b030915010509040b1b04050a0b07051501 70
    0x1030700c0d802000844040d04490740080d010035000f10402900c00381d103a81c003822a200c69038a2000c450012100c102e250341c0c01c2e00007007805038800d001411107660207100f0940c955000c1d008a03050541ca00c1e51014859008071103442d032011401040c0411580c0000c403258006450f0b007071070844401800720003840d503540b400c0c41c43e2107262a0042c4043c0929150704031100d4000203052005c161503e802c2c1307140c0d10841840300320b00180004c0c0c1c0709494100045030f440b0750381200c0304c00c90154100300d00c1c4034200c0f0b17000040c4143d032080c0c040022440032024821120001c19080e03e002d81c48958002c495400c41d00340c0d5001c60141828002008601704d0407400c00100e0403c80010b006240d101c0451061a020031500581082c1d90004140072400300e00081e092524010313002c004615a0b20f40c01072190181080c0e80003403640c1c0286020035001c07601c601240120240b50070440781007907030340d100203100450b082c0e000e1900b0340310004001c800d00c0814445180b100c5801410040b01354905855400c0320008c0310010072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 44543214 1250 44541964 44541967
    0x4080a0f0e091b04031b0602250306020a031103041a0c1206090a0209060a02011e0209180a0e070e041709010909020d020415050903010b100f0804060b03160f05010503041106 76
    0xf01248841d0054801941c0c000b84000280000314004030b12002d640c1c05500013500c5070704080940b07100c880340400035068608410f5045d0074030710380d6000040c2d00800c400405150700c032900d007002c4542c10f401540c81180500110744068903201b04c1038140c0c2101411039a54040104120158070f003c50000b29008101070701e07220102d0b0769140f1900028010009000d5100311b00160000415905401901540311964140044170349022021001c03407142504058201d183d402c0404d001361168182103900600c0680f01003400e41c8140c1da0541060f02ca0780290328000c401c00144801d00a01400707414240032160701c460702c1c1c03d401130000f030f0480c582c500c2025202e84d00020001d901024540568004112000c603540404120b09030107407a0f60424099603001e50320740503000c40d0034038010f0b10395600c0d20302640701c680c0c005078274160460f1080d81c010815900640c50301d08102d29504c003000158070b00e981c03850600c602c1070700700300c00c81d0401d00c80d95020504210b024424000450034841c038102c246c21b41110b445 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 44544464 1250 44543214 44543251
    0x3080d050f220212070323012a050a030e070b0a0e1c08070f080a0e03011b050f16050f0c0a0905150d03120903030f0b03070e040b040f06020304080a0f0e09 68
    0x1174a41041500700500c41440341c103070b042503010380100100d06900080c001340b01c1000e5055900d160052090106801800b6070b801080010740a003000f0008140c0520300440c80c3c08003e201c851a19007290320407190304d1000103030a022680d02100d5000120402c80700b4003610700e0801c8546d5815485800040c2801000084080800011024400c0b016600c44030958850742040b50160801c6106840a40a5404e010781c50440340320301c070b0100080003695280c050420300310070103122194201807800d8004407400d28030200400c0302003010104880e4800000e00b241418201442a080c90030b6214000d41c9041c441070003180315030000030003030740c0f60b0a80e01160b2083c440c0c2011100343c0d02d17440081404500c1c14289005155040c0c000407802d0420420510198000c06c06240c0d90352200c1c49603004580c05540030400140c10120003030b800500a1a09660011450302c0300001c99105503003c4620480002d004856160407281c800312918960511095908194002c40da480b03000400e43c249000d40180c44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 44545714 1250 44544464 44544499
    0x14060306010f0c06050103050a030905030a03020607030e010605190f0f0e061903020405090d09140d1401020f030a0b04050a0204030803070c021207030303020c010e0c03030f030a0603080d050f2202 86
    0x36403c03003a800c0001880b655a40c0e0810f581c030b0b100030010940028041e80008a61810001125045c0d240e0560060040780c0e204081100102240c032800c40030b03175403203000c00110b0703507142d91915940021402c1171160ba42d1500501004a2556034024001c0091902c410000002040d41c1c2070352140007520100c140411503008101c0c0d1100c4c40e04002d6101c0d19000a014426000244003044c103041030310b817441a55100c0803049122400c40e0701060340301c0c111020701400a091070504801c180217640016003005010001c010141d04122400031041e0b40d1280d90303003007a01d403038040c05400580d02c40e4114a01800d5444018131031100801e079000784001d200980702152103e007085010f402e91541030300e06140c6ca9260003400795020850341d4205c1e41c02c1c94183e402c4024041031035450316800600852a0408408054503e50001020003004a42d201000008540711100502d0640034000c00090180b400101a0100c41005059107021a003031170b50004107140500482e89909404607401444454900075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 44546964 1250 44545714 44545727
    0xa0c09121a010306051b18060d0e030301080a20010507060b030c0303040801020d0525080a0605040c0e030615010917012003091c0206040809040207050109030203040f14060306010f 79
    0x101e0382051641c810002081c86115800301c2d00400c41e549401040c04601118841d250103403046e00e1680d602c00e5111400c1c1481c2810041195050052003ca0310030540030403a400d51b0001d0740903c9281c0c20a0403210204441703054001620541c00e9910654012075000085c000c0c01400c10003040a0350b10389404007561380402402806807401002c482e42d4503220080f0a010790442240003203071604000c0030807003500c1d1900d400801306003450706190b1041c20b0707010212580980a00442d07002035070340d1130110b5503488070b014051840d800d0741c4800c00d610040704185881e140005050f50b080742e040b10705444c82aa4842480d104440110a04c500ca0500a003801c1e4018880718920000d6080c0c090385802c610203420020b140700d04644402d40c1c01071070229588070124200c0313400e54001a0000d20000e00051010301c0500716028020304010b007040520340c1d4107401c6503e405002c2e00560b00c007280070041c8041494011014204001042e003042c003914011903024040030308030354180440c2d40d407080d452030b00c19803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 44548214 1250 44546964 44546993
    0x106080a020c0a050c0109090e030d1e0903090513020a0e0402090402131d091902040c030e0d020f0c060913180c0315060512030d111606020405090a0c0912 68
    0xa40b00400c3e241d141050b038800c02180114085996410000748590b600d1041459000c5c5080266182030f44e1882e5200040c104000b00220728110094001500a0b081c420301d11918880c1c0c4801a0307880c1410704200e2020016103056814600420200e83d005030300a01d02d2800800580d0056190018940094045d0059081c0341c9070440c602103000139651140c07103020081c000c031124041d28030b407201e00500e84c0381d14002c41410192401e03141004010b081c40c0c1d1010261003034502d80003510031260b110060501d40d1511240707006a200440c1c0601c000d13014010003000c658200c400d00c3c5002c089102081603820b01780102d4506c07907914114000b1520b008950b0514041d440a0181d510b5501e034500024138200720540d00d18a686400804100740c18400318820f03c10311070000175820000c1504c802c50140090030403455040030f00b0b1100702c9807400e425601d6000f90388608005601c50741001c0603c079205200420307054038107050600721582e5a030001c0480c420b45010240040341031107581801d144071070121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 44549464 1250 44548214 44548237
    0x306190623041a040f05040203040503040b07060f020f07020f01020705030a0602030a06090213030b07020a0807021c06110705060c0304020a0e07030b0d0303060302040c031a06090f0603070201150f06080106080a02 93
    0x181200c9540f0000803000380266841d480c022a0702a07142d9003480100d00045034001c203598001c01c01071100d81c80d003001a0004601c071310f0011400c4003600142c501603820401e401d001d00a4041464011880c142e0020401c8020078801000110b1601c4002a9640c50640014100590010110f02d01040541114003d1f08003c84250b65458101c3e81880004032603110940e241074001c2d010521a51000c2a110f003000c0d04103102c1400c2c550b4503000c008410040e1040c070f942514205040c04001a001c0c040c0421141544210707070b4403031003241401400c02900070001840008104100001aa0707542110030030b485042d54460302a5a442100b034000742403030407085a0044610140d01d0402d43c1c16040704090324800d0b00d0078004501d01d07040c240c1c280c6c0c2e01002e010600c00303d11001d844c07880c2016006001d101e00c0044c80010713858840030100e17815038400d40b21200180d440d1a40083d00030350140d0703054024400c0004849440e0714014000302480300600801381080301250206100000c0d9405851884159 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 44550714 1250 44549464 44549489
    0xb0619090504050a030206070203040806010b0d0b0406090f0c030608031209150c13060f0e0405060d0803041407060c03050301121406070f090602010e03031302180903030619062304 79
    0x341003c035503540c0c4050003180188500300020308000e1010098500300c032800c8005040e181d0130014018480d0300106c4041040c00e68a4103e00d500366254041c000c001c114061001079140910040354050318002c0612005150400000300b04d0000004100e0b10121200c10300c200903030b115040b00da41032036a10044803651202100038001d540300400014507040e91080d80861516580f030b2805d440502845150302d012540d074906a01050134542c000c20b600501c0108240603a01070f5075075080d030581080e5019508045040038803e0582001c1200201503c2c960070294120207003650300030710f03a2005014120315a507048555000b0442c030348004a251031546425204a4504490000e209080c0c01030302200150200c1c10010b500350040c482d0440f251000780255145030756401800c4803481c0c121408903040308201a1500c070500c03d50301250b0280340712201031640c0381400400c2050303100c1c940301c9441c50400b02540c20060b032a0042900903c40c0e0544408404686010a240020340160b1340b080f61941c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 44551964 1250 44550714 44550721
    0x604060509120a020c0406060906021518070305150a0207020904060905030f0a050c070b03070906050906090301020f0301080105070810090903020f0610030203060c04030b240a06080f06030a0b06190905 88
    0x4c02290710711889006036410417141c2e54500f002c44980666104643c0560400d60340040c0e40d490f440c00d09a8040c000c0d00450700c117441401000c0f803400000d5403003a036907a0820943d0001458101d81c80c80d810000005003035090220300c0d000111510000341c402050540d072440c04030200202881611042800e0302c00b15502ca2441d614094030650140742c040c5024000c80c03e011500d402c80c00c043c5c074001e0032280d449032809820684166026802580324550110060180340a299000d000500340c012140060750303201e500d800005420348502410b0300b410b1040e82c3c010450340d0031050740752004032851107a0102d40c010a504059040100c00c0d90020402d010301420000c0150b0704041003802c491003a0b08440d0170780c0c1d4800000c4c40e940100c0c000205903007245404600c40e5100e04400702c01c200340901e08540f903c8450000145401107542c080000710b5200340c1006086261080e500d5440201600a0480103a09503112204950014602d40c401c047c40f98000e480603030b0000030580a0181042e08111504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 44553214 1250 44551964 44551967
    0xf0706270e06090901050106050306130603020d0602041809080901050304030c020a0305061b0702130b13020c0706110a03140a170c0c0111130e07112d0c030604060509120a 75
    0x3508560300d9005207054401308900e5032051150a0403249140e07201411a1140d0042000703100c508400c2c0c0071110384850010016a907501d140109581c4107107401070f0b4444c645044800008040409500c8042c40c0140300710104069030b04640b004042460106c1d41c0c0d0b81c0750b190179601c004078600042c0d00440411004408c0040008041e8003c5103101030806e040c27078000e0f00304c440511070f4080013504801c00802004e02140c00780c110b52030900c0c00030010400c1c0101948080101d8000d180890a0b6500c2400100b00440d00f1140f942d0300e0020300340160462007220f4402500f51012011001c034030040024410340d00310300c65005040c8040030f480c0c0031001ca081603415041d5680005410340d003954030f4212040d8214500c0320481e81c082c500320303100040306440c0800300c1c100500e0040002c002e00207200c94008504105100c00c3e120510072107160f0801c40000d1ba01c0003000c3d94030a0010401e07600c168103d4500e50b13000a0302540c4980e204501180540e01c10145608180050210b0b40c1c03030a20115201105a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 44554464 1250 44553214 44553239
    0x12041208041809030305010503012304030207080a060f1107121404092301120b0c1e07050f060702061e040f02100909050a060302010e04090609020306010b04060801080f070627 77
    0x3c6000355410700c0701ba40c0312810542259091000e035201030068940740b08407607410162182e800760103030040d00c81e466030740d8081d903040c400039840460b1801d40c2e0b1504104414100c2c41499444195665000e0078041d00340c0d036450f0405000100070007440f000c4844450128001c100b00d502a04a055040c455000c00025541d42040340100142c0c0c401c20340000411508503000d03400100c1d5400540b0303c2c9240d00c55158910450380b00d051080801301000c2ca40d0308e6846960402001001e00c980028031250802c039241d035003010030103010b071800c541080052003071000b00480b4a0300e01c070182107646800e0340c80e40d10341030141c2542d030040250048950f04240c406035811040c0303041143c061420034031050703443c0c0760300d4411501c00d404000e010030b0604c503065a0070b0815511500e8218031402d4000b407020781540019213041401d0b0301849d00c51000103010b11445600000803401070480070002c2c841c2610402200e61181c042c0d004420800072000c0700c41188402a440c4013022491b28400442126150b1030041c800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 44555714 1250 44554464 44554481
    0x1b09030302070b07080415030b06070809090f06210309090f01050a080a020604030803150a030b07020c030102180111030d0e0601060f0815011b05030f07020909120412080418 76
    0x5401202c000107403001c4507004403005668000c4800d880c060500f2140700f0444020300c081410142e50300170120080d25098000c0640a0042c0d041c00e031921200d508112014200803d940701c0c0035940811301005803907102c001c1d00420003641442401200450003079140d03002d5803030720079400703040002400b040c0303505103544606a4506030f0780340411540352a081507482120502c005d404c900200402c0001c5446000950f411a40000c00117021035011f00c001085010380c0c0c1c100344c80d80c2180d001401129501040030308040c0070140d00035401c00a0851051070900e0324541a81d050040c544805454044107000310384007c15042c1d002c00c01c1e1010780c038000c0e668500034011040410301904926292038011a4114400c9880171b04101040c0440c0004503004100c501d403450205014460f043c00148d410b102030201086070311961030700c40c00103004000122070060406441900403107201807c40745504104c0b425240704d40c00b09840310440d407400403414890b5610180a01020a104030400031190b04559103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 44556964 1250 44555714 44555717
    0x10e041113060804051f060504021209010605010c20120303010303020604110405010311010f022118061e070203150108030a030606080c1804060302030d05030f0112031b02041b090303 80
    0x1d105886803016504400f007502c002d01150310491103828085290001c0c001107103150744021500903a80c1000c2001da801c805030410760748003103a04110408400740300c2c0d03030001c00302440c0c03d03c02c003401034803200e4198580500c50a40d016288001e541c55444181d14070074403c8a11041300d071350350794a08000b5220001036500700c0b5004440d20440b8500d18083c00b0f810705880e0010007280c0012140700040d501241107000328004e5000712801d5400c00105002c003000c1c1c18620306401542c844041400400301c00304a11a50321482086c403004c07004284100b1104100d48000c2042c0c2d54800282c00040d15020720309130500f084c2c216160010488500210191401076150b071401d0010645a442c00c0d24440821030303d0308a0a80d09010040c0c0f009c1c00c4400280c80d45101074800246079803250007081c100101260f00c0c4021820020501407900510040c042c010810031580c1804c1c9119507400900a8190b550140d411903c560008020340d0b550b0741c480149084241c940400e192546c12025240c072015110960 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 44558214 1250 44556964 44556997
    0x14090f010f02070309090b030703051b09010b07050d0c0f0b010f090c030603110d15051501111902062101030b0709061106010524160b01060c030e0609010e0411 70
    0x11101c024000e0343d1a40d50b1684a078800c031814140303100020310000718403591520910340008042031050010310328500005510100100115050068260301a0700003840c2072010042e04010400c041011b010b13904d05c030b192a00d9200031034202403140a002660107440038107014000500442c80c070344107200301c91034070070140100b6581e807000340c0445402c1c2c44041c00000048100383c0c0a4a402d403001000140b10b9110007407002842c010410841c3c004580c000303881e00440181c000c0c15a000b11243c102c01071550000d0102d40707104a8881c25002c04110000c2c02098042038510809401ca101c401035460700501e8a1100c4da528242428203950550780c002c0426102c0700c02180180c803c114082d010b1600c0d000a01041c2d1070700c000d00c2558490748000641103220103484d010418800300c0207220454861f996000d4405640c2030805c00030301d06a01c510180810385802000198210080f86c0e44803038100d035241d888138007030801640c2038a1002d820a602a141c035003654090070110014060f403035201c0b441d02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 44559464 1250 44558214 44558231
    0xc060a060501030513030f020102070b100302010809060c0a14070516090f02040509011a090a0305060901050c0901080601031d01060f0f060f020a120207050d0b07030b0f0f04050a14090f01 82
    0x1901107850517140da42d40c20060030305c182c2c003003401100c400414401c1d41c4001454a1041d40b0340983d107944c1906c042c82d0243d80e0b200c0c10802d641c0c0c403100b01a00300c00440080c11042c10040c1071161039104462006060100d940c41f070300306a0001806540403d81c010042d2410402d4081c1d100b231600c242801070204040ca00140c150f81d04c6102c0c400c0c3c4043d201c01810404041c0d080090041400c811140c8401c031424041000d01d00544400402e9402140308100504450600912080c2540c400038203261486500384010550b13a0385c00300029402c00303028240003501002e9448407404000880c000c0f0855503003044030000f01c596154020303030700700c4001844210989480300001c981c28948400f100340141d001122440c0480c454604480c07111020b4011614615910008143c0d402c1142400b070326803511080800032500d405001c0c100080c141183d031140c10b0301c071050014103000c0c000c080040c000c0b036517500007400c034240503441018848103c41c40b00c41540343c56813400381d464500050321790700740d42081e40b1b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 44560714 1250 44559464 44559467
    0x6060315060b0a020304060e0604030501020715050a0b0114070204060807061d0d0521070b0c0714010605060409020d0e031305010207140904060509241b090310020f07080c060a060501 80
    0x1550031960460780511b03e86860b02c80219610250260400d80c07000f0308000001c0025401d01c02030020034803408401c1f860302109144102200d10080200120508015441420340c4e8041600b12960ba00c0c101e4507a1505590f001040c002c01040d0800781840c0f1543c10b000c2803541d00400307110307424580300c180350690b1b626100a0040961428000802550225906590000307140c8151b00c2c4000940d8036030b5092060710380320440b203004140c0d20100d280700005200d1040c0010880c01c841c0b0b0b4441c01c0000e100640c038200204016205903c5940d00d619404900203401c1620786d0041c0d0f07903040c0f0540c2243c0d200d01100e0004e00142030580304080c0580700e0550005091b403240ea03455980d44400a0070055a541e0b01c0d26004060306000742102c0b541d01906d003640000251104803014004902244180580b90030002030424055001c06000040410300c00b0350341c03e9500003445c4454018250000d43c4640301000740105501840c00000c1c003151002c41d110306610b40000d94070780320f214218001d0003000c3e0364000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 44561964 1250 44560714 44560717
    0x1008031201050418050a030302040e090a0b390910080108030d320105041107050c120c060a0f080106091202010e130609060e071107030308040302030706060315060b 72
    0x1a00c4000e0540d100422a03842c180d07012252015602e1104188002c184e0360380c038203101c09a502100801d038046412710000c0c21201c0142d500c01280c0b0000c1112048a4840d070044c0e83c001841802440d150004a541510b601d0301840d0b0f003800c4003160070003204000003107449260401e80a450203201400203403030081d1300c90105281224031103c091490b0181e44d1000c1c0303014090306c41602900c0201130501040c0724000d404100c1d100f00b52700c011050107506060400069448400c0540c0f202c810502828011070404140b0207880c0c501111142916003840030400e04002c5040c0d4156407026010461850030742e008859902c002d4801d81d22995660380712281941c40c01c02c1402120700410b44c2001600065005d20b0001178271000042006841e50b43c130507038000564619030043c801b9251580300070030148c05401d03400740e08000c5609042ca8958208074183c0e507180501d120140421019030003180915000340222090359800000c00d125854076401c002e400c02c81110101c880740345ca04803001545414000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 44563214 1250 44561964 44561977
    0x3120509010c080906130902030702070e0c0a0c0512070b0a0b010c0807020103050709050402031008120313080f07020303030a14090c01140f0d0914070902040312030c030b0301090605100803 83
    0x2165510040103d864421450704801c4050390030540401104070400c40c500b41c0302001741071141026960789400e040c020f0500010348e21070810350308142c080c0b00700a08090103480c506045483d00c2c2c500d840341c50030407070300e807580007081d5002e5840005030742800c0c4003a11f907074644500d070581001e00c1400b52001c0111030146151601030025201481840010b600c41e8000e560481d02928001c104c0c10f4940340000c0499000b65104030041e2428170b4104040710f01844040c00422503403001a0440c070300444480d041014900d0003c1081000044540349001050141d4032001c0e006022262a45040c00b070740e10041c0345505e0032460141400c40000da000e500002c40001955042e0b44003046113000b80c2d0300035640d4021141e0008410800e10035507a2030044d610401c0110f6003d0300c40c2e17000c00116500304038201260b54220541003801040144040344490241c40400381d40381c903000030010321450088004024100c0225450350a0104003003d000140e0030035401f650305aa059001039640c0e8411a07944c2c400d01c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 44564464 1250 44563214 44563217
    0x6170f010e010506160204050108060a060b09030303010506090a030f03033905030601021e060f01050a060c0209070903061d120a080f100308041815061205040212010204030803010312050901 83
    0x4018082420400c01030843e00884204079011852175600180c00d54009170880d41c400ea00130400c106c800c8009006600040080d0804540340521081c00b094981c8014002c1c00c0c050140001d070000c003034807211203540c01160040b036490300301c41c1d151038010094a0f515103484030012100e40c040b48040518024483c0e0000c078404920400502403005032600d800017010281540183c00d031250141068200c2000012415005400c4600c0c20448032030440d4010380009000729030140c030501c18950801c0700068a45c2d0100d41e0300004e90742d140d408580c9110250802009142484481c3c040081200782c16407081d5442c0066803041e481c9610228010300070520010005250303d804a5940198410340d9604100c800821000d003603140d03200c130b100c00e82c4594000003905145400030384803c402e5100d5003418050010b841c04001d0b1500302c0c002c1c0141e18000d000609640d448011030115a0342403803d03108079442e80000d6444503500c0c00c00041f1350f007091006541006101e691400403d104204890044205 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 44565714 1250 44564464 44564489
    0xc030c020d030504060e01090b06041505090a0203091c020309010305011a04050904080403050111030403030509060c0a0807020703020a06030b01031422050c0405240a0f050f0301021306170f01 84
    0x4203070120007901014009550b05540c50540c40c030f50740300078003540091074050b245024031070501c94244011140700341c14030190300c105a98240030544c0c82418064001e108640c0c056202d444068855087c00700310001120070790200c0010146070381e00400a022500b00c240c90400c0075030f903a02003860418603401c0384420414070420050100d0b14100360300030b8100c3c0c01540d805050076100c0c2d0300c1900b191281c80542c0c10001c0d020003000105070b41400790a5001c0ca07804081c10207400d00101c90b0304ca03402440030034014030010309c1c0081c204910800400c4c1c000c40c1c00a21070030348955510030240c014024140d4041c00203040c540102c1d025150350724064003407826103071800c084541210220450880111040780c0c10b002e9080032a659903210b0080c0b50060790041d411814102c07849911103001c030170b2140354601610580318200020003113480c1d070600b1120261200c0814204041c00640240f15002c000d4500c4414008003051076580080084c440300481e404400c1d441c0c07540114141040000d02c80c84400340c21 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 44566964 1250 44565714 44565733
    0x108010f060b0915041a07020a06020109080a030b010e090106050c0d0903020604091808031005040507030b0f010e01050403200907090b0304080906070f06050412051e09060c030318010c030c02 84
    0x180b20300000000c51303090340304604080e241c2030302052550f200c1308030442050001c00c0030350561410080810090280f80000c001c1c0f180c0c182c0d900d101a0060300219800c0c1540da00300c41c0f0321030b4026000d030b10030340c00020444c3d0300381d40c0c4999000d06a0b8100f281101014415a058021514040c04050742a41d4004240701d0405242103915409840078908545c801d49600d0301280018030a0805107029190600d2141c44e05400c0070140f20481785c0c000c0015080501785580e08000703840e000700e0700d082c4880a103041ea01c0b601000700140c60078070842e03100034125150100e00e12103c5180c2c8803811000082154088441c0d00c480e002110018018042c11484000420118002955080c000d00b003115026215509040594480013044161801c0070740b10952078008110801038214a081114034181c10400d04100c040c00d0481883d03201c0c0f81d401c0c0c00311500083d2081d095595030064541c00c4500c4000c42c1c0c3da078a4845660743c4021204941d4815560811594600060003401264060702156004020401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 44568214 1250 44566964 44566969
    0x2040507020f070303020309100906050304020d020a0803070302010e070f03020603070f1b0503030a06061b0b0615071b0603090308060d1502031003030912170c1005040b0108010f060b09 81
    0x20103048032040d403040b1182003001020501916008502a4010750348401d40c000c240701c58030000071606820030031840e4003400843c2c2c00c130013070300d4100d44c040c0e0f03440c1e02030002840401c5100d1400c0d00300b1146c5103c085800c100700340e03054015103122048503040e1282a07a44070480710340581d00d400300035401a01070000401140c880d551104030641d00b13103002001039029107456035140702c1c000700645141d00000104145a44c0e94010400148050700e8003603024281c405109803a800300d10001010301001e00046103207559001821034041440607000307560396889240260607a140c16680070a030009080c0c0000b4114064460612000d4250701d0704006070b0b69002c01c10204c03901e00d107421900b040315403141001c40e001a201540c82200f8407088804018214200541050032a60004107a1803003910710711b001440392003901070b003600d041d802d42c2d44905039070088500304030b5610703800380d07100d80380ca030410040c41281c03c85a412551440700030001526100d12400c291344e6280200000810108601c80050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 44569464 1250 44568214 44568221
    0x5072c0402012016030c08011a03120c01061a0301030201080f090c0103050910060305010b010207080304140d03140a030614041a01081905010801090201140c06070309170d240e040204 80
    0x1000001a1000c007803121340e450001e0784040c2c10a0350410020102400804030074407030840c04c110b190200d40164103c6100003541d40351b01614068200c8030105158048080c01d42000000c0c0c4117580d141c90114610702d00f002c0702a00300b44020390005145101144581c0c14420000e4044e6010001a2241d400400019006010040c1c40450940b103000140410001c2c10301c6154050361044001244009a19000a00d481c0c80c0c1e03000000b068000b00000c01c070b40d100d41c0000c0c20107100300b52001c0c074841549040a51340800981e16401401c0c42c0000c0780040c00f603041e48020103640b0075000c0000315849a800b40300c1141c0b01d000d1100080d0040e110020101e42c0107a0002c0c0d13012000f400c05211a954207901e0f04103444003a40503180c141c0d11070b2100030446da00250156481d801a804c5641001c064810b4941e5400340a08064203155507802e1100603c8074080c208510b040004524640e030b0b0207000c245000800c901c083c2c0f60541003a0784c104040758804c050421007215080e84030901262103035000c20008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 44570714 1250 44569464 44569517
    0xb0901261903090e100b0a0c0203030a081b0c0604120c021503070305070302072415080a120503041211010f020a0206040b06041104030308060d02030109051f060501050403030e030a05072c040201 85
    0x14451501108c50060342c0810040012915980d18100a410116111185000c0c05220652002c0e014070000c0440c01001803082c0e44140c00c070101d40c400c42e00a46041c1d030003a001d20300c0690455410114480485413000056005d00f002d55000c01096650100460480c040c005008107600e503420390b10f003000d45542507810b142c55110303000001d42c42d041e00000f8440d5845980254169040041510280030101c41d00114202e010306002e4510b02d41a0784080404000502da8028001850a04213901d0000d5000401c3e0104800c070440d690003001c58003075540c0030116000c64204002400148203800c060040c5a20041811041d03404c0c1406c40e60150703201c0b00001d01c102e4004030344200c088007580d002d004541340d0901450240035010034070581a080e801204000341c0361a81007030410005641d000046900703c0b5050300d033120101041c400000c0c00c249242c08060203074070030b4000200c0c2180078007094840e0494940b034401c0760502c016500e620001800c54010380419034105c00248010b4603413241028 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 44571964 1250 44570714 44570717
    0x1202030106051905152a0a0501061d070c0201141605070e010e070f0c020d080c010c0503061c1205130305030c01050a0f0b0901261903090e100b0a 64
    0x39101d80742e4003c0758440140e5840107a202e450450200800e0502040003418680d400b13001600c1c040d1311040790300d41c840004000e01c40c01c1310100d1000c40305a105208080303c1a51000080c408140d6440c60559030302810786003404951628408110828003a40700700365034aa060b190300c84031851584020116400828000e058200c0c91060400010400c7c0001c0c40a004100c4010740c0303550604d050203c0075031000f40035006009090201000094000310036081c0558101d41214490b0760074506640350303014141420403a90300f04070600090a4005c1c01562041200359009500c0c01a60008c10074255002200604154514400030340c840b4801c0300240249010801c50102c1705030749079070f110300e0340e40316207070490301a5520000c0c01501d11041c01004030b0f03000f0030042072001907841d8000501da402e0620509041d0041d40040c0400701c501c40b00c96028030580d24054514005410b00c02c100d40343c40350881200020542d80c000f003107481801c081c3c03500402e5a8041c040038603040941180050380500706020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 44573214 1250 44571964 44571971
    0x80105030f0615041e14010e0405030d091a0a05040302061b0405060f040f0905040204110c2a030f0c120105010b0301090b0a0504060303110c010906020a06090f120c03020c0102070f12020301 83
    0x9124240418104c214145c100c20005505030301071032480c2000c081a086003000101480900000c20400400d40d082c030b03084c1500c0008e14100703610b0300d008007618240020b9111a0108100314101d0616802188654000d03029207203283d0343c40c500b4040b034030760b00c410b114100e0405010511950406102038494420350150b002c0c5019203410032502402c540d584081001c0f80c54504010440c2464060244c000103200d654504001c1c1c0d0b0424551660311415005c116000448420058103001d220415903d44004c2c06031100346880402d2a61500c4001d0340365801b40725203101c11403004005105041c1203c8500e8500350031a4200fa103020040c203000a40c10342d00003117255000c40d4544da02d1140000443c07080e142d802c850f0358004c2000341084005260fa0341404109103003080703a680c000c02c000e40240d40c01900040d603441c0700d2800260302d940b0703820094000a200313100300c0446034002100d00101c030300a8003290a00f803404001241d403441180600340500c1d95100040041c0c1205084500c2c40798801000403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 44574464 1250 44573214 44573231
    0x9030b1f0308040f050d0b1603060f06020a0201020606060315060703050d1803120507080703020f040806070f020708010903050417030d0509070f080307020a0b030709030b04050a03080105030f061504 87
    0x4119010a80090724550b00c002020000144189001e10082000b65140d4041c440141c40d8040020390007810340c410b00d150501e414003c1d510981c002c030060700d003e00d103050502c1d8690f10700a40d100070302c0604a000d80f00320404110b1a203010006d9910441a00540b20080e10340f0f83c00307004460b00101012828042c1c10300803180c81ca4040d00464a20122101c0c43e0501c3e407505050042400c1000f6130341d205400c5c80e000078041500d40c8050000c1e80000903003005a5255a14146102c00b4407440d0701c441d005009040a01c960310307501c40003039042035540c1c0e400c0311000d40d2910140c900300c0b4000701005002c10300410040000104c900c100d0b0200c0000c0f10240ca0805416601c10000d80780c00315000c0b0582c0d0070107a42031054620700e40a450141051000460900302c0700c0d80424000c40440c0510445108044001004c06120b0107080010710340c00204070b90241880d207409590703078189030390440204a01800206032400d0004085101500d03d100402154480d9000308081d4007061203800e42050302c0e0a0b07070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 44575714 1250 44574464 44574511
    0x40504171b150402011202120a0b030705060408060105010e0a080601050f01031b090302030f01110403060e07080a08071109060607020d030e03030a02100509010504080a0806010e130f0e03030709030b 87
    0x2a4116802c1d0062814420320b0036100040c1809030105101c200c044c8180003082c2c5440c4a500071543c0b00400400000b0b1100021000078604180c03548280e81c41000000c01040c0c01c071001c2200c40c103c907803c0c4c8a200d40a00a4000c03c045a062801151b820760b100400400c05441c0c070a1812681030418140060094280c240f0540f01c0004240c800000c0390b1462070400843c04d00b0000b20b603d5100b0140200404450340a0161240c03140c0d12001c0e019a44174030b0f080e600d200c4240078401c01055110704a4195402514208000c1d070004d17902902c807000d0482d110402418480d103e284145401440f10340782c5180e580c2000300c0303c40c44440507030401600600180c0341d520304000801541c441c40d0000c00c8001c3c02e0640700d41c2a604020546a0b503139040c94280000078090005a805000080c1041305243d40c6000c0125100c080c844c0e040e541c014281d034040700d454000740e4481d2402e440024821b01101e210140c3d460341e28842a104100060312803c810130100303101e8423019030440c0e041c040010109089514 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 44576964 1250 44575714 44575723
    0x609020409020a090209130213060c050f0601170c1909021e210912040b0307020102120406020408010506010c15020708120403020309180106050703030506040b0d0b15040504171b 78
    0x1d01400e9000400c0003151034013084004042000c20410761074912010091504880c50703200301cac070030301c03603185022801c2120920550b81a82800c500300c0b002036944d00c10710030041f600100a848140105100743e030303050400c00e000c03250b2001d400251080c818940818640298804c00003403080200312101d0744502400e0310300a00340c41c000c00140181c482181500c4208030180904002e400c1e07030000a084880102c031000b5503003164103031048203880ba560748400380d000e480f0b00c0107030045100c0c02e0780821040080c0355020740305803009240200820b0b03485000545081c4298140645440e40352441c0ca84c0c0616150010407803a8070410702c0c80d003480a000c0c4c002c020f814040d1401c034096000412404024100008090007441c50071052014551400038090581c0c070480001504154817900012081e46590304481c4441c08007814044240b0500e04204503c2d0300292241240743e00c5541010f0342a00d0306000b424040c54025442c440300540044810030154001d08141400485000e44c1c41c1c045581800b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 44578214 1250 44576964 44576969
    0x71209060203070905040204211a0405030304031103030601021e0a0606030c14010f0c03080711030706050a06060309020f060c0718090b010e0c03130305091504050301051b070609020409020a 83
    0x300075031207080640c0064401034031600701c03502a070b105100c1044010100902c0d000c4005100440102a5903e030030300040b80c4ac0c003d0540c14544120200340300070000008001d5124030701a5032502e041441407010301c0e46900c4240c803054010b0348240b584040036039000007015104103d900441e02e01c410690fa0b10415502e03d98002d40c1c07052583c1400300018017413a032040e22000300c24a410080c04440000140200030f8400001e0200f10440000541c054007a807030b4020341c800e444c401c0326107882d01c1e85028000342c40e044801142d0203082650000d602d50080c040d01200d940e006140449500025041c00920382108540c202a480781c1e580001c0c000342c2ca004042c541d4180a03a020415420504142c3d4501c1c506901c42001002c4602c00c03c5406e4245034180c2e600700c8803108080752903520a00381200c0c0c034041e90500d607502640000b17441d042040844020f00458009800070320842d030720450100141c183c032540515900100f008150001070ba184d014a1050384001c0002901d00c01c2500890701e08107458 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 44579464 1250 44578214 44578223
    0x30e0106080c0f0603101a040e0f0603010e07080a060e07090c050406030b03030a0e0609040e01180209090d02060c13080a030302030f1803040b0906070f06150602010905070e071209 79
    0x90260002810182d82c1070000c0601910303013501d107040180700d80c00e488141d0300c5080b0114447d10400d40c0c205400d03008030b074018010884040c0d800e0900d50914082c0a0040e50150710030740c6000e50300c000d8a040407401500f210000005003a8a56403030700c44c10040e0206811181c860301032034602240c100c000e8499440d00b46280d41c5c540e41c07141d0406c40003804985100e60b6903482640240141c2d190540d12810f80110b0300c006a41060710340c014500410041d007031040250100c0d50034844482503480138510dc803001e59008482c032500f5501c032414440d480d182c98007107601c0103810840004001900001c01803981c411115006480f883d560001c1500305280100210700003034001043c000001319254095810242040d0700503072450301085655503a22403403184000001002c995899075695400640d01102d8020216525000442c502400101907007101d0b240c810301c188802003422441485841520303548000200b400505045603c131100200505030002c0003440c0000443c064520301604041e240b08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 44580714 1250 44579464 44579473
    0x50f060603070605090a0504020c0c031b030c0405060303070f0c0e0103060f0501060e0f0f010c0f0c090e0609070905041106070c14060702091302041407050315060301031110030e010608 81
    0x400406040c030442e07a02001c1004000e0050b030040d941c600c4540001c50324110f60059070745038221038030b604122400000e0f69241c0580f140700320700306d101443c0d803103050703101281503d50130700300041080121503040c1ca019416a00c00c3c031803400000c0e4000c0740a031402e80035a030f9101e140c0c0c0d980c00d80d070b01e00800240c008079503550f20740708400200c0100740510b038003510440c01c18621103010b400214500551441b0240e10a042020544a007640500c2009140340d4010030002a02038590408a01c213240a21074010342c0d510300758a201100c0c070086421809070890300c01604c00285010003901c09800094000d98094002e605602800d5a8010040c00300d544504054405146012015200e86424441040c0140401c00c00180143d070ac045015521111216200c16400141d00100d0010201e40c0610302d078910380041849200790b08840558807421001f0748105000702500148011f82c0420320004080b1445c60440f949245005608840101864079000604040e080721040c00e6520550042d0442d800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 44581964 1250 44580714 44580721
    0x90f0618060a050708130c09230106080c04030f061407030902011107080d050d0b120303041b0b03040b04020312130e090a120c061506260106020304120201020a050f06 73
    0x50046551200444030b0800251134445000b82c03420344010a5208a55a4800700c4170070401c003800326201900d80700200300600c02d03121044010301103110504c1c98040801200004007244108441842040c80900060400c1e00c0c584c1c07000c104140c206400c0f03403003035201c0081000c040340805502d8440d000c2c51b9408650071721240009007590f2215000c208594020b9030040c80007110004130002048640e28110b40c0e00c1d8102030310304004051544010703a01c4a03501da034200a2050000146020350700032031881841d1260608889042205885140e850310410700c0001c0200348500441c80d031050024090b0b40c2000420650020907620006030407068410700003050007201001c11640d584131034020300401d131034103003920340b5020703140c0c0127031002d04220505220004001c0b03160403014441008030b1010f22950b44912010b01502041c201d1072000c3d1151010b088040fa003641501412102c0070340145207040d0902500003e401030f014000c0c2c1c15449080f403071a0000d98200902c01d440c0c817012020300300608 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 44583214 1250 44581964 44582011
    0x120309060f0b010503070f0c081b0f01020a020a0f03021509031c050402090604091a010608010603240501030c0311030405010902010e03070602060c0d0f0509010917120a05090f06 78
    0xc500c1008045440d182c520070320700c0b0380d80100c00c881d004078503030400300c040c41c2c40c14100711f0351032502810040c031901001c12802b0050b0102d6040e082000391a1065a40501050081070f08034081c0c840382d4401684042040d901140da00060a01480c1c000d1041d6a583c01c0000384044502209984000284d84001118032040900e80120704001444c0c40c0309000a00740368002071b02c20744c4007a0503184210350311003941c401c000d20504034084040007000700443c20740e510080074203020390900c136503404241080210f04005540002000300040110025501c03981030100440044c906941c07031400b4160358400e041c1001004001a500c182d02c208c0021520074240d100041111030321800c0e00340241e00042d014003015030040740b9070364420001e000071611138011801250107407140d409000140c4d841d017000c1c0003c0c0801900400d07000b030b010307200c04d0030159091070f603204445c4a40070004a50032100c00c0817520001e6145c1025420509c940700701e0b09000c0b81c030014103040c02401d40346040b140417081369403144030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 44584464 1250 44583214 44583221
    0xd0906020c03010209010e040b01050c2514090403080a06090f020405030114060a0b03060f060712080105150a050f04030c0612060f0b040302040506130c0203090102070806060f010f0c12030906 84
    0x80c81c060b4020760400701c10b02c0c0064a441800c0c0002845a0745469542d0040d03403040d02500c006000640440b000c039012020a0038900259a200c00f415106052001c2030a4642c01b9044034408400740c2500000c3d5180e4800720b85c8440b001e441032006607292100003a0030039450041e1f42c00c64800d00401682c8a01d480105402c5a03401d15142803075007100c0c01000074560b40c47d5035090440702041d101c0c5649541d6140021544001280c89070b0380580c0101c4c044e024404001140004205a0344944940303980301c0303080081d524659500d91900319000c00c502007403644a076024085000014022504098480e50360100090044d000300d030010310a12150003004200d030060100038005c4034040c03809a4109a40340b02c040c03240b800042d00454403100401c4a1751a00c1000411070440c42c00c1c01c200840c80c081c40203449038407a910b91401132088110125150f03a0118126000d01c0009080303c101c400a100151115005840200144603030540000003040c5070389d649a250800c545d400283d020a1403403c0b4088 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 44585714 1250 44584464 44584483
    0xb0a020d140c04031203090206040e1815072a0b0910090503091507060c0905010f091d04030c0b0c0318010903080f100f141804030207090c110d090602 66
    0xc1e003004018011444200412642904e03080014410540d100d01c605a014007001d0800a401c40000580014450740c0c45010034011a1b103002c40782c080101c11500316a4401901c0b020301c80b5031107800041100503002e4402c02c601400010042841244003501110100404400c1034a050a00a042200c43c06003400018590280e2500402c01040c0303627100d1341d64902510700690700034041d20103c2015100b50401340c400040e4041d6040c000500c0003840244023030854820340d404107034000b1000c1c040e94001c51641064070303a603c0644000401140200540c0320010708280c0600440300301400101e0350000c2418821607a0481c5640c0e241865441d240340080c050710410200d903d0081914002503020311141d8002e004404100040d4407041844404a89541c0c070408480c1c054800000c0c0380b466600344103211031802c0303400c0c109426844517118064841214000c005030051002405041c0c0c80d03620090075005a4688000c0c3d0004940c50146403c1d60b54050201180c8810410094140d041041110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 44586964 1250 44585714 44585741
    0x60c090a0510020706050f0d0e01060501080a1a0d0611040609030203160303080601030908040518010e09030403020603011802070b090a05100b06040612110304081801020a020f040b030a0b0a020d 85
    0x720550b1002501c2d410742c0c0c0115010020000b035061608906001910401e10701c015042100c08188141213000300724074072486007c1a501c03400240d00368414403d4003c0d07028550100f0b00f0208a440821810540b06002112000c0e50f0712030b4000d0300c40c3c076140600040c1c40b907a205d07960914250b004040c44c10316035120402c80030822180900000340d1040c0744541004003800c0210f103a085c40d21303102455004607040184c2104401c101c2d00308083d40b1040040c12660303c000c8140b02c9840c0c020314140c07a03100310702019409c08000c0004006400d820324a00200c66a103a000600f402680ea4407a044c0c332109413a00d8119500c90138160080c8102408000c040302e5450b0800c0050b8109403012403418080c034031a0030240882c3e4440106007800f541c00043e00c2c5640344040a81c0c1e8038083c42c1181440c0c2007d81503001d401d6540140c50410f5000150042455030014608040041c201040002401340c44d00f0b0103400d802802410000699401545400343c082c1e10070250325841074408080480f03050390b11104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 44588214 1250 44586964 44586979
    0x30306010905010e010210020d060f08070b0304030c030e130915090b010b0903030408010c0c050d0f090e0603010b10020f0c01030911012a0602070c0e19050601090503060c090a05 78
    0x2449a800075010000c459080c20541c94809600340180e04042c1c0c003803005950140002107080020001d68030440c140d4200344003480c2d020b905d4198030f40e5a80c21502814680c1c1c40d041000c0f034046400f03140d042644512900d0492a0106290085041c0c0366400743c41543e02500e92200c101000040c01c2e8440c1480504902008460344039107880c207003e0010703ca10005142e00140c40a810340341030048030050b0000e0340081c0b04a03c01004024140407001c10b0503070b03140c054143e403105411302c50807150403a80c6041e6500c08440d402d180a061200001921203a40366503650804030064444084451442a854003e07062480e0f201b01d0040c20007182c400954101898104210300084e258004100d84450030b00c0d105500d4244050040340d81e6020001b10700c40c0380c00140914040104580082100c58801c0c01100d07c6195034525410341303140c0c181c45040300582c070070000842092466011a520400500d40910034654400210b81400c0741503544040e0030000050300c40c16800c11100c040c009100984414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 44589464 1250 44588214 44588221
    0x6020303060f010c0510201b061b030106140408010e06220209040b040204150b09010f03020f180f10030204080c010203030603030d0509010902120615060405010f0806040906110703080105030303 85
    0x2551944d0400c01100b81c02503851f0703000d400581031614014028072900244940d10300701d5000c030701940d00607903103840241c2c8078480000340313a40701d6903240d850820b20b01ea586608503402c04500b6140c0e0f21040d101825580c00901002a80c01030034010380c1740960603070002d0405424030002061746031001ea840d840b4000c2101c940c5100688481003030070b922540060190548d6244da1000401625411600b01001d074401000481c2c002c5100c00103020700c070002d032250031000002181c250264010070700010702408091103005c80700d4080c0a5002c1804000506050600300810002007107410809254070000f40e0200b01404040402c20114100e90b200740003c606510309140000d51702c0c49201c101103110741d03c81000c949458001d400442450340e008013903510f2602800211036642c03030101d0300000c141c14080800c0055041000413078060713030303410b079202c3c2030300b285451042c1e400700301c0a04890f40281c0e5a150401c041b40d00381c0305000c00040341e1100ca941d200d40c00d0070300400700f80d410b0301310702d03c660000c0051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 44590714 1250 44589464 44589473
    0x3020a020703081c060b0d14010509010b0702030a08040909030201151512020405040609020d0c0903080a0507030216090608061b030105040e010207120e10020304030210140c030406020303060f010c 86
    0x41c4011aa0f1010b50343c0d6030703014216010080b106805040c035403040c0c00e11a01142600340304001e01501e000c4240c08000840c810083c103001c1403400e05c140d030703000381c10b0030014850345107560018501c160010f002c54580900c981d803800c4a42c2d205500c1690f620345c1c3c901c2500d04065081c011007071103011480100c80e456080007a075061061259500c130050104c1c8a01c400c60300191901038500510006208101d0306a995952002950101d400494458680380c202000d007402105588240d81d000960709050544861080d216507112200c00c0d000c0d8815043c07061000c42014000d02c018022403540882c035039180405180c40c162002c1c10a2802149180d89604140f01e42025241100e00803a800b1402e540703101140350080c4524400a042003041c02421070206400c681c504241d08002d588245501d41c2c1e0000403a128081e902000754020381c955500c460540c801c4092141401c101d44406240c44080c070143e81c519846a4481c0300503800100401c00e031480e200b0454018540f00b070901d260018101d555 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 44591964 1250 44590714 44590723
    0x10170f0d030905100905060106090504021204060c03060819030f021216020a0b0a030b030f0703020f04020c070e01030c090c0801080a060c0e120f0118050d030b030c090a0203070e0103020a02 83
    0x41040c01c06a461032840203200d010001e040390031030103000c100f020303030141c0c2482c948a034401d00072a03001c036601103000503081c01c0c61f1003140e01e40081400060b00030740741c3e680e44001031301100912a003016100c0c0000316408100f0300200040046d801c41c0700c000d411043c0ba01501d44490302c1809400d64005002c006520400081290b041c0a140340640301c175050240700190588040d03410240a1490102d510018250194030003030b90320b0000c5040792101880c031400d50760b545020307001c001d41007c0840340c95100e6003001d07006010090403e900fa140c200f5207441d030b1003035501e009074029107404101c45000c0000280622415482da5a1494418419810842496074440c03005800608669443e1030301c4446502c03407654501401802010514820884148203954040000c40b50040b03500c2c040d88003210384408030b00c011700540c0c440040e011024628005800074490029219054000c40059100654a0440d007511440c0461001600c03414070030001050a0140c500a038185881008240d031303980d4002a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 44593214 1250 44591964 44591983
    0x5040c0905030a0b060d0b0106030e0f010c020309040b04060509070816090308030103020904170408010209030615010e1c0f0b090f0604030801090b04020c0708210f03240910170f 78
    0x780f001340751312031344045014181440c40140c843c920450002c10800c1c0e1680103808219003000441d4420710401e01860b00329110203c040b40982c2c010010b150541c01c00d83c0040c61110760003413001a000c1d581c0c2020480e200c0b000ca4001c0005035100003007108a0b04007603428540e00030a4680101000c0c01d40e81c0709070b000c0c401030001034490707840c0c2c04c009010410300c8881c2d19010204040346031f40300d540d00c1804502030b40018958a210303004101c0040c0702c1c442c40041c64504003030f05a554900c50541c0310b0074810032441c2d0454801c0c080400501800100e07094050341a0406e108100e540c200d860403100301410f10104420280442d08001c0070302012940c0320240d5810b54604000000d140c02d10380000070001d00c1403421002007070094400000d4030020101d42001c0071140d6106003515018100244440da08ca82c0703103149550701d410300c0407507140c0035884490180ca841810500000700d58003000079103c10b104680303c0002c80d081400620148900c100c1d03000c010b03090500141008000d0381100d80e00c503010b1a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 44594464 1250 44593214 44593223
    0x90606060706090501090c0602010606051305040b0a080105130c150c0303022b0203010806010b0406090b030a02090613060e01020a05060a090318330c02040911130605040c0905030a 79
    0x81000d01c14862a0b40c00601400d900c000200306000461614080400389403040b400507510740070b80010210b0058040303c0c100e0181000400400342040b04201c01800884400d13a0425046e0b0b0001c151403000344120780c0142068051180600101c0ca41003100d4243c0d0b030800c3c440a895001c030340c1034542c1c0004684807a02c0d4903080c090384a2460281c03026110400350203229102020b8a40d02d0b40e02400c5500a5041e20451416980d043ea2034480c0c840039449940b0501c7c0009103010750400c1503c1e18500550380182120f480507188c001c40100007907150300400142095001244402c000054000c0a45070f0f02540038009880012540e41b5031f42c0e2120401440009a40d0300d0703402075410140308003460503420040700c004c03c818540b0b550101c4058411017281c00f01d04004a0f80e006944260440c80e80c2071300440382e40c2c03003a03500195400e020241041b14411148000e040c2415201d07595850758401c030655480e03200044451901e0b0410040d00c0000f48080281329911405001a4501140c1d000499410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 44595714 1250 44594464 44594467
    0xf060e0a0504050f0d1107060201050702060a05040602090406140a081f021c0203070503040303050606041203110c0618090f040203030304021002162301020f06010612090510060f080609060606 84
    0x20ba040080c01d02441000008031805101c1c0310072000d81c5c2006c0c0420788544141e003260740881d01c84d20141e003294016113002c000748e841540000c2007540a5001603500c00d10450016080500300404242038482940000300f407010094000300c55402c04001c440000c040202c000c11003080051a982c181594013405c602c10107400060000580f0310740c0c2590720480c650342804664a00d080603008001e13410986c0c0450010703007030401080701840c000c825141600c0c0740d00c0170802d0702c03a070907501520041e910841d01c0d04c850140c1e000d000010b0350b4001c0034242c043c03101314540c050203146a0422800c28801001c1806100c481000d000160703c1c00010391b50f0003541034441c1c540c0c040c440301060740b07400c4005991643c682500c000120321080100320b4500900d45108051804200344801603803a4648100c40009a41c412401004010312845400c000404540d0001904c0144c0742c4550b820800a08140d20020b52100300c200801c80c0c8080d0070000500102000c0d0482e820020003040d00d0741400303040284134050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 44596964 1250 44595714 44595721
    0x1306122d02070f0f060e07060306030b060f010215070503150a03050a0206090604030b040f0605070302030f0f10050301050f0f09030a0e01081b030a09050c1c150e1603060f060e0a05 79
    0xf003038912002074100c0c00040620065117800400703011145040441030180450000d00d0320300078050142960390000601c41c0c43e9540c0e0307060000c00690020b00070704520480d80309a8044c100c00e00858060140f6030749150340c07860011811180e1480b1960103030b0040c584000100b01150700170540c1020345034102c074420343e03507000103000540c83e004235080030b0311900d4010184401c00403980001509913203d00d0b4203101d9540c40c40c4084d42240421a403445000f10140e0018a420201b20245588080180c0010412135141c00201e0b0840c3d00496032084000c81400c10b0101d840c0781c4d501042e034014441801503250030b20340800100a80003460300785042c00880301c00326520781003090540550449928010747c40e40340500507140030b00341c80c4005882c00c6c01038156580c01d9003014016005814145076403003810300c21998500070900c070101065500e84e655050821204601880401d50701007980007900c90365411070809104503404203507805003081c9022410452059040c0941d07610044004002036150f5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 44598214 1250 44596964 44596973
    0x9050901022a011404030c11060f0a03060518100b0309011107060b011d03190602070b07020706080604050f06010c03020c120a0308060d08070206030c1306122d0207 72
    0x14815240320b407450800c1c100a5120381038441111480800002480800300c07005280400308000c0d200500000d000d16a0540410302c3c0c0b000f400c4d400080a0f1501d0b2411004522003246604800c0d101070000c0e460304800c0029217014020200c1e200b49020b20043c050030701e40d850210108161003840b03d00d03400400010340540080d804101d0401c40c00108a598048a02d1300303000030200d021845000c0395101e0b4202a0780501e181c1514900100580108003040c4110040f403443c031070344101214000c1c0c0030400d18000481e2114418040d001c9030f001002e6403401d00c1030241200c60020480343c0070740d14010802c40720200714001941c0044003030800608258590600302d08001e1825915500f180b01c10b552106001400210100554041d95550010f07454170b908000420100d4000a452003505000c4800985400301c0150f81060380e03400003030300d030031810170500c27146006503407001d0b0100e000074004501080d4940101c80c8549030549081c4071441ea00040381a046116400e02c2c904d40c0d90200e8201c0400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 44599464 1250 44598214 44598217
    0x6061003090203070605030115020d020d031e0908090a06390501111317060402060f0d0c02011d01090201020703110d200a06090e010b030408040b0714070f06090905090102 75
    0x2a8002c0c3c2550760031512032001910690003031281d40669001140848485403021130141c504c0903469003d01203240484200310060300041e02a0303100351130701e41442d1910200c070340301c0c0090244c860014540c0311101c960420401d081164080814400180c03109401080d01008900356020340c40304505010b4a0724640002894180c40018501e41c40c00c0741c0c0e8040b03418080301130700d000f0003000c0000c512240c44032034a280c0c0e10100407541c2500d5001a003c90014600200034281c4600f411840720300b090800700c0d460040d100500c0d40400581d6540c1c13a400c07a44105504040030503040301000707128101c0d850340000d42c0c1318006d20024140c0e080b101142d1510382e659103d08144241c00c45501417000f01d0f004003039600c038550a050184110034401001510a0007424074100302c0d8009050401903a1a22016400c55400188210740412041101103070044a400103400340b9801020501c0040100d05080e078036058154000480f461003280080000c65403082c4000181e84070711001141544507812030340d029 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 44600714 1250 44599464 44599481
    0xa110105090105040b060307060210020c0316060606020c0402040b03042d0303060e090616050306010201090b0103050109150506030703030c0507080f06070906080f010b0a14040b070507050604050306061003 90
    0x165420901032010310007054120a00407405400c05504a03210042010742d5082e95214400240c1c00c03410082e40007091580c05031140510020940745008103681c46140c40303c80384501120480d07500c1d001032094550400422030001d0040d20f04529080c145100d4000307a003c01803006240b1207001041200c1000c030380c043c4148003143e5104045030f00120f4540903010f0000c03401800c0c610700ca5a8000303020301178000380f000e0103103042205c00010021002000c0fa00c0d9400109598155900c07451200000f41125600900079401500001010a400c1c6803d0f5001e00580d445425842e017800c0520000d550082010011a070b07143c1051105208640382060921049500804c030a0140002243c6654400b1170001d20a203e503a03900f03101c0c107440d108150741161050b6415001e01801c40014001d0000c510010406540e90703003071220b00c69104121410705540281c018100000002c2000000c20504014100280004032141ca007004e040002081e51424001d00451085d81a840686031950080d48403820 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 44601964 1250 44600714 44600747
    0x7050910031104061e03110922080c030703090e06100e010309150504080717160201111e03040807050904020d0b180607020303070801050d03080c25140f07030c0302060a 74
    0x11700710403204e102c2d9400c22803000b941c40112101e0300040515014181034401c0007000c003400216040c48400c40354043d410101210312000801c1703800d41c920410030141401600c6070340c036215141e042c0344c042003090b6009800706026024411442500c00d4002c60001540c05080c070b00090115004c1c10649100900c40c1565045185040c090009009420005001f06801011131441d40317451440c000c0c8007880b94403054502c0e661101c05000c01503208010f110b0003900610219112201206030701d0341645000c01c00c00680342c4c00000c0c00c110f410380038000da40042c10100d4801c1c507649000d8001c2081703480701d041c000b0324446e070304400104400f8a0650500a214115044690a10b407000703010b592075100341c03001c0b4045441c1d1000044c19103040e6031500041649076031542816120070703040030440d8115100e0070403041e00d103044a01c000146d03280c140320071030700070652031402111318002a42000301d070045400c0035812102061000c03a0502000da8203c2c0c0c0d05840283d5141d005d507000300c5628031742290100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 44603214 1250 44601964 44601989
    0xc0b0708060a1206090201030c050c03030109050414101a030d02060c0717030106050703030b040209030a02040b040608150a0e03040b0304080c0106030b0109020c0105090d0f0305101703030403020705091003110406 93
    0x80034000558404145d080c400c0e00c08000c814043c1d40306899038050813110700c03025841000140403d150540100f0740003032184088480300c43c2d4150b0304900b0f000f0fa00c0000ca0849030340d0000e04809203c40e13002d143c00d0703140540c080e15000c01e014030029191031000740181c1c10003038001a55810840741c01040d00c40740e00528505e5440e56141c1c9401006540210002d50009003010340c0441586883c2c03003160340d0020010020b229079400e035400c2c04041c01e900c0003526481540c8200c00a2000f200707010b0440b00f03441c0d20242200c0c81c1340410200e4111900440d0743c035015481071205100350510030088a8026400400035501c3d6030101c0500c5000d00030300c0e00001e200c100c200000041803a0103402800d079001c10480280025903c00c040d0310707031354011400c44000144801c2a0b600f401406a031016401412117400e1119190b110480300c0c0201d00880103107001070703100108000506034140446000790100700c07980741242c1414603d0407100440382c000500003010400040409940395480340b40206004400c03103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 44604320 1106 44603214 44603249
    0xb03041b09050a020406030516020d11070b1801020f0c010f03020d06030605072a050303010b0f12010308040801060504050c030f0705040815160c0b0708060a 69
    0x1aa000440500c0411103003500c2c05050302c640c0780c084025941e90303e03001c4001c4c2100d4000784110451a012140d44140c59404510302400c5030341441c0086d05501d01c0036034281003c0e0030b0390100700b0201001801a880560007119040c030100241c096881100701c0030340050301c50128400d19800a4000076000358203600075030142c0421420500001156a20380d0344950460703005071101c80c041905012403060710241440042e2511807410b1003440030314680d0341c94650b0303400b040c0102c91202001083c001030009106040c0c5840c210242c002000950b581d0400142c2507000d400340c45003e5091a8002c41c50b81000e0081358068001080042d1543d6200310071699a1748000c1c2044080140422000038803c03020050065400b03020720003920b081c02d007103030001004000000031406002c01c09004502003010b805d4030307680c03002700c2c7e040c1540c142d96582c00250390a540c1e900300300e5041c141c60804 = true := by decide +kernel

theorem cover : BRFrame.Cov 44424464 44604320 := by
  have h0 := BRFrame.cov_init 44424464
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44424464 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 44424464 ≤ n) (h2 : n < 44604320) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
