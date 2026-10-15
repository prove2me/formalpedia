-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3822
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:36.728848+00:00
-- url     : https://prove2.me/submissions/5bfc820c-8a54-47de-9e06-03ef2a612597

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 687230215 ≤ n < 687410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 687231465 1250 687230215 687230221
    0xf0c0d0804121e0f0c050a0b090607050403150b13090f0b010807181802150307080703060b030402150c120705010e0a05030a08071e0f090501020105070f0e0a03021206040605070305 79
    0x40c40c0102c3c0551124403d0001540c89004100c1c0a506012010354020b02071360603540d46420312924003c5c007280c1409403409044001500207002c1c1d802d030381c00d80740c01010600900800088200082c100c085610b030703010710210b0300b11170108000d0080b40c0c0d00920520b01c1d004a000145043e07a40d0242c10782060a142e00300170414000681e100140d2031000d00c1c0150003044049007030078034040d034031400003000e90440d268a81c1100e41520200045002e03018550f1190729540e1052001c4007228280e0141003804041040403501501d4070000007103102c4507400705580340c0790704403420b941781101d40c40c011041c0701d00200d04502402002c1c451aa641031210010f40a50000d9546054880c0305114844050005241c080b4103580d104581c10340d40342030b080c13010b004410300000d40039090309012031990f00010a2402d01150f103520601070310707000d03101c103803120544003032000801d66003480c40111103600200300000020160782d810521014038aa02000b0701180e007401e08001c426200028440c00c18507080c0014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 687232715 1250 687231465 687231497
    0x62e090c030b12210f0310230a171204090c090f030201140c071203030e010b0409030e0112020906040b040f080106032d0b04080903010e070b030c0f0c0d080412 70
    0xb8180c80b05404e0440300c8403c42d401c10100b0540100800d40041c01000700400a131640000d540a040d0b400008490460140c0005018212100c1d500d5094000a20807820482c42109200303594910442c8025100c1506804100040a801c40e500060702c4603241c00d0b901c0001900010843d0280011030040b041c044d00356000a004906600442c1c4004080004d107040811010b02100340136000e50520315040c3c50b0035040040240803000034011307980d4a0480c0143c440d203024800c41c0d60312503064540c07020844ca070000545e40306a01c60b6100c09003030b400700b1000100d9903900b40104050500100060f4a80382480c0c0c0b103031020380c8103401c88000303a0315020303060004c00d50620340036003c846401614840062454240b00e8540b01d50580100050440300900007041001005071000b83d405030020015504a160659929040351042d0f59105a080003c5004040200300426a0200b0845018941030051102c1450440302031107900000d40c41b00d05000130000424500030300e4219a2814441074100d1046e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 687233965 1250 687232715 687232723
    0x91b0108091c0c08040312120c17090307020301090c0303020115060903060209060405030a06060302120316080a0c1406010e06091e0405122d030702062e090c030b12 72
    0x501050740c80e080c2c0d60111180791085440300440ba510001d03864a556891410b4032100440b60201000710b01c02000c3c07a08140135600c100407140400380c2d9000f074044802c038980c050780103010b4240710039404108082005a20700f40200d0083d2072248a0a60312a495420002d0849442c06100f03800c900b600c48040020550000c1b8101c15240c01c40401640c48105400298441c480d550099400d40103e0480d0010f01006a020f0740840b8026100010700c40c0d52088840d89034480c030100f5400400d80c50072608003091206c009083c8545460400c90300031113580d10b504051504035450004503038041001440609000141d054001c032054440e42624100141c00011012201d84000f0036111650700207018804100840211046802c543d40d44e600100741c2c000681d54004411a03080050b00043e03035023940d4554049038480d00d0183e01510854035041000360b0b0352a9801100c102c0c1c0f083d20314401346002c000b05010300091442400024580b826030002900752660713080010320524215902000d400e00100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 687235215 1250 687233965 687233983
    0x1810080c09060403170c07150203120a140412090504050105011e02120c0d0306051e0d050708060f0f0f040308070e0409080c06010f090908071514091b010809 69
    0x38419645620544000c9841400389a0026082200a60080c1d107030f030030301e50001e202242c04103040c0d422040d2280f1000b114510700740710201c0143c0c0200300c4034260540d1a01c1a5401083e50000070548500458440075145001d032015a230030341c0c11104000303490340c000c51700e0401031509450601c0f6039890500080c200074561416100811003d240c8a45042d03c01e02c1b00407191a1051501e40e203a503102d207490b540c0c50404245041c0440e140003008a050700c0c010b00700c0a44065003504445039040c2c00c405104201540f180210362078840e00d034000c280200301f48103451013510100e144a0b59480e1900c40e4404010300600f0030003a54080c6024440840d911210b000d910003060b060850240700000007280060940c0200030b0a00b00020586801a003000b00e101c0f8100ca1503c58128180358880408008035090000700030104c46041090800096010120000d100303981c9400088207200350352008000e03c005c40e80c2c1d0100d40c10014091459003d8155403c04140007807808010515003d60001e5981ca004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 687236465 1250 687235215 687235231
    0x80604170a020c1e01120b0a05010e03030d020a050304060b0d050c0603100b0d02040e0108071202090604290901061d0f1212090405010605160f1104060b181008 70
    0x300704024600070001c80c82d459002130000191200300a010301040d9404c80c803024001528890001c81001030340c000d04029800080000700380e01d2070400155070f14203002214641601003480380c0c280700320301c51016007800d070780b00c0c0ca405948c0d00e0180f4151040710b000c805c15503c908407003902031740801c0001580403906407040d034040c0e6a9844045030741c010000e0541c0040740e0070b10001030380104215241c0183c411038252000503441030b44c0300c11000c1d803584841d01401080b03040344550a005480c01c02440780c2c101c00c001d040011400070f808096420481c9002030340c8039a070342d40d500188050404007035031801000c0302e00e41000882e5400a12028036800c102c000c5204d801c130342c0304540311941c1c5c001041c85031401650840304c2885080803061080e400c40c3e24520b21840c0350000004407940100100d81c01114030024152600941d84e41c0ca561101d003c40d070565805a65052900064a030b40c4541341c043d0040d6400300f601daa80c0c0f40d9084202c04854024503003c2d00449091300b104e1030f00005226000305075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 687237715 1250 687236465 687236467
    0x60306230f0a0f0c02010f06050102150a1a09090a12080613090501141006020105011a0403060c0306150203070611040e180a020d03030606120516030b01020109080706020405010908060417 82
    0x10251204040e00e40f405403400c0541c54401040d0b03425030158070007c60249090410b00000399a40c005988607040180d42c900c40403541e40c00103002d090260b00c0b05c00c000c01001c64800658050303502255141c00c0444e81d507840e45c0d001d0343c0c1e590140035280c20040340b00d187c10300e0401e070717540b9081c004140403490084407030914945400c01a010403400307401281010a07145028009440c1c000f580c08102d137140c2c0314036000340d481c040001c990740c841c8207800017050707130400d040902c0e162031981d03000700614030215503008143da10b000114600407605204250342c00241c1c020341c2c5514260402c601155280c00010320301d168204010400c603403d0f80100350f80000090b0041180c8946080c00d9030500104a2009610060000d03041c020507801da4482015680590b0310401c0011305811003804684060f0b80c102840451050260b05080c425004016580018800801d0040b040c3d0740e10708050704030080c01c58002e50042020302842d6444101c0d0b4009000100c000c1a49080545803211089485004900d0140e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 687238965 1250 687237715 687237721
    0x52d01060b1605010f0926041202130b090108010510050306090c120307080408060403030b040b01080402151611090705070803070e0609030303090109060b04060302031c1103030703060306230f 84
    0xc1c05e5001c42da100c0940c0c036040c0600c0d0380910340b030b41e29444c0c4440318902410b40c2a4003035070a800100e0a0300c003900d1100404603402a51502000308150303202c05840111911440c6c007600715140d04543e20300030810000046150f041c112540e04600d80c0f203400103402a0302c007804003c4807205c0040c001010032002c3c0d07002990070300d03558201821481064005405c803a000540002c0d01d0500083d501e2065019981c208a2242e524080205072400c0c0c0078400d00003004032022074098074009106000c6460189010b600d05004e10a001c034445000000c10340c0e4500d450810390303602c4d084c030300066540031f04a03203085860300c0403a945040840c00090311480c20801440030064803503e030305045914608004084907160703d4088816406805942022645c190900c0c0c000f407080c1c10540180030130f8035802400340290300a80380b0310f03000c0c9901c1c002441f4200494445030102e030080030710040d030040102d0b540101d0030728150b0030003005450168800c00d01d40071401e06601100c9030a80252600201c495091807681c0d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 687240215 1250 687238965 687238973
    0x61c39020f03130501020d050a0509041a030a1109100501020303040605150414100506040b2b140907050d1a07020a06020408071809050309010507050703052d01060b16 73
    0x110304107200c45550300c0001082c50551001c030f030707450302220802d07400c845a00c04041c108442c240105031701030001c1081842040042e01d0590032002100c4001b0001000140f55240003d29210540d801940c01c030311483e410910f04d00300241e20342c0c3e0218151003100b103100c1c94000000d50307902c0002d2001e0440c65640300403a03100704500300c03c2c9503070307843c000c0040c48080d58055007200300000a03203c00e40d071200000c070000b961f82000381c191001ca5001c1b8a8003820045908140d40c03580e0009403150001c90241c4510041c1d20301d45100b40b130140014180d40304e000e807900010071464910141c001d24410700b070903551580003904d03c0c000d0380c1c09402c0601c401d01007900d070b0f0242039103403800f540c10080081c2e0000c0b4000ca2000307000141c5400b10b072000307901c0180d0300000e04240340c200c1d034074150701402e2034008110560b46035001300000d0098611500440700520380d40e88030141808985030600040003020b880b03444220300a211131004a0002c04001c00c4000e1400d440700707815100d40c211000e0303410400c0210320244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 687241465 1250 687240215 687240223
    0x30503061011100204140a0f060c0507050603040819050306212b0201060617060f06131d0c09010f0e0a09150906060203040305060f04080702061c3902 66
    0x90a400103c1e81c400c80b2020261000c0e40081c019a4451b80c07102c10300e050640b030032010f0141150303904118400450b040c040c08650402c0680003d40e505d1003410b00008554031600000c41c402c50003411f0058a943c104541d500341a096405050300300310007072007072002c1580c0e210404600960b40d4268440b0124030861400d0600011850001d10f195100501c10817800034011300c41d40b4100d00343e000f04001511141c09071001d07010030b0b0758080da00e000d40000074210308002099a80c112401808541482c50408182600d01c0064020b400030b00c1c50703803840c1045281c1c0c00b491150840d80e0841c1403030800c0c0c02032000a007802c111403003450402c0316600d140e0455071500d2042401030400c2003014044d5204400c402c0300e04501903c22000194603040002030032a10110588046e80d900001500d083d4039400c0400b194400c01500a42d9800410004280141d03210340c010500407054440302c041c1d0901e1084403808070f62005400102c0d11021440360809410840d0b484011514000c2c12003019500d4a1022458 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 687242715 1250 687241465 687241487
    0xf0f070c05151b12150f060c0a02010e041e38030c040608071e09051f0b04060e190e25140706020d1518050f040305030610 54
    0x80d0040951403840e450010748060300c10580101c034180c0c0d840700101e10803410f20a49041380c4c120241c03600424040b6904407603550b088000200210b80c01c0e00c041002441540c0038401042c0140c0c0304446280865800119043da0031008590810503c070903004542c0545042003004c43c41c1d82d580300c0c0e4000d540485079034034200d101000d200c40f0b903100700034024550700c112610510302e2180c4500d00d001d0b4414a043e005207001e0311900320180000b1842c141c901842c07a0a0342c0320213030361104c10348804a01041c0c1e82c0315607449030030f0f41c01030b107aa05260f146201203003160503008a08120000c1000b03008042c1c010403429001d18054030020440824502002941c080d242c005078181a090320500c5800b10f09008100300080c07141500f418000007401003070700d035100504202d820052042c0b28420114a45a002d000b2072507142e040070450496a401000c002d4045030041d100000382e6503040c590130b5900d8401c055004044c03209045d424101902d015105000040010344144041013a8014a074410012605 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 687243965 1250 687242715 687242723
    0x40f060203010b1309050c0436050a05070f080c071e05010b01080702061302060903100e0304080f01060305100b0a080615010f0816141e040312080f0f070c 68
    0x24503961100c03402c0140b50300401c100000340e1581343d004502c810f0b49214842c05040012900c51130a85005448070224500b810001011a8104881c0c200340600402c031a83c03445c000800003130146011681842110000340c5114108209600d0802130103400015454100c48400d0030709848150900e0300610255003100004031b00702e0006454002c000c4150001c1c0e4040d182602c84100a03641c0c85000c80c1d07290012101e0545041c2280f01400241c01c0031030003050241000f909035000041001102400d8072240b0700201c82c2640001010000b100c0c01344002510704108200911640345145c44203030fa5030700c909850400007942ca00011300706545800c2c003030b80204141c00c1641d003e490100a00c0c844480900742d01070104544101e021542485000f1003480303070001c45c80d01240f00900e090304a4810840c68801c02100303104000c1803903940352408000306940d020700000c664481c114604881c81e14580132142d814010030100344544580d00074a29a40203003050740001d601d5031400c0c000c4030343c10b11840c030240c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 687245215 1250 687243965 687243967
    0x5301218070b1c060e04050606010806062203031103210c0702130b0f0603061f0e03070f030624060c05070929060903030901121b08010305011107020f0108040f0602 72
    0x90700a1110f001a49203e2140003000c00034942da920982000d0b80c01154020015044100059807940c06984035503040480501306500346520400301d4402c2c001001103c054052050b00c0400401d64801400c0d4051040c0f000598203011341c2d00040e604a00e40040303160505103401c0c2c0000e841d83c03c06001c1d00c02d02e680040c802899200d883c0c00200085c5051168140240c61f82c3c20003001d40e0a088003281c2c000c040280c969001950784100201a9003002916441046a0600318650395030301048140054007011061240103480c0d440e025003100c3c00c1d40c11041e07400307012500024094078000f1142c400c1300d509041c440c2000c01c80d40307080c3d8148005038111030200303813400221480b60441c0b09003219a150981c462034025a0380350381045114001c07100360a83c0b48d44200250905544618911100454203c40200d003200060f4072000210030070041c1000003518100041007401824024485280c5003e81e0392840c1c80c1075500824540c00052400b02e05200089000c1810451022014155142c21083c11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 687246465 1250 687245215 687245227
    0x130203010203070908010c0f1b0c0302040c0905180f04030c031707030f1d12091c03020c030d0e0f0d0318031401110313060504030c05301218070b 64
    0x44c01e0141c1354020410950700c0d100d440801d047c05540441090b1100d038460300321040b810001c7e00003003210654211400e00c0c810b0030010050b1202d000365401e48895440d40d1814a017010148212800c01c440f903095a45034a0041c01147d03034180f8081c6821a8152038a080c1c0428242016100c0000028034044046c0946c020405e51540c1607201103408844e2000900072083c1c02d0140703408a805c004d0041216400001c0344010510b000c400900700c10001030300174144200c030394050541091030a8010307000b5800203008808185400d0212410689070750030900c2101e6004004510b52180410082d03006402c441030311024135000b4050586410881c0c0f00905040e5100d01e4504240c58981501040b1036082603000c0188100e0134003600c1c8290401c003240e50604003551180c101405010b0015414088003051000201e07106200001103404c40741003005107141c610043d10f050700b0401c1c0302242e2000381400900382e00034815144c40c0e0481c0600c1801100700c0854030440c0e0a112060b405051440e00016030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 687247715 1250 687246465 687246467
    0x3310021510060801080a03021b03160e0403090f0308070308060a080f0c09090d1202090616080405031005060f0d02190801050103060606030e0a030302030a1d0303040c06020c0a030b13020301020307 86
    0x207059481a43d10000390366640c2071440d50303c20010b6401070143e000244441c41c40000d21100701481c18006003203490003039410910700e075010401e4101d590440320000800052540100c0f0340070003410703400024400d451650b11046030340d002d001030041c20481d551000c40d069594401699010380541010b81d041071002c400455640c0d680c3d081640e02944202000451405000c00c582003a040641ca13803480142c01124420000e500602c849030780300303206010107040d4040081c4c0c80851203210b800c81c141c8e241c0c240010145820301205050020901b802c04000d59904c0d01032507607400400c15a24a0103401c4107200040e0b00c1f1003086e102624856800000040b1003005411850407240a42020004180c440390700718240d55030a010b4101c10b41c441e400d070400181c400c0c1c0c01141e100c81100e0001600745003090107400b034151908025051944044184010f1011041d03d207002003250f8001045410010400705440c800300340b00203022045a1400907140e075015a05c6005900c0d4000c00840d540c3c682088 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 687248965 1250 687247715 687247741
    0x408040b181018050d0f0c0602060a1b090611010608010c050706051503070e0403050d020304080702042f0714031315050a0915030b030d0833100215 65
    0x9001c62103401c000c0503900050380642d41c9090307100089440d0035045070520013401400d1008101c102c030494034000d05000854240c0040d08058240c5a025000b1414040450f506613224601c6041c1000861406414050340002d29070301241c0c400d040482c000c00a410707403a0300401199008141950800c03050800c4030303a12400916141d44660010000e42d29001c00c02c101d100100c1d040580c1560001109112240b0104185548184a0b00d4a01e00e41918505d8680907030700300341c40841c0d01032004140c5d0b0046107000d0245035801140d1002c4070030061101c60b00c2c03515030720071105000e286030f000042200610401000845c006a08a02102d07902c041070001100d0240300d510400c00680400000c1c0c14400e840342e4201c481903aa1a602c2d5245a13041200d41840202c1419414061555407558090541c41c09e1040d454140041d0301c900f441860100300b06c1408076401c1c03e004444120000440710b4041d1002c0c0b0301d203082c50b001d50701b014040305030400c103916000c0e103240c0700b54501c20401c0c04c002c2001944d032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 687250215 1250 687248965 687249007
    0xc0c0b04050a09060b0406050f0d1802040f05060a050402300a14070206040219080a03080702120703050f030a02070807080304031e02030336100605060a0f080408040b 73
    0x500e098142640e00e5040f5070445190f40900031901d50f00b040300f040300612400190a0540450045500d0550582e01c02c80864401520941c868402440c4c000d09514203841808440e2001e102c0610481c500040080c58141c940e0150601c2030394042403d0124070704110385594520580180c0e0f503007072a0301c0304560b415100304a0313014240c80d040008000c0d03444030207030096000714419002084640c070341d94208420b403400030420010400c5007100010704040c040040c0000741303000745c69071984c0341042c0100a08202508180030001d1004104d2080026440003ca81074051000c50f0f00b9100d0702d40c05c1d0302001a1141c880d024020301c2c40410000c09019140004501451081d15820498038290070200e41e0104150354020243e0030a000044c205041f8440d0f102c102101200c41c1054070034406142600e05110a0102105622540c0c2c0c60100c91140c0c812800507100441e4a1414122a41d00003031113031101e00c18035000c000301350f00030a0400041c04117070f0b0050030012001176100c1100741c0c462041d1003601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 687251465 1250 687250215 687250219
    0x4080706030b0f01020d050f070204111215010207060e04050a0b09071205090c1804060f0c03020901090803070c06050a050910110c040615050c0c0618130c120c0c0c0b0405 75
    0x410328608044d8000950000c141d20301e500c03a80c1c01d11101d00171540c0540c001c0041660003544600c0b4142000c1d070100b008006c040202c0035890034a0420b41d001070700301d10120204034155030003c50288440e6810081042a1000c112400f0401e44c1d291000c0c680507040d480c2c681a0004c0800c0c090128a80e0081c2510031a01e90300d60080180399595800c80f950b9403201308105070442a00c01c138010f10b229040c005a58454001c070380c04500f0314581c02d00311048a02c1280402c1c0040d6010442d04400d41c1c1c05407580004084d010011410524242c6070a03040020034402d031010320400041304200c41e8020301c10707900d112000600d400c030010051100905104a100b01010303903800740b0388000ca850b2500f40303d801c003076400c460b440040003a00800203a4081c1c0c0702c1002c0a00c203100d118200c81080d0f41e51802803400300d041420301c030081600079048c801501c2c4128410307517221342402d000240c2c05034040c000019a6035000300108400e00c01c00b07010b0f1140c41d00a00c02504a59040710b0109148080304000c00440b202 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 687252715 1250 687251465 687251479
    0x20606120a062f0a1b0503090d061506020304150e010207150909050604020c0a14010f02030a0e06010509150103090311010504050c0316050603010b03060a050a080601240807120204080706030b 84
    0x2032906083d00d210310030540c0c010501ca1400164001c401050303440f84c0c28410002c4910f4000c00e403000604054500404550b20345d00d80c031321003035541e000351425401805540010341c01e050810060340e240d0754076010100c082005001003080503a200300b0261300108603c600d22040241c001c100100301011500907190781d941410080380d42e43c1414400c0f180c1c0403001c40b01600c152000c5540b038407442040c0001c0404507640740c2d054110340f0303021440114029180c1040000326540c0301d414840c200b00301688058400d14150082000c40ba244030060a1038400918000540b40410325041c0e40e2840142400300096107450204001c2002c0081d5200c00a10110110703080503001c2c40001c05507e1403400303107940000b8103000400154500706c0140d6003001004011640b0b06031141d02051980307074583d009072080d9000c2c1300104101925207000e4001036059860403020034807040000782a180019181d00100010000c420740d078401b495048d50090b0000700181c072500340d50707408014058414800080c0c41052 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 687253965 1250 687252715 687252791
    0x109020d20010e061c06181b020105010608281d07050f0a0303030b0607050111130608060604060e040f1a190602060c0f0d02040b042103020606120a06 66
    0x80100c203200c520b0741000b0710303e034a41425580c0340c2007103030203400c2d16895050310741b100400c1d44000880d40c01e1405558142c00500c0740e02071260324803a00144482d51056900d494014014560b02c12001903000e10140b8694a408814945403625002b8015a4041d01458120741081482064406500e244070140803900780c03e4940c001c0006400202500c07079400005c44000f0000a80283c000e00c030f5041004082d03608000c8540c51b45030a60321080c6196080040001e00c484a0b41c205440e00e1000e842c140c80c01010b41d14200b00403468170311032030188006000011007a01030981d1150030040051a08284c14440c405000390784841290307810790114400c5000f9012150b2441c0715110060031134040c0d90050020380ca0315103224896601c1040580203000c1c0400c28040403d10f07a0000740000e101d4004496542d070b2a0070031582100e00b1002e1491151402e100c400000b003540005d51641000085500d0f00c10450100b40325480c1248001e0000d05071420054045e01c0c1401300301944186054403071400c0c45c019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 687255215 1250 687253965 687253967
    0x10302180906070e0307050d06020c100b010e0108151306050a05011b021c05030319050a090c0303080703020d15090506010804030f0f0536040903050304140109020d2001 74
    0x9541101c841d0200e501440c00146020303c644842c28120b48040c060307850711038a900120b00c1c008030341101520b0309a0001a120740c00c142c00c110b80f204074101c481e401c01c10703158240c00081605045420070741c10004010b000c2020304840e52031190706104010854180d410918038150080e10491145034864031100c0c10000b0994025034046140c0300d820071500490071460350030841d0b9162800c00000041c080d2414040000703800300015402501c40503d41000000140c1c500d1b070a442004010f503d0850629140c0d00c001041c00d41200d054030f0303050a045c9901c0c2d46290049000740103008a80240505050507440740f12141e043c0c0d1015101024000d02880e038564005403641941030720002c2c0028943d0342c0030b030321480c80788000340020f42991070321070315190b10382c1c0b810b01c1c800b43e00c0c84000900d410b070030a4000c1c1284400c0907000c180d80b002e40b8144075080041d1005000c90000a00c0580300c56002000c1ca10541000c0d802071502aa005059260b400d00303504011001d58845d035449074200e012103210307040369 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 687256465 1250 687255215 687255259
    0x60601021504080d02090d030e270a09030207030f0308090c0a080a12050c0307080301055d0d091517090a020411030a050a0b0609120a170a170f0103080c0f03040608010302 75
    0x400d0040410740031b41e10bd0b43c6040c4d000f000110340035421801a00000f00c00901c50900d29086540240d44441c80c3d4109194442e00700510078046c40e120702e48144c0104014440807803213040c4c464000302c3c0035500e1285c1c000240d51314419041c51030901c1c000000d55208003c060340146069400940304e1b10900c4510f0b413090703818500100c454011910b03664081080741c840f85540e0001b21002c0312890203108145552540082d04000300c203451f0350b00070031211400d056020751310340002c0183c58054140440002e402404c501400e42821200c21100303000696210000c2002a01a981c0a4000c01141c1565024003056800c00e0b11011280c5003001c0204030300d040b99018100c850500144250b20f04a14a420041034884842c981011030040e101e50b4000714002d0600c901100c108008001d82d0b40344c0d000001030400c0c00810246000b684284107000c1081007110003281904c0d40040010361316469580158980414440350140c0380c0f10005004c12806c0e03000e48501e04885c03094400c0a03822180025900c3e034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 687257715 1250 687256465 687256519
    0x109020a0b07050106050d080a020f120306040b01140a181a040608070c0b0403080610030504051b06040f1413020909191d0609060601021504080d02090d030e 69
    0x220200301002400201400001400340500c56400000c94559903c08201203114012041d50450404158000142c0d0180013504a1110001c0609400444220458820302024109038010760340c1e41c2c00201c403640030707041c003200d00100c03a2151038440c1844080240251a88150140c241c809008009911052161a100e102010240d018140b41c1405000c80390302000400c010104141c0451000c04a40b44c0300340e49000d82c2c02030342e49101c940f401d5001e11210300b90325810001018030b0402084082900460560804840300000c101a00e200310006851402650803190000c4100c010000d5000d5040c102ea0300860300580b041203c8021100c3c00034101e00440403125000b0000c0c0000944e603076064880001e49010400300081c100d014091a040146040c850400042d88194103000111608205c01c0354080824401011040580020354440c6034010b00020000c1501041800840c0083d8040d1480c0800240c0401c5801140e800c000f0301d90b0301d23281c6086014000c004030304540c008109068000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 687258965 1250 687257715 687257719
    0x31303051204120b070e1009090b010c0b040213020f1b070605040305030d0509240a1416030c0219030210050a021306120603170309070503010915150f08010e0f010902 73
    0x31401003541c131241c0c01c01c1c0c070082180080204140c404901c503514090387c460302c024940d50344100d141c10b0070207072421a8088078000e41800400302816001503410389455500a138144c032100c034010491003c2c20064000c80908000c1f443c40454008420340301400468900d259510803a1782080c3c2d5220182e54a10071400042c0c400d410811950341034031a19080180c02c030f81040b00700c400c4419440080c4e02000c5114032903d49409285090141100c1a40100103c5180310300d0304031000d09040c101c040060031612810000e05849525200d403090080c051400080300400f0307110000328261034001d440b1102100b107045583d2501000c1803030b41c6018400d41d060820b941800790aa6810070106861040c94240038010080e15a80080700051007425802d0300109001d000317940302e007031803d40306040800b650004c501a80c03416550001190a562980b50390300c040d00800540c400c4424032900080c041e035003100300d05c4850814005502c2d00d055000d40040300e03020050301d040d009030383c01050a8070300c0482d001e9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 687260215 1250 687258965 687258989
    0x9032112060f0f040c140301081f0c02032209061202100206070f140d11070c060f08060f180c0d060f0506030103021009230f01020102120103080f0903031303051204 72
    0x8292420315a0101c0d0080c401e80c1010301c8451741b0b4514290981c0e000340c124080d140c105040d42800c1c80020b191030080100c0520062200852114000b5500d0203800d03800403070415610b11500203000e00116082c080c116094080c02001d031201e20030f9540c01211031003240030300c041d841e03854100391000c0b8505018104940d105412230242003822540d288444d09030740b0301c0940c1046403050865440c800c210450110300303404c81e128415410310020540c4640d00107024403a20a0081c4510ba510656141d030101c0308070354a1450b0135501010588882c8c40c0514030b980040e85406001030b201c00200604020031010009110032912465500c0d60500144103441d00800184014401072510020042a100c0c05240200d080c5586034005880342248548064070300d4030254954000e403c08600b810b540ca0402c0c0002d5261110021b051103183c41c0510010340810004940340300490300d240211042c040b40107041340c1c0c59411541c0ba6641c4034100d0f10084a4604c1502c0a83e00f90307505034005c2d035044902940303450f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 687261465 1250 687260215 687260239
    0x24071a101d010905060105090306090705100215070c0609060c0e150a0203030105060906210103051011070f020f03010c090503010c11100c0e0612100605090604060509032112060f 78
    0x80f5000e09030241c200b905121061003071f0b002c035403402c000c0d01d40b0078030600005040d694588018030104e100300c16411811900451581401d034011180042d0b04904a441c00307014075000c0b400c000d4020150100e00604480c1000481d9445a40c0680751015142044407901c005548203d0045003d20500d200040540c00600041000340303814800b80140d60380203048203186c8411a14090a02c203a80c9081c84882c4c0340030030051062040400042c82880202d0008012001d03860804035070718003807110010b0000502e5011801191101d0061421880010700240f001a090401c0640b410500d80182c070301941c64070751b061084500c102d00a40c420352080004d084600c0f181c850102c042c2018510304014405c00740c41d081040d49406004219240c2c001504960504084203812000c8500b030380302c40704000c81480310340c2c0103948450840c0e0448103a420102d0381c0c0e16400000c2400c094070303410b0907070003404145d1205651450510041c42600c02140d0040c245685410800900520510b64950441074034698 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 687262715 1250 687261465 687261479
    0x121020103050a090b0c0d0b0105161217010602070501021c0c0305070c030b01060309020103050f04110d230703020a08030a090302060918090c01031104030224071a101d01 75
    0x110b07a03000b006001002c216a8429222550110b03410b07180700d88600310020320300400450380d20409400038003d00e0010328103daa010a03c950081856018141045114a0996440c081c800b081903810000044001941e5510000fa407611305911801c0c1c003600580e01200503804a2030b03001d008411954403140000c0040342c07000c82d843e402c80d10080f00c84440c40c6c840480400c1c031b205005030080809a401044000b40d0744001000d0751000741c1b180b010504004113000003d0412240107170400c4c81951502c078510301c0f0342405c610b4840702c0b4120400b5040695010304465001048000c182d038001c2d03130801c0515958240484d52881010380300000100c801006100601e002c1c00182000b00000301100f0000a0190080d41804c000ba9980f41169010403400b41180d40c06001d49404015107460040c00c103480d40d004507007409502d038081c3c41c10207400001411520012000d441d02d5540101c8500c4000c2c2800829260301a030507076108045030a42c20002820810040c680001030241c110005c107240d04c1c000f5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 687263965 1250 687262715 687262721
    0x170f070e060d06020304080a0306080309090c090109030c0f051212270925050901170a09050f1506040b2d120102130602121e0f0304080a080121020103 66
    0x4201e511405040301440480c0c83c60010310301036802820090f51359000e20101800302d80d032660180e005504107000103100d5645403510700380d02000081d25282c0d590b041400403140c881080c1c100810507848280d011a400c0d6058010030140c0710203942000241100345800380c3e641120070381c8481c082008010450032180200c0f20520b1640e180418036401081c82d4001072900c0b003003118a1706100c66103c034080d00d94145aa0f5005018585003031030342c074256002d00020080700d0711030000300781320035148003298500328194400340e481d50300002900c030600c809407219620742594903180c00c0c0302d12102011030854641840b64a00c0140c000305655002c0301d004000b80140b4900104400341c00703600500380301c15502e8060804568400080c00180d0f00d071a01801c40d41145000d801000442d4003c81c14100505d0041c02214110300000c445044502d08080140c0624481c064811480000100921040045060203054040030503120700b20145e8981040c0ac0080e0090078a114074a08000714a001550003a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 687265215 1250 687263965 687263971
    0x809031b0d240c0e01020d0305090307020d0c1a03040302061e0a051f06020f2404080d06090f1406030a0c061103071b0e100503071403010e0106030c170f070e 69
    0x50b25201201e200030002c2c40c00c03500144084800f08a1520310b14040d9a0706002d0141d050036181030070401030400c8042c150340ca000300f850090082d2000c2145030144403150600100502d40700362101d0780c0c07030500c80200c03c2a801c269802c40c0503100300000300b04d01406a020102101c0e041011000303480d0341c1c08801d60017801025010b0205200b820814007c203030550350a42004e096150018941c2080c907070f02d02d900e000c00a200074408000401050540000051120361304190003111480d25600304600301b400a05841c0e0010110030701e0b00515401034015a00004d050310f414000c40141d0740d684e44c0c181621098607400090040e120301b8070500200e40034919010021030710740304983c2000440d5407900410000a60b81e842d40c039400103401c0042044494405520552500808035031610305804290b88501178042d0045d16001030300300c28103c1d20250700044050800308001d0001c1541c0303040030b1200b81e5a43c00307440c04000c181e880607602118002003e052413500b01000f0a6400c1c94a0094800f40c8005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 687266465 1250 687265215 687265253
    0xa030c080d0c02031908060d02060f120118060b031e0a0612050604051c0504031502250b09010207030e0d05030f030405161401020604061a0307030809031b0d 69
    0x1402101581e81c82031282100c1c0b0007094000b569a0b034650300284207001143e012207420424034500304451616041d0240c00e18030b034151075041d00c4011526003481d035800303514401d035001c25411000040f00d9080c0c00d079402072202440d40411071541c4500d0160780c5171000b00c682404010a128038070415444480708580c1c4241c040c0ca00045280e2500124100b80603003c0c01503545070700600510052000a01050082000c209500c03111411a4400506079005522004d0900511a50030b40c0000045030115007100101121000d0700d800c002c0450907203220f201c003068484690210010711401c1052089a44058160700c034203a03248412020001d018101d540e04860a000c1880480c6510710f021000d103010b540300714003034404400740c07540307051800030a98400105e0b01988801009141d80106038641c2094102002081c60002180c0d180003d041800700d460f05413140328000800d100f4800054540310380110161401441c51007100d802e988a402c282990000400d0090030003c0e40d0b00c01c10b80604000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 687267715 1250 687266465 687266467
    0x120804110d14150901060603090b130c05120d080a061a090a0801020c1b01140a03050a201c09110d060905030424080405070504110903030a050a1b050a030c08 69
    0x10148a880c2072949030420700c82088900c8061118031356080c01a003014080314603003000241c82e25144c004161a003d03082021801d4064280d80a1013500000d450140001a00000101d0010741d0119501e2001d540000d0001d00350038040b0701c00800c140110002c030b40050080d00740b070602c40c4005407501d074441002e241e8010603542e400160080300f80058016852a1400b510030741c0c410921000915002d5075500381080502543c503140e40141805803615855140303030000702940d50000301d2006229062034007061a204400000444210038000d041c22010380e20552000800804114140c61100030018441844406000b01c141000200c00306080c0c02a01c4c041003144c00c5841d0a41107a00c160031074054880710300752200150581481c2400d4002c81c0f8900554545001d45900e0b17114078480c000c0b1440b0b9074503103a05400300c0f0061b805880151000409480d520714201c0800350003039002004990103e0590010581400c2d02c1c840181c009a4005024003255501d959013100c0c4420036410480b42d40e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 687268965 1250 687267715 687267743
    0x61b0e030d11100f1401290406140c0a0203120a020f011e180c09090b0705070203071e0308040e15060f0304080a110a06060512010b0d0206030709180207120804110d 72
    0x1c2d0f11844c03402461014032024454107c0c0026501030408000708454007401004100071003076020a068800100c0c4444107070700e607011810750300e0400c0d03003d030701c007039490b1240360601c40110274101d00920220101b5000c880b50b480001c4005400e039441000005072468007298140c40c1340307500ea000f0380002e4819040d0080d26486603514812603056582103c5000391395032209804000c82811070540007404c0c0e04145e03040c0f6001d40d002a96800700d5018200090660140000220900024100146a024121940b030b25140c08004814400c100c518124014800034450054100034088501012071541c800c0c5c6140d0740c5481d88450380d48048141d00420080784050b008100c814008883c1180c400d0401040302440d200400c030011301007040c4024264500030f15040f4980e14030001c4050150305440403030300c0340e880800a507812902d035800141c00902100c401080c0c902668000c0c10a01d02c40c8800d22108104034400b11169241107500038900e5260180050031460035100000001f4425500010040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 687270215 1250 687268965 687268991
    0x120906071a1e0105060f1606020c0109080d05011a0403031b020a14010f030605061c0209060a0c120807080708060d050d030f06080d0516061b0e030d11100f 68
    0x404461800d01450300c0d0202410405042c00c2c1c0c0360060000f10348850400c0700020b240f003064441d280c03c40122903058a600350070054690103481c1740f103101e10020090b01c005401c01d64050b07405080c04480c40da03d00340c008211070048084e4240f10450f5218030904160540c5e8080e51064400d4500c005001410048580166150071155002d400010404a0340381900000504191065070441090600b452018401621080300745c0b0f2440c0e1000d921130f010b101c064001a8002c1c0b0400d4507054000f000000c95020068004540944140c40b035070450070880c0c01410215007424056510000254100300400c02c0d20b4400c011250b000071000344803042a0003640da8035132030026558080d1012070388940c1c404509809910420300103044100c007601a0180b00f2600a102d48a8410281d044980707040c1e0020a000e155170100c4204840c40305413083c0d034910070307401401c04955901c0c054800d105034403041c240d0b01e108021040327089400704000e24034003040144e00409402040c0c903a2154030b43d16001302040f8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 687271465 1250 687270215 687270263
    0x170907050a030f05150408160f0f0501060501020d08070f0c140a05010b0f030a0203060103061e060603022a06011a071b03030314011401080414250812090607 69
    0x3103118125015010f12140ba15a051460640544541132900002c001c08140b5030000c1300c00a0410103406a00c5403d41d142002c9480904c2402070480301c03c1030982010007005501140c1504d01c00d800300c0d0806a02040704840e21007045800c5400202544826818a402040d68202280c8a5091403200c2c03152501c3d4a40781141903d0140c07180d0391103c0294800d4200401050341811059018207130003004c07900401d0b641d400610000704500d0740c4d4501d4501d01490240c40180204010606024080d52101d00030080d41200100c7d041c0c00d60341c0244010924804000d4003289020031014011aa01e00107404e02e001c2005454070441050811070b00b070020b410204651070000051840d10100d5080d410020122540d09000107120290078005000105544020750750400003403801101540d00c0b460001952141400d007100d0620400003c0000b4036030561080e58594682c00e41e6030002d0303545881c1c065807121250740e010200030081207040440d0810400610b00c160207954103001c01c4089207604220307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 687272715 1250 687271465 687271469
    0x1806090f18010e060105040503070e1b0403080d2318030c07080a0c050a03051902061204060f0b090c04050f04061508070206100f06030c031104260d170907050a 70
    0x401e002000600040c0c0c541d0542c260400401e03c0d1181c201801d01010a5803604940210307940101500005207805140d078000580e58400d9203d00781d22240d69180c07400c1c3e00c0c2c01000b5000802c906042c00c0b110344020701036440c80010200341d070036601c1d510341c008070490582400e6030f0304159002c00c20103a6903040c01005240c0c01001d401d00205401c688500300410b0359080ba810551144500000402c041000018000a0a41c2c48402d8182c656010310000c1d01c1441188c04c10f00414040100b000180640d0340e2015004641b8901d0500920750240200300d9205002c0740d5266003810140814411401c2c00e0fa5554003405019000207000c13500d500d001c3e8140b411003940700f8009150300f81004041541401030035003040304030308001c030300c18140407070710b140e43c0e038140035400400da49e81c0303100184c451094102c01202489d070f0117150b80e201c1e2a540454901407243c605010b55080d0107110003400c000010705911b481415a030b51441c484500c0258a861010281c004200f80c032500201003025070343d500d08400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 687273965 1250 687272715 687272749
    0xc070b06010228060e010b0307150c050d120b040b0907200a06091202060105030c0d050109241109030304260d020d12090201020a2303071101090b1806090f 68
    0x3840c1411441c150003075176a00c082c280041d0341460f41030540c0e41c03000101070058442a0441c903903c0d8070201d400303c91340755840178082e280d80300c0c10450f010101d4100c58482c040303003a414420301909a2202c14001980c44d90003a003070f00039000030002200140703c0c01e01c09240340201c12014480e01c40002c06945403032011003068070119620f500394006c10000c1e00c00003460b400180040c001e1503241ca00082c3d201c00b0302c0c142942c0507018141008040050a5000c07030b10943d0300c0900400105c007030003510f54007040014411900189088509003000740c0b94030986068440040c01140307070505183c0c850301401d90000c0f2052048821410040e0200c1060280a21526040c0d005101c1c0d8400820024030403c0754001c8448818078040104001d41d0307001c00d04010003508540002c4107880000c81c01c41c1d8003200e030321f00081a808003280d500d04204203045203500e1442e003680c0b61003d140d111540040c0c6ca11400c02c030090901202040582c01c0d040c000e02074101306100a021800c4d090303903a404604d40c4142d10400d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 687275215 1250 687273965 687274033
    0x2010f02210609150105071e051501050111060a1a0603330325120b0402031006180903050918091621051612050d080c070b060102 57
    0x1410340700540d06166100004541842c00c605000d40d81c09222203081040d281000b8001030407500b03001016010042c20315080d00300340c84440703090070500d80301c5840c03c441c01c00004801d0300000781513209180380c9250440090180c8016101e00101c0d50081440502c07120981c0d501904000749a541c03040690701c581c0b05054810807003a0b003240e01003a0288001c06d051384090031030b4002c02e0316407030000764044005010704807511600d240301c00000c0b2013812940a81c0b010002036100104005400d1049400b40d40b00b50221419485009008026a01c42d401441c00c00104014184080c2040c0d4011047c81400f904065180150b20b8000c180f606150503003901c6d1100340d90342071041c4000c040018583d5100d038885052941405d00a040400100807410b00c86490365095102c0140003061108102c101c10b00100349580301d0f521000d462200221078030a440600a65140c982d149001d000840e00c6040300f81000742c030740320243d03682c03400000c4058000c604502c10081a030022640c18030748080304080074800d030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 687276465 1250 687275215 687275257
    0x90e0d0e0d120f12090c03030305180715030e0721060e030307080411090c04060e0f0301020c010b0a0806010b0f03071709010204090c03090206121e04030f080916140102010f02 77
    0x903004c2c4810b00104034203240307060055004a00d0485100050369810b260101c0d00d030b00c5181c0c00307102c007641e180e01700b13520f50040260020350b07018400172074030303461156450a100c14440a00d4044e200c10306031141074141036460029070100100340810300e401c01d00c80c01c170002d0032000301d40d00f0f44c1c599007085032140d02061144041c0700078062610355810301c140c4110f80d0124186044c2c0d031840c0050203580b20300c800380f1218440551450341e9031200c0d841c00340e901400846d150314002035400d02904076400f200e03010f0300d402e00300401d00301000702d50135060340c140126803031401040d4070300203005500041014082013503c40b2a10a40108405c3c12030085480000161f2954107212169049900003100b00061618140c44040140c589100f03503404d10300c0d406102031103541c986080085a8454800c4041089040810482010307000000305050582c682d0f203403e025514a003e40c1d6031030101c4074010360104044c2074104104860543c94621515061002050805800010300c00341d8014441e4002c28215140003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 687277715 1250 687276465 687276467
    0xd0c1803052119030b0a05030f07091b0813020109080d0206190606120f090203060a020309060709050d02090402310b0907140d0623030106090e0d0e0d120f 68
    0x4408110a01080c9851601400f0229140d0500050f240c44003032503101d140c07100443d5207000d02d60b4002d24018041d60b01e000d03003501030a0340308c40c11401141c00c0c840c90714000c2c498601ca5404440d21428850f15940e1103a201d9a4150156410345203049042003904100401da1080038418800102c059400402103400e023226418044c000702e13072510701401c2c502801040119800382842c50b4000000200080b80c1c8402703201e01010b4803804e84041e4142c0b00c2c01c000e100c0c518082d940118407400703003001541c0312a140e1180c103c460040d503100e21503221000029a0015103412414960403920040004480c08c200c070b00072031080c0e4581c038884a00d400030802c480001031494010000c0c0c6143c03c442c0040240340183d00a0460010b41c6130075200443e001c02d69400300e0007640d002d140901030450242c1010f60341e1140d0340c0c42454600c06143d00075401c010340010201c4260080501e041401d10203000c4004040703400720351a001710ba4855070b0215501e910040072400343c01c941e26800c0c00030755408000c1100380300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 687278965 1250 687277715 687277753
    0x60f120311010e0a1e050706091508010617130209011206060f0b0708032a09010f0e0603130519080901020f030301031a0a1d0f12030105060d0c180305 66
    0x2003038841da6410101c903a41c4071800440d0030f00350a0b40c0b103514140c60340c1d040d000201640c44003002c02043c500c0f98640110348181c021240f10101d91011089603035a41700640111881542803141d200403035800036039010b01e034500b4215a580140b02d108a8460b9170b00742c0d000113910782000e80c000e500400d43c081e02d44051024038003825018119004204140624100c40050b4030f1060715800303083d0960120109284030744070b0b2000455000e150303002180d994035128104400342d01c40c1586c140816038221820305094000c4100c202d00070701c01402c590660383c0e80e5400c81070071a807114084655028070360182c014a02c0080c40540c00c0c81c01544040e483c1c3c210760001a02d05030208000f041c50341d109000400000300d840e0400b05c280c8443c003142c0a92603c1d45801d41028007194610791000c54031100075003218480c000f90010600800004a40241c0c5032003c2000c003038802070140e60303084881003042c1c850304c403031036084100612020310340950201001003c00081d0034482d003003100d41760403d00d001d070903d0342480d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 687280215 1250 687278965 687278987
    0xf1101030b0f03031e040806040c05040e0d0c03030f14011d010e0906060607061409060709090603260403021305040b011517060316270c08010b0d060f1203 68
    0x340e00c82021001030000070391380380207450303030310410400801d0082207040c840004c0e1402813034030004441c280d08180c508890400c0381d0b401110300503403600c091044080340020317a01f0a1407040351181e00c05654561401c5000d8174004a010320440c0e20382201010708440084010b00810f1520341d030500c00c0302d114001001c0018107903c404410000ea00a019007908086442908180c084800a07512101031400401500c0f10308600c085403003880080001030320b40800c00718410035040c4c3d503a0700d1321030300c0f44000c4007201c4840c040135020044209040d007034000040720349002e06c100401c42c1810a80e80f44d0005c2c2c0800c002514003408983c03104184010444501e80d05409043c210100c60460802d200d00182200c404041e031075103040c00540410840e440511a940c1c5403001c1403040701081c1e1301c8464111400101c0c0003400c0100741c01c2c00d001c0c0d000032141e1141c010900342c00c1d80c1e902a141d1074810001c01039041041122051544d455000503481d030342580d61b00080c0054401000245410304001c0e01c01181c10b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 687281465 1250 687280215 687280219
    0xc0f2815020f0d09030c181104030b04060b120c060c01110304080703090509040b0423010c02031803070303081b1903050121110d050a020405100302100f020712030c0f1101030b 77
    0x4c1c00305000242d2009100c0c0c054840d441d90010b100c01c00041c008014043d00f044000740d90741c0020300402405810440640301c0d6000f10010300c42002d900d0184500c00c0020b100844250f004400c0d680380c680750900081c40112209000482d224040415601d1158000e44048801c070700001130510401d40c100700e038000280b90442c0e842e2003c0c070b05501ca403054542c0040004040704174031000220b4084104541c141c01050b100000c214991425030040c0d5258032034070306a20b54200c400b142d4805403030300040807010340380e2607a505206600c5249260303085a1241c4004400c081c000e00c20074108030070640015904601980d8085007951401c80034500c9510000000b0f00880f00c0788000380d02282d600441a000c0750b6080e00ca5030300b0b07060542000381c10b203896480001e40c0030382001d05109240c2c0320031107014181e82c0210707124403032000c00150980309180c84c40a0300c80940c01c0b0560030800d11145400450b140790081c01d1050120390a6070343c00c0801810608101e4034514005514001941c0c0b61290002c22181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 687282715 1250 687281465 687281477
    0xe070306080307060e03070c030804080c030a080909060a0806070801141c020108130606080a1118041b05030f07080d030213150c050a060e0c0f2815020f0d 68
    0x4101c4110784a2181082c0600340c0c0361140c0c0c0d60310070240204201c1d03015a40180c203090030280c0322700c1c0c00e82890340a4031032110175120310748040403140740100d420512180c3c02604c0c149410000c0052000246005110f5503001290150014200c4400c0c000b9611910460352920304540c100050703868200d1034030b0f88440c0602e0103c0820348a451401e29506071030b50f0242400d03d0f856450325816688114a5074001380090305094000917091030000352428210b20a013680402c80e281c0e04140709555200010016108145c200440c0c08650482208a50610030400000d06240c0b51070100345441880c00c80c8010943c4a60002c00070100c0600030800d580a06182c154a0003800d4040e0301a904c880c1e000320440c000410401d0440b5900844510f0301255103c0c040d50003484440c103002d001010700000c0038a55001c0d800140025240c440f40481005030014503a603071352100e0310900480e40110188540c03400c9400003011888503010a0307002c83c05d01540d4018100f000c2441070050405103080000b40502038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 687283965 1250 687282715 687282719
    0x20090a0b032b031d0703060902040501060201021e0f0904110c07080c060d0f0e0d05220e0c031e13020a0f0b09240706090605060d0b01060c150507090e070306 69
    0x80c1d00d81641c0b1011454500450b008404603024900d03a100201c50180f14401c004001042003081c0d000b85200b2802107504001e503030303607400b4241c1c01e07031080c0c0c4000007410036251100541c140c80440a0002c1220702c440c56402c1078403100104086074040c00c6021104980841d40507124803080001001a18001025105080e00b034400708003c0c0c005c0e941650425030300c407246900081c166521001c8681c40200840700070000c8694090425401504040750000e000490070030b0881c105171280046410341210038000f541c4503a64481d00b0342000c1d00c10641886041e96803c500c07a8111017250107401000d24108103404a44100640c003041a0703c00310300703015803107810031100d8080302c151100d09006035002d551a101e0344803071a2950913071b2204079003c5a404a00d20303040c0122584840c0c440c0f40705140c100322300d46a0504102c9049a448001000c00f110000103100b91031003001b20030004e900c26070002081000e03d40110041c0c03881120b1182c00541d045004000001102c03007460b410410605080200d14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 687285215 1250 687283965 687284023
    0x40f1d010b060d0209010e030618070f05011202070305070c080616110c10120e0303010906050105120412030f0f091b0e070e06041502010515190320090a0b03 69
    0x202683c0c002d000c08540c0481e82c040564062007007034824045c02800d40d0759501d8821084100b01102c244001c00902c1001c5020035402c14640c0288181c90058488801e0060a0a8150042d602c480d90403000c200c824484800007408000c1c441020f00000e40c09080c8a2400740d020078a0405c014903864100074600030001d14408010549101504080d00e20301c5080c040b60200307440d442c002107103a24019140030b54031601c00707201001071416118102001d2090701d9458004446d0750143c0365049040403424030100d80000c1100d403280c00c0403100f42c14046034109030b0035107010899080d586000714103905c42000070300b0441d0305a90b03c125440c1c041410500141022808010250000c000310180000701d002d070003403a9220003d413402481803074607888080301031210090280c90b00b078642d58644d0340c82036a07078041858049440003041c0c1101006d00003261640e00c49480320b0070821800300c4115050310540320561034494a940c0b1642c0c030707404c01107a4203a502c4141407404017000080440600807a500710b1410b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 687286465 1250 687285215 687285217
    0x90a140c030601090e0c0711010e03030d0b130e0a11040612110d0609030e030c010201051612020906120f0c040b0a05030a0e06070909060e250905040f1d010b06 70
    0x3068039442040d40300c0c1e6a150041c0c5855040d41c00c60b561020566003009480a40705000700b070894030600c9004060481c0038015555200302d42016541501300303000982045c429680800700503540100f0411502180400c400121080c00203c08003a0304003220030710902000030091400e00e0810350f070400c032041c0f810411340407052080600070400e906403003624255a07240340303c0c0070105412441c00c100030302161402805901c2c2da10440d60080c0070369803901c8419801031241c0741c810094004804800502500d0844501d40390343c501c20110303036003070002c203040e501d800300600744600c0a56000001c60401c811003080984000700080100300c01000280182d60340c0d00306482d65030b0b846080c1642c69445080c503160180441d0a205c0440d403017410f08106110364400718141c221600641c040003c107499a0103039206620840b04115400030b01041e640d071180d80c41c5041d884c1c8112501d8101c2c00c3c251641e000a0540b18000c215800c0e1544400401c414180d08041190355078003004000c11070007260102040803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 687287715 1250 687286465 687286471
    0x51506100f0504031b031101020c0108150319032118021309200f0a15050c0708060901091707020904020906030c090c0703080f1e04030e060a0e090a14 66
    0x2000401c82100181078060b4082e03c024540c8080521410090035521001c0c80c1514030058402c81001d0f507005c45a9400498039058800040e503071100720b41d070340d0a034404048e00500b8510b0340502c1a45461030700e40e24000d1a00c520584290789410b150324040060b51414420f00d03030321120305817500840040d800700c1543e03a0322480307a05813281c070b00880740201c2c400002c014494028100c1901944c28013000045003a441d1210311084603103000d075682d144180440e0282501a2105d044404681c0022041c0a08050048010401704507480c00340c540108609003031059070348107840e030344a1b10101c0030081c607032058061a82d0001d00041c200805030300003070b58111003c0c001078012444071000c10710a0b107040c0400b007091032000d03000c2081c42c1402c1c909046954819441a4005490080821008080c041d81c040c000d074421403d402000e0000b2504858841000d44128203001c140e046040e20307501d0f80400f0b0603003ca00c50302d42800d244190814040c1c1060010612600540340080c005501011000f103160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 687288965 1250 687287715 687287717
    0xe06011505030f07110312090120070605041b0603060807050d05100e0304380c060705030601090f032303030702070909060b180108101a010e240705150610 68
    0xc1c080d11102001e032650198017141e1025800300090307200940c60301c0f40405006100c6003008104a1040000c1811580704821808e1103044003000402c004c0354483d088903810074002c02a21507000100440d0b0782200306241d00950103c0d40703c0c00d0802c031400c010b021590040ca41a42e01c0742000d809c0342e907203a4584050b00c014052080d507a00d14694403c6042042d1000391940302c0040900004200701495541c00f0007800b240e2809414441d000010619002da410b80c035142c200404051700c452806607903171341009151034100800e481001403900e034400340980046008140c001031807c215000d440740c4501414035250254420428000d0031070340094442c0c215240c0386d00010f18240c003454100054031941500c51f07400008a800302c00c900c03420134031082c1203880701401c4800100703d0301a6030050744ca19106203041c10311810820a0554020380420100410007048030304ca05844807400718101c1174441d000b200640010540908000d01000342a080d00f404003c0d094981c44c05030001000381d11070881c888 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 687290215 1250 687288965 687288991
    0x1603020616120e0c0a0617010b2d0d0609050906070206040c18140a0605010210060f0302010e03031315020c010c050a030c1505070509040c050a080115020708010905010e0601150503 79
    0xf002c410184103044e120030f401040780c0d11441e5207030350081410840100408501d2002c01c00016090100011504524410001c10203d08408003171820500031600701082c2d2000304000d0600c4242075440b844000c0d11030b03080300141c6410b2501c50580380240081c0048103541c8000c0c00e110110b03002405110480d800c200c0c00d5020b0411304031111001d08031210000d20400030380414400022640e80104003030f00d0742170b0308540d076402640b41e440d000d5402e50702c142c002042040708144055441412903000e07004010b4200d81c980800700c144103c900703e40307610010200f4200540480880c1d418400d29240380780034a0300c0341501748680c454581714110010f0040612642144101c20013080f500d034030442d07864008040000d4034140c40c01a000d81d100308031442c40b5038a03114a20000600076401e0311040030595a4030540b903030920301f000007052140c0c5000782c10b510699a000494541c24000d00b06441d03c1000041054200001d8491510030180c014004c1c1c1000803d607030501030350040030b40e43d001c00089155 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 687291465 1250 687290215 687290231
    0x90b0103021c09111f0e0607020310060f050f03060a0509150112030314070f0f05160f1106030115121404060c140c0c0f0312160302061612 61
    0x1600280701e00e001c000710340e5034031507030b5500d0380e000355032186425501807881d0302c0c2032921410400070706041081e20aaa40d260111180500c28896030060b03061100243c5800c0c03a180f4160006498404107491900d4201d4841101380004043c00c24480c0c02004195040001c1d4140840081e0b1070340001030410144a41d0340d40024851315040010084e500700d085d09540003035840c0d00c450b0050102803a41034001c2030810a802034000c100500c4648210b9040c0c0d41e003184800c418104441100d81c03006038004024007405440000180c03001000034840c0b140b200c4e04111b80091801d902d02d0000c16003082e216501c01d100400501d0751400b101240001c09182c01104110201c59560040c103111a420300b05000c5041000b00b009a50361040700102c05a0702d031002c0c504084041c01c0c0300307403049120858030f5800c411084001403c0c058058203806c40018140d81070300b00d08044405441d000f802d62154241400c90001d424140c040c01882d8104000c4e40c980c9020ba4100d100250070100d03100d0107141c1050b034030200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 687292715 1250 687291465 687291467
    0xe0a1109030c09060f1807110a110d0213020a03020c0c06030601172512140103030e0111150705070c060c0308150f090f010519030210030b120102040e04060c110601090b01 75
    0xf192249100c010309080703036070601b00e20440786041c0840e40c01012616802d4010300003040001d09250041d400075074988c09644c02000d001158103010303401c907007116a4044400c1c0090241c0003030192021070b50b82c0141c480001912030b1f85031071001e2031014040c00e0200148442a6400b42c019451515111200315035a1116415000912114600030984203002c45a24501ca0762042642c02d40d07500101081c00040300b900041e1000e003c0038070009000c40c14081d20000603502074004ea2070120100020b99070710301c0c22a030400182803802c030b4100c070000c2c0300051080308100350390581101070017140c6010104035661b564080d00100001e404d019941c501305107100c51580d00e9240025030900080d100703000608044c20407140300e030000c2c00380302d100b1090b04401c9600d249000c240c0c41d044030b40081c01e2001c0c0f10a154015401410140c620a40080e02004c0c8001c0d59502400100300a2a0311050003042d8a041d003070000403074401410810810107070094500d05208001152030555a05c18000903502c0040d00c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 687293965 1250 687292715 687292729
    0x50d05030c0c0a03030b0a08160306110714070806070f0507020d08160309151106130c050901080703050d140d0e010f0e060f070f050a03090302160e0a1109030c0906 72
    0x104034882d03441150701e0f0b00c0c100742d4503401a0f100800103807541100306464242040d159801000702c14003d400521080012a0a076048842c0b18078190b005949006915191601a1075003904640300c158084042080607040410219520012615140d500c0b0801804010030a2190190280c42070300c05d40400c0c0706014030b91003141c514030754034507a400c000000c0e4a8013400c0030607241704a21302e9110000b031a42400b070080a100b0809060000640034641c0c0351601a003150b0b50312841138620003d01080401c0540301c40603881e000c2c2c8818801400d00c1031540c5000d074a80700c0c2030b080140c10001710082c010203044c002c90980b0020385c3d40314804503030000d0911020303004080311030009034114240026842c807920041540d5004040d580264140340ea62100d0941e070281e01c1c0d00e58a40051002c20118440e2840b03a070050840c10700c6441075a2070110058440c404040080c1c2162007044c1c040c0c0d0902c1808a000d205210010b02007103030450405008400003900c803034601304054080c1c404540018825a1800c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 687295215 1250 687293965 687293977
    0x6032306160f02100e0a1b0602150c040503032a120d051902160c1a1905070f0303050906071110021305060f07031b0510110909090105090c010903050d05030c 69
    0x144c003c209807110008410b0382c94010348800d40e8007045504104181c4595203807508151401d640040805042e00743d1404000d510080584240050a0001181c1c41e5000d20003000710008042040c003004a1b41c9200c0e5115040c00b0205c880c4640c0700c080c60340d0740f207030560098540c801c540c2c901c0054159240c0b10041900b2400c018225000d51000070504c4c40c407008030050b1242c40e4040c003a0300d0003041e142c402000c08060300c0c10185008800c107018219030792842e5039100c140390702d4074500b260a000aa41d188006c41d01f004100303c001c00d48880800070701c503c0401900380d10041c00d28001071240b00c080040340d183c000114085100300c0d00000e02c000d40d041c210050070010000a04100d0381c680c0300014251098000c000200c0001315445080b8078440100401d406049801c100030f80091300902c0351640c000c0608880c0c2c03186144050050f00040c1d035030340050501c1aa40c0703200228051074191102d07410314200c980d1050500c000914280081080010559a844c485081c85a0f483e112407280ca8664042c0c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 687296465 1250 687295215 687295243
    0xf15030105010b0d11120a0c020f070b0318030a0804080d061205031b060709090903120f05010305070803071e050a2109090b010f0305040c0906032306160f02 69
    0x314000080740f02d040c1c001071010784d801d03402c100b03d58004250119010b12404100c56645404c030000f203051003a065020b0b80302e402d0140100e0304908040740c0100e0410855500c01000214040100b040300354501c0002d002460711311001d035107803405034080940303408000392000e0301c05507000c0b412f9499662164040030203401c01700c050010359103e0345000c40e034903072116a4642404030103007803445110034002101e07401660984c07220245141082100c030700905014406404010660130b0b840b400141500c20340004545164000c10f8035811810880c0c03070641d0552100082e540101324450120b00d06044000082ca191003a980645d691800c01600d090031110002c3c00101100c20b0340d5114165203910b40c03019003016103030b00149940d02c860540464802c400c3c624041a9250200d003900340c4250b0201c0e030301c10302c1802100d03406600e40c54400300300c03601ca402c200c1d003180c1306040b06800c24107001c3d070071000d4182d024014005490441c000319121943d108615003440790703c0c4107403103080780280004201e007514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 687297715 1250 687296465 687296471
    0x801081b060903010e1b1206010909080d0e0115080d09030206130b0a18050a06090b09012d02010b0406080a140a0605040b070e030a0302031b0a0804030305030f09010605090f150301 79
    0x84544046d485030003280c0156800007844035200d11900b09131410048210496001c2c000c16032a00002802a04100008031007502040001c88941032041c4102c0d9103002126000160704a00c40f0180d0003681c42e40d8000861950100002c1c00c0060340c0704854005507613050b81c0050301e400c80380e0345049110860340c1180b0b642841c0840c2d00582030780d000d84d00501002c2c1103900700308125555018825005d100b0f004030800124695414071210111300001c00c400e0034185024000b202c800303004c60001c94100118908100c403601da4207036542e41c0c2400740010455084070204590303442c150342c0035a16800d000000f807212655012101305280c090115800940d007110051010f4902880d04070b44035541110b81c500890300b00c0c0640d0301c40d030030005010810700d07605400070f514001c4880e101c015440700300c145038203e521904140c900016950000b400003148a81c85960f100e0900406d41c00074114000d04441603a89001c0c410800c503961090199004a004800758030302e51a0030070614424503200c1001901503007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 687298965 1250 687297715 687297731
    0xc030606120b0c040501020c0d020111070609090e16090c1704080a0f0203090d3302040e0601111207020117090a0308061c021201091b05040c0801081b06090301 70
    0x71018608440640b01c1c600050352030b6680700b40040d40303004a0050340d0060b4060900d160f85400c0454080c2c2071a40141410b621480210744001d1810b0196004080004e1040b0010052030b410350140d00700809004014002c90f41d1242a401d03880350030f40c0301d00e800894482d0403210313081d800b40034408a50403100d5a120b0991030142403401d850b9000700242400582c0701103105400300d03c04130039224821002441c07a43c11501980b1500034003c008040040c0c180307001194500700c024004010b18031043c41e02000b40c0c0300c40c544405c1e1109200022314a60520000c0e0000d030303480c540c000c03442c031000402c002551900c90442c0c0c00100c6100490440703400c3c1c1d1004010070712a000c1d200094400c4007920a6480c542a65102d20600c58502d1079486000c046d242248440001803801e8900e0a507031000c49000081c140085440e44100900b0760303c82c43c0000078810071300b4417003428140a0054181010304000380d06500d4080c6095840c400000c204282c0700c809120308107643e4800b02210812180240240300e800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 687300215 1250 687298965 687298979
    0x21e0703090509060a050603180708011a0406060e030a150b1e03010c18030b04060f1410061d091f06121a0603010510110615131a04090c030606 63
    0x181c18041c15124203028800105940341c211905010340d94090889401d68946204414151440399540e0f0790900400c50003050182091184661720b452402a6140611820044c08111120f580103c000c112840c004202240c40014035000c01a03071000c10200144a040c3c3c3c4080101020301460782d0000d1075140300c4008050448000258440071002004040d0540b80c05683d80000440c00030111144903008102085200c094070368440d014400100703d05103210203040850716808094041081c00c5000d000001c3e6031010841c01500e443d090150b07480d008000c0401c0d0100103031007214400c540e03040000f880348144e4641c1b003074417119004041c07a03043e842d440c001d040d6540b10710381801c81034a09108a030117200407001d541220107001e01480c0c034603400c01060020748404094070600f030010700325503201481010010103204150383c50340480041111360400c6601c05c2c02c80041030084d400c209108a003050341021511100400300c40000382c2c881c40d881d10382200f02c4140d001601c1a031800c10006524 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 687301465 1250 687300215 687300227
    0x121a090420061b010e0d0f032d051e09070909020d1209080c06040f060c021f1e08042a032003010e0706080408030a022502010206130b0a021e0703 64
    0xf840404001d0190001c0c40c1c458030398500d1644882800641c11030107041582e4000e910212111403440070400d6031240401c0c210090385034544440524980c1c94040006080c40b480301c45a440b240d83c0980c1d140f60034641402903656801d400781904036641d410718601155603c0c1882044564407011401d9038001c150005403020803203100d626840d00905200c010300346070940845d402e55004900940c100c5043c04070448a0032110241280c0004145005a05d0f0010045120459640503a65a410101c0d01074148010001c282141401d10400b41c09000001342400007a00c89950212406a41e16110f0f1001c040300302c030180d0001e0602c01e0440d04d12a000d402c41c100000003d0000d40003444030f440c080307000c036580341c44601c0f80200081d4200b010400103420a0000e641000c98028054200650b24040d101d4455a9480c800e0080084041a10465070140210342d4080255000c0380074110030313500e030242200710060000b00540d5001030845402919005a403a10003110f40b540c03600c40c2c43d540340107082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 687302715 1250 687301465 687301507
    0x50c0a0b0402040b010c03080a02030c04120516090207080711150c1c0c1211010605060f03072c010e060d0501060908012703110c10121a09042006 64
    0x43d0703081c000c4401a80d4055820004000d40c1680c4a01540d611390b44501c0c020740000c0d00e0100f20003020080000c45148000210706007a0148018048210004010041c0a5040d5210f410014014000311011640d104143c3d100c21350800011403554142c980012190003441c0c601040c01140494400707860000001d604070b80c0c20190700c0c1d44401c40340203e81500d25082c440c1c0010901c441100d03108128078030601500203031441c81000410007a403034400143c2590030040110b46421004020041e5803688800c5002d1f54601656038003010f00c030b035001080800c1908010890600c801c105041503d0349680e402c641820080c11800c0090303584855004200041354411010a0340c00d2240790781d200b071820400c8404e01034a181c0e14255000e000e940c261103251400403c038056024004034000c254845140c000100f000e10303170b01c0400501410151008656845c00a003281038405038115110f6181c002585800071740104014041500d50350042a502c05d2000021b60002404a040e2600c40185841e01e10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 687303965 1250 687302715 687302719
    0x303051e0c011d0c0d0318181b0f0206010614273f03070c0801020307030c020307020f2101021204200901030602030c0c01111b060403090e07050c0a0b0402 68
    0x3c40c0ca00000483c955903ca2164100e90200e408220b15000038041c1001400c806280c802441803280d0769204440ca25002c1c1800001c029120f030f455a50203003283c2881e035001d02003424006d11340005510020750302d40050050605110902044060024a03001a652100d0f861000c058141c000b419802503030b07c1c03040c603c80b80a0031245820b809922800020007207070b510f80c003030b15282c0000c02080c21031120b500080424124001000f03110045501c422900f00580242400543c0d43d041108004007100c00181e15001150000d20240d8010703903c1450303035007003044111088440c8281034140d40c07a206481020545a03980f0000e0134544e0145050201803242c0e0017210550300b410300c00d1241f4032003011840240381d480702484c001400021441e6000e583c00c0180802c9c12401c1c00c80c110700d02400c6461900034104504400316024041720000c000201507440d00e040a0800d9041555014020790528000d8100d00712140000940b91272081094403110003410b01191220381d224201105030b110140c901764 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 687305215 1250 687303965 687304001
    0x19060912110624030d0e0a06050408100b060f120703150608060d060e1f050a02120115030f090303090210050301060c0807050c030601030507080f010c090303051e0c01 73
    0x1409450040c98007400d0300300403a001d4081a0b8961200c2c0c510002c44503010038164541c0419661075840400071403802010700d4840d0031a0580180070000301c055240c1c460010818104420b1102a2000c03a4500700d031200314402107071400317141001070360034082c4805411401401040c001070182540781114056850364a040011003c100b20f00d9a1420b007a00907000414004000329140b130038000c48001c0c481d8024600044c11301d007004146070821081c00c0d90161201c2c00e00303c104c080f0000c3c500c00c0d00d812002e001401c500e84080700160035220041440780300070050030310055103091402600000e045080860b03007002100200e2902038018407104800380c3c040ea180403800320070280120101da05a500e25101c00070011200d6a41c2c01c1030fa4404002114540030710801d5089948080000c0c9019600c01c00180007954180781204d8504041c039000148141c0c10810840c100c91740001c1035800f525094a4690b5460140c1403085402d400e070300146950302d42c1c2c0010f0300030041c0d0065120108100c2100c4000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 687306465 1250 687305215 687305243
    0x51c0203060f150a031718032413030f050d090611042405040512030f0c0105041509030504180b0d0320060c12042103020a03110a09090e190609 63
    0xf104156801d0700004003031008500001b00010403500250186440403c1c3e40815454450007281c1080441c07030b5811212204090380c003002191280025503c621990030000844100c0d403001000440300503110305c24850001481c003030007003440e0405541260400814080124281c0b03160300340e6409071050381c070103100c840a1007180c007282035403003162103046984440c1050700f0705c4100111000000d000348003510081010700602521207001e000c20a03004800021185070070300b052400309400c1c4880b00c0c1032a180008a0740001c0c0c00806440c1590b0345c1d10030913186505844a40d60040482c0600c151380b01c0c50650045080541c000002d0300d0701c480880f845004030400e4454140c0c0c1d002c007654481074518080c0109100c031b24090780c805900c07601402c0c8008852046000580b610840f800c440340009800048841e1210342600482d0000ba0140d4100e518242d601e0b400100349801a00406018640f188422001080c08215442c0384804c0034400f00000c094902c1d002000b00001a0211a2050b000d020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 687307715 1250 687306465 687306469
    0x307050703180f360b032a0f032a010903050618071509030f050312070e030d0c0503160203010e03040b04180207051f09060501080a0b060415051c0203060f15 69
    0x80a2400c8281ea51540300e5490520490018001180c211909403080010041020101101ca107c54440745644880d07110b07440402e11074052001d02103240207510000081e031503140d030128036503e4840d16500085002008000480300384a0303592003d02148070780814801b648941070700c90019050840b046030020fa98441d01c26803124440c0c256034010032249001000070a5407500b807003107a5846142600d15051600003e81c0c0003035002e41e20b80d0b0010794451001c2e010341c01c041007505106d2030a41043c02c0743c0030203680c0d940d0b40d0344141c1c0810822656200034220840d1425013242c1c441c900a241581d032103c0d180d0410968980040c4100c060500005030403020360900e1f1f2003202c00720742c2c021024102d404541e03002182e10b8094403600c403480c16038508003000824602d100d500d003e05480006054030481500340343c0c26252014140e148900e182088190441c0501a050340440d6404e80e00c98000308601440300000c812480f0010703408d07002c1c07803007003100300d980c24100c4601c14031546800c001c0e00307002201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 687308965 1250 687307715 687307769
    0x50c1801080615030a06030803010e04060b0402090d0f060b060d0209130c09030f0c080d0c0506162c060c0102091c03231303031806140307050703180f 66
    0x4981c1c0d086082c80c080100d5004440b0b0013141d02101d581304c00711300721386d07255140904d0f64400d0340100a080304102c10b004c1080700328000c00701c00d00e20494081d801e0041e01000507085071412030000700842c1e003012540040207450340114140c81401031041c2d454030301c801c03080d402961100e80c9151042c0f140e400000844c28140c0310780c0c40b03d42034550317035100d0a03401d41c0c0d501c00040103440f030300b55041c0c1090000010012020400b040032200300c0c0e41c40d44005140b80c0b070b190340350a00c050100c000c0c40b038450742d500f00d00316400006844c1414080c01c0350000c004407045d5406081d042c1840f1a900142c0001d0b480c0c00084054008215009040e200e412802c42550400d42c56000051801000036601140840b00f04d020b00c0750072038001e00210a150b240100d6412104144031032a4412008030700c0c845021141aa200040b4100070b01c85410302c60680c2d5461041044a80f1005103400280240403403441c0925220b205011034210a1012540c6650344841c0780014100c036038030820031950404524580d6100c0158 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 687310215 1250 687308965 687308971
    0x3090a0f03050a020409020a031b0906360e030f09090711030904020307091d0103060b01140d0e16090207050d051207080603030919051003020f0d0b13050c180108 71
    0x7000750040007103541c01c020141455240c20b0b64003000c00321001c00406c01c01ca4156025801c0ac142d0015100e10302022036041c0c440390360001003140e207004010320030354841c0d181000005040309140100102c3c1040c080c0002d0409100200c0103200c0030402014080b070950040007001d40880c0d0010040e92024811200c1c01300b506002c8070250002d0100544605203600170f150440e24030300b40700507120340700c194400c20f800d000e2601d4503245055100400c10301c89140b088116030b80e800c2c6000c944807030701e40000204a1240501d426050b560b2070b11107501a500c04c3c0301d0714504609441c03440201940c0c1e200b082010b90410744065555025030034101c40d2a48c010001c035044d2102085008070780380d035050010f440449000740041d4150004010b1000c8681c0e035102200340800803010080c00060a25040c400c450110040b1041130510400044070401440e0081d244450400040460102444004600107081e4150030701c490703c1c01c005c2400303061a03945c405009104000c00d08a221031010800466240c0000d07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 687311465 1250 687310215 687310223
    0xe01180317061f0c0204270f080d09030f142a070b1908150108010e131704090f0605090105060705030f030f180714010f0e1203090a0f03 60
    0x19820700348a00c400701c1510741e40550010094031554009043c26115030038020039810000e8800c070f2070001185410320900c101c0300c14980448034a240ea128219420300c0d0340400242184811081d904208002d250848240b43c15815003800383c01518039014016043d540d9103c0d002c00c0201581c441d00c01c07070f001c081c3c07038101c0d0180c501e034440c1034071750000c0601c0c0c075520401d10086800386002c0410f16a00e41c00003084516400e00313148055218041005000e0840a07002e9011a407411000c880e41c0da0b404012581550200741110940341c585c0381c03454109054854008103031844040030b0904a0315014060000ca6489210600c50303030522504110407070320386000381940b140da20340040c45142002c4000c3c007081c52060701102d14050303190403084419081290340d845040410b804004580c3c031f5580340400c02d03000712b400400c002e42c00c080e0a8603030042c442182c0c40c1040002040402c070188201c00f00500e07003030054031040c102d080d42c11105489034000000140a00041e1741c002441e542110700f00800c4a803c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 687312715 1250 687311465 687311477
    0x5070b1503061f032a0b2812110c07210318080709060e0109090512030c0412080702011e0219240e06010b07110913020604060207030203060a050f04030f0201110d0e011803 75
    0x51f0745078103088100110f1000400c0600c007003500080c0941d1090540700e4041803841502d40f40c52081c01458000c42e500440c00c0c0091800d81e0202e1604100308408260f07070b0606105d4625181c901401503800c1c0181d00c281401d200c1d40d40002040200c65101405444100c0c0c007002c01680c0398002c000c15103800340e50080c5541d02100d0308a6009400802450f00006c0a11140b0310b843ea4482203011101807140040c0c80000000400b201103607000411307050150503120402e440c0740b400c4440652561500c401d08640510001c1c240ca0401103410001003d80d81090058000588042602d800501e9101448030582c07140d84008501d206c1c0b9001a91503480d40b0405482d81100e040080c0401c0680203002201440504201d860059540001a00142005a000708000e52039801058600040503044c500c2e030b03619240a02083d1040440da00d0b612a415040082007000c1c809000c034010f01c204a88a000000c004c6086050b00c0c1207038120700d941e0740d0f100009000004049500351070300b0742c0c00c52008000c41c1e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 687313965 1250 687312715 687312757
    0x1c08131205031c060f090e060a050633070b040302160f18020405030f0a0506060607110409050c0306010909020a1706071d040c05070b1503061f032a0b 66
    0x12081c2c010604142c000fa41c00704040d40d443d01448102c1850f5000131440a8682d902245d40c0b2804006541d4807080442d0b05106604085010454590088003000c49112402c900c040e00b40b42c8004042070b4038201c40341d2844d0388148900305102c100900782c03001c40050240d03040c41006040b6140c4050180c0348421031180540b85406009a4244044011520496001d000009907980c013400908108030515015000f90547c501c0c00038148880244501c0c400c13042408500c010812140c841d681a410560340041c62900b1400c04a2402407401c1e0003640c5440341c0c0c800850040300642024001c144259000590f2036110802c40104000c10b09c144082a484400020f681510800c2015104100d03100225900070058000c54141c80403102160040b0b100010101d0401001c41011a8007903104212405a0340401000944503200130f80404010700f03c049e18031007080c1514075418015030340f200c028020884110305045a000b80a541c0111603403c0f02c0380001e40100480485941c0300e44104004c038401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 687315215 1250 687313965 687313987
    0x506160816030908040305240705040308090d02041d0d020a0203030702040b13020304030e0a060e0f04111201080a05060f10060f090308030f0603010f060515091c0813120503 76
    0x7219044148205070f200c4180902040d40308004201450244010300020700720b0552518800161104040c0c140c529401003014507903008041d00c1c00e5a6120410f2a03a80038948005450b81c07038040d034080d41c401c1c50182250389a06228400c40410b070020f0080d100b0305020f06000740d0311902c5a6001a40540040141c0c2e40186800c0c2e205980746070008046010414006150404980049500328086040360040b0010f03031a040b28000003d09191908150704041d50012a03501846014244e004541340e0aa03014015050020346410106078131044c0c150390307506e15003d60784100c40d8109850500910001c503c6420001044030720503ca16485020b640b441c005041321541407180c3e181082007202100440080c41440055000d0710303444041c15124100b0341c0406084880c1a0742c647e810924080080000f40c4502201c01d40c0c81608500355611094010041400180061902e10340f00101d01661820458600040e1010048001481902c5903d540941d200a030012401500a900030b100082000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 687316465 1250 687315215 687315241
    0x30c06050601020319080402011704020310050720100b0f03060103030c081c09030207050915010323070503100801020304080d090204062301081014060d0e070b0705061608 75
    0x11071010720450b403a011a480d400d41040b2000c0e880f910001e00c8800a01c0255a488040c41d211041c42200c0b8110608240c2c0c0040c0c0d0700c0c00301f50680b41103e40c413400080c0c011130254403442c12480040c0e000d0300d0000d00c11002c50761244014a00808540c0c50815030907c40e060410304020510000ba0091003182d0860b03e003990701c2d400d104011580c0813400c20202005011580185110440808010403811075614010b0705001050b008607026000359800c00c150203140003844501060203080005038840510300d95800240c3c0c160b002c038082d4407450180b0040a9001c001588150036089200ca4460317140d00da51801d034441a20042c090500a01441c020940c59501038040644000d00c00039640d030b900c5914402c0d11021a8091b20120f200c04100c174081d503000b102d0168060040b074400103a59040c2241c510024042d081d48034001c02020580414980013a449444c60000510460721100e55030b0110b1203aa41c40400f00311100d000d10000b0401080c003400702d8101600258490b200c240e45c84648400030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 687317715 1250 687316465 687316471
    0x71d03070f1e0b040f05010516060204090c080702012a020f0d110607020304050306010504110c060a1a010e090f070210050c030103120507020d02060c0a1406040b0f010e0a110903030a0906120207030c0605 89
    0x14270a1458010002852480100000c0501510101d0f42d01605132016001940040c02202564100144100078100701140725040ba100c4070031811011310740002c203c0c6000e02c004042c0703a480c800d40700c1c0e29156642205048000ca20030104032500e42d5114001280c50b4000d6110303540d00755114400500803854290407135031106104444290410741c01d003000c54a004025036400000d0356480a0200c4039031480c901c50184c200c000e00302115030011110100b803803043d004000034100c00c5010046145607100b40000340811201070414840da040250080a035503100b1310040390340081501c01148103a004809443c60035400500c0300d04815516024480280d0010b20034032110302442e000c1c50000340071002c2091990641da4001e1600d45014a40702144410140201511548090041100f86040305490703600c100052008251010500c800c05c60078016009039550500011604100790360b44540c0304800c17100c07140e890820300185440420102d01c80d20001034000342e00c0e1060400424656000300790 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 687318965 1250 687317715 687317737
    0x6010b04151b1506050307120b0105040b04020c0a111816031a0a0303030f0b0a0f060507051e03090a17031b2404050d020105071d03070f1e0b040f050105 67
    0x100101083d5181d1808a0514036281c40f0507070345110501176800e081000300043d1141c44140c0310b024650782c46107100319038144102e91080307880c4c0c0c4400e000ca40310780d01510380c8441802d040300ca0f250141d14003856246d042090981c0a208180485202c1c02c004030803290280da04a07070950040403100d14100c001d0459031452041d8540c20f1000160f00340c40703403500741c4003c1d1700a60f80010144a0502078070140c40c109080d040c81501c072200d06000061420b1741080817a81281400390303480383d0900c0c0c01c074104030b850301d0561541450080143c41810703010000300f00501040b07071061507940c0c43c1c80340d86400c49032004104065500a1010b010a810590201501289001e040303c200d900c40e100c101c80c201c403a0700c050a010586031400d00041204c2003022040e404510300090005140520300144038110000c1d8181c0030b14101d0b01843c003152400e001c060007800b0a2540e101c503682d141c0f4094202042c41c80748840e800040700300c000400000c0041981d0548080c40c1302c40d40d010f407500c0d00444d120303000300400513 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 687320215 1250 687318965 687319007
    0x3070c0212030f0406081302090115031e06050102150f060f0409140106060216060503072f011d011a0105030903130909110f1807120905070806010b0415 67
    0x205075810104081c00031101001c01c0c031583c0d40d041540051051002a00d4042e0030080d1101040040e522001c00d41c0c103440614040ca42140101d1604502411280f0f0b0742c004900c4240f01c01580e14440386c2c00040035298280c00300c2e10442c1d0844240081000c0490300e088042ca0310b14007080c41843d00b240c482404a200400101780401b0725180d41d2441c061070203510340c543c3c1d5900000c0022503010b00102d5200c2220580c40c140042c81c10b003010b4035a100c01841081041028080c8518482520b11070a000d4000b0350a0a4100040d50a085008143c071020300456100540c03076031045088140500d5003544100012031140e160380600650b400e41014210030008c1c08203022480700c411100070800005c1c4000440850010b8a130308291500260844100d4000d25040b0003624841d180d110712510b034000d4502012445c0e5175010380c220f0300d128805c0a07405009003003068078403c0c4040059180181d542010075260b0607683d13100c4804682c0700301c2c402c00c0001c45a072040360400500802e104103003095024001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 687321465 1250 687320215 687320239
    0x703200f04020307050714060906011a04050d0609080703080709090e030712030902180a050c09010e0d03030f0c0507060b0f011209030212040308030f01050307050f060c0a0803130b070305070503070c02 88
    0x3101143c0070645042d14541d00a00800c0009e001c1040103a0051107403450741c0c0c0350408852481c420604c039070b004150241818040c90010001c00f90b021006e0203030800700c1a601c0300400c2c0740080c8114070584503280040c124450214004960b40300b001d05203a00000110318003941540c402400c1d0b20b01c240c643c07040c1a0780350251809a00c2c0c1101081d04440002c1304d142c4549004000d0b4801c80e0300103062044c20050500c0850003903600040c01f0f00c842c010071240300303110300c01518080b8040c1c1700e01c101004070b00d0f041c10040e4600319003220140c595680320b0747c010300415001071b05010b41441c22180160000f02000b20000307074135606910090840c0c2c041d105481c50b0349102c0c00c0c2c50419074810340c82214103050000030081c000d10080000d44c0908421406011800d18140009601035200c204c5288203050000c3c0705410407100f080200e03622036012401d07540700c0c035082c0856020622111015503802640100141616100c0d1103540e1244150381c490f03c0c116184d151003180d8a0341400004c036000800a211 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 687322715 1250 687321465 687321473
    0xe04080c01050f0f071d010507050a150905010e06040c0e18070e180d08070302130f27020403031d03010b041e0c0203070503071416080703200f040203070507 69
    0x301d520404109680c080f084c1000707454a0040480203018500f004140c1e12076104010242165440c02c3e0400d1800d580c8031052810720030b05004116100030300c80101d40c01264210440ca810029041d0300a0b0000c20030b00c00100c00385034036003030200c5005001c01e40ca104103004d9505603c0380c154100b24078464403801c0c44000000135140c06c40640050810150f081c0400460020100102c0004401d15024205909000101801c103442c0500120300381500810840c140c0100110441c0082000c48a01031202d56114000320322000c04240344070340c0c21038440d103040c0100203d000b00c400b00c0754150b50f0024070900030074850107a0b9024174000355140d501c032120f0b00d40c01d03030341c0d4081c1d4815100461150021022503140b00c004a13600c180300d5170b0640d0024845d0b40c0228070040140e0b0001900407800c412807100113850070381400040040c51070111072106020403003120000d6000183d900c1182c40e071400711a0081e80c40050750045079410b91082c01000848120704044d0040e54009409003000d9050000b00c2c3e031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 687323965 1250 687322715 687322721
    0x1141803040b12010302131404081b060f100f0b030412120f0e01050106170c03040309080601080d0e0105252d1707020a1a0d0c050d0506030d090e04080c01 68
    0x1404583c0d10410300140158500380804000c0c12641610401004040f80b10301e840c800c40050002e0300e04032001c54903000201035130040504030901c03081502c2580c5844001d08401d80d6040c1d60b0b805092200301008945a841004202c1c00d990180392114255603440d50360000d00684001c000c0c0170024100c009403152038050083d80c0e00f041e01c0100204011714200c6c02d15085a505038404020401d0407080c0c0c2c16850880e01d03805801c0440e040d81c05640e540d41d401e00382d4403280c2541c000c80e0b071807040c54000600e86c00003040001283c000d80e5280e80503100d1220046a483c024101c8400100004130311307543c403d02e04802d01c3c041c1e1a103c1c980001c5085140142d801440d02100711480c603a00c40500c0c0762003042155558544400e0611294505200302600071420140850080c119800c010402040c40d14442c01c0c203550301e00c0315010f03090040e00380d41000285160070441d0400421420200030440034600428100a040c4185d41d65594171803400d036072001025000b03007040d51818030801902203903c800780 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 687325215 1250 687323965 687323977
    0xb031e180f0705010c061d0a030507050705041104060c140d050a02070f030f1b0506071208161e030b03031219020708040905070e09090c0f0301141803040b 68
    0xd605000c0c0500c929180707007866000d640199203504200c60500c51070380c101c000c4000d03a40d0840c50001e582c000d0f61000c901ea81c030041d039801c41140f049100751810160b002000b40741c00f078402d90a859156a0300c0b01404141d0b050100c1a4000807003d00c030500440d889003240c010028002c98900030b4410f8050411b6080144a01203800091000507054210503010011b00c030050405400000c202c61560305c0d072048413014240d008290740b008903840c884500720102e00d00007602d4024041d940d10150342c0340c0703408125814000e54001c40e06000004080c3c100c40507440703007a40e0242d121840c41c0100d10141545d40200c1203582da05260740d407040400302d03850800180c00c11000c503401d50704076070601c2c00001e8200c20805180608a80c01008503030009044002514102c40781c1010104240d211450260340124001e06010b42082002c07040200030788001030004c1101c1011b40390410061074113024507081e16407000c00410b05400c0d14011850800a003d001040ca080000a49040035101c0b2800d40c82a4010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 687326465 1250 687325215 687325231
    0x50304060507031517070605040f0603090c080102040b0702040b1c12021f020703030509190b060d060e0109020a05010f021e03130e011e08060f0a020d0f052203090b031e 74
    0x40300714010420406c0000c00003400980c01e01c81c0c14a031070000481c807a4030450040000701500c0d8407110041010032002e40c0054010403000750348841c0c561014546a400949084c0c0c4a1409c021400c0140e0400c0040c442c10404044159081d06015407106600880b43d46001d0003140325403c00e141022201c4214034090300c451800140e614079030380c1002026580c0141140c403542d002600340c03203c0803c43c4034003040001d44c40035201105694050000d80c106580d9800500600e00300440311240c25410b5000c07030b01c083c3c030072030300312100315110b40045604c01d00b50700210002d41d00c10102e005d810051000d00049400042082380c2c0707008500803c500100b05154050030003a008900180b1605050410081e21440c402c08c0c60801c1510b400760b80e5903107040c0541a001c51060500c0070814006140d01265001032940307005002d00744c2100e680000814003142c00160340b45900103205002810035012008803609962040700b00f5080007000704055101801001c5084910003140f0b0840f000c60b0380e05449403000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 687327715 1250 687326465 687326489
    0x9030806030d020f0a141005011d0c04051309020609150705060105030c010c03030b030c041503021302030417180a060c020906040c08130f08071101120209010503040605070315 77
    0x22140c20315280ca1414090707071096400c050981d00c050580040d00b00c2e1001c0e0000304018403c20315806017070602042050302c1c0c0201e42400000b042c4a20002d800300115000ba03410317802103035070f11820074802c0d006901030035500006004601d030040c4c0722a0802c1c0070150000304207502d070000c441300140c0d03210b148070f05545400001089000500a060020f58010803040c0c0c068402c000c0c0c1c6070002003640c203c410004040c10340d50100c886460301c0070090b000d00000b02500802c441c242040f6001c20343c904500c01240724542c8000501520b003880c0c0260f90169512100c010505d0300e03908840d4401e80c2144413104107942041512680c13680c0d074504440020401c1d40c507001d03081343c4036005101d0b10001c0144000e0043d0700b8900100101c940c400c1d10342c4d5101c00054490740c40d0601c02c0c503040f140001c50301005421606c001c02c600c000d01803120b0a014040e2400d0300c0b4450001c0a8412400c05c0e0700489c80c0c11400300d003041c0002030218240e40c00c03507688025140b900203a540070440c0481c060304100c0d00f140c3c2c0c9540c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 687328965 1250 687327715 687327721
    0x306131803181d04060c170403110f0109051005071202370804020f0105042309010611030307200a060c02010b0d1713171605040c0e010315050301090308 67
    0x140400941c00589003440495403c0d51081c000e55403248030180008000030f540d290f400907901d11804030000c40c3c690202081d109402d050400900a00d40e50300c500b04075018200c1c110365070000500c00c4882c203070b6104000e0011000100d041da002000c0050806060003502050011001c1081c40101900b54880e581110089003c40030b01d8031755404589042035180b2307503031161503089400c4a03000f54425411508a04038081c1c00004aa0781d0045602401516418412260920303011103514144154241c554002c180e99650302150610302c48501e2070300c1030700f081001c520140d100b4180c020201d070724080b0845526001a6aa9103040e800000903565680d5815885121a60a00507660448801c80380102c420a0945038280c4500c030070f080300390403407100161440360311a030b10b1300304001000440c2d0480000c100440250ba11607940c0c2402c3d100100d0005000702d418135151040b114070400b1a920021080340031001980140030010303144840040c81e010008059030240218010130b8880e91f00c3d406242 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 687330215 1250 687328965 687328997
    0xe16121b0927081c020405060d0e19240b06160c05300c090412121a011101060512030409060b040602030901050a17040c0612110306131803 61
    0x40408030079020800070b8207000104803001c09940c3c070800c0703207440e4440241c82812203000030304c1150700aa4100780d000c1a0810701295503401510042c6041007034808015142d0391340c150f444802200104038001d50301c61400d4204003032031022080c1d404171a000071003040380c4000440641001c01e404150001c541c0c6100e04009429807068001c001c155100c0d000b100b0940420100301840d140642090701e00c00301c9a485419081224100111000e800a440303410641000c00c000900b6928003c0807564550034019211070901c01d00709946000e41c241c80700007030300000448035010f411800310700547d21907002140903510300d03921616402500c001176a4a0b49046013110586210340d1001000c5103040c88204019a000302c101c40039850f092900f0340da94000d840040d510340043c03900c448041c101c0827041004003d6500403070740c2950343c86c1d2a280354200071055150180c1d028006090f01488061011602c0c90901c1a0541c0c14000c0b01c0a01241080718110044501030300e002c810703400a9204500f882c111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 687331465 1250 687330215 687330251
    0x30109050910091e0305120112022e110f070b19020a0503070206160506011512050601020d210509010c0f02030c030301030213020403081c0e16121b09 66
    0x3500315584103000d503a40076200d4500c20f19041c8800c0000f100b0f44d07450310040500c62400c41d83c009140c1c08a00c00c00d1351b107540d600029803071040303022405801a02803104041b003c400c00c0c290070180d005c255140d0b810790010304a0ba042100e92050289106960f0308075042c01041c0400340190995584194071920009460a684030b4122400402d5401140408010034004000c940c3d0003501a621641c1c0c54000d81200c01c2e2072070030b030040600307030707020754000480e04d040354001e43c490900444d6244402c40c51881c0c4800300f103e8041e103400340568020302502004071301440d40381c0b11101c044d06081301c0180000780d02d202510300480f101d2440da5034800110900940088140082a150348000c5043c85440c069450ba00d200601029100d040000f0710003090703050b9901102e0142d6480411039460300a0101c038110740f4542c409900c401c040c20001001c0c01d05070000b401050001c801c506000a272841e01c4807100c00240001401c0c0e03007907034486400650f402a04d250382c0c0010f10307480800103508842e060b140494 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 687332715 1250 687331465 687331483
    0x110403060e061515040e06190e0106030606050405130b1507060902120105071715040c0806042714010f0e070e0f060a06260114090a02040621060b0301090509 69
    0x215000c0d003d4154450480c1c9030a0350140d0750a003070307502c00a403940d20008240c0c42c3c891810380311005902002280b0f8274070240b54641252981c2d107050007101c0d00c641007034810307000e64003032103400c0b160440c1c00105046840d00005800301c009425800c0c05138128400310f07519400701509413400c0e5268400c280031810250109a50b040000000300510304113458018288443c102084192100207800310742070262102c07018020080040c02000108030390103018013100ca0840740c1e203202e01d142c01c00941c0ca400201040a05403140203c02d00c48042c0703155501c3c104000c01843c02c82c110342d6070700040c00212920388182038101c5207000040a0841c9010000444884018500e54a091b410810f1200c1601c6680d101c20079102103080c10702303451aa10710040602d1070020210384042e07514000025400c5c00f4004002c0f034000040d120360280756904523424040e0f01c01ca12070300d00060125416140f071651000c60850501088520114115940302140745450f0402e0b001628566900c005010651008000c0404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 687333965 1250 687332715 687332719
    0x613020a140f0a090902131703090d0c09180323040914010510180b030612010606030507110606030d050c0a06110a0905090610030f0e0f010b0102011401030f06110403060e0615 77
    0x41f8020b210b03810b511003031045104500018000c00c0d0949101c08041c0306840c00e08a010b8110001060301c2d00b045498840688a0307182d00300c2c508420328050030b0441c02c0c0800243c3d0103071075000b11401c00030180e000520301c0c9410100100030a01000c00c1136036082c007440003a81c8280d000111254103100c10414100d101c1d4148205115a60003103841c01e550036aa40c1e0122854109255102d41d203550200b4601c2c840d82150300120b518221010800a41680c05030b805003120795140c80940c10203140f41680d5200944001c0d5040c1c0c8000003800c43c0510601c01488003000c84405d90348200001c1d601c0000781c820000d0405216000032421a4415a120030303c10010030044606d03803a14201100881d54140107204018200b40d269445075072010303a00c0d0010742001cac01d8481141c2031141c0e658495402882c060025a0040d401c12000c0703542804002d501c18162a0084402884007080b50743d10402010f003003001d55413003013041c0000004070b1158450548803000c11000ba05c0c9600e46641c6900d0410b006201c0c0074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 687335215 1250 687333965 687333967
    0x2030a06230d3002070b0c03040b0304081b0304060815011209020f030703152a180e131406190f0b06031303090e0613020a140f0a090902 60
    0x30a9400c403401c5110400740041d07078a42d1030318540341425442c421021148900144603500c0c94850b408508071941a080b9842d800c0c0d4941c0303501c4410b18403040c07040284e203062a41c001d0005200101c08a401950440d224078001490301d030030100300780c07225200c242d501019a003000c10100421134111035540d0b4044082c000c840748104107440040c01c0ea00e01c0003188040a5555841c200c21034640d408840d100b060f0044c129132845030361780303417280c0888007580100090780c0c1820008818030f0320200f000c103041004c5c0c030803480c0c440040c1c00c403c1742c02006202c900100700412000004140b002440030310701481c0c181c0c415201e6112182041580c3d840f1380d920700c80a65100380100000c420601078a410804c47c0014003013034070b02c455461440641400c140c2b0641c410030001c240101c030001d0707444000b407442c0700751180c00c1c040d88d0b100720f0550704a5080342e0058100c10b10041002100b800c0368000c0000540c9801c00000c0f0102d091a8500743d07802c006c0320260402c40003c1e44841541d0001030400040c000c00e0f41c25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 687336465 1250 687335215 687335249
    0x1505030a08031503011506030510051c1a010608010e041a070503041131020415020f0607020f0304120312050a020c1015050402130911040509090a020109060806030c1302030a06 77
    0x8201b0110f01c80c5100305607440002c2082040721b442c2010003040001c0520400194500502c0310700030704c4210403a108111028480c540c0303603c0d081854101d9245440b2203c4507131800700c803094000001041250748070b80003844018070139070290303056000705140e90384d0341d45919003882e244640d01030210949200f4606a030b456200e45842c4c48140000b1032004188103280d01d070500e1000041d005582213403804040ca4503403031500c1680003d00c05200c0722510121001512192000d0303840300f509080c02e88044e0030800c001c0c440703602080402a010382c40b81c5400000c1200007031852003182e5041c1c130b841c001540c0004000210540400c52604412510242004070000300303015148641071920602e4082d075004100350a942c1b0391424840000d1a52300818401041100311040017a409400380c2480b8040f4072001c200d1103400060082c403c83d41c1a104e6100c03041c1802016907188500a000c540d1602c116820495030383c4900d180320f041201d1030b0030090b0b00c900300f0a50250940e070380d581040010243c03075100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 687337715 1250 687336465 687336491
    0x10030c09200a02010e07080c1f050313020f0910030605150a031b0f090905010c0801120f2303070611130b032a120c030c0403061505030a0803150301 65
    0x16440341e00881c0c000d040d55444001105030301401c5030301062402402454800140c1010114002c0f000941c1118041c50040d0558500c03450650310700e40c0c84000071402e000142800d030395035000103102d6000802000104856200103014485e00711180307044c0806141c010410841a0700400f41c00150a05628694464542c045039012095200151059031a40074510101c2510000e410242041e0604044516214030100c400303020569001c4603150700c2c180b03402c4032480c814200345050300c0d0b0b10117050a91510680752281800f25024003510104070005005120819188014a05107100030103141c0303600701d90a0100480d03849442c0a841240100000c101100c9401d14200c01e40d903240c0240c580743d0b1070351507049404490710a29506414500341407608090103080180c20019003203520f00f603c55031a261007ea2501041d101c3c080c1d480b0003032000b4000540650000c3d14603440c5201c5950405540b06d001030316023022044155403404001050206c00b503c401c003640320000d010340003032042142c0450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 687338965 1250 687337715 687337751
    0x2010204080c010c021206160912030804060f0b030105090d1107050907050f1909050f0a030809041d03280c150b0112060906150c0804030b07140310030c09 68
    0x104283c10001900c680108554621810804951010b01210101c0ca00307001840340c20f2070f040c138400b40402c644440c00074001c00c1070340e44940413990541d80c2c004181c440e9500d20740903201050a22441a458a049080c2c0385c609214042c42044202c0007456146541700c0040c1199810b03400f517841c5500300c84410f1001c0e80351400541e400011500c1c2c9030f5980c0d1160b10340180c070390194110100659006044065405170f01c030003000c080d02c0080785c5510341c07102c0340d10410101170780314840101210360070300299609107080d900080c8141ca0007894050550420711802d400c0d80d00c2244503080b20f50f06040c00d01080a80594141c0412150781001c100c4141c06840f8400021040e503103417103060f501e84500071303000e074410241000c41845da0b103c10700c03000307445650840160804d40228080704d10f00d0840310908520410b050700b2a80d41003000c403841c246c00c43c2c6814903920340051050041c040c2c2400708052036200c22005600c1052042d20b00000705081d480c0c450844117982c4e1100024038100304001041400b000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 687340215 1250 687338965 687338983
    0x60912060227131112130c0b03010512030c100209011214040b160e131b0807020607051303110402121e130305090f0a0807080c091e040803070509090103051c0201020408 74
    0x1903911844c0d603480304071086e616012401c005080184004000491034444006035041ea45e04540100c080a003804001d6030b24061520205407561188a00b441041c41d640d0081210380c0040c98107048a0181d5070000c002d40300030880481111080348200420b018600d607141d600a101c4195148246001000090442420700030480c4120760700c100140701031a043c0d0240c0700500d5104408095018034500c09081118221108400741c0a180005503000d440313079003201c2a1100015440e4241d90454407070f403e015020155107500980d08000b612092400b24981510545002181c100c2010070b489040079408000741c034900061030301d410702200082c0c000058456007501a581040400045400039000f040541d0202c3c00d41c0c040c8903008104218040743e006840b280035070708600c19807034201c91411443d4600012100d12400100803e000940c1400150b03003015152800d681004203d00010b959180c0a174002c40e000d500c207007004442e121a0310112124a01140001c60409241c03140a40c0c60f01c2e040303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 687341465 1250 687340215 687340237
    0x300b04090506070e031507050c07050f03031204060f0e0d0f08060108011203090b1651111c09051c02031b06010f08070609120602271311 60
    0x10040350b04d43d86041019142c0d18042007941c218a040001c80900355502c1071390b03212070a0054142c089903a003001084000c2460000c3d00552a00007100c0009403d2040608212182501e40d8499900454940510510095410050030348480018000ba1441a1404c02c0a00707014102c001c0100303580c0c0000c0680c0c11110b08201001c0c401403d8a070071036013040c141d005034000c0301003c180c3c100321200d594400c420300303441820030031a01e00403002d05845a0f501c0025882034402c01800120b1024402e44049100382d030404109050b0701900c83c03942094400c02e07820112002d5000c11403152506000b400c01154030900b985c01c02103a00a91141601e84000361100401d82e14485400d43d0010300c01c00803122181c040c0801000c082849106140d10740e1000e2241c0f0060601d00c00d00810001c0c4089009011a080c94541015042c5040c5080600740d61a403016508240c3c00d01103201d13000d240302d90003908094400050000c0701140010030110380403069020085526100040c6044d1525000f20707500d007184 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 687342715 1250 687341465 687341477
    0x7060305010509150105071a06120c10050a09080307050d12150b03130804080313170606040c140304150e150c07020d0c0305030717090d020f01300b0409050607 70
    0xb07054010ba469100d804001421a1618040f445405000c0d241081c007940703040b2143d0190744070ac44545c603074800c03920380303241e40c0310b8030060b866180700d03000320000c2182002909000302c14942c1c418a8a08503000074005640b580c01420f440c1c1c100c6030780b060f00880c40d0f000040c1d041160300c1e034861007031318200500d0190f145030020001c04610076001e8405000d070300303d27401114503584070f495481c0552660044400c01140400041010402407420032a4424085c4c14500070085036803000100405495500d20390005e000401e180302d0520102c0c0c800443c41a80034000c1a110f800070781c6200b40031551139150601c2250004070800d03080c051003005494003c2e5071030b03404c20b4071510350b800001c1c002d6883c900b000705541c0443c0c00000420001001a0130141d02400b61500c00016813200120a48100840e05c1d170701510460420700185401e907001d50b500705042c0b601d111504901040303a181c04d901028031140700e40c4011400750341d0f40755030700504800f80c5054800740b103a40d00c0b903901c0c1503031840e0281030307a4180302d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 687343965 1250 687342715 687342751
    0x5061902190504050906040c05030a050a0204170616050301080703030e060c0a0c060e0402120703090f020405011d060d030f200703080301060e04060f06030b0d02090103110307060305010509 83
    0x44250165245515110301e554000109404054650350207031107624003800401c000141e151609204004d8401c0d05a12164a19070703980e40c41000401008021040d410750a02020519070b5060f0380020010324540001c0c0b0741e0f030810100c81d50b046003420381000300b00003040006120448004c43e0800c202c0740e242c104a4480841040052080e0154240c80358941c42040e0840c418800c1ca01180c50803030ba4103440c0d0600c494685802e03c000d0744590b1000c8040c104041000c90711161099014145660080108524801c402c1d400a412f4600a81c0305031540484501080c40d50452000143d8100504445c0c0c9170400782c035039901030411003403482460180060590850f280041b411071031320540d9020360940c1c003c00c0d141d103000746141c1c0003801640005100f145103400340c0d040510502042c0c2f0f14001410030064a00101280901002ca001c103400091f190400d07001078803601c0b500c901031449800c00d4102c9030a01020305181113501e600c48001c041c2080c00411058a510000c241c002405003064204c280d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 687345215 1250 687343965 687344011
    0x9010c03020a0203030a02030a17160e0d0b15030c090f0609101a04091a0102151f0305010605040b0303070c0b0706091203200702010923060f03041e0506 67
    0x10602c01d002035090b001c0040c882ca0216400b1009002088a076252200841c0e400301c03d4041019048610f1101d600144903401c420f1401a21505a6204010600d4440d1000c86d0749040240703e041d00d2100040d03e105180f2403c1d0701d006d01c400108140151505885440c0c606c0c00340000703000203403000d4010346103c004034650514282c071010107000750b00e101ca1045284041500b10030750181c400c55020610302064519070780070ac1e500038106818140d009000340285c3e08420707031240b00040c2182014540c004070580c821081214088001d50140e0700001d2003d14140034041a600c403818000d1190300100100d00008612241c00f4065401c1c0a000e079444100ea4608103004100040380900410705082c006121a941904000100c1c4404036511003034080304d608055003402440c0c0020f000c074200f0380d0f05011503030301401c0d180050a4604112092100a000442c04540c89088520402980001004203025144500058080d82150080c02009441e1505500c0e02809850a8a480480c013900b040d20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 687346465 1250 687345215 687345223
    0x7140102010b0607080c07030212030301090b09060306070f050405150c07210305390c01020102030714070c050d030c1106030417030901090203070f1a1207140432030f0309010c0302 79
    0x2540d4050895036aa2b480f941d0031960f06d40092260201c140d080072045012420a1185240141d50282c018500c0b81c175142c50a4814030048600102000340a1000042961b50808a84144404010303603039503032030b811000181019050f42041110030b40241c542c4031a4403c8040d268982505403400702e4540340c40c103140d008024510f8821702c0d107400e501001a10300c2c0da40b220410344010410303000c0740c01c0031545600690a0b400112001000f241d00081884401c0c0450760040c4180b61048514101c00c03929003000407076100c1c560317206400041c2c41d4105082040b007010144481640704440030342c00c619195940301900345507622110030700b04000c408100d030004250002e05a00790300070309651126071148008a0241034500c54044460400c4500b1131080c82124122550b0740741004c80c0800c02c0d55504015108010121464400c2c40010440002d034a0a9010740340c0d001d094054110f805e0343c0d442c018400c1b2201c2c2e000402da1098012183e02108588000b0445e0041ca1007802e020f80c3d2400c1e10704003070f070070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 687347715 1250 687346465 687346469
    0x210712030605090f090d082505120109020301050102061b040506220803031b18060f1b060402120d09030201030b040f0509151311131d07140102010b0607080c07 70
    0xf2a5000d01121004031920b040c421041c01007107070144505c0c3c92044070760540a4444203042440c080207041004500c503e601c090301501d00300180760158110783c401a16401341d00c0080c403d40e02100504c00d40d0f0341070000c00c0e00700368049040702070441d1000c20720010780308074441c03035103c1d800000350050b031000744003205c920203100c2d0660703a50340e20b980700f00160312544100c800c81074100c40c550f81c1104485a8034240c9403800100c140303070b50300341c414001407001562014400494404041c40600101c400481400c4038100b0b4440c007421030f50070103105002c0d001045c500d100703005030000740c09000d00b283e008217042c0c1225024640400e241102e4004180100840300300c0661150600003041039001d400185009000300c0c0b48046501c6903206407881c1102c402c1040000c180d145401414240741c506018480b0b804490900d00061840c0c000301006800903560b2802129030308000010032608a54401c10010741c8020b0009019074119400001d282d131040f400c005003044404942c20103052020090340d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 687348965 1250 687347715 687347719
    0x30d050709090213090617070b07060e030a0f020d1409090c0c010906200403020d0807020a0905040f03030f060f060302071e0b090712020f060d0b10030c02210712030605 74
    0x1680b4508040b1a0010401038068481102c6c1042000606140104c450382001030300880940f140d01d050020010090384844002d4400d15116410188020000d100a00d070301200c81c1c840021041069030007038140190200d22100b0320031030b66080d002608002c0c04440c8030b04401c8603079000030fa80300301040c00c044c084c481158103658a410070407400c000659103c892a6594095100c40c045900c5122081d94031481c00001c4d0001110750401001030103080151400c18801401c03022015110420304e4201c4400f210305450036400f10b403521017819050320400000711005c010910159041c60781d071005081c483e11615080590000d01c80041c42011050301021903286501010310800311b04001c10b0010042d52142c2150050440006001e050090280111607020b8078162407083c2c40340421409801103000304488588548052883e95100c00c54a071180e04241c80009180b12008002480d04800c59006403034013030a900d01d05100707a0841c0030345502951000c0342507031800c00300c0000c801400d45903000d26 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 687350215 1250 687348965 687348967
    0x9020a0918140115080f0307030804170a050418050108120c030d0608061f08070302130b040f1b0306080606042705030d0b010c02180a0605030a05030c120c030d0507090902 75
    0x10501c09040d0400c218440541a00d4101141c81e1441c05d61252001214020254410000000000c0c010395540e580240981c0066203c000e070100c03030812550241d580003000030300000d000d1046031401e1030108034980c44d4030300c20081c540c1400302e62541e0f40316588040072021008142d14030120810000c8900d64040008103004203a5030b081c0741c82c1d030ba280645601817000c02d9442c1c01446050100710010031141c886c4014400c4600d1502403040d071109102c50103403034139103034011040d8070f03155030140e000d01c0360710b520002807001145424215690940002e1400b0507081020822040d180015075581020084030300240409580d14008609650255100b10f02c0000992980070f000d008005071000007040581441080e4180c0011585211071100c000c0d80103d0740a6500c8003810300d07001c0150b1064004000080c9961100d00192400c0b41440007100c00b40d0000904078241181444522420000b4210150a01090160341c0d5140e00603410a6002c00c0e988200240d10306100720b075060000c1504940071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 687351465 1250 687350215 687350243
    0x21303031110141008030a0e04090c09230105030312011502030c07030803010303090911071104150906090c03050c03070e010e15220609120809180f06010309020a0918 73
    0x140a0401040350066130104c1c1118000607024004001c0320f4991a059a80e07400802d201800c002c000d04500d141501c0740040f01501013680a0244100c0e8401c0d8003007100000184495400c0a045520582080d8042c3d00180140c0d50f034030080d41191415580200c03065444044658030482c65402405000041442203d200000384100c83c0002d5040c0c80c001d40c0ca120803192a011070070143d844180c0c0c0445010802c01100d40031a8010f00040e841d600c0c020000b01d0032440d402c1201ca2000040d4000f09600e9950b504200904c1009104884810059042c00d004a2074026041038903800f00030443d03000c1c04549006d40d00561b00c502c161654a00c002088000d0910008001040ca90805900c0f01c44c00c0101d4890000c0842c503810300c0c101142c91a5580da00020300b060991083c50b510b441c1d08607818101444003e00380d0341c90031010040400f09900301003a5140c4038289100c0030324040c1655050503c0c100080c000340c1c440c00ca6000946051440210700110904401b0040c01d05150001d0080300d000101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 687352715 1250 687351465 687351491
    0x30e1906091208160806090f060a08100605040b0a26030903030a170703090506130c090e1f0218120f0a030203042d03060b150a0201061503021303031110 67
    0x403c07409a19000340845002d07001c4c0200780c40d003000075203446901c100c2c0721002802804552840544c410400340071100030f5980c840190707280203018550445466100d101c00c0c02542064425068050021544801c00b40c0c50600c03020005509028072407001900d070414680301c07030010822101c0300c01001d02160b94803010b4210081100c5500016001c003600f500c00442d4503180700380178407a80c90341c000020307040036101c82054403550442000304407080d054a1000003114019841588005851038025103a03203050942041482d028030039480541d079106203c080006c44c44000c10042000307050b42c00c02e1003035840201507450704d01c0784081c00c0c43c02e1240803654800c0660100180003202c4100c1912441d901002254ac0e111031740c002c4280002c4550b400040021a00c1900080c07000071014207964258407110101d802a58460494500076070b4444d00d00308422902091075503803420b00e610b411030a160001c0703424002c038026440041c04001142880c0313210004288040d07044010030400401000044040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 687353965 1250 687352715 687352727
    0x170115050c16030615170c060c0a0c0f080f0607020a030302090a0b13090b0a1206050403030608070602070e010e01050d0f230c1026040f021e10030e19060912 69
    0x13002c010717090b01c401c42c0012402e00d030400d4101385064480180001e8004a014025207800040c48050305209103090180803034001641d01024000c2d56642e4140f1905004034a4030704510103078034003090b40c003400c10813080d41c2d40403802400c81545898050303aa00380400000724403590726005250900000512650b401d01c8042d08a8100c0c0c0101e0f0051000e900da040170880d200106110306c89040d51061070500016080d07920441d4000e22a050004690b602d40400702c1c135091340360f0017000141e4070018050241043e10303840f4900400409480c20b08079810000458060050300f5401810900680c1c5200300308480c201c8060310480c8405d01e1002c03420004051940d480d4030741001c0d64040d5003000040c154091050740d07804c0d181075030000072107507000101901c02040680104165a800d090410303410060360f890b40c0410040495422103043c82c401102045408450811014249850028409a482c60200700c9400764501c078100d1a200d030b5080e0a016028101c0307141c00405503040c0005101d02150001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 687355215 1250 687353965 687353981
    0x20706080402270414030f0f0d150b181903150f0e0d0e060901090e07030e030a0804060e0703021005160c151205040f0611210601170115050c160306 65
    0x4100d84c5c54041c0c0048000b9104d01c9001440040c2000801690389040100d00080280317074840b40d0f00155003242c50501d103580076002c2c2c004070310300300001800d090fa4941100c0f445000d000212a036005a6400c940c0c4100000301034800103080304800d20041d0b04140844d8041d1004c100da0309000d118007500c5406694490070f800d107840d00030071494081105242416000d40b948070006031114003040f81803410f07c040c410700041c0000708041c1c850840201d660028009410031403005e45405000d4201032030700e00b05031010070301c1b07001d0f46512042003000917946104000c1c17404215410308540d106519118425141c04110010f02000c9400c540080d81d4002080466004410395850b8001c0c0f0103511810829110706031005401d9145d504c000c030012401a90004c002c0c60128005507281484043d81706011407080e04242140d20300c81e0342006001d5070007400154503401e01c1c0301c071136020b50304051303603440c3e90543c00d0381e140c041060200301808990710401686489106640410903943e68918040028210740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 687356465 1250 687355215 687355223
    0x906110307030c03060807170f0304030308060406080a050d0f090b1c240501121d06070806030c0a2c0a020d0c050702030604030806062502030d020d0207060804022704 73
    0xf0410781c031a128403d100d0b40b8141e812107000ba001c12031034418446010181c1d40441d010f80d014444400e4482c0300104001c00c01184203840300381540ca0410100003c80748607a01801c455040004030708001034022035410f8080110b42805000c540c40702c4011034a504243d0002c02d545040040c50480e1244000c410403e0304c00200001e200c155415100303555189900c405524480350312040c1846551300901d05441002581800081c0c01845030390b14064408080000e00010b0700081c091107da15030203049140d104d203090300100b1401030080081417403407625104d0a40000d001148521001500c1d41a40302024140102103080e4103142c000c0500a602c140c0f064243c0030b00c0c0012020509005400380c07403005400501505895966880543d0011401402c00d54040d504103c418903504103800c40c40000c0d01c0c03038440803698400d240f040c1481c201801100b0025540200603405802d9800290001694901e260601e0141c5a61005c10300341d040b00c052443c81e02002c03444083d88000003512a500c22402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 687357715 1250 687356465 687356471
    0xd03020f1009020d0b190501060f020c0a060c08090d0b070f0f0c02090403270807180506400b010f0305040809060901120e0d11060c070b0406090611030703 68
    0xc0c50410100300c880c42d0b24000d4000452407080804188202d03080e40d44101541103850104862010302011510241c11100204940c0c010384160702d82c2c1000b80648030130040d0b079000078480c284036014180240d01500240100d500203414409a210050a41582c5030310054181d59070410300005044580c2035442c1d00002080c14100343c0d48144144110150300d900a80224019101c0d51401c4600281580085000c070b21800244013007060007022200042c002c681c0a06526030800e034034261a4401050f83c400f8040c108814050382d582c8118126002d031440400e2411125074640d18420499003c0121501104480d031424080da50103800c41e60700080f0176a2101e9908180c050103400302c450594002e00081400c0c00900240d040641c000c3c280a541410107503000100b010145069801c203041c1000035400508540542d1604501c1c030900d96281400a000c103840c080d51800820f004404019003603182000200d0b080c0000e03640528507154100e1800d200c1401c0c01400004c0070b6005441081c00030f85 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 687358965 1250 687357715 687357733
    0x233607053d051b0a0b040302070f06111506031f0c0e0d031707170c040608090316020d020112020c1b04090209062e0207031509050604030804110d03020f 67
    0x804811105a040d8858540c60b00705404840700d509001c81c002d907407003460b101361030003080411044824103104601c26401001c6a40c1440d0740c13032031401070325488001440f2003001d640030403e201089030020800c800070f0f02ea400b6a5480e00082c03a0401003800c0a80c8940c54041075135454020390000365202030316407900740d1b040c40b8502c24051508a00742e006000600204c00e6500403011026205130425081c4c5018985061480a201c0314244161048902d05000050802c11036070010346e91030b400107550020358204010185042e002e4011014001c0c820030f1845001411617000300b4891013003a000c0d442c21911740d5020300c00030f40c0d00d25020002410b00034280b03c00c10038619042c0507540680c0d0313010340740400941b00c0c43c040c40411760032070b00c0103410800e5049159015182070520b042d40904194007c04000c1d02e9030038000c20022088400028190130891a800800d1001482541041e45843d081c6016a524140710501c5a074101050390301071401c41e40c290a066002a641c103e07400703400c0695028070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 687360215 1250 687358965 687359059
    0x5010605060d0c031505060706360204150612020d061203080603011a1003020f0904051e010f060e130e1009060b0609211023360705 58
    0x100c1d0324406c417a44240200300701c00020781160020604098441942c000300e80d50300c40d0b140070421040200000c400441d014042c00e529003030050b00100c2d140798461038001c0b030034514004c01404003c4050f28440e500041c04507140c18444e40440001c102e91180c500e1413003c0d80c0380040c602c100c01c4e5001807107982011b26841a050440036205510703d401003401101850004056029401c80318508240c0300c400d125100c0c4603152801070710b100d5550384036070b0780002019040b80d42c0590b406030411644030b090000144042c03500f1000491070b02c41e0464180e5024600080c520b000b400c1c2000d42c181d030300e0096800710f10b200c441c5500032040a901c01c0e1018000c50b40040e083c40424040da05600c0c0d400144d40e40201d4651000b4008107511800201c00c4d02c0e000303030003c000007040d685002d042a910340100d11840006000000c030258010403000d5038407012203950140d00352442801d001d880003245003a1036002e00d03e4003c1087c8002014003503d90200001002e0040109040d5182e280f07906505064107000c1d04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 687361465 1250 687360215 687360251
    0x515010608061002070603090c0f0906031a0906070c050a021201020c0129040203060a030503130617071d0d051e150417090d0212010b01022505090405010605060d0c03 73
    0x2d61340c01030000740c1c9081422000340401900650300801d4040303001c0b41c000d11a40402000c1e25035840c0120f4424514078040c0210f0710502c800300501d1354101c0a20402d000081030594004101e49003950007040141800c50a0201c0074a0003036000003004510350b0b0840c0107401600c46119048000c0194828040c038010710b10220000307240150b80c5482c4185060303d49a405107070000343c0a03104101481c0c890b620f03280b4691094001400d802c8400788100f00a0b03901c0080c5203c2182100d01d0a421400c000c02c010384440c2e8078140141c8446403a08040840e500d070103410210041d0820300b00d41d482c2c1004c8681401c0d90040029030015030207203127507a040134001d48003030318011a804080c3d041085001e42402c1480d4103c8031032190310055003090304001d40e96921101c03809900d00400060603041d044000380c9842105002d5100c00b0b09225154404c0c0a444030049003110310542c0e024089940d186889401040203800c01980100042118110110542d020655440c0d2030b460030011329803c07500b00405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 687362715 1250 687361465 687361489
    0x1517030403020a0312030e070816050402090603040b041403040f0e090307050601090926091207082a04060602070e07022a1206010b0c1506181003051501060806 70
    0x420015002000040c0d040017030780351030110034940051012110402142442030036400301200c0d5000e0000b41900b40350380360807640101700480b021072401c1001c1c03008c41c402d401300410242c14043c5000018080c00701500600301c09020410a50783e40b991a4129074a900c80640035000c01c0c0320340d080026194040005c00c07520400e80103001003005a10703008410000d4032031820102e402c94403045941000c00ba07080004030310341603c1c004041c2c6441402007404883d600110903140c6941c0254800c0005c031001240c1d81e404440c141c0740d809034009030395a940701da01c240280c000b600949025000610b040d40468010f003a06e115006c0801c080d150564102c0c0e40d0380e04011000c9000c1110306a030028084c0b42e2209101d0a140644059100c1040d8029181000d200340e0102071807006c0000c0c25009418140040e01240e810000905050708200001c10390412400f80307400c65009100c03002c03c800c10324907102d0400541e0701008a80c62212916603192507480c087c886c4030b0118150b40003284e03880c43c00c000401c070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 687363965 1250 687362715 687362719
    0x1080d0201050a0b06041203140f270f060a05091c0212010204260a06050114010f090305060f060a030506090c0f0102060402010f030c03061809030f0203040b0702091801151703040302 80
    0x6c241402c08403840290312401c40c0460074031003100c0a2501c20111500030f014800c100c0002d858685298100c0405042c0410200303c0b011010b0058101c42d65681c0031014000800c1964110348030244c2000940b454801c10b40440e80c44040500035455040380794202c2400c4038401d40720906c0710180b01d50301c1421b0f8021806030300da907a003071114206502054008041178040302e9504aa420342d110362213120840c1c47c01c0e0801010800141c41c041d5a0796088000070181a616203008d0710760521b145c881ea61a030001070008061a0100360224290395a82c21a820285400000b03950b1242000042e07160348030340030318407075000b00d48520480078590b0010030454440c035010b846c3e0031501c01c10500c0817002040720703115080905641d020080381c03c11084109140c412802080042c44000606020300041e00c0c4481074001c45d8010041400f4103035500c4280da000640c1a99451569201c00602d84911007001c207a008481d0f20782607440c1541000c0910013400ca800b014840f49000c418004202e1301d902c100e01010b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 687365215 1250 687363965 687363967
    0x3030c072d060e040b100e2d09071707030f1103070203070209090709060e1f0b0d020a0306030f0b1608132006030414010f050709030b07021501080d0201050a0b06 71
    0xa01800742c000070343c085200074800200c025900000511505105803503034000781850242c9211401d001071b80c0200c50341070040b00c0d0110442c080c110840105140355003402003002d2004200c07030034094070140700c80703450356040c3d4052850081c00c0100103080f100300348401541804a002c01d11020070040b2401402c00358040e62030031132240c092219100c0040c20a04251241620008180017507101e1b24001e000440d903540b0090600c4d290110f0018007441d0200b01c01240e80e80c0c200b051605403030440d120070a100304090f072a4403000f9000d038003d0100d9807001c1c10f6031400600301020400b0b6440558481c11404d00a0001a50300810494400e03a00700c0742d0562580b440000100411541501840c000d0390704500fa01502011001252080d003069a00310f940003001d01500c91003001c02e01994540d80400d0b503080000b842c01801c0240072031054840070b4402c1803c04041160036100740040c604c00d0050712100075107940e58140003641e07122034145150055280402156500c5035030302035001d40303001c014003107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 687366465 1250 687365215 687365219
    0x5040b0f0d0f0503030702010b040f18030c03030906020a030b130b030303070e0409080424020f030a202a091b090324041416180b03030c072d 62
    0x882407000000c8020b459241d860595440014410001144251040e03800400ca9400400a01c010b403070070703210000c0c0c1640c1400b94131300305c00014180240c90305405140900843c1103d05043c8d00602801c24003811072400041c4c100151505504500b00c24241a61410121143e103480300d070803280c4084240da450781040010403007017445141e0200c04404006c00000b441415036490401652083e4458810304a041014068251002c0600d5400c0f0a0500141210840000c01d1907100c0c803800c1ca5503800c0c4030705110243c441e081544005000102058202d0303003030409141403010500b581c1041019404555244010a404c01210310790140814000812042404d0408202940c00c1040c640b40c02d403040306145000303580340707085001020001c0b508440301814241040c8140e80ba140060440c180d008820b44038801845021200c103c40c14a50b40d802d514000d41145009440005103859040c03002090b00f0a50200c0460800d0480d01c0030420b00c0079140c04103a8091143d203c800048914440003001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 687367715 1250 687366465 687366469
    0xc0816031e1701060518091512031201060f031d06060301110f040b1602130221041110090503031b0d03090215090310020d0b0111010506030d11031b030307030605040b0f 74
    0x3400d840e0421258511680c0d20f04000700e201801c0848030031180000324510781145050808101c10101c80349c1020710f103010f203043c043c442c60320810703c5403504214500d2451001c1d2031003540710612040a010301d08030381a480d103800c07550f034400549101c1e110354604404001910700c1c010484180c001d08441044c245845c048104040350410610000c40701c1e494002600141e603046102c803240d20000d00c0c010385038080d050226140d8005c0310314403401031002c1e1050001040c1c0707100b0180200b400440c0c1e40611940401b2046581441c80d5006603014071012400307080d40c01c0000c4145906044100c22944148203111040b0181d4900981c040d41104503282030030050092800104480c050140032245e06140352250076080383e00c00d00720040e40d00d42e2204064400d41e480460a82103c030040000d1043c0d00301240000c2c0c950760b50000010034045c01c0301c00380c820760805100b80c46104940c44400b81100703000e50746a03512680200d4601d40020302c0c0c600082003c0c50305102c0e088a041d40030b03190002c00400201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 687368965 1250 687367715 687367717
    0x50f0405040e030a02010c05040f171507050c010605300a06020a11060603070308460e0109140d0c051003051b04080d0f11010f0c020c0a14010c0816031e17010605 71
    0x900d1a90074051005542c940c03074203100c2ccc0540545843c0da243c666880001200608546240d0820361049004044282d0041c01141c2d5010810041c5034101c04201d440403035103840c10204d0b8000420b1035001045103104590821002102d9803214025100c580d62020105600d40b0b41030b01000703005610612403080800c0d02c0d01d0200308801c40610020a0f81d450108502c400c09000c407080c5068410712078265410036901a1004800140c02e003002014581403403002085200345030035042c01048200c45407418130500700c48000003044068003030310040038614001800303800c0071030f40311190764002600c41050901c1d00040343c040b00c180030060000f070382d0b03075010845104800780801d0f42001140c6441c0c0b02000400c1c803a4009858100b200081c401074134100280c1881c201600781840741041103c01c003d0071080c2c10a071308044009281c5600d404025151001481c0140081c1c030840040c0e22100c2400c2641103060230f10602c1051000100104480e2022654090341107818921000d07500c0c010020305005070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 687370215 1250 687368965 687368999
    0xb0609210a060e06010306061401020c040e070b0d24030f11040b1002011b030605031002030604060b0c01050121020f0d0c09090b1503120703050f0405040e030a02010c05040f 76
    0x1015240001460344070b00040e15000c11086007030341c01800c010800c1000c90b100350801040400d44a04c4011007050000c1e49a05c00394140074040c0c1e40720f441c2d0158012050046d90080c02c0c0c0c0f580100c0c1c4800e07000c0c40c81d00050030350140ca5080c81c006200700c0003114902c01102002c45c9d1b0b01c0711a04030ac2084983d10f000056049108003a04142c4444900810756201e0180f0440c0d010240d00001e002c10482010300c000320078204070346080c5445e0800074071068030085a080010340d4461400750b900d0f01c0700008200180708541c0998415480071410341500c140c1900b03c2030403103048844441450300800c040d01d001425241009500421006d40d0a1b040e04154600180080c040c02d4150a69540c503002001038908c000011a1100c0c0c5200c10000303184003c035020155040c0c240c0044c40b41c4050301c102d104a5101d04c49018007032080c003080c09400f0001060844015100152050009105040170b00d5503036000080c010004d942402d2271b07001d4449c840e038152002c490703c6e450905c420301d14080c028942c6410300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 687371465 1250 687370215 687370279
    0x50c1b0102070609080711040e2d010603031205091203221e140309030a0b0a11040f051305150d0312020a0c330c0c0c03060b01030b0609 60
    0x3882030b503010074032603c00d51240c903004460160b40d0f14818030700240d000c00c00c0c00202c0d00c00c1e86414800301e4114000103681841c0d06003400300a2071481048481c085010750f192248803590f00b444004020554043e502e826445010002400583c844100c2540c40da03540c0b081034400c1150030f00001d224030310340c82080c151500130700c000d0002d400a82d0312401d00c2d120281010142c1d103021800c610042080f6070348400c4005011801540c20814040e0000303407034600024025003071400312004030300c610f96941e1004121089010075150341c0e540e40c1d0382c4243c180045110f032030b100300412020140c05141d80e000d0244101e01d4403507240707d030741040c6080000082c0c84020a80800001051001651100384010000c6207040d45074102990710902d03010344074481003d622000c10b007620805452801107083c45541c2031310f0590b07004ca400e140154085070705281d843d01c042d14044000200005102c1645d00c01e115800e4280d07000d110703c01da03903c1030041c07078441c25a05541080e100c0380c64406500c00b4803005001d41042d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 687372715 1250 687371465 687371467
    0xe01031401031b05030307170a021207050d11010203040c0504020d0603061d07060215010905250305010501121401290415081303020c090c0d060603020301030203070801050c1b0102 79
    0x40c4090800d20000240c1044034504818a014180c05041d91560001450218019890104950380c3c0b050f002002c030002075440c07078020400068050003406451000703c0c11251141c1c94201905060796607000b28a040d0303005c03880240103215194418001c813441a074000c084440200c4c40c1000f03001c000e60006215060305541c2e03400100008006010f0114010310310924002d090b070103544110300f0403140e0341c0f0102c1554848075661004101c107a1303280e81107910340710b000141075403650404849800301052443c840034a45809034582c54042c1d0185059074000c0e0b0310580b8481a4601c190100d4407005440c280401000b00100040300340124580300b05062445640314200200c2954001d541051b002424030004c01021141080e62081607140d1015250034091050030650704d001c1d440b240c0c00e14019000340d2041c0c0004924280040841d40b03104609003040001c5969514000e00940080c001288613009089000411840500031107000703041c070625031445c0428903544a100d0110900c808030b29550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 687373965 1250 687372715 687372731
    0x604030c0516090b090903030709030f030c0209070305150102121e0f0703020a06050f010b0f0a02120417070e07080c0a090803031009200f1c0c0c02030601090b100e0103 74
    0x500741118000f002221030128101c08141c082050703800d0000d004951070341c0248204908580d1003070010040780e400440325405107856041c111808801c02401a401400c810706000f015079041d40301620924849500799241e500d0200120780314280482c01c60031a6800b4400d8030040001d030700302d40c104400340000b1140b8121412800c405a0342009000b6000341c2c018a200e00d0500c5035078014298040c0810500702d049605012a49041f401801d882481c903010200d901040f59000300b0806041543d01d40c10340c1e40b00c40c1d654448100d2000c0ac814102e0007400303006000160302075510610340c080c01c9942c0f5a821603039529803280f6100d4010141d1901004401d660018146409000842c0030328106495480441d080008880680d01295403000e85403a120800c0c452240202d020380e590b80c10515003540da030b01010501140030000c405c8108082c00d00d0900312179601c030f03003158090010302d109500341c90032030b0390f01c3c0e002c038084510380454075070819820216100d100b4402c2c3c0000c44200e00505000070200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 687375215 1250 687373965 687373993
    0x3080a0b1c141c090b031509091f0b0604050909190507260c22020301140f030d08010515270a05060408030d09051219030f05090604030c05 61
    0x800446042d0741d4070441c1d00b201504000248960750b01d0425a041c180140281440020140300091041d602d04000c040042651052105581d01e0b02200080100007207042c848182d54441c0f075140d84c44003c0c29800400e000c0385550310700403c07424032402461a41003500d800e0030300c16007013402446000140143d021340e45618401c2d048480116006000510b4402d040c030740c2021354245500d51507400b5020000850908420010780d4009222041e5801030004400c01400c106102c890900c0c1c00409001200200d004c443c4a000b44e1030514007101e42807000440c0c1001d00d51600490501c1e80b00040040c0014820743c2000d81e5200f40c00d018105260b846c02c0503000c03010b81c00121b99000380441a064800500f01490300c2000e4030007500b01203604628240c03a2415242e0b807442098084012a500d0b0440c01013401001c1c4400049680d400c1c0c01d465440d10300d444610803001c03003018000e000c41c2c0303014603124800c00c2d00e102d04ca208200940042c60107484644054401d900c240504440c0d07481643c43e000402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 687376465 1250 687375215 687375259
    0x10603081207030b2d01110a110301140103200f06072009102706030302030a14070b0c16020406080a0203010f0e0a14070b03042d03080a0b 61
    0x50701854201e035081050004068440328002d05110720700c016042a00c0105140034100c9222840c400c2c68110344e01040140e5064034084080b030b866000314800c1c5400e0181e02c0c499a001818124000c11240c8038606441d03025030703400e0001404140000340036034900402500310040b03100d00141184404540d040000d821580f021204460201c8500e461051240050307645404513001194054821300c0d100c0c204131f121582c58805c103860950310903810b2500c1f50107108000e61070380c140c1c001481403d80380d06001c1c0d0b40743d101003620400200c0c82a106e03441001d019082c0c0700c2895000036107a001d40c45d101484041030f003090790301f4680c0c02c0800400708016665449818010b0100401034410b5444900405084a0f803001e0940e07003c900381010540c80e210007082007402e0075030143d026080d84d2444c050007446c0c1811030301310b41155013001041c0400d1001c54078119001c6204030070500414a002003000d2440c0224440c010040342c241c0c00414441c482982040c82003041c094a581e0910b00c242c40c100201d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687377715 1250 687376465 687376477
    0x80d09150c090b0a2a060f0b132309010b100306050609010e0414070207080f0610211718031b01030e1002071a0106091503051806040c0f060309020604051201060308 72
    0x103145c480d40107104004803405003400c000118a820401a050007000c14404030140c0c6461400a69a0320700400e03100b0311280511080030100e020301060303d0402903050080049941061148440c1c0344840807281c03090103203405481010348042d0a040f500f000644413122400c50b0207500c02d40f42c881181e400084640c040340718540702d5004011741031a204019050560ba0583c10300395420203801c111141070038054003c100c81100c94490300200c1040381d03403070040e403528030001d000c0c2e165000601110300c918805001141c4555101400010402c010135030703948001804480400100000c5948542c00307a401300c80c3d602c1e1881d0581d244499107034428070072a44403040446604003042e8000805014050b406400340101c3d062640e42541060b06960321003204c4501ca10400da160070000c0d02e984003429044081045c034100300d07191400c1a2411928250b11030084003d038039800d203000034855219014549900e5005402e039881c150070072061142c1c0980e5100001001e640300d500000c0019515001441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 687378965 1250 687377715 687377777
    0x12d121d01060e06010512041103011103070e18160f200120030106091802040312081f0b0a0518060f0c0d090302060f1303080d09150c090b0a 62
    0xa90141420f210300440034002e4220b0381041000d020381c0440c11048022290000d402850121003101e02c0c3d8002409402c440c4465200c1c44004010322019030340050a203045448100d404003505030342c020000411400071161404c8070681091200426801070540e007291403114a8140740d03c1b140901e0f454070410100c81c042d07005030340d80d20240c01e0344021130f500c0d081c103219640d00c2140b9551614500501e074040300d00851441350340d000901445050b10340d04940056600c81384e9043c1d800d1603400040d001c24022a084036842c1d44522148e0850021402c08200f915801d041c03007400c2c801c560100302e81e83d801c0014600401c911024142c02c0701e68407680030f0a03882d4441003e850380ca000c030b80c02c690f0421200c0e42c40d210500906000c14030050b40c071002640c5000039500100c0d51141881021201c0035005030340050701c0c03403800082c0350744c0a1030700e5085040d0940c054410302454690030b040f00307403c507080707031105d0000580303c45030a110030080000180718100507442c1010340c0383c1c00c0c4c01c901281b01ea107d1140716 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 687380215 1250 687378965 687378971
    0x151b0f14030316091226071e020909010506030d180e010b0903070e15060904090c0b0c0115050904030c0c09060b090405010b1e03060310090f02012d121d01 68
    0x28942c0f0101c1e280103048003045d241c2c1c02000750b503984078119149044494038105030410f84400d003c1d41c81c054581070b03a049260301450b890000c0c00c851601c820128160f000391003010018025840c14010075003d000050002e112050000004842002100c01884150045080d0015014103090a818040c00c0c503018510759450019040605e00030503640254041007100d01007000059030308a5402c000b07801501d2090b540d003503040c0000c00520500c0c0300100b21501c1103a0104150381458082c05041c0c00c040000c000a9103110749140c02c0c84054815154081c111200003000641708001d042d140d140302c0d8807444410344c0c03519200d000780c4a080d0402c0d4150300b404070f0310301168940b03402014014201420070030f24004601e4600d8040303040f030700040b00384000c002001c5851500d04108241c8440c440304001c0151900c0c510384002c40d1018001c06a000902c15114200045050341344010f1010302c5289a10201c031280c3c4003522111142e0800500d800d41d1031682c2c00b19598540107020705c80c4c502074000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 687381465 1250 687380215 687380251
    0x10c0f0b1b0c0607021504030921060912090f080604020f0103060f18110a0806010309030e130608010b0405010602030a03090201020a0f0b040308010b04080a170f040807151b0f140303 80
    0x6e02d0001400070010188421005010101ea003140c40e08050321000c58180180c0d90381c0c95002d800c40c0160a000402080c0703800992802e000c0c126181500126041d5185008142c0c0c0314407407041c4503081d000d5800c1603007010000c01c0062809a50a031030186040c100880c120341c1da0760910300c110340e0a074060540b000e0041d007065480b80031885a840141c5114840c00e04058031100014480203008000505065940d25041d040c540921441d101500004000c4808250000d981a000e0304461160010960800f401000d00e49000d005540c1a595168002c40c01c1814a1342d049000d001c2028090b030550180d4152000801c110780041c0940502403004003000f82880d1800908501059200e4092a80188802c2c000c90101281c2045482e070801c5400d202035040300818441c0f44616171018061aa00041c00900800003250000880308480c046642495900a058415800e000070000e007080210380180002503400407160809401039006541c000c2c203003a8034034070315441070700c44010b000050001e07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 687382715 1250 687381465 687381467
    0x11503050705120601120915020403021905092e140102060a0e030406030906020d0e01060f121106030a0b12070503160e0f0910060b030f06010c0f0b1b0c0607 69
    0x9040e41212541c90110318040f64005003592030000034000604005292010480400c1160083c0766543d800a5160715403c01104030440298014481203000d503812000f000080a0f00703910601c1100d41c0a0410440c96403403210300041944107507110a1007580c0c0f156514143d1040981850184c083c03c00025000203078000003a20306074006045105660405e102e928900c903002c02640e00700c80c03460401090268891078503101071b0160b040035154461030b03c14400b50414054012004403049078070801182d98843c140c4841c154006800a042212020500c4403142006030007540d0145489100240c070f0110f480004006030403001c130500e810340c4039040c280800d1030705102101301c0c51141030003c0f0311546009100074101500802d059401903117800081e4040c0020b00c203070b104106084404201d40e5854a0480c0101e8006448201d1000036080010f1025400340401a682e16044041094a100207076a00410080020a54180e203000d05540682442d0381c00003401c4001d040c00301500080c41d150f04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 687383965 1250 687382715 687382721
    0x12070302040509010915031209080a0b040b011509150908011a040c05070f0209280e19111201180501020304060e030304020d0f081606020307080108010213120c030506011503 76
    0x444150345401c0d5404d541003801c6d07030050f040340d03841007003180706038a03000040e0399443c1c0541c000d050324000e81000c42e04024440040a00c00c0340300c2d2841001698940542c140000480e02a08011404c000000e1206210320340030030416003480d1800c52000340c3c48602c0b26080d606950400300c05100c00c900004207600c1d05018401e03d000562802904261079911002203401c82114044e0207490010007160515500741641ca4000700b80d01111714005018045070030042060342c1100a10b400349800c0510a81c0302480b11407102c603080440c4501300d0045800f00210306511099102c600c1d0340e51100840c074100400e00c00c0512034041da00060301d91420707080c020250ba44040b4415102e81003042000010fa480601e00300c2d02a40120090600599501c0c208407244111003041c03540c80c140310354500030042c0d690011032050407255100415a603803a03008500f81d00581c0d0b4440d0404074402024407400036140f8610203054001e00c031121380c4d83e03a00d4555500b028020b811a00c04092a0003404000c290140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 687385215 1250 687383965 687383969
    0xe0406152c0604050603060604120302060a140f18010b1012110306060f0c120f090f01090302150a12020a03140c09090f070c0b07092108040603020309031207030204050901 75
    0x41c01120000c10001a520744210b00030144503960120224149440f010181d4010300084840350401c01c109040181d40c8070400c0f1140c020403400c102d8200c800300162142d090060104c548003081319103d010510b9200604480102059961890424105e07914072150740051032207a00c804000d542e42c03e0307480b015100350780890101a2010018000305031500000c84441404450040e611040d2407242141004840d0302c012440e0840468100c960042c0c070401070440c0c4608680d00b00303820040200654107000305103c00395000e1101214a0b01803070564006002079003651a010702103000d561001402c980205058000003591303408001c9103a100007465540000d40d8205181c104141d1000141d05000028461241e015641001c6402c05004d440082c0400e540403041401a280110004020612500c10885103201c030501c040d44240e50500002c007016000700d0302d00c2c9001e00744003054011354405000c40c155071104020200e0b485821b00e002500600e00d5540143c1e4451401081103942c120607 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 687386465 1250 687385215 687385277
    0xa111201140601030e0a170315010c020f010e0409080f0a0f140f0901090e3408040b13020a0803040806060f010215060111010e100f06060f0e040615 65
    0x5a40340240c1d082001029500c50800d10700424850152030085d4204615420b0007440002070300308034410345443c1d07409188600c0151a0542141880b00011a40005c4081000c2e4105103100f4041280f54459100284003807406000071411840d545c1d241c000c0d40e404803007a5100c485020500c107141680c030681150859102c1d242c031210380030460002407480e20829080b81c0d080400016200030f907074080d40d030900c001d041d1601d28040d14540050780c400007081500c0b01c0d9805540c850302c40c44c000000c1c00f2400c4590348007541d44d01d245607103503550f8503c490070190003080c940c064610340f580141e80340314065000d0400d40703000c1d41d2a149850900781c42d118020b0961480f035601c120440080c5e0741e00080d01100c4041c103114600d000c1c0c849000503510351106009000c82ca50a08103000e442c9000003d02d65804444018200421107155030200211001030142c00e0005240c0d40f040040780e44200340004109000400000f4403503602c814281080d05002c3e40030012810030340d103d1041e628880101c100b035400c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 687387715 1250 687386465 687386471
    0xf030c060a1214042406050604030305070b1b0409020309010b19030605160807030507090906060c2a0e0a02090301140601020c0d030f11010b030307030c020a1406070f0201110a111201 80
    0x981d98240a8031260090260f5005c4071100c50600341005411000040034094281c2d5900d580ba410010040e500c03594081c2ea036842504042000240010007040300b01c8646840142003030b00307140308a00030707520140030b9240d503640756207401034944d42d4140c03040c1040041e4003228601c5491840d0003416a00010540c40d0481e40e0707100852101904403041d16800005407800080f40d646999054681d001d181c0c0114645624000d0003242d859000413003c003230240624003049107114007180ea4040e0960000c00d074848550a04010400301c000c03999a075170801d080f0f002c05410203a440700441d00312241030088810703081c4d645062107501c2d6014485005511001d48402076400360300c3e02d025003c000c40d04044410002c03114546040d0141c00c1d8842c0c0d0301c4810040540b0368a40b81410001c04504500700268860a640000003600100c500d007800e041d000c0103042982080e0064590411030020b4100c182d0510000c0380c0c51f0f0544860a104080041c3c0c42036584024401e0b8503030078012000c21942e03c00030107a02d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 687388965 1250 687387715 687387721
    0xf050603100b03190201030e0d0f02010b2e26010f05030309090f09030c0a050d020606121207020103060302060d0507120227031216060b0414060f030c060a1214 70
    0x100451100d41c0c1c000a2031300364610112502c0121700601e1328800c2c03100c06006540d1700200301648400c400124406039802407111000c0c0d04200700c400c0c043c680c290200712110034015400608851144c5c0914183c074203010b416035440c2a000c24a458411400e110318401481c0184400940903000001400090380250b040c520a038011940b000c101502c0442c903403d16400080e12210b0030070807110b40c2d103603d000751003207800d8600c2e042e507944070180303120800b41c01201e000590509201e07601c0424039802e0070082c00101381e084422111980318003007d0b410562603600c0840941c41d0000103003218031407010001000d10301841c0040131045d2869591496a0042080c0003900554003400c00c0707030a240742c2c4072031341100e9080002460310700140079807010301c0700110707180d601040da09034040c002d00c0c040c40c0c4c03e0000101c490701308812508200c2525240070500b50204e6502d090a0107070030000f01c00a0300b1120b0303016416000811035001641050b0008103d5003000300c1d412514000e5075084480409071031102d003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 687390215 1250 687388965 687388969
    0x20111030402091b1c06030c060c1a09030d1b08100b0a0e030115080601080f0115090e0f010509070618030b0f0a1401061715030304090207060209040f050603100b 71
    0x200081d2076188603064003c00c441e6189840030803242d10f0742403e0b003170043c41e983c0075a0a0010340814801510300561a107000200b850203419911040d036806000c03024501c0d030680802c000c3e020090030312041031100f0b12600f00388980b188580008500b101150503802d0f103102800521944d40109080fa405600001c00c220345484034065418001281c140350182e071803c000400d00614400c801010b1070600710b64006400e070000b05c0c404e4142c2d8098001d441c10626070300306807401d8501e41c0300d003401103611280d000c104010060313005654190074802a42c0503200c10f0380c001804e680c4117480e40c04840e0800e44080000130340000101c80c01440e14002c1c070401c1803454913014056036000700700c0d143c02c400f440700050481c035142d4070003040903151204600d51540c40d01d00041086112501904000f0910800301c0d003041c410441350f000b40000200114542810300301c40b04085d4200d40700c00c45005030240001003d6980d40d00039804d40c4002e4540004080c0380120030949410070485031551214175000902440b9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 687391465 1250 687390215 687390229
    0x281707031a040e03210105030d0507081204050307151a150703080402220c0e1206040201051308060c190801080709050402120d02061501090501021005040620040303020111030402 78
    0x3480c411100081c3c0700c0d41c080e42141c21446422003c640014549a4903081401c200389000e05036682641141d52100d2041c00688087c45504c5024180813014843c102c90719881c0015250300c2449407064909002d0550340300d41c540036241e00c40c120b00360b07101e00100044010700e50300d00721140c800312907d540000306050341000520840d8000b8040204010001d000e41d20750105000c01111100a0301142030340b410b207141c2c001d115500c0b4142c005148070b07010044524106141665a0203c40302424490f2103650044d0790030b41c0045d1542064040c01c06001403980c2e000c0c40b80030320800308a007400d45c3d40d0300014581e9403400c1c0501e00c00e50500a1401c01809003a00c00a4444141d50366420300041d180c86a0000074078036250340081c1e44141c071030160020030099010802c94001d911504c815003020103404010b50355502035000c1e050069025451004084040b44c00c62900540500300000d40c003014480721110081241d8920420743c0300005080041681c24403591240454102c229415802c040e8002010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 687392715 1250 687391465 687391511
    0x120501062c040f060608010f0b04180f11010309290a020c3d240317070206070602041e0905010506160c090c090e150603130309180f060504050f04030528170703 70
    0x1cdd80d64150160400380c0d02a510548a80d80c100c2915480c046423040342189030700262076000d01c4240b0000c04503510707448034003d942d02003008070080e00716000028100202107409050381500e480f0031600300d400e96034060601e4000410b20301404140300c0b2141c07018403021441c02044214468043d90b0400210b50b0300000c81a0085481411603610307032860000903841e000b00ca002811262002500280524460b00050104820045c0c1030101aa4840042c0105d0f8000d10500350041c400700060b00c1c103020590000e44145200310b01104809442d00d001008480032540c0b0f03200800c0c030a039411f11112181d41c1119901c52103610f10580c505c1c083d000440c80e54040507100c91001d10207042103501b01805220303000080d1440700d80030004100c2c1080d0642c050501100c40008007841d0603004a054101130051a1003030403000b154031419101d42c0d804880035841900d5a0081d00541000354641c00039550b00c00e080c5a41c1e42d5a031f030004a00d90307284003500081c05003106050614004910604c50010380071450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 687393965 1250 687392715 687392723
    0x7050306060f0904050a0219050102010f2a050708070305030402030609010204030f020120060a0b040e07080307030e060d05010e160e2404120501062c040f060608010f0b04180f 77
    0x40f41e49a0b850704520381918000020b42c412962a0140302d080d502040d15400c60300c091303000f4003484c80c070f80480c4802c4400c03505540502c124003a00940701000040c4150102d581203150003450f00340c4580704c90001740c02c15071084001440000a10065140401005400c000307020300842c941071441d0740d03810700c0c1c543d0124000e05001c9500f201200c50000314100006014201c0300b40c9045290011a0700002c11880c1407061140e850712100c401c080c2c4001071810182c407050340c001c40c07408003980c034250fa081124805017948848204041403080c1a00d000d8540200503940d00280c01c0c1c01d002411014000d40e14824100b0094240310503104d0350b840101894042c41c0d0040e0741070309a03992200620080c80f9a402800b10024a070f0340003030400205610445c100c40860002c800c02a158503844024500e4a00751002d912060300c01150124204c2c250340c4941c144207000c006092555640e4a03800e4611408074035407103d40c1e9041103d400c0c00d1500030040e0000c00c40401c604003140b10303640d40c4040d07403079001d01030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 687395215 1250 687393965 687393979
    0x803011e0e0105011214130b010605070b1302060403050a081e16170c010c020a0210111f090218041203020309031c09080301030c0602010b030319030b01120f0e07050306060f 76
    0x314410440c3da0110314203d40b1081000746d280f6000e00345484815540742c040f5101c0301e1000000510500c02c0c0103441c0300301d6001e00203c03030940b42d40c86048000c0c1d0010b04207980c400300411000000500400190865900c64a99542c55110442c0c4050322001082d8017410b000800300403a50088000820401c40190b03c446407a1044410401364591805203ca179034541d5840d010b11112010b4002818186840c401c0715102000d22804200300c910380015802401c0c0c660003030b102c40d0a1030910455404290030102000101c2c0d420316000a06121100d0624001c0c400e0b020b0300703000c00d000340e1640c070410351802e504007940340d4140380c100b0070345c0d038481c5149008006800008500b007030800380c2c2042d00d1094104a030145c0300d50312420700c40030842c2d03540718520241d840c1c0750040843d0b040110a4840c1d0900340406c0401c1d43c5a00103003503000d42040c5416904000400703a07424610481d6229424400b031070300800103145103076603403000e10702000380d00824070a038001c604001481d03441080404609009481407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 687396465 1250 687395215 687395237
    0xc0f020603070c020a08070e0a0b01020703080a05073201090b0c0c0f0f01051801050114130b0a060207091134060903020a12210213030c030803011e0e010501 69
    0xf10384461010500950150b80c15000040041d070010748901600d20000c801a50354039084a0441214035483d01280943c00c412005c2011840d404054019520142856032801c48280d40e00710a01c1e1450100883d040d40c01c850b9500b045014402c0c0001e0004440000c105d01000794039000e40180c2e002700059203180380000c0800d24032805014914140e9134501c11281040000d0500a0182104075643da91a5030300d0b003600380510700140203440c100d078007125044804402140c180560001c1c21114004c040d038846c00b4100c03094441a0700030b0003c00450b4090082c01b82840600c006961603065144500d103010300030185544402e64004444141242d00f6034110000c9040500344901801c2c405400d080c94608030409250300491243c402910034400b00c409444100b0043d6550001c0ca00301407c4902a0901001c00184540c002c02600d81c02c1c40b1260310440e41c82e55903d405203600e0b0421185028040010056254000203800c0e00034402c01300c003002c071410150090300f441414407034581004000646 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 687397715 1250 687396465 687396467
    0x150f09021e0d020d020c03042d06080601030e1b030f0d080c07020d1e0b01060f05070b250c05010b0306090a0b152107170c090603070909120206070c0f02060307 70
    0x1203c03509150a00701755140c41c1c1c40c0c5c006588a40180c41182141501a103040d250001d9096852014040c5041003115460a000c401c9a032810004c0216040c183d46051080c203025007001b54a0030034866202608510021106050030500034034001781d0646d114011404941d030300b002015a00005031112540c68085a0000402ca190310304005031072003500c01507942c1c1003500440c0380c0c150715000e0081810166601e1000326280030b449142400002c4050001a0000f040d102d6003c1e0052645a04980e1541c42d00800031500c1d002d00302a203008c90444900711041100a0180da0101c14048000e0403003843c000e0407450b2039244204d402010b54101500107400c0c0c0480c6440c8407519107003e00f40762001e520300c0c1c0c0070032114101c41c040104103214610001480fa5007151384100c0b00090900904035405450301807005c4003c0103090340d5418050b481d004039500c80503109102420f4024040999a082864006800c0890240002041043c0b29802d0310114916684500c01c1c01d5041d2507141d46c0f1395402c94 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 687398965 1250 687397715 687397717
    0x11120c0d0f06090b0c18060307050301061101060902040611070906030f12020f061005040509060402220b090403020a12020c0a03150209181512062206150f09021e0d02 73
    0x400502d8040600c0178010801d00c148050a80c00c1c460328804030348080340400b0000280800c440910001f40204018800244a0f000340c102034000c25001040d01c903252142c0c4810390700035030803c40010300310b00005802074034100460780080680d070400700300550643c2c890001c1e000381d0560161141101002d00a9014401c004003509001d240c3c007916010b0500541c81c88200220380f24852040b81003c001c0780580c9008034090b8040e81c0c1c006d0200b2003403060081c031084040c46111030321101c06d50b01d00103150151182c070052071056200380e000c1c0101d10300303d1030440401c0e0044641041150310510048070035450315000d410680780c10403c7c0384207800e54003030000c01038460076201c00d80040004200803036084184501902502400d5442d040b8040d4460610500d182790718000c1302d0945c0003201041410765400c200500c20080b44c40d008918661304c1d01c40c001030b40d80d2808030142903504044200302c03017503d003003100c0c000d440c503101700303501e071541503e8230003000b4a04102c0c1144c0700f500052101c0014401d42c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 687400215 1250 687398965 687398981
    0x9020a0311010504091b0f0201050f150111030409051b0c06072a030810060203073503010b030f070c0308060f010e031501050f01090812160f11120c0d0f06 68
    0x480e060001b250414031100a400a981712000854202010400f90358018000c1512070040581040c00913526070b4440e10000e0b03150303d6143d040c00000404002c1204045c001400503281001e400b0503681068184412542c8107440c1c1c4110042c02849041c011080100d8a00d40000706450b01030100100d1a000d850031030b22410210801a00c5c00f2050700426401011051042144c0c0d4441032913580d4034a01641c992145010003070800700940c02104075101d250800703002c1411404c1c0b44400309204202e200c880c6900c203800c001d1500324040101305440d4000c03d1010b9000035586400b440036601d903a0045c3c0050005420320b4810100c4194941c0564400c205c041100500101280e6880500300c220300b1030f403a028091103000d1404642c0f05500c2e075014a054808840c400030080c019000c0210302d5a0242d080404000c00c0c1c00c20501a080115440703500c0110143c3c0906103140c035141040040200c4040014008001c6800001c800750f80c50b61840562042d0a0300608a00301c000d0207803401800400c614 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 687401465 1250 687400215 687400229
    0x903111c0308040201030f1802040e1507020307120914040e0129030c030606100f030f0903031a0a080d0311160c050117010b0412021c0b071209020a0311010504 70
    0x44400405042d4802180c41c052030003030b20101f2880d04c0e15040d980c15198004060b10201c56150008001410035030300c17401102100c0000d45600f8010200c03581d68021003541c2860041e0300c04035000080c400303141d61f4003604626a05151441030310f0544100d2110320380c401101e01c20307565400d10800000080d040034040108030351041c2205001204031141101a100115001c0d00c11902c070a844c0341400a40107024030380040404511551180c000c4600740400c1d0990410151611010303208038502e4000c0ca9940c03031083d1000303d00d168018103146401000d4985a510a801d000380400074600d011604402c0300485203001710301d004070450751100f10711502c10b101c1c1034840407100c00e0b410300c002000f1400545100b680c8032554403e1b044c01c0071f13000300c2c428010100760410400080208909140e440e01006201620900c10365510110601031085407400982c3c0c48504c0c00c08020040794004403100072007010704000c01c8642030f2a000f094031b4200501009211850712840c401c2c0c00d80c012000e40e4018066 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 687402715 1250 687401465 687401509
    0xb0a050616061e0e03070812060111060108030307031b0909150e0118060806040519151515030e060a0f110406051206062b060b1201050a05030607090311 67
    0x2005442c15030803854603601c40803981c9840040404913102008650324942c004d080c05080c0300c101001d116000300083c03d92414051b194191b41c00d505018444c0c0340c000c00c0030001541d202d1034a504041c4c1a510000d01b50900f0f0820000c1d005449500b0803901c5058a11040e40040d00355801d2000360281105034100f110141c1c15400001205044091004a0041c0d0404140122b0741d513a0b900903644d16058070700912a4100304801c007601400350f484804098003807002c00f184000c1c0c081026003200c1d06c203144e02c2404003442000f40b1481401c950b0000c0344a07820300c1d0403c0600b6444441710f8481802802c4c4040c4113460f079481000491a0b60004194180c940119650360b40d44c800c4003400c0390744040040d9090316400000948180b03022020303600d1120038074026000c41c06070807c0a18542d00c80f11b048854075580c900001c1804481103020301201500382040240a50528003040680100307980036a10a601c004200203045a011403031604807a44003007219683d50307407040060b450032600c03098400c0c1a90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 687403965 1250 687402715 687402731
    0xa050408130b042d090b01050d050a051015051c020408121908040b041e0b010807050112021810031b0c061a06190e2e030b0a05061606 59
    0x1001c40d0040048410464440005040951314131030540c0f81c16900c4d06070031441c003100304105c07038070358100704a40d0b01d051514600d0904010110303c02c0380c0d410386411808681e20001c101c010018602c0c1c2da005008140050070f01d604584400034000d108605403403022210b4509a00c0d25076500d0707015100506450380680348490900301d8210308035041040e0304622203900080001c44039000310355007406243c101007240025512500c3c0e540c030190007007104d5840d096481340c2000c08101c0380e20a0740d01814025010301922854400014a00a880d040850b00c0903c10401c034090840c4500e40414011410b9070049107003000304005a0040640b0910b412400c0c1039010003a80ca02d030f02014240c07405110750000c01c568014400c641400d0010221466041070f03003000001e000b26a0211000307013000443c41c1800340c401000d8007041080e4070300c0c070050005008101030840b081458000c1d1084000b5140740400254141c0c000103003d6400c94032a2a02030103000401e4041c0610306003980303105d2500440e013800585 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 687405215 1250 687403965 687403979
    0x30a0b04110a0f1b03090302010e0f0a0f0609051906030c0210020309030409110a170615190e030a0b011421071a0a09230a09050702061602060a05040813 67
    0xf50000000000003001c0d03038040d0300420440804210340b942c03d5a0703808202400e5a0040d81c2450500e8a0030b9070203400004002c265a840d40703500000340403107501d101d000320b18000d005819a000c03074000c940702d02000140c103850748101c0ca0075002101c15610b0003080c90140f803181642002c0c4043c0310013031483c4c000010083c240c44000000c1c8206d40840750304000c0ba034001180c203803007401031a6074200016540b030290718248140d03034210ba400c00d00041c00c0c100c0000c41441035030341552044040d600740000c0c07064111107468000400d03a01c4007205501901268290355220444680140581c0d0b15680c001c0400200d2915009100e100e03501050b854444601050765103d5a102294840d0050740c0c2445511700410500072800c0d9103e07841035443d003512490170001a52160a01002c0d648148241b180300341c41c1c10796a88a4060080480d800c0000e0340342001e900003420070344010412100d40762600c803000d207000da00040d40755001024210008050b240d030314098900348201010403d0801140102040003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 687406465 1250 687405215 687405227
    0x61e072d0c0503031f06080106020d080907120506010806010501050f030f13140105040b01050a0b0912010906050f040309080111090111010902041a0310150302010f030b0d030c050c030c06030a0b04110a 88
    0x48003030381405017030059860008580a4609004007401a003001c0d448800b118026940503421072201e5094038011602c8105080d400844141c003a922a840400104041c00013449458050142840c000746082e00047c03c110031444080d26a0040c42903400008011182410f2007240450b4418040501800d02481c0d4034003814040e50240c642c0b02460000040624050010504032408080c489007020481000c0200c0c0c041c1066a120301552160b8401000403550320910740700306800c1c00b0001113410030f814024100346050700304840c01c3e85450482d0311880c410a0941d50108000d1812000c049080104035004d0590007400070740040c28102078032042d01219980d050700c4074082d030480341030102841d030000c02c1d00c0d00c05c444000021500c00c42803001d03500c182d080400c0c4039a0742c10085030904d90f900210340d10700910107042c1c00095040c01c02100b04082480810f40b0900102d000b010a2004900050070510010300440903069540c00e01d050581c40350307040720501d914004503281c1c890590103009444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 687407715 1250 687406465 687406501
    0x32703160605090c1002061f0f090c14070305040e0604021605010501080f07030209070c031107061e0e0f01030b0a0f0e2e051908061e072d0c050303 65
    0x80750045a031a040f4506029141c0340034003c070350f8014030700341c0c0790300301c43d004004d0704c000c95500c0e50040d03040045449c40384915007000402081c10001038003400da0400030701a9500a00b4098280401c000480102c1d83c00400d40d401c2d600c031100d071041035455400001d4000c2c841c0c191000d6007030f0640c040320014800103612030390481d8209000d59590707850981d5110348410399400001c3d8401e1600c400303c2c11041c0b08524019203544281020100d0010f0b0301041440e0030701c035510940004452013514401040700382542c10740d02580341880380740401000001442c90202190541c1019a070315425511560b40300c03400401000b00d00c8905440c0c2c0e844007642411118126203030102d40c1c40303075452100010060f0b0710803840100150041c0c410f180c00c10003000304401005071210501c2007004c9011a07203101c1441440d004440700c0c1110541e41c0c44211f0110b0040e280184183d06000000e500036180f40112564030300c0d45074000d20804c40c500360a9200703941890440a02415501c8040104110000e20b9028912 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 687408965 1250 687407715 687407731
    0x20f0d0f1506050c0616021f15091119091d0406110708040306021c0c0e03010c090f05150708220801180f0c1503061406032703160605 59
    0x351540b076007000d80b40362180c6131401000b540302c0300019900040800c05070070500d00b20710650700c001c0203050141c0e030490458259004607640c0d40c01e00080307003a81c4900e003600800000c2c3c0203104100d4400c1c02c19003503010352040c0100c80140354201000346842204800d02070a0100f000300280c42a000142d400650120340c00c4903842d25003104400000203000998000c55402404285000d046681d0107010b504406140a00c000300302a65410b042410700640501c07031160b82e04c109904204104240c20b64800da542001481490700d418400c1d514100c08400c25240182c420b40041c810282c00c4c903c140c81f4507840a0076680b00801c1140b040d11051190780d000502c0940584000b40d11400c3e001d00302d400c0c00f80e1f41c401c40e4840c6c01d02c00c0000703802040500b1256000300792083c005a5104200096401d1040403100001e81d580f801b80070280c1907040400c04140d050710a5402c0d403030220500c0d09030001c00000b600400c401103100580814080085407041400010741c484001060300d0040c011b04000d5030207030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 687410071 1106 687408965 687409001
    0xb2b02070803070e040b040e06161e0f1101060e060918060f1e040c094106010e0d110609090f0711060118020f0d0f 51
    0x1480f482090b29001342d0728100310104011a031000d10801d10407481c1c808460007100c00040c100354880c0d00d01e20240c10700d54503401300703544001c0014103100401082c001441051580850b14403140320b607030f0b1104690064100c028a080c0e51550242c41c01d0680c0410000e642c03480c0c4103119036040380340008486519044222101d05080b81200c16600c008080800d203c101882c1c0c1114061311015410000c05504180d0b440020501d200d02c41d854099031240071001d064214a03119a040d10103d00d244a806400315405180704101c0100f4440e50f0390000002481030f50180500d0000d40b28010230b82000703508982e03205000c103a04082825007042c018000d0940e82d40303c480c1401d0081d034142c5c018864a1801d046c006140f841c0c44011081607800c1780004004000a1044450490740700d10000340e1118040b103c250003901039094481001410181018491100f95001401010300180c4c4c0c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 687230215 687410071 := by
  have h0 := BRFrame.cov_init 687230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 687230215 ≤ n) (h2 : n < 687410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
