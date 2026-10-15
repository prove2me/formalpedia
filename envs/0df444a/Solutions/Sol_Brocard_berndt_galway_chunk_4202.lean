-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4202
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:47.809032+00:00
-- url     : https://prove2.me/submissions/4860f80a-352e-451f-8731-5491afcd0c99

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 755575539 ≤ n < 755755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 755576789 1250 755575539 755575559
    0xf090901030302060631111903090605091203040308060d0f0f02100908070b1b01050705030f0a140403050310030b1608010e0108070501112a040b041e1d0d05030601090906 75
    0x40f49600a005c00202d54920040b6a01319004050f690000116070a007001d4032310b40d041e0429203000380140010400c5840c0c1c1c1042c16030359000408c07140c804072000c1c4000f4020078000c0000d139a001c500500b21742c200c2c06560740c2c4c0320651842042e046030040002c041c20829818a0000130303c03100110b0070400700090400828030340d100300c00d01c40d6052101c400a03e01c102c1020000b88054040b205000a0006050a0034043d11640007108c22102085020000070341c02e01040c015175482071500003100a441d1505d8904540d1984000c0c04103d12210703c1074000f00151300c506425105844c40b20102e9008100410b008242150690114888024480040c030000c80f02203501d4044510909042c0c0c000c00200140f00e05000101002c6150b0a041100c0090a40d0741041031f01c3c01303100200c41c1000484441410881111400b95540350404501d040d111807150403a031004444c102c83c1501080d03076006400c0711504c2c00d0b0404400340002070001c01844410350300086c4110103807149402c103220050420ba1050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 755578039 1250 755576789 755576869
    0x616030b0a061d0a180903020d030c090302060c160e160815190b07080a0311070c1401020c030a08090306010e010612051302060705070602071a03010b0f0909010303020606 75
    0x140ca842800341070700056076143c414070300c0103000f41040203401c082482c103505e004243c201002d90160041268074403040c2c3c868400c0080a250319161101000d00303540902095401550340d02c2401e118030f1035a4040a01307401c81c140d00910000c0d402c00b005241850031034004111440d2444280300800d414040b080c00c02d40000c00b003c2a0644407800842d4000304c44407043c1c26140c0c042102c42c080000c4c141e0074004044000c003c3c031000343d101440b07550f16544185506d0b00c01c02501404440310b0b008280070b844040300158104403c144102c5000d04000300000303060201704041110350503000a1102c243d81414481c40380100104281d10090398035190000d400c505c0c4405099403990340c1c1d100010b44c1603021252000f0303041e4001d03040325100c032082d1410f503075070315201e0207098050b100b00c44000404240744569500c0c24511182a6030a607441c000c0110075503008101c00700d000c0c6505001180301030300c40d07500700b80c002c5000342e00500b03550405409101c21054201c0060494a00d9100c40f03e8245460403000307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 755579289 1250 755578039 755578067
    0x180102040315020a0c0c0b0406170c0a110102090a0b13060302040b030f060d0b01030803040b06030c0a05060c0a0212060114060a050901110a02061306080108030405090f0c07050616030b0a06 83
    0x5613a50707400c0c503400c84040c1c60b107040080c02c0440090307003c0b81c800307030413405081a81e0290700c50035607180340b011102003610001c48840446610170051420003d125010300781d0134400c200c0002d030410041000003040001d02d80c0205d900340f400440c800c44000c070030b500c2c40c000030b000c50f0408500c0d203030038030f68923000620009005246460030103012030000d0325500030054466400090640540d6141d260180d402da10959054400c420301d03030041201803501140c101c00c07550008040c00c07426450541444840c0c1c2207510260320a000b01c010b2640503840c1c49016411948000300601650360611080d1000200c0010070750f070040c1801d0207420001e94106085a154200900f450b9555181d200341107460a0711011340250031034008608100c41c1c0122040c003200b690010740300d146031a030701e42400540e01d0080c0c2c4181c560100e00440811050780044d0300726908081802e19081c984205511100d203031036400c4e103481e20103524000d4024020743d0b045c807400982510448803020a68078050004040c0c09000020b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 755580539 1250 755579289 755579291
    0x2190506070c0503070b04060c080907060f0c0507090f14070c03050315040e100c110a0807060b0a03061112073002070b040c0501080c03010807060f0905090906180102040315 76
    0x400401d1040c20005c0d29596580040c03902ca580c9461b2074114060f1800340d800e2804a030410303001c59011000410682c0548005964403140058100c1044a2540c030010741a00c03180a50310000c140707240d45024210a002810f100441c1d8640c1d4062040301d40d0303100800201c04c1044c41019074002136407180c1203a0304040b02c0e400000b0394001d00c02c00240180807002e00a0500c0c855a10300b4000e00d0201d400582890380241c981c084640c84a80d02a511025550401040b0981c10803601c03001401541c040c2d8100000603003c40742c1d40d6101d0741c9040407180d603511400031440001c60f4000f800600c4038039980c0c1c00301f86031030079820501140e0025000e485070b4440b824180711042e410980079000503419640c2d1503402400003400c504041c00c0c0790140d009103000d0b582c001a0b6800c001099140c005040324121401a00140b588a1900f0001c40d100302040c4940c00400c4002580000d4650340d005806005e0360703002000c0c08090402d9090410301200010002b00350340d0051008001086c000d02243c000464074001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 755581789 1250 755580539 755580557
    0xd142125061410030c06020304050102150703060b070c0e060409030f0806062106040c050304050d0c0203031215190609030623160e0f0f0f04090c090c0219050607 71
    0xa03049010b0b15485210000310104182000688601c100b90841241d0044400c038800700d48a6400701d80b24410b03400361a026901600c23120407200c40144289501960900d00026410344540c40b1041075803080d8810780c0c040007210340501030908540810364020300202c81c03c020903d0b1691b0041e2414190010351408d00c0f0f081d500003012900e070b000488a090b0380141000780c8a01000c1c800d44056102510210701882c0340000b84404ea50048046070700994000000700802511402d080b655103e45040403a0180001e0044100c01d080b65080c450045604000d000710100c500301c2880780a03281440600d6402c80442e00401c045a0880503480949400c528080341c0d480c0f0303400e102042c40c1440d082c00d02e00d40311900100300c0701201c2e910a0031503000040c0e441801e803040e5442000000700740b82074000da0201900194030007525003601c06034803815015102050080642d11071070080c1d41282d12001216445101422640e0b81c10304c1002682c1111282c444040f030000c2d1265036941030010444000d1006e015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 755583039 1250 755581789 755581793
    0xf0d08060909070509070507050c06030c030103020d0303060305030f04140d121b020a030b0f070804080307120902090f151e01030c17010b0714010b0d020f0d142125 72
    0x403001d54042c0c04c029181c001c2d14140b4000041060307000074800d50b01c5000c0c551506c061440c0c02805c9031b0003809440070190559095400300300c1c1c41c070040f040031024150740f58000030004100388040d0119042d0780a0090b211072070101c1c1d40c010700304a80116885212a00c1c08800007410040c02c0c006092602d03e8200080b0806d20b106003440c0c810504080d520813406032000081004d00c0c54060b1140780100110403864980c0c02d82030f51425001e4a00506c1c000b028000295641d1042ea1b803030f070040c0c100d00b201240040c001c0c5c02050440c0801e456410380c60244008000303121041c6000080740315030540b400d4508500e00f05020419610040340c25040503150000103604d203100c0c154903600c81c544286090b030f60756980c000c403010f03961280004580351b6901444803055004184690001000084c10362590b812083d42046400d400c24040250310000c4c0340b001f4070120b44212004814100340c02d008029045000410740e140c40c03202d4000c00ba00003c204141c0b42c2c0d018a11404005099140110464480d424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 755584289 1250 755583039 755583043
    0x1302071205030a0e0a0f050c0901030c03030f200d0e03150a0e0c0a060306090506010c1a06060c150103150c090608040503041d1b0f0a0e04020408031b0f0d08060909 72
    0x10700d58101070744540c240c200c040c45111008101c030940718008984400d40b010003440350089d0700344001385c1050020201000468002c40036100b10100602d428059190310101c1440104600c503043d82041c0d111500e0300c0741058006648090f00f4004070010705c00100f5544444d01e080f0300040c0410803d070f80300d403912801200100301095500d00020410031041d80c4401e0300030002d2560707210313824503076081c10b01045055000740396840c4100d401403500e0111140603281c1510580024040c560050700800405281d410140404441c1c907c0b0383c1d0881c6603e500d14140904150b60b1540c0c081c140324038005070a01030f00e4000348258120384043c1041c048a80d07079801e25605500a80d03110800400c1c06080c04440250b1310035040b07100c0c01449241c0b6802c1e0340c4030015071409000b250482051064204041c45c1594081c1148240ca4000140701500d0581c55000a41c21508412894050000d40e000c24101441c0c05204003600039603844010003544005074401090204054a8140502c0d801c1010441c86001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 755585539 1250 755584289 755584301
    0x2040608030a021b0a05100305090703080a0306030302070e061c03050708040f051305070e040e0c0301020409092f10111f0e0f070b0a1205010902091302071205030a 72
    0x104001e50b81c035000100c1c0c01a4860340f080c800d409401000020500320351424450490541ba405400c02402c2c41d8141410740013070102901d43c2c2d0051140b1200040080d03001d100a0450701d40b1950086070b1036244d864040e1414046070480704425046404010f0a501c0c0c21580102e42141040341c609545680d0500303036032901c240341024015400000f07000c00d908d90f80c0c1c0200e0040340c0c03064640c6920f01409401e0031080740d10550715800020360760f4800140310718058212025103036450080e12600c001c018000303030032070380642c3c4030308080364a61a0200600c508009960040790080b5a0400703d921110030b030140c600c0704404070f18481d0300f8070404030024174070500e248111300d25200200c40c3c0c0c9448a03054883d911a0341111940a1030820f500e01400d003e010032500058400c0000410841c0c0c20030159140c0c50300103180040400c165541850b60112860180034000e280032403005a544000009000940d1140c2c800e40300900c0c01005510005000740c040d10306c15944c03503d8015143d8542c506081c0203041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 755586789 1250 755585539 755585549
    0x71502030405010b100203031005091e09012c030409090303020403025803020a051506010e0f030a0f05072d15050316140f071103011e09020406 63
    0x1201104020401c030b015030242d100c2c40002ca40700409915101c5e41280c2e01d00c003c640f02e0142c1e640302d0404100e2401c2c41d000c090b03003124070416081c50b403072011050521b00900848841045a4480b00c0c42d0303907030840009603250004030500e200451280091240c50340e80c403491080807103950746c400c0007000b81072003030341998099070b4000c102c201c4074200e400003028003045100d80040d1400c0c0e0710101c49100408a60004241ba40b003041c40c0c403404101c400c0e4602c0040080c5001e80a60280c8010140021001c1c40a62401600b5921a041300d00b032400004200d0301c2800103090107540710b85096010707a640080c03503001c083e038810b10a1400c613140b46000c03030401d0000d512003403000725065440d80d5a041900c108010350000241c1009144e1307521504202000400700422001c00c0c030030000b00e0030040070140e41c85c910300c1c82ca042404d003400c0140b0121005901c02500c0000c40350700032032480308100c01001003240f0f00c0012002840a0f919a5003803c802d0000100303c03084440d035070707144c0344c1c1152180e0b00a000240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 755588039 1250 755586789 755586791
    0x30311030f0d0903091e091109120708061003030e1e040e03041a03070906050f13030b07080702011506200d05040807080105090606040506041d0f0c040e030a050715 72
    0x1600c010004014100f40301049020a41d0520003080c61b032041c02007240d0111070000c02d44c5c541c80c03810b8007034001071002e180d4016070290f003000705940607103401c65807142e48001d02c0010281d140c5410a064280780000d0080c0040b0880b050b000c20110b03500503403904801c01c0464030310311000c04400710003c0e24030b5210060707074000d0f0515101248c0c40c4d2000c00a40210307036004546800102441c0100003c0348130454280001c50180c4500303002d00c0c0d1140001e0079950031904107003482e00440b08098581d400c001d80c401c8800188080800007020361140c1e400c0d802130414002840388440700800c0722a040d03050700036102004041d01180f00800f02c41da4020b8076491180c410340c3c590045914004005500c01d014501891161400009080905100d8076100d60081005040c1c1c5440301420840903040c041e0041c1e6010762502c5844210064040152a4005440340107000740a81461060b04201c020710307642c0c0c821490403011034032424000c0201c658046051070b1250b5200e18078038104040500e20b400d0001c3e01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 755589289 1250 755588039 755588047
    0x117031201050f0612011e09062d0b0c030a0e030a0f030e01051b03071214040b031e090c040e0d1205100f091413030e040c0509030d020a06060b04050a030311030f 71
    0x80d00c1c115551300c00c0e840026502075961603c82460005a481d94483c081140c1803013500340c100c0c3d0b428a0152b4000000d441507101055941d455a8034003900811b1003d149504001210b412441d000b1503008410304058024180b900b145844810308506244005401e10408284002d480c0c0c3c86101243d1521a10b40303012510403400d0300c207c40d581e41001c6000c480c0c0301864650300341f01c01e0065020031114121403070081d180c00c2c10b042d91240d03581c10181002680000e040700d4030409240312074609219400030001064405119010003065a035503c60f041155000104440c2d4001c1c4e000180b0003240d100ca213404107050715108040300380301820340d0003110b80c81c851090118500038039800403c01d02042050740c07505500d640000c2906640c1c0b503500107001c01d99078030544400d130500d900200e034a071703030141851820a0700780c1000c281000a5540220016004101d5000c1003161621600b0080c00381d09140c1c1e81010304040208403004800d00010303042c0900340400f2081d806080003118000d120526200c0e80b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 755590539 1250 755589289 755589299
    0xd0e0111030d140703140106030b0406151211031005010810050901080d0201110906040302100c0204150305070b0304020105092407140f0109081902070911030117031201050f061201 79
    0x9000b00c02c183c40c1407070203180c0070460f00340c032900508650003c1500c1c1500143d203010340543c020503400101e55001074440c900061038100101482d0201046074171070618185400201904682054000c807030000001d0080c801c01c202d19410080c16100e0a0a000d2029122040c116841c40b4055202c942d004105074004598580e002c00d0940240d03496400901140540d15032203109030003020245604007105110030400351400070104501d004050034030400c1c0c0307420340d0045400d030b4024184910f450b0f90a520100100001005800c0061002400303040c11400c2c242e0001700548542c1c00200e11903803654035800b450040200c0140360302c00c4440e032110303500d030b5451810244946250032541c0c09401030382800c1110b500180031b54014954482c91052a0150850105081000c1c80d60a030045204011020a00f00404d2041da040c003003011480302d03241c3d072408007000b1030419030203d00c40540e002442040d101d10b1349404c4290546100b1910341030002d840303101050742c80c051381c400c01c09840c8402c3d00000f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 755591789 1250 755590539 755590541
    0x705010905060f01080d080402040212090102180301020906071b1502010b090a1e0510081b09090d08040f02041404030305070807050c03040b030603010905030f0c0c0f030d0e0111030d 80
    0x500c20788560180d40072960b80c204070016815007481692141d070400790910a6651141510755405480100010300700380b000c014a005a075012202c55040b40c2d40010800051480c8001000e000700d0f00b10002d51410a106000c1056801000b5000b4840c0701e5942c40c0300c40003440306110750302520b842c0024052020640034000c2c0038064401119016a111101044224415004400800c02500280290700001000507802000c00400f40000d41c1c4d000680410550070601200d01034501522208103201030010800c03c000324054440b0107140d021f018011442074001050581c071941101411402541d1030000c5000b030301c2c02c02d0701c041d03441c0804800c000804d40c16a110901908407940d80034211741d10f044081e1a10f01c0744901401680d40107000822496150600031507200170054000704200312503981c5d4902c0c50b002401e809419032707008981c11410b444e04000f8510b00c10011120f05000ea21241c01281d11550031120074010001034082c80b2050b40d000d40380b40a000b142c00f02c11070b641c40c24080c503200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 755593039 1250 755591789 755591801
    0x80d09020f03100606180506070f06330e060a030f2909010c020601080a020405060a0e010320060901121521020102010b10171302030304030c060206060406061b1502070501 75
    0x40206e080c0454080241c034900b401d0500baa0000f50040380380c00d005031100c800001e0010700481d180ea484401d00c2458842c000045403401c8159450060030000880e005006100590024400b1080d01c00070040c0a59031140d003801101c0d042000d0040c00c4d8501e00b091030072009000100007115040811485402074150006031140e14074100801c00a030743e0800483e204c0c8800c0c4100412680202004005807409a1045402080007080010459a01c0d50681c1c50103100742d1098030b11904242c17000e080c1d071f45042880701c44000708854043c903000184001030303d0b01501040340e401003991018903070480780340410a10082c01c400058010ba00c03c414030305038081d00003164200d0055003055015000c504007000344884e844903584030305490a841e0700c7e032220b0b0610f0041101e40700400d17006501c2c001d078405000510255028101c102c07007107810090003928100307000d404980134900e803a40400c1000d80c090b0a1600035a0003d01c4102d14020504007804031114042d0308040c43c43c80020300108001d0150710003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 755594289 1250 755593039 755593049
    0x13150507060c1e14090616020d03210615030519050a020d06061b120c08030f1b120c031306061e0b040f09050406020d090b04030e0607080d09020f031006 67
    0x40f00d181906083e003101c21850400c10f55100764014440c0160300d2070460090700e03240054895007441603589400041e610000d900c1c1c154003148030001e018000000c2c40c1040d80200c901290140140c3d0b11307002071f02d40c6030f01e070519400042603034402c04150201a11000765440020641c0248040d090040000c8000d5000c42c00b1408050700c1c000d070004a00b40180881d2202a00301141410354000a0b1103120701c40c5c101c14005802c019001d02d00000144034003020390700419001c1c2d603200803843c2181c1304c5010300706140e41c10303003000b0f409102c8640c014500b0300d080360307101c031401c84920b071030351660340c4031025007442810002e010504040c800716102100002040c0c140040d4100c2c889010340e10f91081070301c0c1c07003940250300300b07103c119105111002294012980062040700010329000107011040b080703031110303039084880e01c1061080c00249984000300015001044a11034504803035a40d466240d4800c540c514450540c03a070b07100300d0070343da07440b229400951400350a035218010006003203401003055000d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 755595539 1250 755594289 755594327
    0x904290619050105091e0306040b090d05030108100902041e020c0106090b10050a0e1c03020105010602060c0403140c09010602031e0a0c0b0604090204060f14040213150507060c 77
    0x40822901e942084801141ea040c0c4415141030b501c0c1c8148182d50484060560a84110420819182e1020000644124024580c4000900b4140038160a280040c81c0d00c00030008244014484a00301040c0000d1590314144000fa01081c0c0d40301041c007401c16504c858074004002d014083c500341c450380040007040c400200800c0782c0ca0b1507600c0e071012101d144c141141c2220204080081c5a4041d0000746950001c50800024914000c4001010000728600721118030026002c40340400d602400788a000d403d59002500003840c020070007030494000e501c406022118000d175022440c0130280441c041480c4060100d071030395a11200301964a610030b003000d1b442a4030030320700301c03001403960419140440b420399241b01400d180c03603c3c0e05a01c0140030b800140d0041e80c840d88040181d0b2540700303107801890b120004683d6146050500761002c150303d0b00e41c0c0e0243d40100305034895013185044800031b840d030540f202c400b44000c07904101d0b00c40c06400401000d032440e0803010742d0700e00d820040c881503140c42180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 755596789 1250 755595539 755595559
    0x40b0706050f040b04031409030601090603020108130201081f0509090d0f0f080708190c021b0405130201051b06010f051512070e040e0a0c03060509030307050909042906 74
    0xe82c0c03000c4401c0444001d0b1052645801250010f44100e122811486282e141e05040006180001e801c2803000c0c1d00820350b85940310001c1085581011480e0f5014501d58a8403241003d9600083d040c600c00401e4611104e400c0501d400c1956a5407081030060000901407004926000b40607070340d07803035075504042d001c10381a4040c000943e1050b2440e0080090a40c0c4410480d2241c1c4425150000302070b00444907017000c10004182c4c60100d1040940d032020540c01407154079172040150f9060303c00b84100030b028074104401c001d002d00404040e1110f0303660a10309140e407034441c02d801d404905481d100015860140300000680d40c2c03d0009030302c0c00c0c0c5508440020910001c0c3d0180011845204400c8a00f5210040020714081c00307040c19a0b0203030b0002d4008240040203c441904154809200b00c0720198080001d0080c040c184c8105039200c2c4a140081d4550305050b4005807403030044a01d00b0303119103c040300080811107006401044200c00d002100c0d102d2100ba51240348201c401c070780d524041c8103488 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 755598039 1250 755596789 755596801
    0x90a120f14030f0702040203060406031e0b240d0f082113200310020a2106080714180708072a080f0c0610091a090a0f060803040b070605 60
    0xc4200c0c1c0d01c0f0010303030040ca403820a0036801c1c000a0f401c0103104035401650b0b80d0000001c60140e103421407405172401020124006c49103001594004090240f4041c10340031802030030329120070518217220140c119459030408110307240a0b43e0a00d50458020202903000c02c070301d11075051001410015400100c405a06680d90515010000014141c09010074214818000c0c040303006d00200085098047d0a032111101c541c1c0e120002c3c1e1307010040b01070008454005560704440c240703014885803460b90000b030003080d1915880720b5551885d401041c10341c0380c07086483d002c05e98850b00988400c1c0740510000540385071a035005410b2080484540340070400150081490700112006e000c020502c00c281c540c9540c003103894042064024180340f59040208211115183d02e08108240c45000c4101c07040c43d07400c0c1444403840c00c3c4c3c1c1013010105404291711845a07041d541d401c00d020b52120504c01e0000d207140c1110484009802158005006404009004941189404014041203008403414803580d1540c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 755599289 1250 755598039 755598043
    0x5010e03070c051905041e06151e02010b100c0501050f0f131403040806040c090c39050606040b190e06010c140a030f0e03070506090a120f14 62
    0x7044014032200501006001c189002001d03c10844840000e03032401540b628089000c54040904803a02d401410070f1140080803a4007a88010b000803486c1000d00e1004210701502440d40c0d82e40b681c1951240301d041a5a291003580128040c0f10000c01e40305114016a0010f00006800141525030b9401c117000606080c0f62442401d00500c2d0715000c2c2c0480755120080c80701c1c4d4040d40310048500400030741c821501558104043d00c05405800b02401542c24180340004104075640d10118030381e418841107201450300001401c40d1050314512080340c0800051807070910207016044900d03400e00400e230010912400040c1c10348502010380d002c00010155504101c6000c40560140c1c0384035103c50000c0c084288118090b0350880c006040510200e078569580c4070034584801c680030341c5030348140d1041e8149a03114036201e41e81ca2650a000c42442c1c030040200791208038a02816000d45000285440d050b00d480f11054010040000000c0788039209281070b00148144a20a4a500a0105020000e00300c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 755600539 1250 755599289 755599297
    0x120604031e1e030f0609050c040905060d031d010c200a06020102041a1303120206071206060c170c030d0e0c0301020c1f0906050702010f0509060c070305280c05010e03 73
    0x1400a0342c821600d2494118098034605a030701002c103071030703820014404569001d441e006400380c48a0a444909140b5404200d440c024007941c403500c50800c80e480483c2c0c04c9106d1410700700007c0c004c0342c4503d080d0070042e1200401c10070002c20500b00e00900c0340c0e04070040b070380e09404240c04441c0c0142056882e10100d007130740540d0003080c03a504104547c4041100c80c0100030714034014103a84101c0002e0340c07501c1c0d00007140d441b41d078210b01581245c2c00f0440c640d5400010707020116403801041242d242080c000901b41d8404100007060000341c0c52021000403584801c2c1c4540705107400807030741d840c0c410014603000f40140314500100b91098100c220134916040c0280d03014414000c0c02441498260314015450586018410b4010360743c40f419400840c602d401140e20545039600013203807414110403d4012103000800c601d040e500200148a5410008811980d00703541501d055521020009808499609071506a02020381c0c2d034040a44039035000081803103501d000780001c0001b41c440344071203512442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 755601789 1250 755600539 755600567
    0x903010b06030610210608060f060118050405072d17152106040303020403110a08070b0f0c010e0d080a020909062e0305060f011d040902120604031e 65
    0x14130250105031188141880d400e1201e00100d100303081d8480d184404211405a00081603d401841c20025190080d403422500070f0740070300c0c140d958040c45441007180810a406028400c0e502c58010038080c621400364a0940d50b0b4100301c1000d08044901101c114180701054000882c00744502506c0040405452a20a0642501500320b074000001001503001d1000e0094107824101c14401000d00c00820000c0d10461098170010303038072030a60070b051403203105112191f8414500400103028005c0c0115446046940320290f075034945400c105150418094100524165071900c1c0c00c0c1c900c04c1d00c00245880e40140c043e2504940d0351202c1ca0703034105034490f42d0011074210042e03401040090038002151003203400740c40c1002c1060801450420210007681460800181e160814440e851403c000b00b00c84440302401e042500c4040300e8010030880c1d140d01c180c244102d58821842c0d0640d21511000f0101803062001d55282c0c2c41c01c0e20f030162000d4003400100e100c4001004809031f10900864030b0301310b082 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 755603039 1250 755601789 755601799
    0xb040f060612111905040e010f0906120f0206210c0415020303160810080d230703020c04020c030c070306021312020619051905180402160f111201020903010b060306 72
    0xc0100c0b40301a204528140354081001070800c000903011f0444250580038000d01e03655001260700e0f044206082d6002c0307170031200b1000720180560740000c031603400030a41c143e4184c030a641c48103000c2555400460809140700e11903070160080001c003002003401482544c4001e2a46400403a03001c00890340c9010403151045004403499881101030300544a140d846400d0400703030b900d06a280d140c01c0e03041413520080302c80424802c40042d10604011501c140d100000310401a080100944000703580d003c514480d18040c030350000f17540180d104140204c07600004200112a88144d03240341003402035211848040c076213100300d0004102c00701c00356981c1040a400070300c4903041c005406c06445001038641001c406010741045010130030402c0742d00c0d44404510310b4540a454860b107051101035106036950716441148108401c20420442003610311589070004011102105c2c2c80c94000001e020244441c3c0e440040d04604210030541500144500c9000350300a003e00090039003484600d00040d202c055101d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 755604289 1250 755603039 755603047
    0x1110408060c160f060b0310200309150c030414010203130b090a140706080a05090d0c030302120f0103120903080307030c1412040b070c050706120b040f06061211 71
    0x110111002600c41402540324100780d0400b0707135031101c404111403c001c0302c409444448035449031805104c90021031800600c14082c1c0900e02d1007413241e034a40a209207584410220201e40c500004100d045210549503030103c2150401000440c1d85030000c441c02c940001ea510000d14038402e043c000c1d40e01452801c0410035001240303640354810510b00411400481c8a8540d1800100341807010740e08420340c642000e46401d85c18910010401000100b094103660b041a0510070303041400504507805100c1454180080544ae1404a010784503059039800907222040922500303202092049049a1044488071101c2d5071003d03040c0c40d19140c80c4406030030b0711000d00000d00118001e400a0000390742c0e40c500320115140f141d22142441d0003e60b800401100315034200f200700410f50344800e41041c410700303003074982111a913900c6554000078040e0000b0030000e02d0720741000040759001140c1c0a18018014448040000b04400082c2a180301da90000f42140542c0041d178242c510a07010000345852802d468 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 755605539 1250 755604289 755604301
    0x7020f030d021602100e040b0103021614121c2a050309100509060f06180a1e020307030e07050f0f0910030b09030a02011109090712061205030306030111040806 70
    0x350400e091480351038a84850200050b642c000c1c0170341010180307803240445000c2c1e07141480210b4440050b01414948104442903640040604030906070340d2107401410700941c083c100606211101c510a0350104010030151a2140301003040c001c83c0503540b5007003140c1890300c141481c0c0074180c0e01c20003d041036500c50000c0000c0c1300d0380045034401d80f00d03822119030030b51140c0d28a086400072207400c20550000c0082c441c030003d0110700140c04c110f0440c0c00558a040710320380c0044041c0003a140c000c102d641d404a921580d00c0b50b01c03805400341c0c9801360854807883c00382e070301030098108101d070f28a01d4062800041a0381ca05000c42c001040c1c009807420348050400fa0a0165403400a01101030341006884004001501ea03c8454403070300c107000c081c60310713013006410207400e4034030b00803813143d1b800021301c5282c80c1781e00c03100042503101840c2c0c9465001d01940c54001401000b40da0001c00315480041c50801c144400040114003a143c1540200400c118040f0b42e041140514062000300340c00c0a13020070300e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 755606789 1250 755605539 755605541
    0x10206131a040309050a06021605030313060302030a1413050609010e070920210c03011d040303060807060f110309030a0f1505180616050a14070507080601080607020f030d 75
    0xb620034407a0510a038501e031100e0001d504401c3c69402100140d1100802420840d002c4c40d2070f80007030000f0360045040c010503843e900110090750281100301a8007100090580e00180c0285050100a14842d4502c1c10b2030360210991076040c041c180d0b22071017090085140b907031051064041340700511018107540350074004103502621030001c07443e026511500998807844981c0c0300501c5500300d044410713141c03180444200c02da465002444041003507001d01c010002c3c0c2d034007580f0b251000c1c040003020f0400c943d0307945829002410190488007841c03180300c0011a0b010b03001541a44400c40585074008204050030115941c0e1040c18203e0740c154115000183c00102044800f880003881021051300d0481000c406070111041118070410345c00c01e00301c4141500405008550300001c0c0720240c294a851041f2000e80284209610f850030003180d40000e0f011000706030240c401041e404010b0703400c56035980380d0440c2e03101030a01600610380110740c0402d48071800002c2200741350000d03902030760506401d120700c0c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 755608039 1250 755606789 755606791
    0xc0b160b0421021b01210509010e070f06080f0606120a1d010615030905101e0c020d271802030604050601110a03050d1d1005010504090203030715091e02010206131a 72
    0x11703406c01003580d0035500501440c06800d124001f4180005a0039038400640c41c5882da10ba8040b500440c0f42c0241030045035807112010b83d1001414080c40030070745511001c02d03071034820381031041441480d11081c090204c00f281c0000381d801c50080e44c405c800d0880f4035012400c9441c2c52090382100b01c000241d140d0307d24080d4024556003030251081c0c469481c004483c0c00c0946c0c08010006110803000020000720384404d10501c002d451451000380000c2c1d05000c0701410107041080e6200c00040864101c0100002040009024000a4440c41080c0101075082d002079082581d120313201ea402c250024105511070000f1400a00803c070003003942c02c0085c0c9042ea86640700141c1d96100984480846030340706071700010307000102c108900400c4801d200c0200c00c022114107801c02c0303201d0b40c02c00c1d941c1c40141e42c0010985492641001c41d160307100c000803012400801c07017000010240304413080c000300000036560000424034001c0c1c0950349076507078002058076a203185e2030000702100380b41c400321541445640401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 755609289 1250 755608039 755608067
    0x427020405040618032607051e090d0b040203010f14040303090204060b0403030518060c0c0103020d060e0c03070f080c04170c04020301090f060f030c0b160b0421021b01 74
    0xc2c002c0c486040110700080c0e42c42090b00802c0d4102136014035061500e000e403409040d9496001410304024030022305c84d110b03900401d00c1400d4400103010404440303c00721002c6000003001e401040c00203141c01c1d11401d40440c1c06074440c0d46811a40c104610312402560710440280b564400107a5031a40c080e0020281a07130213030f030460703541c45011591035050402480a5030007520360030b031038000a4180800c11302e010b41c0c0c8203008007801d0140c24058500001d62a1000c1c500742001358070b902e40036010300e0040110f45d1000c0c1602203c1024003600c0f046d000d0065008d0102a582c048021818090135034058000303803100721b8900401c00c01045551180b5103400d02ca00c0a03201503801503694940002c0a907003007a000501e64036910050304d800c1840c04d1050400074000b2090170070b540e61440d12100c1e181c00c0c0c0c83c410450b00010024640500b900c2c25094110f0b16039100c0c03407100071400c06007030983d4075008031043c44540401d014181c2498500008041224404c1c040404600c060b09800468984190b1040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 755610539 1250 755609289 755609291
    0x180901062310090b0f0c1002040306060609080312010b070f0506090c030d022407271a1603051b030c0d081003110603060f06120604270204050406 64
    0x1000c904144050318040305003401c40400315001d80300d5030810074950350030140c5805110a0250400646180000365409110301c2c60303039143c68150b010040390402448034001001035100007008020410180e0004040e44c038155a07e0110545803013400d542c1e0b1080102280018280700010040c030584a00107001e068410b441148041a883e17940529000064410a0036030700414600300540c04c1c02c11282c0e90503145407000381281c3e000200340200085014a04403120400b520018200501500c007000070b80e101d049403079110398451110f880880f0251301408088841c002143c4d04502c1d851802d40d0326070448022040700000d0180d50503200b95200b8a178105058442d41c002030b00030302c001c1c030103051607411001c0507149000404038020201074008060240050b00d001b014000700b104803c00084480d416111641d0300d44900c0d00142290100383c1074aa0b0000b00090fa40b1041a4000d40c850b0003900c0c05d840921162110f50405601b84406025214140181e100e00f100540f07456000b0503003090003464 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755611789 1250 755610539 755610551
    0xb04170a1b0f02090703060923130609020d05010c0f0302180405150a0e0414060c120903131e0501032d06050603040f120503070e120f0304080a0501060504020405180901 74
    0x3c0440e501c40400c641c0100401d5a42c1400c00042485014100d8072000d014182c5042e41102c1c100300c00c400f007015200401080c6081070070f00800c01103601c015866138009048090740203d81c64100c0c0a460185d041d074000610b18182056481d01038029038041d8034000141c40c8007440240300307120080200402800b43d400310305003980d900303071101e0540c0300240c5200a0000081d02d8070b802d0081c402004c0341342405d440d6004900b00300c1081c400409903501c0b000300c070744071220540300c8403145480c1d40250701d01e000600448260004001c1c018516488407507201d904203071310441c0d9940054045680201d00c44500045168000000522003600400e09540c0c500000807103541347c07408280b03541c104650460b640c02c2c80040c00001c0c4060840610000786042c40c04524601e80320100030106699140c030799002d520740c550702040d06041441020405003190003242d0310385590b41d2907580c2d2009615000c0e2815440e008000c102c1e41054000c41e070642e0806080c030111242d55158507918060001c01240d1b481d5a944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 755613039 1250 755611789 755611793
    0xf0c15020c0c09131e05010b1c120f09062d030c1407080d050408070b0a0b01090f03080a05030709030506010305010207030e1027050406030b04170a1b0f 67
    0x21026024280d07040005150707a40805082c0400e4000261100c26040c1e0207803240c03400107108001181010070031084009165409103810350240c40b03203042050340040c0d00c1106404100703020f50850280740c02403560520a14482c402580c2c0b0301d24829600f00020306201c0207003c6180541c150b030503142c1c4400d0004041c01d6641401f0680042d590f244480003036101ca0003118400d81c0108039000c1b1002c8110b281d0b03d00a100d56400c9624401d201c40d41b1101500da100050a2008001c15038940c00e4200c82c24211500d0000c804800a002c0001c3d03490101d44140404181c5428003120882034a5110020f03614100140d5810346040d00020441c42c2080f0040d80040002601484014000c5205100242e200d60851801400b4090744880c428003580c101d09120f42d00c164045000c11f4000380680d0302861a9491801d4401c1c0c010306508203581281c20302500004101403000c06521803030003110000e0050b0701c4000b0003c1e045c0300e2400030400088038103100010b0800300b481790300700c641d100c3d00701240e42820035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 755614289 1250 755613039 755613041
    0x1c1709010c080c030c0d0b010905060304060605130b1c051c030b091506161b08070e0a0510030803101a0c010b03030c120306060f1b0f0d0f0c15 63
    0x11500294140d44415008280300d401c0101c4541003500c0303070211411841c16076203500803401108051201349440300c014482c181d0203003d0a8001e0300c0c0240c10a9640c4c68141070040c0a00968890075001d1010003000201d10303036103440f0320540c00390018240c0d00b243c0701c10b001000740c00c0031441007514075001d0f182480d0140c500e0003030394001080c2c680d240402c490f40003c08205c40444010501c48008400d40c07000c1243c0d43c0c49008481c1c4110402c2d005040f4010136042c0b103030a001503404a1125010440d00200e902c640014009080310030000c801c41d100c2d41c03910800350544501ba11103511135400e00c0c40c10310016000501035039101b210785074208422a038908076500da0442c489801c00103203000048241c81110207004515007444181c000314034000c220302c0420703130320382503100c401800c03642c00b20104495645100c120f40c01d42d00c24600300c58441b04101c18082e01d4100404003643e0340e105e4030310307107e00410001c45e49810142d103d0f01c1e03040c1c09120511095421450284084582e2104a15802c22280c41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 755615539 1250 755614289 755614291
    0xc060b060f1204061503080d05250201061a070c0e070c08030112050607020a20010302120106020601330f020a170c01060b0306060d0b01050f1204060c0509031c17 71
    0x2201c112182c03c107400d01c80100c80036800d03030a003210ba6450703040c00810343c54000c4840701b0030704403000240c2d95030b82012503d5038000c010b0781100d250120b00c0c400e0706640e0305401260030380d0520007500c081802141c020024900c14032100600c1000b10740307030402480304c0e403a05c0340d9404002800c0c1142c00d207140303644520381540260400191a04200100f4003402000c10015501c0360090004025031074950701d4900d41c08070b80003060182c21440025410042c0d00c281c05a0300c106a055800c2c954650f180e4074080d440d24024020356100d0071107030a1607208860b42030300300c02c801c003081c201c440101c0712106000c4a1180304138a0320002e500c2003211030b10005000d245034606403103000031036503140c81c40c10643c582541c406501c05100405d044c0103000c0756591b410f0845161034441e440000d51094842c00581d014001d804840000d410b0110301406400c003641c01719031141d40b01d00c004103c042d603035040c191218020092902d4165025190002145201d41c6840440c1c40301410510019580140b095420b40c0c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 755616789 1250 755615539 755615557
    0x14010302071e050d0306060c02030c0418050f01050f2203030b2b021003020406080112020d0b01091b1b0b0411060d0e0c0102070b0d05100b19020601150c060b060f 71
    0x1010000034201039031705225250242c41e103460150000380c40d035000642d0702d060326440944200ea42c0c085441d4201180d40c0c00c6810a5800801c0e101020103092500d8000c00c03080300c4101c90000c0200000c2d403d0030091580c4400c0b50b412038150310050410fa281240200340704101290405c0002d01c00c0e1b20700006c0c122000509503002c0c0c0da9603006404900c1881841055042044140342c0103020901c060b6070000342142c10b45040b80e9401499034040d000103400c05242d1200500520070700c0001140d4000313290400312010b4400b18000703078049582c010440701e45500e41c1b0b43c2800c20845403c4200000d000d24809034206009540d0f11200c2c072903140000d54154090801411f40a81d50705000303032021030500550f12851001d001525516142c012280c0c00e92081c224408440c0355100006408030080040803009001c00001d800e0700c545100d5602e20100500d107002801511503d000010064000c5d0041311038a0700c2d640c1e403d608500d13a56103810191901303441aa900c0320080c030940a000d141440500401ca07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 755618039 1250 755616789 755616793
    0x30b040218042a050c121b0706080103080a030f1103101d1b0d0f1508011401050a0b0a03270c1715090a0b1008070b030114010302071e05 60
    0x4414070104002c0307a403600d8026100b42501d656101c14406488282000c0c84140c3c24a1541c60036104065410491844030b1a000990003040100d007030994540f051010141ca6030485042e103807180300540d2010300900c001400110700308a89440113100f5046002c4203981d0907400701e1181840c0c42140340d0780e04100d6041989201c0040e04202041280403401f800101004621985007000c4030820f1704041181c40b940c1e900c860005494000810030f6100b1864400c54240c1080303000e840c42207502c040d41c0903100d10031441d070a0040ca540300c0411821054104c0c0c1008040c060700e1440c151521035070381c020201d09400c1c10750311300061000d00405802d440301441c0021319900000d60515041c0a103489070340140044045a00382141d46200000c1c44202404c2e181503440c0e00e945e1102d2940c0c1c90000645401000d44040038140100264006c12010948000c0001c0d6050b054a92118400b24007091140880c8015031010814055010354000c0000e280507080341020348601c0244414180c0c0c2c00c5200310340d95 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 755619289 1250 755618039 755618077
    0x10021c030b0f0f030601062f07030b0f060d031206180f200306010c1103010c0e1c020105070210050c030c0c030115032109050423090a03050a05030601030b0402 70
    0x5480c14852140241000b1900000b0382c1c100400800e40d110b80c1401200144040a203a81074089000d008c1080312034040020a40007032903039088a0349410585c8005c6070412503d802244403440540a001c0c404d4001905802545486413000c94207800030488142c00d080d520400443d5807640c1c1184502001c0c2107010116074003030102c50000458903051020003255411030881450b4451031421039400420034a0455180b1a5500700204210030b00004a54150320b41041c00041c5500005071960180048074525035181081d00c503c945040300c10030003800150200030304401458690144280c012840c60046d080c84400700000c1e245901580c2c446166038020701310607c9601d4240500400080001e204210440c0f0710b569100011a041000a0600a4100440c1c140c148101340305002024000c20500c2820070765240344103200c514180c010100107058001560185002a055141e00c1d0315a44062501c0c8295a085030a50005021641019100d4441c0085552140090901188042851528 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 755620539 1250 755619289 755619311
    0x30e040207210201052403011112040b150121022118010c09120510290a030803040f38090a020a0626040c0303141201030210021c03 58
    0x400d6080b40070344011a810001000300e1050000a9580b081c61050905035056003a0000640905001031084503281000719045400701c0c007104c03a990042d17000700100b12603a02c580506110b041290718440f40170a0038007007000c541c1c041400c102160b4001005005003005207034030a40714080c2110319086841e00035a01801981c401d040080031001c2650b00c0200600542c12002a000400e544226940c2d4400c1c0c1c1040e80030300005004090800b803408c0c00812043c4007821218811484000785082d0304140703250a9411824420402010340e900020858110f40e501e0340c441020002010081300c7d01c41107401c1c0f031f48442c1d010302422806125a8031620501d18401000d01c07410100c010182c0c54254801c0c4e590341c1c0036032030310750001d010740e01d5600e400d0494030b20002c2400064000704c00e030701e80e410441394200024007a51492000550b4425a10040ca501c1445200d456a01403551090004140340004000501e841d00c1111795a448600503510440c0ca0b42c282c624511070b8000214021985550030100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 755621789 1250 755620539 755620583
    0xf13090e0601180504020108040f0f0b0f1506030105060315030f0d050307030b01020c180a02090303030c070b0603030f030c13080a03030e07150801170f0f1f090209040f030e040207 79
    0x543d0540e880c003c0100e850650002001c0c0b803409000a8011041071840800340541c0d41c2c00010101c1d00301548009600f003511152018403800c07103025041c01942d0700d8000391403801c2070499040741c00090810341561114a400c0c031061600d40c040c168144203065503116050028024036150958a448031030301e07031030105006802c5d54105c1c04201e0444d000000034112603520200500305003c0e2000404080360340d1100208000e22403080c8203541071002104011f050001c05000302000c62007041040003a40341d401c18180d4078022185100c8811000744000388400c1c050402400142190191440d44140d0b41d00c0c05a007030240c000c2c001c4d00040d445e10b10000940700200000c200a11301d80d40e25038003582c2c401400608201060155082070882203140d1200c8650811001e80d58891076021350b040d02d00070b60446a60b4000710340c1d0401c03019111074051240c03060a40315001e562900580651080d40d90780d40c410088254840c0d080f8140240d04074201c4054a4502c0500041c03441946044001c0d505014250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 755623039 1250 755621789 755621819
    0x30307113601050a0510050715060909080306120106080706050903010b150d060e060607030e0a08061608090106050607020906030a081b0c12150c04050409080316030b060f13090e0601 80
    0x2400346c0d6904a8070512164004100c900d10743e005403565600540b044c0c8010041e2a440e44411040e90415410109100801c00294090724085074a5400282c0809a190a890031032040c685d03c5e402c1542e04020700c900807030041c403101078028000a1201c2c1813000240840d20b5000c00382401102c08103810251100c14070590001d4180c0c003401d04903d15003c00007031528420b500c0001c1c100310f450304c1c0c0b41d0055120a481700c0f02908800d4143d55442c541103035601c0c1300420059280340042c4640002c91031058041c420740c0d090f68400760000313180114035000d01c0408200a418650144103007140500070030181c1000e010f20724050b0244402c0f4130803111601e807801c000c0ca101c03940b0900e1944410b44858100141340c91200c10960711400c40c03030303032215116011409194450368119040840c05d808008c410360086111b11a80c00f0030f28141010020210f08980c00a4109500600d08101d0000d103032075000082d0120050340040510203580303c020381c43c1551940500300d505684440d00500041800f60810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 755624289 1250 755623039 755623049
    0x512160e0d1101050906120f060a0905010515030403050c060c04051216090915051006112a04020d091208010e1312200714030307113601050a 62
    0x10700d08140300ca40b6400e6100c1003400c0d1080c103101d40020a01065180d55050742c0c10f850202540b808a4506002c40c1c9a41c02401c4618520800b061000450f03541e030070b0300c43c2a0694a000c5c1c14800b0442a0b18911481c40e44040d03c1542409801d000494400d00100725451040ca041c0403442c2d00e551411043c8a0811428240c056142d04040280c100001203030702c0b65011582c2c01d40010941145604028007151544a20071601501301010041d0401c00c0da5554000c030f9400382ea1741840f00303c096100a80700c1c031054032101d000c86c428502c0d9401803444807214800030000184014a40b1001788800780c03c44210b110221114031078000d0741442d80350010703049401000100c0001405180c0b4285121841e050800c0040a10391010b0f01546101d2040351142c3d2b01400030043c85401602c0418981d0341c4440c544655050065000821003c604000c410746070708590251944501403c1c61003000104440e07002008044201c042c40d2000c0d0342000d0320840b6110220500350185135040c801030241340e4206d9084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 755625539 1250 755624289 755624299
    0x60e04031e030b06090d0303150f080c0604030201020c011d1801030b06030a050a03030c2a110301021312050f011401060809190b07030b0604060e1206130b070512160e 73
    0x1e0804503840303000496034007071710443e82c00303030303103403035614041d4003e050f80280e8a52403280c142c40450485206610042a601e0f5082210040120101040464404e40c00001c1c01a080095004019402070300800b0107210442009194a500d40c00400d11325500f82417452503808905004105012644200c4c80e00810158080d10601900d0349800c2d55070182400c002b010581d030b0302c12902540344070300d0a050321a04042c1803160700c01014060090440b580000a40c0c0d10150000003100c1841c4c14801c90740e035000d0b01c6121141c2e0600e0001000c600c00da222005860310300680840f00c550b04801e12450702d9107140f03604e80410315418140014910040105003031001d5202c500d289191060040d000c2c51403e62001040c03889507112001100905081c104040c3c0044003c1800701c0c000c5e421090214004c18103848003410b0544102c5011b81d42d000c2aa2401410300b040c09004c0081101644950343c02246030a0540c42c11464080988240e40d084800b21000e10384903419081160344400480b01070714007102c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 755626789 1250 755625539 755625551
    0x5040e0d1e0918022b0b010309150e030714010507020d08040f1419290114150c0706030501050a081c05090307090f020307180f0e0a060e04031e03 64
    0xc0252811207180101d84028510400f0000da0a01c1a012598941780160341c1049081c1d1842514411110350768480200f6401c22201c400a94840c1c41440c3e40d60b900300c2880314690911441440080c946150800480d0004015000104903a4143c0310360200200f8000540e17413510420007800c18101107c45000c00c1907031014440031480302c4083c2c5000c10780011503401246a00b0035a07501d4504010345030880781107020155001d101c03d4101000c1a4001034100040c200360380d00c00b512000000b40a0007004400c84038900880d402c180100c2c4005200045e0702c0d43c5403825000100e40790002c55803007c1c00007a140d4005211070f00348501410010041d90008081d89101b02d070040701071540d0350b10301c0c0d0108800030500340c00f69a03003001120001d0814603030802c0351120269160029600442e0314001241c00e01010b415455405898001210fa212404482803820840703070105109010740f001034a1500c2d1040401c404a0000440380101c1c0301c2e07260660030b504444030b00c640800d802c50f8001c003418030f440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 755628039 1250 755626789 755626847
    0x702040501030f380612100504050c120a0803040f0c0f050a050103050402100e03100207060f050106091a030406090c0902180913080f0706061203030e190602031005040e0d 75
    0x111001301c81414030360300d81c411962101c001c01c250005080400503d40f00e19005800710300c495501580c000c0d4060303000e5070410042001170085459861882100d1940440c0052000c142c82c1409150030602c181200300019041d81c03112010100103070000513040d0002c801c200614039114101c040106802c0c20f05104070b192940001c0c5054012003000000d00c1052166243c0560301400458030040d40c100b0211744400031401e0a40042c030440d100c1c01c00c2e00d40347c0000880c1d5035014074501c500712000c08032091044804132094428982016004545068030740c0303c8900021803054014000c0c046a400042e1a122400211000c2c205201c0069000d000340034103125095a1942c1d6101c101c0790070070030f1540e5500c5a0451203115108403038001c1c250303910741540810a0100400c204401c24040d0350f003404207042c02900f041c0c5641e035a481c030b01d0180c1205104c080002d07901c2e8014583c042030f40711840008c207503070384041010380300c1e9522002026001032540d007640070740200d4846c0c041c0b604085039103c488049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 755629289 1250 755628039 755628113
    0x3091921090f0902130504151d2505070807080702040b0f06090103202803020a020c15070203120d0608010b030304170f150f010b1e0a03020702040501030f 68
    0x54003d003508150009609032419000408110080002a1041041e515120990b11400a40b0301688850a0000410002901090f0701c06c60059a603202104250309862096440300c0901c03140a20601c0b4050200001084038074014024880c0145126580c030903240c81000111514407425030303c11200005c031025142c8498050340c080300800c2c2000541c100202901508000400c0d0011950070800100401003207000e1840b24011012b01c03030038030f54210b03202c10190180d002d1140802d006134440e030700d04d03039040c0307080a04490040c11981020703160402ca600803d0a2003880c00c1c803685002800118046030082a101d040c1c002c1007500000c104400e0b4002c00a612031245100e400381c0010350101126582d07600340101d042c0201d10000b01da801c260109051042c0303078000c68a903000842d16071300014a1081c20411100d41221401c1d11801800e10101ba5140a4000781d484100b0181e003400920016112132298502840c0952640d500342c403854034221199030b4124480110b8098a460041501d000d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 755630539 1250 755629289 755629319
    0x21809070c030509030a0204051005120316020913060f0c0806030705030312060a120b060f0103061d0406110c01050a06090605030a060905011103071709011107080309192109 76
    0x70510b0016031310401c01000901d05150f004010398007510781410301130650030b1900f008003222000c0d2504030700f1524000b94561640200307100403840080380341d4050018a41004000d03030002c9100041002403103592516011078000459180d052555081e0a00a0075000b4400f1544600f01320001d00c031103030515020035100c0c050030b688419852046030216405a55983d40540901070b040201c8050601500700030060050076614640540c1c40c100e00c41c0c205500c40d001d00420740303a0300c0c540d10000c038101c3c80182001050040c804d035899035072488040c0075040a0401004c1032600034002165508001500c001240c80300d502406565103051801c1003683c5010030951a015007106000170300c014241881d50244c0b20301002002112400020070000503000060004036a84a2031860119500c2c00015401c0300d9001210202c401001d10101c0300140c2c3d10340095030300190000c01d54950203011450082050804142100d400401a1158480003805c00f04084034880c81c0c80d00380641440c0110503c1c20303441d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 755631789 1250 755630539 755630543
    0xc0705071e0b03101203121a06180102010e07060c11030d021218060d060620070902090307210209161211090915040b0d121b0c09021809070c 62
    0x2000710000d52031140c140300b031341d00a043c41100c03080480502d20307004116011a44035414100d03c0c003c0904c0007012110b1510081e00800b820311444c1500c04002c404401e402c480b1080d0456403a2602e0380a411010303c1004000c010584070a000100e1038074120b9203005060700c0060099001145002c0915400101c802c1c00898030740303406540304412503000d00000c0342c009a45401ca51300003503d40e5070808a6000d48102c07007207582c0321640d500100d61001c0d01c4007516507407a01d40fa400760a0070710144085600034940f88a00038102c48006a403038041034007200580101784200b500c10040841542070034008194828040804005e8075812100c0141a1040b041902c4106c0c954900c070f139811081401013100d0f005100100a09298504031500c0c44608603040a02406103060100700c0c4200c0c10440c18800c6665840301d0705508021051104540c410880107241da80203584280280120340a104d00402415180d440584e03a1041402e40e180b64000c2003040318058503859007000400c40c1d0009081c40559 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 755633039 1250 755631789 755631809
    0x203060901211a06041a010e060d0e0f0d0e1906050f04090e060402030f030a05090f0409020a030b04031e1e0509040f021306020106050603041b0902030c0705071e 71
    0x4104a80400042c40d54074030000d101203a4980d1003844034484603480c0f072080100725014006a0410314000a010030a800303640e01003401042907590714640b04018050305800c0e904002003521940000b80d15000c440304100d8259000550500750050740102000f020780c0c13003680d0705581c0c154045000044803031907104150811501280d84145841c907102264000c100030b0b601030282c0c1d6400802c0a44522040d00c0880c844d1085030103e50081001000350341000c901303911680d0900b9806000d2181249035040ca40340d119a440c451800165241c002050280d030154030130084a240619002c0c049503010142c00040c01d5003249100001030f40800440f5513902c104a0804800e0700c844000d07152130050101442d07000c1d040c150348450202c4141d001d44070304400969042a00e40e03950f032042e0300722590f90282980005082000070081100c40180c80c00c40c2000080121515035621040002c98009a9202140d41000600b400500070b040001c2c138041e002e6640d040d40e2805145990700c1c00c81c0101d208a1900d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 755634289 1250 755633039 755633069
    0x30c16030311070605160906050906090d0c0f0612140a090c0e090d180e040201050c0708070303210b01021e1e0303090d0503061003020c2401090f0203060901 69
    0x251294102c0184154450407842e225801460204054034046410240c1c0b4442681c101c1c07201d5200740042e4044410680307545203041c00ba881401210362103202a15008001c151986001540c003410f007130010710704002030001803414003c008110303406403400c0e4200141000404180c01c0d180007503c641101ca550f00009044025280501801c4142c2c0d1043c800d8410001c204803410002013500c041000a5075281c41d40b0b0440c174215101400c03a103004992190758008005030055001d040200001d111400482c0c4401ea6035a00440c5400e00540044000520305200c4d2404402c0d4507110410390040c10320b090094448480000f0f517a1090070b4901881c181800b0428001c0c0b0200740907501e1420348071f05a0240060311100043d0b641c0c1d109031000c107000d100e992000d0707401c076103c1c03003c2d03a004140081aa2002e0550084101e010703400c0004403c005005200714aa0400d0b911490803c414000544d196030350341c0742c99140e20495901d0000341c0e0307295004008001241d60b460b0215070545800b100b10a5036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 755635539 1250 755634289 755634293
    0x3090501080a18080901030b0603011202010503040c0b030c13080c03060c1b0609060f0117030d0c1b060f05060a1d0705040b0a0c020a06210b0102013e030c16 69
    0x3034040031002d040300031900607400044c4207a8200401c008502a20240940f4001c0b0040c07100e1072000740309851865500c0c640c200015803207100115000f600a0b068044255212440024a607000351103114040c4c0001500c110a1852520103800400c28000500120940700001c2500c43d0801808030140c1c80000804c2c1d000b401c00215211755900c141d00844610f80b41104103540d4454055a1034a102c80c0c40303100004416101103410102c000c03054020358100740e140303444c1d07101030701c0b08050000c184000d010b14016800e01002089140700c2c0603a8010a4511101e4010021568090030309801804118018400740c0420a40340704515103007580c106440e6217801088819000716000300919440000306404816030084d0481e058074000c90303680142641d20711003515195402e500034111000c4402a44201003556030007081c0781034040c0004140d2001d91080440d19074502040c10795006181040c6a540810b500030a030070110b0080081031442c10700201c0030143d40613005150988071900808641 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 755636789 1250 755635539 755635541
    0x709031104060803033610050f10030f0303091a040c0605130b0d060902041710090b0c070614090d03050a0b180405010f020f070213090305090d020a0302060a030e160303090501080a 79
    0x6244003001d06e0007442d1181345240f1501d800c002c0d03c41c0e4090034103200110744104104007070140201c1c038604c1003e100c3c1d89580e50784650403440001c242c00789590b400315003002c41c0284001c04485004802c890f285403805140000450502e500850104207043c8010100130140350f0365041038402483c401a182d07004030360b8810107030559800c0036038805d001040004807180039907030b0542032814001c04d4031f844449034694003040310f0310590040d20f140c110402282040e02018000d10030b06018013800b0840d00c64000c21180f0100040d40d490f400c0d580014100e0350041c2d0706210382038000511074411300503030481000283c100c07070510358070031040042c18001c2030410600350710510b40c880801c070055403a684904104d0345660499807081e0300840c807654621943d04030740d200d04668682c1c10780f02c05090145036402d0143c1c4000140040b600300341e030347c0380210250340d4072005404100c5284c0c0d004103000d2407030304005040176104081c0500c101e440ca242400001d0700304000b4400d40e50203182540996035031340441e074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 755638039 1250 755636789 755636851
    0x210501020c1203040201300e0f010c02060910060e0714040807140f0303310b070c0906050307030c09050714270d0f060902010c0506070903110406080303 67
    0x741c45114103100d200a40316401c024520980c001d03202d40d0a0b00e918442d44000f010500c10315941d07a0b40b007114144500b01708981c860182403080e40c3c200c40449140c800942d0071a9110710342440968890020001c06c490100101120004041d105000c010b207800c03010344103c1c2e00079101c4001d10000000d01c0161071311143c00d4034001c00042e41100c6205503501020040c050441d00076a00690351980e082c0c00714100001182e070504010400302d18000c00c492100069104600c059070104047c00d1000509459040094584940140504426540740c111110115940c0d0b070300032406500010020800700b00b5070510300d81181c04d007000c0465960740d03c3e14112810500013054400c040408100450b200e245103c2450082c1521600740d1240901041007104008646100070030800c201c0060704009203454010645551043c1009030340c4840c00c0c0e4075a81400b100f11201c8000420001d0200203002e00c031007040c12200e034240d81c100300c001e081003c0300d9222300c801085071203402001001c2c0746040703c440c8041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 755639289 1250 755638039 755638057
    0x60e010905031b010e1507030c030513060c140a090f091b0804020d0c080d0e0901151b020634110906030c06270a060504030b041a010e011d0121050102 66
    0x18078510780c00c210f4041e101b01415034106d40000d00e4450030314420760281c42114002c412009000c8040382659072468040d21041c1130420400030007202c0241a02c280301f0103402043c03c1034980e00122070900c5564021117006034000200c6a04203070310030364504140a281905041c50b4500f0403031940c1c403400843c440080c5a0802030030104170791700c00690300201007580011803440ba40c0701c01001c0052001c00001c00da003070103900c0940c1c000e440207060490068151900120025020700b03c0d401c0e83e034001400503080007000c02d0700d80768415206001340740e20b20542c0181c4800083c22440004141c0c503959030010301c100c0024080c0b0044000f01e8000e907820485405000c800a0400340d540303e2051048035540d06494019015442d920004030040c9080f14600007070314155070303071170b81400e145403544080c000b40034005a17022107100701507500c007900340c01d1040d01808224500c034507954074009911203805041c641c0c0b01842c007d81d50060008240141c100125148100c4020580740c1c05810b0041c0288580041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 755640539 1250 755639289 755639293
    0xc030a020f0d05161706060a0908100b120d14090d02100e0a08060105130c050403050d021c03090b06040e1603110a0602030a02150a020904090f060e010905031b010e 72
    0x700324000b0040d81c206901c0382910841100151031604815900d0340109170180c034020080344005101414102c3c09420307040e02a281a84d5265503421085090803801210b00c42540c1e2a808c10b1415414040e0070141da0028010003020764100441f001014584854000d10f03d41d42d00143c00c91a0343e90301d40b0307064130054008101c07040c603480f02400a8140c1e80360344482402a555170400189107072022500383d0480302c01800310200300d091414014000c01e6440c039214203102041c00040041002000345035041c221907002080031a1424001240280c0600e4040b4100350405030a9400582c0408900d0f40010041d074001c1200f00c91018140c0c00d0490a41b5000c801c42e10b40e010002c2840020000c1c0107c0443c241d40000d0300d1612a00c04984074414007443c0e40c0580d0240ca22a0f500c1e0380082c40550340078118400050501c4203640004054602090007580d00060100b42c41e4180401403080c0c8111016420080184008550b0781035142c0c0514614010610440841e0b201001402c2d0001d9102c0f801c0d07081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 755641789 1250 755640539 755640547
    0xd020d11030a150b070515040515010308040608010e1e0a061205060f0f10120201171503100c09060c0c05060f0a02011104122613030201021506090c030a020f 69
    0x880c010718100f03070a003040700d5035280c0005210480e002101c44c400d801c10003070031b200044400d0301c3d030300400080d104407180e101e0741c80d90b030f209081c0313200703906002c0e511428a942d6203510b0598000c0c042001a0011684d000d22034050141d22004c4148060504000d002e40d00015942d00b2140c0300105801d0b44042800f20491281da4208500411078a101301c00b1214200256182c240720703803401d148121a0b0004940c00420b0900484454800c5680c005205151035885da0000301000010004180c0c0c10501c0d017221000c1100981c0b4050013030701d5250b421200e08100a03ca60000245082428464a01070060140c940707000d0180410503040985070140429595400010b281c10b07266003d20a00e800651078140c655042d05034400c202c42c100c620204d000d140c0e510702620741c400413108000660070104a406100501f40702604040c000307101c4102e90303140326249580006420049180740c030180c00010a810007010b5901d090016800155203140b0680341c3c0e9441c1403180091141310344240200c10041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 755643039 1250 755641789 755641801
    0xf032003071b05010c0f1104020d06030b160801060e01120c0c200a090c030e060a0c230406110a05060103300e0f01030906090b041a0c0d020d1103 64
    0x40100711051041c00601d0020708549039911001c00d00e40180750000350640010000300c1c802e08100050180500f1600d111010000e00180c101c7c0d10040c02803c40b1038440d20200107028002003100d03072248034110f114a0714911210001c0c910072050240d9030902050031151540350f44500314400000c0599641040001d1492201402210b080c01045485914230344456070003140502e214a051000030784002e042d5410000c400002c2e00d900385180c010180d4541c82544030080c00c00407907001d19400400020701000b00d0b00001c002180c0480e200d207641c2591260340e105060580d0031503085504d01c0c5400d1a09442ca502c1860a15941400c054034074820103002000740081d01800500101003e0360407996020f6015020f498083c504880710003107903144061300b51606004140801c1100149000107260740700e50380d80ea040f0754005006039960280d00040000f00407091122000e902d0700410040c04a29200340500740d244903040700c40d400c00d41c0200ea8082a16101c0c0c110030100c1c0c0044a2081e101c0c6000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 755644289 1250 755643039 755643043
    0x1202030c130618091e080d020904020706090f02100c0206160503040e0901021312020105160c05040e0c030c01111c20030d0b0a06090501140f03090307110a0b070f0320 73
    0x3428050340c42459603440392445885c501c5061000c0340c0d0000c00e007802d0009644009000350130060445070007980030440000014101c2c030407c044a482000c0041c40801d4500522502d401c2c0800410b007403000c2c8165182c00340e6640000e84440b00c1c45001030414150562030040d0560150307600048140c0403460902200c288190090010b25070700b4076000d03944039620380b81124582074804029020410030050703401c05020801070b045440f4091000c1212040c2d41c0c00c01700b0110f07030f44081c03911140c0d0480030050b8507510b028050b05080d61400d2818000802c031042c090340e120001482d0b8091499080c24500a00e54080c00d0040d000400740c0c031420755180f14112155413240e2210782c004803000c1c47c24254201600e4100c1000f41960f80640e2100d00403410400151400112082d84102c00041031200c8401b2003d1040154814950900515122043c614005a0340c0101000241c4240800d01050108030000c82c1176854440e0401300c001c4ce8a2014141a201c408101c00060b0120202280054600c080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 755645539 1250 755644289 755644301
    0x31605010e0d0518010915020f0705092203020f0303013b070f0908030a03020a0908030703050306220603050d0f02061302010e130c080406061202030c130618 69
    0x1610092201191100d15a502c4140e5a1a0303200841c4050014042a41280103203000d00315060402c401e0b941d440f002c00340c030340b00d000d080d140c80164001c40c0d00740c80e8490f00340700b9180203000907108003e032400d00c0c14913203114000100100c2041c4500403140d50a240c0b00700090703414806040e003541e513a540c440f0051100c03004000e0300407a924001b100514450880d1603d0380d04500484140d0010355201d000d030890307920340905001d81c10010503c1d0049040001400100041103081c2ca0050b656028003030040c1035843c41d40e0103903034030b500705003c803d002c40d4121044a900020454480140c4c03080c0085058805640315501c00255241c070030040108072001034100440c3c0d034641c44e003541c0c0c640300032001c81c8c1e00c810440e102c4481080a80340000154000c0d904100d407458000c1200c80b1034910201c0c0c2104031201400d01c940003488882c184000c0c40030034450180039010440f506d8480002640109641d503d4800109025250255080c4420728480e031020001c1c0c01050092a00d010b11210301c040a040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 755646789 1250 755645539 755645543
    0x10051b041509081504020f01050f030f150102030f0405040b1f02060114030a020a050d0c0e0a0f0c110a140309030a0809040c1106040f05120a0c030807050315060c07080316 75
    0x1c080b000480d40742c00014642c40c010a0a0400c038505a81c0da41c00c0c0180ca0285065140c1030010030b1002461501809021b54880c882810100303443d843c0c104021b240e110445a0100c2c15500104800f1869a005c00c3c221410341c0c00640b0042810145c000c0070400303c01782c08154480c0b940c01e4511401b545540841c0441c1280c2d088215a10b01d035044204058035180c003150001e5210b148154204410304001d041e21030030318000c28403001380e103581d035a0040da80c580c22580c2c00ca030300d43e40d0180003c1c10001849034601e02e040c24a000220303520702410b119960503100d030025201d1210365000e00c61403c6d00300112124002c0280984007684c0440c60488169080b5138081c1d4816800c00040d02c40c064030400c43c1c3c801501d21203008000540321511a0400401c20107410b0720305000304030041d00300e800c82100501e600d21450303841c040030001504004000010142c41041008810030610050b00c00400320300c0142039086949a030707900310b0f1044503803070b06900394409202e500001c100803001e60140411b48200e54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 755648039 1250 755646789 755646797
    0xf0f0712081603150504110708030103050708150c03011e09060f0e0c07050309090406090501090c0518280e15180111030c0d0b03160602010c080910051b0415 69
    0x190b41014280c040c0c465030710418500d062035410400981c50142c201140552000201034601032051310b03060790075032098009640c40e40c0595006c201d050001c11409650305200c40302e1064a040803070b80521140300c180f14124903003441d1b602da0071200d04200b810710b005104015003001004d58404544054192520502e402d440c2e00c3c00c0041c902c104040101c0300c0c51a40000607502d4110760008028140c503001d802a68900e61710070540780020000d10a079100076008520840c00280f0300f4040040c0001d24590310b003090700e1480b042c0050034202ca81c0b448131200703840307500e1410950081c803e04010b1020080030705003403050000090000f039041e000c003402008082d242c10b0008009110440c2130710b5901e041d00c0d2a00d40d04000040e50702d1070300c201404081c0c1810300040b60b541c0c003131800249084107a05070b0940844031300707104205040c2c091140c419420b9560502906e98549003d03859281c1001c051204401d03074840000650f80922070900702c3c0780c40c142020f2075440b5a01c801d0503080060100710020085 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 755649289 1250 755648039 755648071
    0x8010e0d02010e062701020d0f0b01020a030c030f05120c04031109090c010e0f090703050a1a01050f03070306080a0c0801140103150e03041205100b150f0f071208 71
    0x1107403040c0a241c40c01c440480090050391908007200c04820803103416560103074900500707110000420f0004040e0b200b060040410f504087c091003000711015103480c02d05541c80004c6040009401201c03201442ea0942041220751115403420780311480b40c110150405003002c130400919803042000f400c2900d001c0e2002c281c03d4100e800501c520003030141c0301e10203540d108605012a96109000700c0321000301c0500780aa810038150086043c1c00c00a42e240c402103500c5a00b00101d608c0207109054000c10780100800c4a041820700280a0740304240c0c0f844100580000080c41c4a80a07412140060410748111461260309081448849405005605043d4280a0401e03107a0300032042c0139040c0d075007110244c003003640102030780c40061900c0a03d08603a03010600001800320100e011042c842401000509009074802c00030300b0880c0c2d20300c044e5074030a030807209020b107480030144103450401c0e011210455079820610500e81e101c1c0540540109400c0310061801150b580c049280c81c09031940000900708 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 755650539 1250 755649289 755649313
    0x30302011d0601030c0e150409050c011218060e0312040c230609060c0f0d090f080106060c0f2109030302161410170108032106030a0f140708010e 64
    0x40305800c4c4000780c015280c0e0f0b0010f11804480f80e070080d800c58428440c0d50700740380d004800b04058840e188015111600540f40107003035540c02c1f45081818400650703040100c0110751220b00c41032541d10102034030300c40c1d65003a070314110b100c100100c0300e4200321038000e269145040d2601c0c4680d070b4914001c00120401842c40c8030302c500c60004881088000c02000e850500c885002441140d4200514040140c80350138004400d0002c18441c40d0001c1d1440d64803036150500b00461564802038580c042105030385010001c002c2e050f07100d8180e0b584568000c010f841501e05a0900500c41c00c0089040c21102ca01c804180104642141c0c480301282d1298080e680840c44200450403010954821403d01440301ca4000b1910720707000421a10203480d508101010200c3c4648100410000740c00540c4154000141c040c004220301000d140000f0760004d03032a600f450301c070740802c0c1c4802d01030600401034102551140101302200c0c410746c99807285d000440d2100759403100094040d040514034418540500000488 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 755651789 1250 755650539 755650543
    0x9080403050109111908060601082703130605070b1b0720011d10030e031b0a0203010506060301031e0201030608030c012405031e0a020a0b07020f01053907030302011d 73
    0x1142d481c0d82c0500415a08c2c4c500641e4841001031002030501101d510032110780400705c2260342900780c4000150f494600a0754000c001c00d140b5004541071020921441d40011120103850794010300c8492070030300205540c0181381c01390094110003000c3c03c6010a058101d0385105013501c0c04400260f0b1074005030f003d25102d2592400244107190b800142e0299100505406508800c0d05091042c007140c3c900001a00c01c41814181c0660070760180e00100c1e802400d61800340285900581c00703d907540c1c6194550f40d03d2a40c03080c08503c1e1f24004081c40d918000a40e800303688020010050035003a2036880b60402d882d607000300507004010f003504081c2c81c0401014445400c500c426558041c000300400950680174481d10100855164050f10840395a8401601d5040b00c0000400c1c8200c040c1d603d4000034810090080001450a1704000080c07080b40340e0070340300e00c1c0c15400c03042c8640c00020020602c00c0246d6014180c01d180410940310321780d4000b04260341548001d007100410b007503008404421030100b139 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 755653039 1250 755651789 755651839
    0x3030903140a02030a08060303160311012d0f02040e01030b0609010819030315051203030f0f160e011419030501120c0e1513050601121401090908040305010911 70
    0xc0069105002c4445c0d058010165141c101e2001801c503818980203503400c45200303c208204800017981294542d03040d5009024030104820720200c00b40505002c0f40100e400c03044a0345202000c5d503144c2a04150b070400d25411280034156025007401290f8481c10210f410000507515140202002000020030b004c0100e004202c0724038584107041d90350321a0304c040340039041240443c0b03000b821050703001805648402003602d20b55800c0e00519140d140c50785119034401c2c0010301e001c24020030710f801c0080e00000794980b03498411450426100882e84500103c4904540a66882420100084914107007007824445040082240c0c3d0500150f80c81d085010000511118010415107420f60240085800380c104554403092607036241525103841c0000824003144a44071060162340c1c2c0d03040c46240e503070001c0d00c01c1d0400c2d05100b041c44103070781c480304c0c0d4184004144a03180c000d41c0d07910340c6034040150035400c6500468026000340031681082c20300000481c3d04100342440340b1003020849801000c000000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 755654289 1250 755653039 755653057
    0x70e090c040510050402090f040e1c110c0114090301151a281b110414060d03030c0201060b12070801171c050d0c0f0e0a0305100b04090f0303090314 65
    0x1c5a034900e004c050102a4104484842d80901d04078003e403e90b40300ca100d80501c1101c55001801001284800500c982c000f040c40306007004180e41c0c44508401c00003070742c1c264800c800c0c07030424200312119013600c625008020095070706508000c0c0a01c8209800048502a0f43d6412205e10182c000c403d00c41140d0312070041c3c40215181c40055000c40000c5080902e0620b0a0307070f0525401e518482c13081000c8103914254105e4080c000b180d40998542818130824200300c9460754103006d01d007031000c00203d0300b6108000050405031a007482d8a81c0d01c1c800e40006008001c440684e0f611a9040e48000103281c200701d400c3c1c0300113001803000080c41c600b100650321100b10860084d14444200045203080b221a02c0070000c184103040210303100705080c9201f40b44141401e903407000704141d40d43d18020311076000401d1551241c043c2034001d00c08a64045010043d801107410700085000311803011801401003400040d284481031000101850741540083c500e19210759204640c42c00303039001c00d204a01440f981 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 755655539 1250 755654289 755654311
    0x1b050a03121b1d060c0a08041505040341010603060c26070c08180306070305090c010305090c0a03031806030c050307050a090e0a020d14070c120c05070e090c0405 71
    0x2010007925011000e10084014000d0303407528165185d0305290124821045980490000b020019514420f8002d031388a41d440c54800d01e400c1c610b84a540d41513003103660004e000140171001030440a80c61000f151340c00e05503607850303940140c03994009008015520090342e4070f9080c81020b4aa4030b21070740c0e840c62030a07116a0203008038046641c207038808076401406032050101140551000c03d1a80c0050300110101102c580751003a0800d06041c00e040c1c014026506150406085c880885800b040c82100780400303180014541d130f84c079100b15150003ca10f13410303504030003a9400403040c55441000c89008204804000b861280e541808170200d901c01c03140c03e0000b0b6400d00c04585218411002400c0c545107600e0001d8005c1c3e10307040840d0f0456400e0382d00780d80340c82c3d00281a0200011034001d98543c260444050b03846440d0500700906030320030045000304200842890350344203a000c0e960341f040243c1c114003120000342d224044580d802000ba40e80913800d1040d4901c03082540350501a0622071500800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 755656789 1250 755655539 755655557
    0x6080604030f030b0301020301030c06020c041e0f0204051009080f12030417070204060b04180207051203071205010303020105070905030303100902090114071101180b0304031b050a03121b 82
    0x80490342e00d600c81d040c00081540703600364055607507000d0010754040d500403c170042c0140d19110020f80351202e0704030074a0059040020a481103442c404c00707210085441e01011501ca001c014000009111365004160701482d2050b4408203141d01154090a0b030380e2800858190002544601d40d0f01c031100c0b00d00e58070200c8200005000100c480042e450300b800d071a4901810140c0ca6800102a80c81d25002400280750110341042002007a0142e1030b03a0304409038046113031400c0ca8403915260000c11540100c848000004506054800c40c1030210001080700108100e584030310f0028007a08069401200145030340b00c01290b5440c0120490380249085044215811700d00074010303010b5082050500d050189003110300004222880060020768030903510003503403422010000d401c211000303250240d10042c40e4018400062004c084940044d0103040c603102075222a2907014000312240f8000f0440c1c011950486c1c2055000190300c00010348860092200c0c0e42448500e0380c1c00d04003200c0d04800a140a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 755658039 1250 755656789 755656793
    0x203030f04260a031517030414010c020909010903030b01050a02060703090323090307121707060603021f030c11120c0307080f0c0d0e0a030b06030c090a0b030106050406080604 77
    0x401c1000360400d40c800c0c0c414030100480703206481500044a010082912000c5c01401e200703801e54004060b058220310741c00314403094204141d0340d0007140102d142560b000c08285009a028600300340801743d0081410129103000e518490103494608070403400301c0d050000d200c10340e60241c2c05440c40200f1540c0241020380c0d41d20000c8016101c1c64000b80d0902c006115600102c100850a110b00441003841c22641e0344284c1c000c3c545410040c0e0301200e1403005a4014070001200340c1c000520003007801d1401501d446080c144840280800e41c8022340c401b0301462407691441d0741d030300380f9000340c0d4040e01c080201100030503040d0750340c04982c036002c00ba5400c0700e0018081e061170440034101000c006402c903418030a42e41daa00084d503006440d500c500031800b01701c110450341b04010004e505c172024600950b0411048000c5014940140802858042e80000007001c6807400c01c103050040344020181c084070f0520800c00402400c410040c1c1d4003079400d0800221300350600d8080c0314115901500105030503a565 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 755659289 1250 755658039 755658053
    0x308030406090c08120a0801050a0812130f1401020c010c050c0d05010207080703020c1521070c050a0b01230d0b1f33080109110c060c190203030f04 65
    0xa4802110a02200c150106080c002003140c45c0118450502c4e460f660b80802c440588922030580c001841008080c1c4d00b44004500031447d40804414640c0c041c1d00c444040080d00c0c00c031079954014020070a00104005003001104811038810442a000d451107689000011038003008280405800c0394401c800d10f00417410402c0c28401c0302d5020b82e00040c1001d045a4651000323500c608410342c01030f0b0201c51003440c05d180c0161110311f079810700f003469407038414402c50008020880c030000c0f00140c03030349000060700d8074042c289502a641e401001d9842c030100d40d20f040d00400c0c1c000e02419014032012100248101c1c2c0844551707a01381d40050032008001140d9980050b07000b00200308148c00450055629550070064000c0001b0346208541400d80a10140a110124070403942040c0c915030651503071031450b504520000c0c159a40500081451600210780c00000d1090002c0303139810b80f007004108a0114901006829200e008400601d1459049903041343c0d240800d07038030700028003d44c00101d00050b4070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 755660539 1250 755659289 755659301
    0x20307150c0b0c03070f18060c02060d1d011a0a150306030b0109200a1b0813090207020a1a0f0309010f0204080d0f1107030b1801020c21040308030406 66
    0x300349801e21080c00300e69a80640c03a1400e0b40c0d03c0e006a07202006010400350868070001500b00c4520b00b400d407080480079001200000f80c402c60741840302024944040d9161a0700300c94103019104024440502c064030300c0403086081c410442c030207510305a0707411001d001c0c80054502d0075100070007015030181041ca0400c030411107080c01c002030541d602030010000e0b4a44440303d0007810750381c40010300c10148604864500310038001c551780140c400c20040014903004200c220b44c1140c0e5042000390201d0714a000c0940384140c19001409001040c00001d1020706a001414080d10985207100403c0d546c04085aa95459608010309118240812880100b2a4000c0c650185040d000480c00c0701000780110101c0c6c0c05a00200170030b81083c0300205110713411541c403500c080424500406e0214248190f1a15204130b400000c10078080c460101d546000307422a0840440402c0000315510303144242415981c003034900c4c050116102046404810000d008160340880e07801400b040d18542d255510b42c1e0003407917 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 755661789 1250 755660539 755660579
    0x1227030a120b0d03050d05010b04030215030601170117070e07020606130605040f0f0b1f12240e0f07020a110d2411091005131502060a0f0207020307 65
    0x5501c0e09661415036454040189444c0a6125240d40700e820951130410b50300160003000242908100810058542188244030141741c002d0990700c0303031184001280c08100d801001ea00e5070b45000c002058080d6180c0c950500c1d0340202c01140e00c1c0b145d03030780c101e05400c035000c48803000580c111a0004041d820100002c048646070007100040380c0303882d803000900705c6e8000c2c0c1000e031815540d40d64802a074215841818403d803800c481c100060030300d6005000081d83c00102d800c08108541c1440403c1c1c8482da080b610070703981d2900117566890102400e11031900420710031a01c400b4900004214401703064400940502515800b5113000d59044e10707240c0030701900c540c0c46600030381d4003007104000c00d0314480003054040008459804200041030b40c4010380d91045145c62104200304291082980e60411040c030b184903c3c00c01d40d40310402c07040000d11880c0103074000301c1843c0380e00c941c14481c254085215480383c81c9035002000702d036100001800803030045460094040d40f0804052080b50951400000d20503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 755663039 1250 755661789 755661791
    0x30c0e180702100e010507032904020a051318110703080105010804030c06050f09210d0b0307050d06050610090503060612031c06210201080103080903121227030a12 72
    0x211180554411200c200520f04c440340d555505109a02d84c1c1030190030301c401303074100b402d1080c001c040411194003070490400030701c119030000e11661154000c00a55421940751a00c04407001c1d52444117941c3c0041c004101040b0302e281903a9541010100d0040c0c0d550076804d95101c0015038204801910701e20806007003a0180201240c0600004005014152050104c50416819800d089010a1a052042d80844518460005461950900e01080c1d5a002c800b4640c040b48020221010070300340006500031917007050b40e501460083c4079254020034010381c0c003601d02d40744204002d10200c802912500030a50700d07820400c00b20b6401d1410488665448c00703404141c03898805030b5240000b0590041d1601680144c5445042115481045540184000301a00c2980c8150360b0750000303296a1050000401e161070120b4000c05680302000380c6100e03100410000342d074074007414010004a200c1100d80400e40d171011349804400c10303003101180e192002c9110095080c03850440c1c0588041841c941d46960803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 755664289 1250 755663039 755663053
    0xf021c050303070c05012a0810080c01121d030a080a02030f0114031510080f0606060f0c0a05031b010f0b131a031c12051b0d0212010b0a030c0e180702 66
    0x44d0841035041c101003081f031089002e00b0485420054510400100720700f0840048810401c01110701240349a0400024070f80030743d200c4101c000000040003581a000f1911501040421039030000000404058000d500c803802d40c0d5481c14480e07000d0784011104101401c149800400c88200520307080082c0f12402002e60780c40e04e1010b0300a4034000341c01c55008102040d4070b1420400c8403414170001000c50403140207041649000c2c0e021414910400d1aa0034541000040440482e1010700c031002c008bd40c400c0580703503100c81d40e0311a217004c52580380004203154a0103207214020031441c0708540c040d510252244040c88081c00c1040c009048041640b80329848665240340300d59001c0c450001004001341d042c0e88062100800100008401040900c840c4d00d010140310581f40d80020064031040d460314082d41c0e862120a50001a0051201f100101e581c0200040395602c07a0402070403000c1529070f010003c1081e140f0080340d18186058000350003200881a4030300003591440440c0d40f18601d40126448 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 755665539 1250 755664289 755664311
    0x30703031d0f06061903050a0215040b0c070f0e04030903080c0c030a08071209060504090504150207030c1502090901050420030c0309060c03040203150604180f021c050303070c0501 79
    0x1066568405181980c00643c10071081d440c0c511400c82815101202081611b420b598405503580001d22000e486403100100c0324801c2e01b0040220b0f030181104100313003512042924455555400c46000300c40d80f800c80c03042c4c04103040d242c0920842c03140e038041d038443c001c0da0300d907889036607065000d20060f02d403501030426a030003140c504200f440c04161003a40250740d6007045051030140168201007007000c0207945c00080010300d51240c00e031419240505000902c80e220303450300c1464416a0540041d40d240082150400e15401150250342180581d0203880e042d0100d0072410100c1c85400203642e4000e007002c005000500303082c0e01c04d1030814242100000042c910910654040d041101c1056120200100300990280e0920240f9005008a03c126041d81403507070010f0744805005602d650038040d044002065a5502d410091404005114018030a0700b80d0401e0303039520200210a0340204040f40d24a5000568800d40a000706d411074051030a44d103c40c7c0048460240c400c105442e55900d5800d80c0c1c0d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 755666789 1250 755665539 755665543
    0x18040b0a0f090e0d02060408030a0209310510090e0c220e0a082203120f031803020c0d060603020a090209040c020c030c040c1106040302010c0210090203030703031d 72
    0x809005241d104200142c581611001592020100c404498100700345070342015030001070140d00107500060b8a500c030790342c6e6040403009020b00c1e00300d541d01c440c15962001090005083e648240c25920003044655190001d140d801d0392001d440000741e001e1074101c200b005c2900d5500c041483c54901d426102411441c20004060000300c00d040281a25409800d0303401c06002e1040c424040503580180500000301d48607200c4e94040c4c1920090086080c26150040d9091072100c4006075922043c0311b002038800300300c01000d0714011000500440c0c9402c7c1d10450f00940020440700d00ea030b044d40202000407921003072001071400d070075044615a803254004030040c2d40b401540d4002c0c03c950280140c558808400f040b003aa06000e40403c1550001211681e0b291804162541e81c008180d8020540940c6800300b198090707080106201140181c60a200c105907064000410b800d50701c0c0e08807041203902c2c01078601294402400254107520410170500024001d03040800300001d80c0c00d04804041c08189024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 755668039 1250 755666789 755666809
    0x8130201020f0f160f060503070c06090b16020730080d0507030f1116120c080c01090605010e0c07062c07090609020f0313080c1b0307060f0518040b 65
    0x403443e0b420038000142e100c81c2082c5010014901c04000940e01840c14001400034400980401e041115205101b802d0142c1034000b03c544650049000005292000310034003414450040d060044c003030b10030001440d5540c200503030144098101603901078499a8001050384400c2101243d03401c00a100d0003404808901c01c2e6440350541c0d0700d02044481c0780007690030444120301c030406425001070028020703080486804102ca50b5001c0309241208800d00c0e810760750012082801800e858000030321850425042d0894036010780702d241e051180341d03240d030312001a03607a044510391002c01081c41020007080c0f13545c0080d05420000c0c175558194000c0c0802d00c20b1100400001c1c0340d40c07a030114a08010079010b52040c04010510190114104500781844c1005484003804154042c0441d1404509005100c01260408213074103080782c840d84860324003a91542d00c1301c000c02d4030a01500a00064041c06409074018050700c079518140342504001c80800c08030f1001040c01d421555402400216464200c07542c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 755669289 1250 755668039 755668063
    0x31209010603050a080c0610121b0506040b04050901050906030a11190621050903180a0b0313050601090203070c0b0711010e03040503070b1e0f2109100c08130201020f 73
    0x5c3d03544900405803d480d144000d880b541d156591301004200c000001001c5190b4641d100461100360343c80b00000381c1d02d500c2c05400240d403017a80090b0019452614100500449009450440c07542e0398460070450000d8040303413201d400d50030407824100080e044404801c26403400500b551619040c441031503600011030f40045020030302c0307504868900c103820000141480c08901c020b01ca14944409c00b13540724011000b01200280400e8100c3c041a503901418802610b00c0000380c0d5161b20344510422010141030400b0b50341e5001e02390010640a02e14021684100300d19110b0140e11482d0340e80e9000b00c0311004106104000c0061541c000910302806044075140d81d00c40207580384d5080c401050b00b003103400d40c41420740f5142000700d40d2080000c1461040e01e2400b1144081d100e88000c03021040500c10040e00310340760000550071034102841c20204178050380e800011140707400c240510540c1201d101e5a08000840d01440006a8001c034440003401ea80c0c1c4188103460075422100b0105285c0720147c00c1c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 755670539 1250 755669289 755669303
    0x30804021903171b061302190e19090203060708090c030c10052503092d0b1602131b091a0f040b07030f080109060503031209010603050a 60
    0x910080d0300d0318500c095446030062440c18403140c07035035495040d450768100740004400c40c00b142c48041d440b0303604002040c903400e41050f55401e00d814001004040d144a000328400d1625007242c8581900c0c03084004280c9110035041e412a0716103800161003400500a44410181c0703d0307281f400142c9061120500409083c0c80b14003590412000f21818562802459402a40880100744c0760340d0710f0907100e0f04c00036002e0030404d035078204000d07000d0060f10100c041e0314400d84d01072104604050303112201600321120301e08200c244161600072894066001a400d0301c40e0015110b040c003115450400805103c44800303a6030321080d80584c04a01d0300c00c1c3c00504070480310317507071145100800004895194900414a440d084942c00d04d01d8054804000c4458410040d102203591104180e2140032a070150031a406200d4813200d0781c0c036005010030407190030341c80081ea2240001414074501c1c0540ea00b0f03124028051800c00540407616500e240740141081e44541d00c5000000100342c0901c4500c2e0003500800c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 755671789 1250 755670539 755670541
    0x1050d091208101202011d0d052506030b0303091203090a18060506090a0911071502270a0302040203040c03060c052101061b020109030b160e0312040b0d0e07030308 72
    0x45081c403c1c07206074060005000c88031030f110f00503030340031030202c607058500102a42c840041001242254000c044018040e200c0c0c4100e400080a0165481501102e5482004645902d03064201e0941c0d074001525a01648144000922494082628208864070008172400d00b180c200004040300c40703da01c090704d40d91030040c40144000030380c000d5030040d0405403003003850561140c0108110341c5140c4152000701395a1042d0452990100c41201d403456000848d0300d04284284130458029400f25044010303650504103003a00310003545428034001103005003500843c6207590240300103548001c00032941c0c6601810003000150851044640041c4503a41d19920340c040d5000f11440d8001d100400d1801642050040103407076030041c1021361140a0800802158115200603035912040f07800081440000e030b002c00c401244081401ca400500c255505801140d0f0320003030584440d540c800160350500700700414030010600600901c1c1d05003414800280381c003c10207015050011350b800450010b8078900c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 755673039 1250 755671789 755671801
    0x1906030f2009040621082b02030f0f010312050f160605010f060c0b01050d02010c050d020c011b0804050904020307170105070806030d0e270c0a170c03010501050d091208 74
    0x31041201500403265049903003014003901884422217610003c00050300002d0b100845c415a000040510841e40300390f400e040c0501d0083d4029402c100c440302c3c9503543c07c0c0700207100c104c4801d0314035048035004881d0117441d44c1040c0044030180e1203140e504441007020443c4041c1c0c8054030f004504039900629000031154186540c034a1120650b03403028080100d00142d00000c200149001411503500b1940b5901c60b03c031520041c0e51042c40d0505c041c0071805100071038058160003290910102c2000d0340c910481d0103000f440000390b680704580103000d002e030a000a121038207001020980043c0000d003103603001035072580c28289000c90b0b6403104c21a65141c8090100039070304185050f402070812070240c215840d0004002701400d4003400543c1c800c1c42c031106e071a04400e011021b540f9407400303c000d54091900d058000d041c01903110340d002800041e4007003042c00700c00ba00100d4203801071080300350041c5140d02e130134011501030b0080303800044110b59903031004000801c41c1c0c21200ca51022503da03202e03145050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 755674289 1250 755673039 755673041
    0xe0d2306010321050304052806141602160329010f08070b0c060a0b1f021b2d01121a030d0503091207140703030203181906030f200904 59
    0x150210f0140401032080c00009100850421501850100d02080b00d00c50004051010b140f90b02c80645294900107200700440000b02409108029909548005054010b01240d5484400044000ba0079401c1000e100244500200c07200c068a080f0050900300c0d200a2030080300c030300070b034085c0c3c505558185040201803000d00490009040c9403100c1410a1400d05005444a1006092413800e03030758cd9004061aa075040100400d071045485e80c1084030210481c082d5a8032520060441d405244014040e10362801034000c00307503941da0218000010402d010300321100741e20014054140807003007050b0504000ca920850001417641a03003006083d41c918285418802800010340c100b05013042007000580e400201e0450a0054143c1140e4031141070030103e145075a0660800b19a0240d901e0001c03d156000019014440080e410001b07e101c03404204848409480d62462007800c5161041110034000d03844525410300c1842c002c900760404901c080350071003c0e8002c1c814403000220700c3d04a0f038145 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 755675539 1250 755674289 755674343
    0xa0504090c1e1d012601150b0d0b09041101051806031e070c0519080c030a0206010608101206052212020d080c090d03050408100605100e0d23060103 65
    0x1140d040000c06504114010484c1c0384842000f02c501c8174840f05600c1079400075400f0b101481c1c44d00100d003040c0d6841c3d409419081e4011903100880d2424801401850310740700c081c2c580076583c0078001080c0800c181d170040da410f030030004080c127444071421802101500d5860056102d1034071110342c950031096507003032422042c1000d050b140c10809044041e0b00082d10000d03814071004036001403142c12100307924029645203c1c00e4100501c900010800014440c1c0001d0f5240c1a25101d4807089070b540e5421446440031005846411500c00e40a0011000325107640d01603508a80350007010040c505080d5110180c1070384500382101c5001c6d0812840e4240d65040c010ba00406080d0714040c0030a09200340c0c42c1e1010300458944500c500341c40b0160004040c0100101d80040001909441c07030120b44017103500040500307200e104d0040d60140c0358210482d1161915148590005001c507030180020788407010f14036010120038990b07151200e103045000c4000c0203814000c41c4951800c3c025580300892422031942 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 755676789 1250 755675539 755675579
    0x27070813020109090b0a050618100c030503040201030506010c0f0506070807020a020315131b03051207050d083d0608130f0c0e090a1703060a0504090c1e 67
    0x22003000c500050381d00c04518411115441c2e00400c0e4004000b000030407100b442d41c451680a02c00003505000810740300f051884012701150041680c003c6e6080c1543d9002c011034000b400200e04000181c0158001d5104540194040c540042c0d10000e680c2c59004081800e902a0780c15409003080141559100f5041030f0b00c100c0a2024182c15149507000c207544144e076034406580400d4410024285804810a00e00c1c0d00d074024141c1c005520380041c562518400500055555000f26041201c88001c4d87d030844090f1a48840200040320142d4011118080003401e00f042c0454a2600d040e415440b88510040388003900201000c9021005601810160f86900c9035050005100400200c000c1110341c0380c02d410b402c1100c49600341c4062900100401c15600710040002404007440708036000080d40580e80340c4a03600a401e088503021141c00700c0d01003102c0066002022060600c02c1c1e0800d608500d00c0c46129000c0003001644a80100c01c4040c46183c6111000c28020400c000210301c00c81c80304103e0f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 755678039 1250 755676789 755676811
    0x150c020d0303020c07060905060403060e0150060907140307030f05010504180f05100603080405310207110a0e06030610050d060b1c060e0106050102030c1902270708 72
    0x3920b02402703d80240224400075010a5031000120b40822080d0071005a1f40156806410220300c0c8182114001b0940d80a11210b031000d103100400c84403011442c0c0b03480c04100d152106070fa42c0c481e0100a03040c20014140000c12901c0c042c400c2d401c490300009540220305549000c2200c80554560204446050f0f21943c4505c0c100003626042041d00304400401940103550240c80c0e0f44a0300340a440d102201b011b50202034a442800024449884054800c3da0821540488080d454404518a111200500102d03c00c040c4509003a0000a136004041c5030340304d4602207161440c420700261031105241e000c042c041c01c04500b001003628041c0303c9554401c89408403011030354101808a42004c801c0c64000300100e68032056030581d552600b4515019000142c5400101001850308201416400a48100c01c2d800c16502141c03a40c0040159070040c4042c3c030080003042c582955022961131641c0b8240e030050b050804a41c02ea28203060401d040e0315040c60711001034140454001e1140d0f40050041c1030344 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 755679289 1250 755678039 755678057
    0xc05121b0a0b270607090317030907150309140601061b0b040803040c0314011d0703030203030c0d110f0711010509010c0b060604120f021801030b01150c020d0303020c0706 75
    0x1600418410f410a041030040c403c660008502200303a120180e00740c426902ca614200521968040d8290b070650740304060b0030b4900302c0707102c10b013100c64001920148056004801d0920580046000d0382d0b15101081c0350101f200c080c40e0b00c0715015410b9502c0d110556402c440d005000c0c1d039070418450901010240c0b004401c01c4026112245403101c003400041c4448000804107061080c03822005024640203000c6084002002c81c01ca4000c186070000000811403000c87c43c000c01a01103078020407246c054020798655940c00c8c454904a900400002c4601a41c40b400200704001b6800602030718840d0003481c540c0c2d0403540c00c100c80c0094200d044241000380400c10046a80d0740320201d4041d0680c00700d4080c0c0551030720300010700180115005410f0510343c06001303000788a014240b41d40e00354000d0340c2000b40340e02c0c92007034070851540900000d042081c661300104040c07000142101c6103e9032614241c3e152221039800070703960302c401c0b52054000030b401060802c1c01ca5410303c44100140080c4c1030140751 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 755680539 1250 755679289 755679293
    0x603060c0a0206010b28030207150501080c040f1d03040609081c030c021f14090615090411090403110606040603031d06040b0409020a08010e070903120c05121b0a 71
    0x190380014040c42020702004a401354030b01d4072401d2049411b94914809821021750050018001d4100b0175003517403070b101c0c0405101040f4600c1c0c46110305840c00d8070040c011040c9840103001c050000e030b9005400c0c850383c03501c480c401500c0c00c00300300b145401014061a61303039141c11001009100300c0e800c0354880ba0816080407007805000e261002e82001c45080114200e0390060099041103000c80820718079004040440c02009200c0d0320800c202003113050201110303214803410f40e030313100d904640002444c2034050b21004180344c00c04000307911074480c2004424491b000c8001c20088079081c1c40c22808103818000307444074103a0600c0fa981d808802a10308126092860f14020500d030b0000300c680050a00402a03c181900c0d64011940030300b404020f10360355640e54a01950007944501d00c9440012441c80010548443d03c205682c042c1159a0754500d1150450310345c010411244e403500d80c00e1102c00340a8500290090062090001044021617100c02d190000e00c10070101c080303500100d5400c0a985000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 755681789 1250 755680539 755680543
    0x50d05090a060e03010e010c09080d030e060a0b03120403030c0b01050d0302211303290114061308060406060f1d010e130f06060501230a0f030f02070501050603060c0a02 74
    0x210b8007a441c04440101000c00880d00528080220341d446500b00800c032194141c201e42c4200403146420100d0300d4070801000220121000885104503540280c0301040c1080002e070407480280b00002d0544081c40584245060140d01543c0200c4c040b9a1030f858103420303c9034554880c1d00502040d1103240200c1141d42d402525150303082d65425102e2990204401040440781c2651942a54100c0d003008051701c81c10100304c3d00c0c036003580899100c2c02c02c404c400344107681e00310158100d80d07282c03250032400c0c00c1c24800c0207000e400004110448803585607002034040000c004050049000b10313030000b040c90805078011001c00b242c0d00106010101001e1026003544407004050440f080c0c2c0303490740c0035900c0b0790001ca491364080c14805494460254403107428403986601070b8045800c26254146611a00503101d0300c420740c10040b18448a4040c44078148141c000d0741d0b801c1400c4050b250000701426601201022604220401c0e14030b60366600400c00c05082c20040550041d0344124614142400410025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 755683039 1250 755681789 755681809
    0x40b310b090c0a080a05061b2d1b0d020715112104151d0108060a030c1401110c030303071404050604240c0305090103150801020d050103050d0509 64
    0x50015200c0030000d2141c0c4014002c1c80c4000c8001070034040c03c44c4d901c004503079480182d050203481d54010540807440018400c2c80e140d400f84103210186040c41d4241500725101002d242244440003066100400c40079080d200400e00c02c59890f2440452002101c812841d1580c0b00208101355070100000b84a07402d030f034414003c40c141141c80c22034203048255402d0380c07c0920b0201c0000001d01107200034448960000050720540d4a01013035908103480b4080c00320b41c1161020f80f5a0a1400020300102c299440f030307066a40e20a90140504262a0707aaa4908584000560000f106182402240c240642e4008841015030140f40c000b00021501080000e46900c40507000c0414800080e0340d0f50807600008007907600410005103110740f9290b4401401082202c1e81c21103044002c070300414a40d01c81e01861880c4003441c2c2543e1550306003050500150700901d000c022042c070302480300b04006030f0980d0900061144018100000c10721794554070f00315140c070010032801d0042c80801e00c100030301500d85422070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 755684289 1250 755683039 755683043
    0x20118032102040b0f0c0d031e0504050f060103140c060708042c040302030a0e01022406061323090408030a0b060c15010e06010f02100221040b31 64
    0x60742900c10348410000384078503480181c80d413a0216135a0003c0040d24003400700c241e07241d001e80720381b0540e01500300d0855252001d0341d070311003e00031f4007142c0500d01e0b0341c043e6505ca4818011148080702c1a800c0c1807600c202640111070fa008600d820410094051000440146059944c2801c0c03140d00e660341a06e90046004403410303054207000402d0081e000004c0c40c0000f14400f104072110f4100340c00c000752070740d00400c061000f003200c105814041d5440040d408040010301251010310300c0310b039004d6880c8200c0c050310380d680c000c10034002c101c0a010000c082900903d1060520604000d0a5070300d4500c0b60040080c0911030b5860307500708404203a00c4000ca82e4003c80343d48002407103400c1700001603520f0041c0b1000b1601072081e1040401030540e000503035410303203c4d203a865039080e0303440c0c000450303840c80b00c180c1000c01038125031050446c074502a006000741c00c400c2c1c1000f40802010020040c100b0070100c3e01511001ca40400b4405a01052190300d8513400300304181040c40c201400b40b0fa0307640c01d020080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 755685539 1250 755684289 755684327
    0x302100c051602150f07021e06090f031f0f0506040c17100308040e070e0f010f0813020303030f0703050a0b0f190b0d0c110a11010f110312010602011803 67
    0x442c00c00c40da120100c008a40d440e14090544403510001078004d15007194600703e024242c2d039941c448407910441d071000403011004040303506e440401c0c0c0a1250168507001403075018442c00e44c00c107048051808140600a000c008002504016419002e065820242ca294080c0e807401560000c0c0960008694a82ca9100f205003103c0d42c880014503160201240c0c0050034008001c036005c1072040d064240613000d51a15507031100e010150504010030440301403e102c0c08a01c00d244954201c0340105880d90307000e00c0b0325600c41e15044113a0042401d50b0f008a65010295014208100740107070540310f000d410602c1820200044009000481c0e0207400e085405403040389424040600c0016112140c809041c0e804103880e10303800c105542c00b002e404800314400c0400c004540c0890007201c005407a000654111841150484604c4015141e03250703c582010100400030205030400c61080000701010b031302600040c54258901140203003120305051440c4500c3d40e040b80c15002082d0b0107400d588420b40d200300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 755686789 1250 755685539 755685577
    0x20904110901141f090521010e03071b0305030d24090b011202070b180a0f0b010303080106081b090102070509010f03060e060f010b1819030302100c05 66
    0x182103000c0003641904a40c0300800100110f105003848812880592040e100035200d5651900961003018240c0d40082c00541007080030000c13460240380c1c10740c1c001c0ca60300504400c80c258002050945070203042d14017240d400010f090b010442507030300b410040d001c00083ca240c03040c00c560f15252a80301d144000301c15a0384650310711864183d255049060308241020081c0d50607600c0300b604cc0623141c3d004030240030070601410013020700c019000b11540194072044880b0582e60f210205522040d1880c82d0b1081c0c0c0c80703129000c3d00020190001c0103080b901131105007000d50715600e401040c3d000b050b040401000085024070200381c2044444113601425100540d4807034002c82d004034544140c41c0c3c4010f90140440e40001550080d20307440806690142e03501b40314a500301484c090303844c0b1050724074170304403840823004004603000c400150030554803002c240c0004c2995000001c0845404c02d180b981b0082d8000410020103404011828800380228801d0020110890000d1b00074000c0041c61551000258 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 755688039 1250 755686789 755686793
    0x2120a111e03060403020d080901150308130308070c050306071403060114130609090b0103020705030711040b04060303050d05220305130819200603070c020a0314150109050f04020904 80
    0x110341129910702070100e032030300d240505000b0744e1350038042c5408001c10301c60004100100c1060103404840407103510250061440c50b5580c003407682c0120050110002100800300003d01d0040040001d6070042200b07a0a1074100b41c00c05003403080281014007441160542050812a100b06403035008500342884a03236403041903042586803040c078030508070b00408007902060064100801c0001e40b12625410483d050050005400328800c036400500743d58014002d030f1001442e03100e044011910b01030008981e4180e144082401c0d61a90340044000c1840031800d060980018030940303074080c0b10049071480700c0d0b1038400c0e400001e282004028042000c000354054030700c40c0c403d007180010309070745046600c02020980c000001c98170302481244d0000a80c404400d032040b1849250703903c4d417001044a0310b5900c03001d00c10703909600e03010b40403a00584840000000f203402c101e440d40861141001a084004600003080f61101c2c05802c4004041d1038030080c403c20310750140f181070740b0a5042d9014200307130b1242c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 755689289 1250 755688039 755688079
    0x1215090c021f0606020c060901021c030204080d110c0405062407020d050f0609010c05300a150806040c03032001050c0715020a0e041a030a0f02120a11 66
    0x14040c4620400d42c8040c07228600350030740d0080080310101c1d425114070304400300801100e4422445440d00590050b001d20450000255842c815402641401481c265032040802e05061561048002061180703415a0b8800f4041c4019113451030211010002c41c5480c40000f00094100054000011103200c0d401d03074110201c0f400c40f0300f015002441481e100d000c40ca00140c0c0c40a011401c41440d01407140826100c40c1d05000e14a14010f4648410b070400f5142c1c070741c10b11525200c40c07490340c01d2100f90141da0140d4074440600c0d0b0207840194008926404e014040e681100410362101e03a50307900200c108004200a1662031003560351500d054080b1b600c4459403a440e08201c5806900c0d03d5103000c3c10311004c00040030061020502c103046a60042c281200500100d0040b0594034002c600140c6c4c0d284401c0c45c00b0b41c85000a015070406210914503007602191500403003280445250748048c9100042d0714180001c2e50924068400034500c0b5809541d440c1c81c15001c42200c503000e80e4041d89141c3e000c00e84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 755690539 1250 755689289 755689303
    0x18030609120a0207180e0c011418010504180606200c091b0c010c02010b010c050606090703200c12090109061101090204050403020606040501060e010507021516121215090c02 76
    0x241800303088071210344172564070040c0582003c070791051007006107590085d4040c020090903401d0390351403181001c180348041c1d8445284482400e040080800c03000c2420000c16a0100558450140c0003a4950820b10b0140c8012100581b188808441403001d904450000030342c41003d950960f040012502d844d00b010302420a0000f0a030340030100842e22a510b002d0545c007503c0807845031b83c000c3c00309002400054a5803099400041c0003508400005516410700401d00382d0000d52900d800100c0450328406010018400d01100d042c0c00c100199100c0740c94020040e0645096080b52500e192a1807000060180e1004d44501014000d440c0002082d04200b0b50049079202e402403c28400d51501d80307002901d0710740490350301c0d10503032401c0e0003c03a11034816a0300c90712550f8180c503a00c0c0750202d00c0e000c001080c4010380c19841c0da00700070884210900b007503501020140d885265400f1540e559040080e080c03c501c12501900c0c5440c01d80700e109071140300b00c1814125460f0600000c0c1d2240340c060b04a0030600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 755691789 1250 755690539 755690549
    0x1212050709151101231b040317031801050a1a0406140907020a02100c060513120516050a050f0618030a140d05190c030b10081e070518030609120a0207 66
    0x2261418105c051035454841d80c445d211400d280036180c10f120140740c00a002e50701020f0000400140c81c080c80340c00007402141c100720206603103944011040d40141c2910422075051200c036866410402921203281500c4900c07001c1102c052050300d081c00a2520b00c4404401001c0c401e11040c00819074150090100e00240c540140100820281034003000e40380c2c0c549040100c90592920001400101c00c8040d0a90203035800703028154021400350342101c1c5e035003028441c0c051139044d030054100041c204001c0d4a07103540c8583c0260505000342d070001810102c0040201035a807400c0d41101c44241808400c90714040c401c0e0410110291039100540018050009514486413238035040c0402c0e94901c15441020000e400000d00008200789003c800b51444200b400390805602c1541030070182c003c004066100d0300d1151a01060007640640603c102c00070b03035800c80400c0001480b02c814000e40b1810038a009401d5004150500b0082d200a03a15001068005d01e8000042094840940700707000380c5000b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 755693039 1250 755691789 755691821
    0x20030103061a030d2c0307151403090604170c030d060504110c0604060906021e19030e0a06050403030605030a0c051e090a0b06071212050709151101 65
    0x168491500c40700500c40e04052071080d24044042c118a03207800a0a86507800d125034540c20038800c809450a132a51001844044400c84190042c0d61a1410445800102514021a01c0c1481300d020b02500c0c40100002038014503500704100302404200054103070300700d54081038601802d10511000c01c102d000d070703030034004080c0000110102c1d0640107030012410790300e040380c0410001200c9407401200f8070030207401c0407054204a000a0118255030301c00056070340130750005440c040d4001440c107000034ac0083da00e446240086240c0103642110a030b420b084c0c941c0c500f410028004000ca91a0740d8900380e1400400042c1c0300c0c00081c08041c42a0081401064060100d078100061403404c010654210f00900303004040803d02041741c01c030140e281e00d0003010082c00c030400d44d032112821140a00600700c541500000300f0001e0303000080c80283c0d42e5090150640ea0b184425407004030a809641014011000b080003460f01800005076454040030680320718288410303c0e454488005014020081c0184045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 755694289 1250 755693039 755693041
    0x406080d1103160308070e240c01060b0301081015050f2101110c1002090603041b0b0a0827060a0f09050604050a3f0c02040603120e010509090403032003 67
    0x40d0071510702c5d40a421192581700505d4488814440c80d4081501002480002080c0b10002104a000140240302030080081a01078803003480c095550f000783c1c0b002419a00240034000f41c507480d4415030103541d0203d003640c005249880005800558884406d80c4984d807603294901e82019501e000c1d254a2141800034485001d504403000081c1e005114604000e01070a8032842d10080d80781b08440c49010010821420350b00d8585800d4100c0f0f18038404107007048400b01d404125000d2900190602c08800d40e1003084500c0c1c92403003a0303012a4004203200f00161240c0e80302d48907000101e0150f6009a14000c0090701d020244c5905024200321503001c2c0c160300682051000740080812440d00c3c0c60f010f01c2a40c226400e44130810014002d80d1040342e411038589892092421000d4a5000110340141c50b1031484800c054000074211181e5510480b4407143c005640990f80d904407084c03d601c1d800908283e4204000f01c000301d000c029009000804041d0789045e11040040d16840300e21071030300760900c401d8a0f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 755695539 1250 755694289 755694293
    0x40b1806150111161202150d0c17060102072d03060209120a0804030201120b120106050901050a18020906160605150603240301020d020a03090b060406080d110316 71
    0x116280d264860b8001610800c61030101c010008000120907424103c402c420b03840c046042d844070f8804a0126401489411220340e0307101140c01400d0280d045001c0003d0005100c40040c041042d01c07004c03107280020340401c1054a03a008251881200e07000c9030b108021440035801000c141d10100800f1050030203d100100c140001a4003522000c04113541420b02580c0d108c10481d03454544031001011044200002d000652007052540701d0100241070104403802c2d80c0001a1040c0390404030109669506d2108002d035241c800500d81c0102001d580c0040c1450500080700d001220789244460215000030310360044d0b031a60b404440c080060403041000d814142d00d0000d0113001c0949174100c001d5a4102c80c20124a8020100c0380922480000c40c025001985520b0030048000308841c0e038555800d10000c103903012540001d00b0001410f9030001408122494881d100c20030103030180e8001c515151042c415072500054560443c802414030807080a440a1064030718854560005851705000e01c070398003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 755696789 1250 755695539 755695561
    0xb0721090803041518112710060e06040302060f040b030705031b090d23030c010e0f0109020a0e091f090311150a0c1707080714070506040b1806 63
    0x405180b180d601446010045001541a25440d50f010002d0f50224070b8a0000912a00d050b40040c40001d0301015005082220111000c1138161f51000b50f05028010400790310000c0845202030310781414041700760f10714500442d003580200c0c04002d0240c4000941e142d11003880e4019540280075000b03103e9528a01918000e1030b6801c140c40315045644100500700440005d541554200c40014000c0364502e00c4a468150348196162490340c20444a80700b100070300030003840103002e83c20a0718008604c001100d9442031a08442c1c1300b4480f0244d240c1084078005950703101d080c40403110380e02010110f40d1107021b80a42802481c1031203031065070b00c180c51203000745030640014030202d00940f151010065882e44c160b45946040c016400c600c40003500051800304264002070f410601031410f0308c80b441060844008101040e21404040380100c07003000300c503c1d803080c130304000003d00101580c05d0030f03c0340e510150781d1000038100900c4030b0448000541d402c4200301840e42c2c4804207508641c114100759002c52 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 755698039 1250 755696789 755696791
    0x10204080f07032402070b090105090709140129031905012c091e030c0613033c17130b0103110d0b0a0608070509040b0721090803 57
    0x1404034010216542000c6201140281c1220b802101c100003051500c4c600300c45144903100c41d5002c0550a02c661400325503170103801c51003058000d00004043c18450829031901e06590310245600e800c01464100e0b130b41c03245940d036045603208000c00071080390318100e103046a400c3c04a180030542001c01080490035001006225444103803c2c03c1000da40c0702c200176000e64550f420b00c008940c4c0c1e07588401111004002d60541e104030b030032090312081c80d110b0b5650b07003101e2002180e40341c4a13800400e0b50380c49540c003440041d4000c01046400d406040542c0d40140600422a1444081d40b21504102010203e42c0843c02d20007404500c25202c0b907000f008025109180301c0a810b0300e2041c0c1040083c00394000181d00ca05c0450300640074818682c0b03190b0328000c480c018240c02581021b214400b010009030340c0c0ca0018080c038103094001c900542030440d81c0b031401005602161090740d08206000200d0780b0203446581100705850301b2802c0b0805100084404441e00111140e19071503c44010140648074003d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 755699289 1250 755698039 755698049
    0x42109050103110306030a030f091809050f0304031e020f12010207060e06060d08180a030b010303081b07030c050723040e01090c06050313050604120e0d0308011e09020408010204 78
    0x10003035407220081200e0213000840d04290594003d03103103480801d003d880880883c5907030349403c0e05805e0300c1d0540c08120184880c101c000040c1c91b00e102c0010410241310615164905800175810a451600c55001c1954040c2c1001008414019003030159141c0038400c102c2c100e0003901002c1c86114190255000794003410058410034038001c0102d03c4854040b4640d40600c50040c100711161600f41c5841c401d541c09070ac0920070425100084113410745408040100460144c110150552314509010b054010020308a0301c04510b50788010012688000c20b45140740d0b00361808507808102850540d150000b0340c1c20580b15611000c803200c1c214220800c1c1c507401c8040c01d640c07d00c50490500902801d032080e42d140240a40c1c4004814402d0328070420103980e01c080d0044000303051405a4540d5404d2000544068440460014100c2c14507034000ea072440e1102c40a17907554641c030030f094400038140903040c000d00c41000580306550f20b601c0300c2c00035820701800f13903d0401c541e22aa81c2c22901c0c000d511622403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 755700539 1250 755699289 755699291
    0x3040302192301230a120f060303050403020a080a0201210b030124050105041503020c07030c081c08312f01050c06010501030510080615090a02090d0b042109050103 72
    0x45410380c80e2148414200b580e03082034140c0e0411182180030b895020301c403101908100d5482900f00d410001f1400742e040250300a0301d416a07a00d056006200c100d082d550805115544004981e03801031b6841015850b00600241c03038226118500903112010b04445e6540507455070070500d43c0303040c24003900c00060340c018040304040300c4680e0303903001912503000740c0c8140b05c84031842c240202c1905002c3c5e0000c0500e400b1103020b40380e0799503e903036030601c0e501c0e4a84c1125003a41d01103405114950b56004040b4880c901c2401e20300a24900030610f100007805041402d580d09480000c0540d00b03620400110354001e6120040805183c481144d0070209840e50401100296180080700c01c1d950140742103036142000c42c00600910303070070003005402404000d00701100740d2080c40300c00a600d060501285002e1200711011390304407c0d2840c104170100c4805000b0b0409148100107511541e526400011882075211407121342565903820190ba1440e0402c0c4400352103000e11444031a61a8010402000e545003601c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 755701789 1250 755700539 755700557
    0x90914060f0406060210091113060e07030209030a02040c0210090503031005040e0703060e030f0c0102030f0c0a0e01080c12010b03010e090d1b140f0309040609020c03040302192301 79
    0x104000c2d26121300c26403000d038124034400c4070101a40c1c0c00c1516101d01680005070300d18040c2010802c0b50060722891480945d82d200c4c1480b0f10940d90742c20715004082c902d01075007020548800251106c4000e10000c1c455552000d4183c070301d6009121404420b040d0304800c00a462890410b41c1e200e0f03004032050020928091000700302407030705111742c540a98260b0010501c2c5410740c4c1d94107004104401c2310740d01c02d2005105004000e8540780003407a56820345800581c032418580e0342516480381c040c2200c0b5540e4400e001014107207a100c40009800d001c00d02c0c29507029100d6941c5074520b4460100d01003002c4205100110369040f140000314100c900c0251040d2141d42d54950a54880c544c450981d00001d8203920b0700050303038880030402041a40544030710403007910039410321854640c1c410080384040d04040341000c0d1a14043c40f408000340b1441b0750540c030340550540f80c20340324802c0d8000248900b070001000c4003100c0c3c403803c5e1480038200f800413813602c0d080c403081c81c1b00c2c10401880c0d14600040d0141 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 755703039 1250 755701789 755701819
    0x604090e0c060301121707120306060e030d0203030c1606180b070914060a0203120403020c0307060207080715050f0c0a2907050a050903070e180f031909091406 70
    0x103048134100c0c0c07080700600852503090358900e403504403141110020b11005006d0000415940803492030481c51588000520f030785441c202514589603144045c1c4a90069191441d94503000b1040b00d51000100c070810b90740300142d05142c107120090b00d03806001e00d4501122554440043c0b03e643e1001030044800c140c0716503402c8002c40340c41503140900100b804100c02440d0050800401a022010050040ea41802891b4040c1c400546040b030741071b00140d1002c0d02e00b072154103050024501402c505d1000d0900c107410149516644c403a01d101d60403001074082e060440041c8a07405880e0711681100403290f4a01c071440090b50703a201842e0007a40e125104503000d880c58481547d42448404411030041030665440c90292500d4010044110a20404010f4032660b0760b401e01c190350103000b0001211400d03060400314102220302581d0001d803140d01c030301515412807100005a442c0456a000d07141c41c000d400500445a031252030b4045003526007811622421030000c0302916224810503200011050705c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 755704289 1250 755703039 755703049
    0xa110f0a1b060c12050409020304061e0c050912031b0f1009120309110a03440d1b122702090402120d021e1f0504050c0604090e0c 57
    0x307100d0744001c51248420000003403e01c0138507003040409414400d042541d40c400300340990b84101d43c11907545545d00d48900100000c001606c2100070005001c02c5040e5a24001600b94131030300010a103d0300807005007503221807041085176803080d44515100094501d9020141e529800780605122500400d41a0160740207140304001a0f11f81241610034254400b0f8800d500a10306003c013500c0600417561b045616482d0514610001c40c820aaa80c1e410040441d2005d03550400c24882c00c01c0c0648100340c05908585070100d0484016250003450ba240f0b1031040302d000030240030030160540160316904410080e04200b0205023015031840900c04400e1400b084100c002c015030080c1140c0302c0000703800025041903084143c8c03192000e00382c008000944c1482c14a002a406102801a400034042c05181103120030700030180d400c0070b001070808803d407001c080315941f0700001004040b80e40c0c100050074410104400e04c02100c015011540e5031751102038040c003424034180142050320603007900100d14280 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 755705539 1250 755704289 755704343
    0xc060507031e091a0d0f050f010e250e120d0815040905011107020117040503030106080702030d1e14061c1407090212010605031b0a110f0a 61
    0x81540c4000c01102400c00012076a551120007a04215900360302186040d1080400350b85540e01800c0c840d1030b241807501030380c02c0e10250181032103400d0030001803100c0041d4a900703a905490b040c0040e2280d90b650b2404040344000d2190b10bc4c080072100340d480a030101c0d00f10040c2d0500b0081540c036641505a120409952140c0c04000c12000a49160018030b071107242c40c1c000d1042d450010b00114070316446480340c2c0d09451101508840d03445c00003400d07000b10768005000d040f03c1200c108c1200181d1409441d210303141c2c001482481e040c0402280042c805c00c1c42401282c44e04034032032a040040310351010010440c800700b03a1041118070314050461200420f011045442584020010300700d154403441e8a81402031950800c0f0b54207060426407402c201c006124850140080c03090040e10f03010f040b90510018501a4402c401f841410018408003c3e040803007050143d1108260940d9118006400c80c1d41104940c50304005000350038a20344002c00108844116602070310f080880e540c0030382034030090008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 755706789 1250 755705539 755705543
    0xb010314150307030c03080919060f1211030a0608060601022a0a0e190c0804050a06090c09021605070e070909240308070c080102030c0f0d180305070c060507 69
    0x540010580340c1c41078a04444054041c007903a240541d20b9032150039a103095001143c45400200c0c1003070103400c1c41c22000040982900c0780c84160f600d0400050401c8104624000c1001164164042c10340300b25001035518887c1050b000741c5d20725100ba40711004020a02030b05a40e4010040819659032001031710040420318626401d4407411010070012704d140000000c26005248000b00052000324040ea00c2d100d02c4c10721000314078243c841c0c4200d00485141e40512410720184c1c80c05d10010800004100000701da00a000207100501403c03c0241c1e48290361080c54418000141303111070b080304422420815102d80100d80005840c0d421560595408071078600000b401c0340020010b4590329040500c03200300c0b00b402c0750001c003881040e8030b0301c41d07503642c01c2641c1054000031b0a00c10005030f480004018a0018002c60540c1001b2442402e10f100d803070031201d03041c040411081201c0019900c9200a9030002c0740f130300408803151078003400c55044402d0556401aa80d140003030421b010380f00301d5072415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 755708039 1250 755706789 755706821
    0x50907090b0303120402040f05010e040c0504090b01050d0f060213050a0504060302090c0708040801110a0206090105070518041401141504080a03050a031e02040801200a0c1a0a0902040b0103 83
    0x6a0301d0a010713128034900410503039107c0c0e240c5010076541d01039445254060081c0c41802030103440c00e1300704000100d00310361100e0f000c0c92400d410100410074811700c0c1415524201d80b000c06110060400446141451401402240c40080d100000d2000480c00400f11074003507c07040c000341e6039541080100d80c018400a5040720a540c0060074200400c801040014815008941003e88603000716003107841c00700d200c200c01040095061348c102d404005040c3e00802540c0284510f2520307140090641c01a1800e00e240c2010b010602c21030b80c1c0d140e4000d5008081000d00c10b0846603950b0480c12581200003040e14003074509440005d4581d50030780708031400d0b0381001009003001d000b03680d4204d4140d4080c80c240e804050f9540012450301d00002034032221030025110241e04c582c2810440390031501c03030012544984108114813003520011505403540408075051043d404060f90410f0042d40d0801ca031090036141c4004100602d030451540540d00c079a00a580c108400903615006400720ba40312840b8440314 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 755709289 1250 755708039 755708047
    0xb040201110607200c0a03121b1212091a060a0911030106110a083004030309020a051e060a031e02070302100506060909040c0801020a0905090c030c0d051018050907090b0303 76
    0x208074008c10200380110180741c105040b8540c41d84c04512030311060360803100217031100744070391115078481d600000c00c107483c04080200d81711603690007030041c045e00300014204030180001a1941d66001d2400020312411006120320003000c0340c070700b0340c590003401000b0108401018804240300006401d260b102e81c050142441c2000e503c1c0589000491407400886010301c2000b10611030018205840c0514800e8402040d080c4aa10400071068140c0d00194010360710303140c0b02107080116401c0400440d00c140d031015030300d80041c0e004802030620114500c48150112417502c2c0c44075025801002c03a58002e6003690001007106040c3c10503500155103a550195060001002c07501d0034488842d001340c41203210080c11039840c2201750136a04035461007008203865070340030452410040c43d85980310884510305459403500405600306406100d04004245641b100001c02c21080207641c5000b9081c04423a041034151805200000340c50112040491030140c094002001d80e1140180981c03407200901441c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 755710539 1250 755709289 755709293
    0x6020f2422020d05010b0f0f0307050402160c0303020a0b0901110a050a032408010e0c1804110306100312080603031c0f050a050627040b040201110607200c0a03 70
    0x3035120080c4440003403200c0e04500d0303001a580d100c4500f288030300c0382c8000700701082903401b0007440c51041341c0454000d142170171000b81e8954007c1401800d9075400c42d001611940407400405400c6288d800051104080c10401301c103040c1c0005d140d0b580c0c9445100045500c2da10040b040d0b003a00c9003c1010000000140500104207016001034075061003d4a800280c0d41c101103516100d4044512010b1500703401030b10240000e0000b07010b040080c00301c0c0c80c01803030b808040d0340200d0503a03540300c82c5040e81040000301243c00c00c141c0c410300a4a0350300050841d111400d158092017240c42c4288011140550400d950f908280d004008151141000034041d5080200c1c07003207a501425440103a002c9040d81d940000d0301c1c149528451240245203154001031a44713001828401402c8040d95110400c0b6203902a44503422030b050006544a0703801102100e0b6500e4070301c01603a54030b001d090549418020003007008403443e0f00041c0380686504070300b00c2000c03600740700001e80d031181e070080c10417030304102c1210301800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 755711789 1250 755710539 755710561
    0x1a1e0c0702010903020609060d0609050610080105030606091801060312110109030827060c190507320a0506040b010f1a0307050912060105090709050306060d080f0406020f24 76
    0x30880101610300380c44c01020080940803509213400041c8183e0752802881005d04113080043b288028504010005505090001e9910100240003070300c5803a1102c0003074007242a50b03007021301e051104402403050300d441707191040c072040300e5060351000100c0c1c1901200422a0502075841c400c2d4258a8100c540c1d126983d40c0e40c1d292042240030f08050844040f11101c8040400149106210031695030791031381240d501e42c000c0c003010300c070380c82080020903c400d0740891030071000600c3c070320741d80108403c10380380c8071728407074503420110400200c540140b0100c0e83c140800424030700c0c80b891107885c55840c140e032600780c003c100c0d049500441c24004011000080c546d640b0b00d0055802219909244d41170a4580c800103110700d2034100b0801140d0421801007003241880384645810031002d082c90782d001814040880c4c0e03565401821315110b24900d49143c024041e5601c01c0b01e119204a5102c5a511902ca21010f5030303c0845c0c1b070f200703003043c828084402c40400c20700003000e00d081c0001d807008509460305580302d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 755713039 1250 755711789 755711797
    0x81303051306050d0e03091507170f09090609090d200a050f1513030e1503130506010b0901170702030f13150306050303030109091a1e0c07020109030206 67
    0x40034860204469505022502041d0000348625a20240d42c0e90b60328841c041602c03200c00081809600a108007900347d90350244041d82e450640c05955100c141c1c07814503244c01300b24802000f0350030748001002d00660f1442c0d0000c200858050741daa8000e51030b074009009022a0840d051217554108075201e03112a4031840d1a00070418804603608041c0c410001040d007844001542110036034000c4421111402d014041801064008030000085180511625901108111004081204004a0f055295205011004d00384071203004943c90740782030041400800c06c10b4105a07401c1c0b19480001540c1c4040c882220500070060303484409506040c4842d412000c000f602010a40c04240112081425020058485150241d00c0d45c09124a8007006608510400d0450001c140c20890244003a48002003146c3c11104000000141a840390500c0d018032000a00c61450f486110820b01c0111525600c03503860703201491100310542d0701c640400c0b04151140100003804100e030a5010070252402e54068 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 755714289 1250 755713039 755713043
    0x30304050112020408030d05040b13110103050405031b010f1410090b0a12030c030e10140901032702040b060c07120314072409082a03040602010b011701060813 70
    0x1d1304058540c80407034190381121a4606030b00d69180104410320a00000c0c041e0090031400c1d13501c1004445031070300c000c0a980c1150311414943c0f6480420100802002202c8040182c000512141d03e20121188d01a02244004012a50070516000c10900c0e51064a42c011200c1c01d00d00c101e46484d0100b12000352030141c0b10079500c001407010006910282001c10b0101600c07943d03901c0007080062074040c0c100701c246001c2d94010b01c1503401d0a0303d620341000f80d05a007400084202a101e000d840012009441c083c6200b410b07038a000e00a0305000c120700303094450078130320844003844141c0a04050191034003c0c62040c12032984401010001d0302401d0781008000c40c040d10b4008042204a00c0105072a802504101c6100001c03080c5684801e0002c0520300100462020a0208400c603486490711400345581c2ca8154030b110080c0300c007072420000244803e0070500741c00e032600c1da0359450000e4003c01040c000a80410505800305100000c580b9609050350040d032900e4205441e44c1302c0c40780d80d01c85a1101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 755715539 1250 755714289 755714291
    0x6150d0f080403080304080403020901121e0215040306050a1103070507030c030201060b0c30180d061e060906061403130c0803091503090d0c0c0905010b19020606030304050112 77
    0x3021000c1200131004501c0b0310700840326580d4030303480e61041c4081c521059101c042c0046628a803600001c4088111040048400c071403520108128000616084886036a0074020500021b000080050039001184034001c1d20804204e03c01c0d40403150000b6101c00c0b110030f070006104018020000e40600c0d450080c60340280700025820f0784510740344c0095070003010b2150103684810b00803ca034444070001c1843c982007244c55040c0507214540e14804501410804c2503842030301841424003901c602111140c55500490123124207088148980100c0c620002c40121050074200d0205501c240c030b01400c0211082c0341c0c0c408000d0041c8220400081d0805000003c0d0588522003036002324101c2c40c02f90000d4000c070005555500d05a0042082d903202000c038101b603040051040180090307000c04c3e00601048103040211070b100d458900404004816044800611324000010621928080c0038150100c51444883c0400d4080c5405030b0b601c59048036100d505900410082c041940b213580407050f9130b960594 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 755716789 1250 755715539 755715547
    0x51305060403060e1b0a090917070812090307030926070305010501082a060c0a0501180b1305060a0209060913020a0305060a0e040b060d0506070206040506150d0f08 72
    0x2000480c10307401030b4030555101c2d458400b0040d48040a024003442221100705118031690a14041a4159550721400c08000d40d100b29003820700c8040318459195600382c0040c0d40e0703a070031103107403444003500003400514400c02c10700c00003903040788004101d4201c40d8154845a030102d2901780440c0001c039000c19100784180d016003071506094401c022035000b844c81031002061030740c1840c01541c03070802e0b07110301c00050003114020030b80140c229075040408034602386c86140d0b540d40c4842204e443c0c071b00e55070b000034a6586012009400d10f0420a40740c170800e481001061107035111346000049215000304040c00e190046008100701d58050750041c41c1003074000d0401030600c072010002403da9010f00e01078001c49038000800d511a01d5040c401d80b54845801c4031600d0000c0d040108454038a0001440201049a040c0100b08280d8800e040080456449002c0f607141d89020380d00252150000e48040302c01c1e00c13030440400d122405110349104202b1000c0c2c904441c9241c035031161342001030f803540181d82c1468104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 755718039 1250 755716789 755716799
    0x30c131205070306051018020d1e0204061e0816091208030609011a03070e010306120305090f01020606012a08040f0602070618050906041512030305130c060513 70
    0x102003950084002e0520186142840400d84030024603044141e0b040341001e00c22840b03240080c080c03445c240c000060300c0741114203e07900201031082da00e601100103040c5101d0302142c9500104261890340c4d4a01085039280c072080180d001400901c0c0c004a0000c1c0002141e02e03c100401e840907403403030702d0600391040e80c1d445c005940307210b1700700141c60144c0c00004021150400b42915401040081c0514010415240035200e550001030f04190400c000701d102440d90380e1203900100040c0c4114918041414158a400f0341140d119021070b43c01000502ca030a0015030011034014803812040c1c442412b0400d09440c0300b45104003681032240001c2035449060041600c10002d00301a200907181b00c035081d4103245d0040d14194140d44207600300700c840b031450410700100040080846100b074806503107586610000a015010b00c0104101c042e00400b0001040c0b1580c3c204880c07203502907141045180c807001e00a10201e001300c940500300c000c00441c100102441030000b400d40b00400ea21400e102c0d500d036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 755719289 1250 755718039 755718059
    0xa060c0204200f130f05030304171204090506041a06160203030d020a09060801090c050906030a0f0e0d11060f0610050c07030807022805010f0201023609040503030c13 73
    0x4030f09059080e040400e40050403070300500c43c0006031504c212103142071890076002075a01c1c4164003031080d41a007544001c1610700c02c10424401803110020350541c40341c3e1100060388c020b102c02c13a00b0610860401002c08900d80717410700e00c4450340350060314051402071100b050001c07070130450404a0f00b40c4020400c2842c1c0540f244080d080440c5aaa03480c8520f40c5070071401400100c040c1c01414541c1c0c600445c00d0002c0b900f110807500c140b4801c1e10519140d40d1010700d41c1005014000c40f00f103e45003001c01030340c0c003a000460700019800460f2141a004018620690303a10343d012900a00e0788070380c0001040b05403a04c40c0c040c1403010350610700140b414511404150400c00319500880b5010008030b070504c00c5290009501d0031500c145117011058801c0c5050400003021548030b254140310989507030321078551003901141d8200d008440107001c0700000f076443d035200c0c200d000349880d071040d522459800d00b407901c03545036070055400070300850458031010038811165202c2e8600802000c1a43c3d40002d520880e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 755720539 1250 755719289 755719297
    0xc16090608060601050307050405010c0206040b0a080603010518070b07020f06070804090b040209011b0c351501141c1a0a0e030f070614091b0a060c020420 68
    0x5129010654610740700c01070b450310074040d100d01d06010007441003111459021069034121807003468070020285203400070031800e00c50754112021100c000681c0452035a008051075002c0c0100f030300200001d555951007804040d0048160b080140c00c2881c0c100b00d4102034030080c0001c14001040d40e01c5e0a4055400074140d617103c040103d441d03031000b00e01000800700d07038454906180d40035101546054030010000340440100c10702c005100525000e0181801102850714000d011205c0035040f00d0300c40c3c41055035440002003506644c102601540f04406040810003d101c0c2603102040e400903401e0103c04810b0b45090100c1d5134104000f401005150380c500c90382d0400030f6010780003840140601126003d10440001c14500140303040c4a4002d001c50380000c00c580072a801d4110f92502c0b4492490308101074500400c400c103140080409000e2907107000700340600c4c0b0f845024403000c11124083c0902915600b035204040224403015403040140c01d00c1d0f0420440140e0041d229003000184204045050b00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 755721789 1250 755720539 755720549
    0x417010e07060c0302070e01050d02062a07030c0504150b0c2103181501090b04020702040e030306121c0f020c0904150f0506060a050901141c0b240c16 66
    0x4520410f6006168050001d03202400c000c1c0c51114003981088045090326490050080c000c0500141036100e007109801c241000b00d0340c10f1141c882130094000010f030b40d5801800191a003000c4060001440c0c98148144000744414000004485141c02003002640e080401c0345074443c052901c1208140e0640c501c0da0046980b08400ca50302c80c106981c0c2d1983c505a403191514181c1d00c05000c02034400c0003400c040e41168911003000c6880a4031070701281c081e0241d044000c0d003040c2804d10b001500100400a188901420340d0300300c2403c0b40c880301c515500d0725a0b10170f41c209070403200003400c08284034103074002507030100340101c0f44a5a030000108410400c22103007030b07450541081011a510390b480c018801200c591a0040c0700c5801d0032000200944a18141401440785c0003401080d01d9000c0d18000b01e81d410030301305594480b1060130380050320700309281e04242c240f4a0a1240419460b0a404104405668011100404045101503d820342c8041148501407140500c4501464550580700001d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 755723039 1250 755721789 755721797
    0x20d151113300305031b0702030a020910030606140f011704120903150504020f01170112060b0a08060609010909030c031d1309060e0703020904080708070f0303090c050f0102030417010e0706 83
    0x4071b40444a0084505903440c5002140b200304030810150387c000540c090500c0d01114007180747c0e100c6002124183e141d550000304514180280020f46440709200d0032840103041d104890005407810046400c6125030340003012184a0a02240201d0295561a02c51501c1070800b280856120303107a5040d944a5404000c400036260006c110844c03d103519503005815080c00c0c211582030400da0b0382100154140510011044c48070802401d10040703400010240070302418008149031034010498a40d82c2c101c1d1400e02070650f8100010300724035a44a24041c039509903a0ba01840481d82d901106e007400c015080750031065580001010680c0c582c0050b0148232250074000910240516040b42a15071048001055400101d020005600e4440ea01d640c026802000c00380c0d0f038002c030f03d0155214094003101420361400d5900a504045d05540700c1d0002c180668004000196240100201c2c40038400d18180103801c2484100056581d40d852502c10540400010841000c0441c0303c42c50700c0e43c00c2d80800001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 755724289 1250 755723039 755723041
    0xb36010305061b03270a060204030c06140418050915090f1c2a0602030a140603010b13092103060f0824060d020d15111330030503 57
    0x30282d100d100100c0c03030b80004002c0b400c41c60170700c00718540841c034162040280381031a4840d001100050062030561584100210744650b2a428000700400f041c0c02100082090140710b4990070038004140d50844400c00341c60340d51140da40000801804e1701030310203600c034801c10400c0151840102c041502c81c0818030020018200040802807403d03060b144400c110300e03200110120481d0b4031280317280041c0340360302c694024110464070f0a0055094807402401851011050040858143e00300741e104040251000300d058072050201070803a20b010303800b1039208808000480031805150002c0003154051048802455610b42e040503450b44040d1607100082e80c3c90100344107034400040090b01130724a0100400d0442d6070301c0000446480c0303242c940d080d100054400a0560707900c0d0034003003c2041d406003500e844110380340b404115121920041184941c02d2005078001e145000c0b082d910900108611484071911700541c0c0200d4800e0400c3d4441400d00d00f0020101181c0c0c809948107405100f56076043d1342e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 755725539 1250 755724289 755724301
    0xa111306080601140111122505070501110f01050106020a03030e1b040b150705010f0c0f090902131806060809010c090905060607120905180408030403030e010b0301060311130b3601030506 82
    0x4814421a61082d8230403480d0081801b0507030015840e001d4680a00705074140c00704400b0004c1c50007428441100140d030070000046011075000c40c000b8420780c0b1986041c01400d03040c0003d00d0b1140c10f007803400000ba6510038883c1c3c07040c0c546900046a8841c014080c030070900c0021040c02002c0e0b01c44030f401d507034a0791503e82030301d01c51505124075000240325181800000340c0075440200805018403a2000b015000702c1c0d422065003905120340001c00060840d43c80b0312030300c0700800c0040d014034032501000c12111000103c400c00103020744001c51040d0ba03a03070760007541425204001000c018080365080881030000400194901400303081c0c6030905e8440080b0a842c3c4000c00a14500b44d818105580517001c0520000840c1c04081d290482da160a020800c07103985003045004195080d4403990540c01d02400109125002001c036409c280144e60f509108504060008140d8032920010307a045803010602d00e400c0d00142c0107503812420820b441d8080310b16030300161581d8100a03041514960400c0c414081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 755726789 1250 755725539 755725567
    0xa11040914010e370f1a0f091f0f08061b040f030312020f040b180301110703050c0c190306150501140a0210020409020c15071b0201110a11130608060114011112 70
    0x3800000807120320843e142c07941c0100700440c4018090954141d107000d03c29824030792491440020f85201c16401c52456aa032f610325543e450281c0703070702c80110781300801c0701410a041412103040d42e00c580221111145540d600300c03450b251060008003050790a1140c8518806180001e0008000b181401031301c840070240403088036006110350324420783c985080401e00041500076035020716014100180c644141d20344903410100c400e800c0d05d030722030080e030b50211500341d00440041c141c03405084200440000200303843c000d4a06402003d000c43d17108180c3c01e000b80030510042c150b0440d244141c8001d02005041c1c80d0a036001904001043e076004a10801c0b01902007080d5001c0c0182903840300c000e0306001c00060044070807140070300da60141000d503130001e59006200b9107440040c820308450f890b03e9141428498501c0c0c0303642183c49120b000543c1d000c550030500440d070942d9802d6015254903440d1001c924885076404100a042c0051f000a075103420f80180b003001640314014028542e203000b42c80e80c001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 755728039 1250 755726789 755726831
    0x120e03031302150c1504050102090315220804090c050f130e150114090f060706060e01080a0c180b041803030b0402070b01030206030a11040914010e370f 67
    0x12003c50502805000c054005500c403000e0a000c0441d4240d61a03a0a10038068131075a55851f426210341c1003c5d24401c0c20044806118012500c40e81780084028158058010460388020301201c0080c40b003400780420030b5200c142b03010140d0410600d07012202c104127047c4c0d0420010349100074121802000b50482c1e546190390b000300030707819142e0320001c00070002e030941841c2840c0404020020580044645810b0010800d80000401450b140d079410700d084009803006010b41c03c10a4400c1000041d200b100069002c10103510907603458400381055503080c00081c44c0c05c240e0003030030f807101101d80035070319544a080c0030408081402c003076031401400d010301034a400c0581140074520400107800412281c82c00c050540b036045450030303900c0c0c0b01d01003a40040e2884041124030b9a030000b500107010b6140361b22100724510681500102e50780e81d4502024041000c8601103026851103400d051204074030a00841c580718070555009642c0c10f9041048122441000301c880c100e55128620070340401101201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 755729289 1250 755728039 755728069
    0x12070302090306130303180b0a0c08041e290a060510170621070603050606090a091e150e1602070e1b0a0e040e010516120e03031302 58
    0x540c98801c00c1e00110380d986000501c1904e140403060191010548240c0124114410026524003900f6190901600b5500c0649106030000d2412001200590040d410a40f199400007400000321400d18200740545410301c0701191145845111102484540c00014450050302c600c903040c10b150404509040b99460b40000d480b1f0094643c3ca80d070865802908540c0d01d2006085130740d115141c40300441d600c0383d85000c9401038441c0001c9900c209200c0010107408139421a44c060115894039002d0003494854011180d4000500900a02c011044c41d04103d10704020f40c0040c0603a0440d840c0320004980c0301c40885041c1300c4090500b0041080b848030360641140c0c0388440800452000000170f5070791201445601981380d2004001071845070341010400c813a50301400010340e108d600001c02008410340340403a600c200e291034001130202c001445150710411120148044045810600f42c60110000d0000750404d034603171028500c400c0060002d5809000700884880c40701e4511302c10405215006500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 755730539 1250 755729289 755729291
    0xd11070b04050d090807050d140604081e03010303200c10030501230607030f09080d03050709120b060f060c01021308120309070501030f0902031c09120b0f0603071a120703 75
    0x920801c1401b048040444004481d854503000310f070301c1e00c3c000c900c4800ba001c0c4018043d0354100401c0c004104018516091403000712503071810444801584c9000a002c0940003484886c0c2c0d440c003c00741c0031321700c0d10082560011611000d00400c00104215820341924001a49a1004010030111001004c0706601c13a000005604580f15001c00c1150190420203010082c0f1618003140c141c0c0a0741044019003010021b44400090208010b0007900d0140d17103140c0000c0b40900d00040c001556645140400e911a03a240d6060711041c003081045a180d0b00c1d0306074051400c002d0095840c0007440100003080c2d0754100e84040d80d01c1c1622144c104004807000f1000360000304204120f130f04010540405030b40003420006044040180d001005068620000350148074003254108903020014100403540070030303039401900784e0b00d40c2c00b5500c0c51b0040c410f0061a25605d00049401c0c3c400105402c0e5004202908030b0300c030310f99100d01c80c42440d809182107035004440001c0d1201366005802c42103070301001a0030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 755731789 1250 755730539 755730557
    0x90c05010212090f120303010321030e030d09050102040f0807030b01060806010504060323071205100609060815060f0a18051e0d081803100b0609060d11070b04050d 72
    0x10080b2418400c00850510883d00d9510b004d4240e529100f00000000c0428100c903125a100d10b01392031039901c0780610303103041d0382c60b12001c0001c503110303010b241c0c4103480c208061801d003606100340c0d4001d0821424212907a540030302c00031515603503110240000b05200780007031002900d1414010790840d410307008607003040032031020420b0998020040343d0031506140b60022380344010f10104003035480b401041e40c110405200601c201e80340d10400314108458410802c0003151034a0446036440e4042e8822800070612481003000340078040d04046030300510f4031304d1a00316005c0d441c0c0000c103150300c0901001308685020450105503540200c2d40c41e041c04000c40c035070600c4ca040900064100144a002114103103580ea0206015100c5584201007164404100303034541903138204a021810f40c05070301e9806803084103240d0a685d081e502444144190140100d440c001003081030100581c03240102c00c012a0f1602800241e5204510041685900a43e540142c0703050502d0300c0782c18110920751002c20481410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 755733039 1250 755731789 755731813
    0x8010806010302090609071b030e01110609060a1805030a080108070902030c19030e0607020c2e0305180f0309040f1e0c02160b03040c0b1c0b01031b03090c050102 71
    0x40c0701c4d0380210080714400310b96980c402088600c500c1500c290440103000421f01020980c009030200b001c01000d0700c130300880d84100c02003581d84003000c03500d42c0c100e80e010700d0201d01d82c0f40c2079601c680241148000a949284e00b03d44403070b0300d150300511301030380040c442600400500c50144500c001500d0f2058065141d0308142100d5180e5015901c801c3c072801c088482803020845c041d07403081c0e0b407003006241518110f1601d4540070352140740d0140b6050240d004066240c00e02950340d01181e00144565000c100c03004c54401d000c030002c01009000c00420a40400c0c108a03003601000019000a0981c0045942c0d0301c01030240400d0303590508418140c0d60800695025401c0c0d00e0b41e10b14070f224140c1c100002c0050010500305d03e405050001801540601000414682c1000d401944203a00410003142c48e2591180088180c2c1f04154503110841404c90690400e003280c0e4001001c003030720500d0041100e010104529404a5500c000703400402d6a0718084800c011101c0300c4500108000d0014201541c86a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 755734289 1250 755733039 755733049
    0x16020f19120b1012080a0c0f050a030e031204140109120501021e04030f030c150f06240903110a1d06180c0a0516060c0c0510060b070209190c0e0108010806010302 71
    0x182d000a2080d174003c00c0c4420124400c00721b045680303802a44c2d10482c003c003402e009880d80c113001e0066000807550b400b41c0c442400c00141003441d40b190314041c186801d01c0d054a047c1040d4510780f000341080b600c00f0000400030484109488018040c07030005035a810100040c0300b050b003002440d21695007080c00200003080c000754168407500d0301803c1500d060a102d1500c0302815012420013064240b0b05503009002076510350003407090362001c0081110a800b60780e0300d841c2c10600301481000090400800780001846481030080c100006820540d8041d1628100c07404448002852010090784604000462030012048441890b0b149200955030a04c2c03400780340284542100c803014030000003244511108020341407249150404000c01c10f05049010080451a000000f55264460762091015982181c440c6208860b40450141d2500400da800d000310840020702d019202d1404020200340103100d0b0040311a07100d04c90b80d546146c8c0000c4800036002c21010b801c60349203941302e2001840142c5403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 755735539 1250 755734289 755734319
    0xf060f0114030703020319030207090203130f03140a0f0e0a0e1f17150a14041202011407180f1202010e0a0b0706020d0501060516020f19120b10 63
    0x11181415035070394145021a14215039640001d4040c4200034510300b04030040110501985c1c0700741c0c26600f401f5a95059402640425505030350900702441d03980000401c85c07c1c4c040c050031f00c0303410031000d02040c00f080260640c100c400c04c400454220342c2e240ca0060740c80020581f8200702214800c02003400c4c558800349004004240504a0419204070b08580c504400050014480d510130060311002c1382c03803072035100c8000d404058002c4080b1404106240602e0041800d120b907811500307070142d41ca81d1141851071000801c0030080d5541d0301071034410b0702e03078103400700384590195240d000704038444518103004010940c0c0880c42c3c030f400222040c040240e80c11a551000b07074091034441085903103c400079101802580c001c0c0444a0001400c604203c21600900040024400704100700d81e41c4400580d024030070f8081c0c0c540c600301841001c000516040b0074405030302c04040c1800380c1002d074043c408403c108149c1c0084040400d0142c0500c20854040c110980c0314200155150400d4a00049100002c1e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 755736789 1250 755735539 755735549
    0x30f0618011a0c1002040603060803250c0b2b0c1b06020f0d0c020d050c03030703150503070e15012a0302010b22060501050315040b03070b0c0f0f060f01 67
    0x81c4102011889400701c00c25030f90400c4100741918614a1042c8a41e0002d500a21851000c00e0a00c0c0d000130740032602005580004002070141d8070a07480000d03a2100d0855101c1045a000290031004280400c20b00d0141268110120306040751103480c2421114102d8482a640310940c01d00d02c034590019032050350b200e6145420b5048800d42201481c007078010b405010194074501c1c4000c00c1543c0b091249400200070b00c07a0a8090b596035201d055800ca6480c410441020046d60041000c10140c030302c6544051503041c010710314010000d4485002a050007036076031290410f0025a07040c08283c081c50596110b24917000d00b0054090304084942c0048000c014910200c00000344018000f40740c000c0d042010582e10041030761518011607210340e801c0c0d41003a02d5080c041407608a0129003940250216401210b41520b0800c00002e1041008003130203024205541600a240e000580101c41001800105900c00e01a150b0b145042402074a0029021600301c01c40e84954103108070b041d07a04c990581507507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 755738039 1250 755736789 755736809
    0x60c0303050c2505030c0609070e160801170703060e010902010e06041202010c03020709150306050a0e03160f0b01260102180402031315020a0207050301061401030b011403010b030f061801 82
    0x10340b141011405c60145180450480c040d10b01088800080410391805841071000080c19580301c0500944096580010941c040b407400f00050100078481001c00140c0c80c542800c586000341c9035a200d03002e0f2140641c0746880340c1c3d1a4807a86045681196280b11a1f02c0c0558800b41403030318003409806c4c200d0541e80e01078140039415140b502403520070320000e0050680110b0a106080f440030329001006001e21003074440c60718080215020882900602d9420145813000710704010340912241412941e8940c120341d841c14000c0703020006030f46003035004d00815400c8900d0f4090260f540800280048900c176440340e41c3d20421054600c040c48555030510403109480058413a034911440c0034070408c064401a0900b03010701402c03407030703501103400800103000e40da806d440459030703a10141426200c3c035008040d81c1c00c1c40044e2000b44c951081d4410039040c80149041c040010b80d08862247d103600070382000c400090b0020800c20a296601212034201c50207442c1d05240c0c140300d45d1000008141801214024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 755739289 1250 755738039 755738107
    0x10e0307061e15030312050f070f05071502030117030304050a06020d02040801021813180f1707030309030306210f060b06120f060109060c060e16060c0303050c 70
    0x55800041c400d070320480c1c0103404100001d41030282c6881c443c2c151000300c00088140380b207600d180b1058043c031130240c80080c8140785203071500202039440c00704045800080003018030880010580400c0c0703402c59000703034442c01a84c80d41002d0103500107114484032003210364010001d000016100154041c0c013250800c0740140c0b80c81c010f100f154007070701c6141e0180d466036001187c00420320800d000807800005044a41e1355404401f00520816220542a23152070461840003081c00b20b103036040350110070341c0304640e1001c000e21141c00d060400d0b0441502500029600c401040070181c140c400d800c094900d01030212a29070240c10800b160381300c0390f20300410b014013440c014000c114640d0096500c0500050040380c490007034060a60115000310707120404804401c0c04600300794000d4862030151001a078a008051150f5103c0d01c000e0210480450494400c280d000e40b00c40200c10407500142400f5561124102c01505008090b40e80103040c0c041a4101040784010345441d164002107032224031601e010203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 755740539 1250 755739289 755739311
    0xc140a0b13020f09070e0406090506010507080702240c010c030b0a0b0d06050a270204080c061312080a180623090901080303090d020c060a03090503160503040f0503010e030706 77
    0x12041c91002825009890310042c400c070f01b0b030050030031142d801041d501000301e02d6a404164003075510a90742e09001c2001040342c40d01082040d8024500707a40048d0404068140a100c400961900d03400540298900403c8110b04c091b802c1c00307801c4506100b40b40030300200406d20700240409031688120ba00201001400507001550340e00120b008200041048181035a2051200349090b0428200035040300d83c0019a26001110b00c02d882c19101b8041c0141000c80d4010103002c200e902c20544030312408914440010102c0c010041f80d1150307403103090290b413115010100901550f0304c2010303500e814090b21105001076540b0042c48400e1000e40b000b04000c0d41c59481e13858100c1d200e034880454000c00400c00115151070004011801607170400122143c9941c164012a150070184628030f61000701000440c078020300ca9003003240914026801e891034080b4910701e50012201529040350a9080410100840780300081d20030000d0900790700074805951001400c0d07890344640e11000f03003820390b030b40701d5119 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 755741789 1250 755740539 755740549
    0x618260f0d0203090f0a18020702120307050c090f1303030c052a070608071403071b050f0616080f131703150f060328020a0c140a0b1302 60
    0x4050400d00040c1c1d03848220a038002901e81c4d000007422402482c042401c0c814a051040d00b4100325003030f130603403000100801101d95001e0352014909907840007a007030044480080c18001406801d101d01c0080814180b0001840080c0130000c0c820002c920304101040081e5001c40318151a0325410f140018148403105025256405001518070103151000590000f800d8152000705081c1c0e5990100d4000b140d0301c58086600c0c070000c0320700c40005240c034008035003141c0b20000595082030480c00c0040700300000041c580340d02c603e480b1054034541d1088540104005003440b20340d810441102c0480d0307170351408200142040c84040c0406c00c00d2035255001403c00d1800c030402d6000150b0000380e0850300e175400c030407208241d0800d075100750400d102c6040e80c01482c03510004010440300003505007030850b0b5a080c0c12005c0a0b143c00303809074015100a8450f0707034a024038801401824925255150031194505100840600964101100b540001c4130039001c28005800e05912500300d0500503003c0e80b16101040f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 755743039 1250 755741789 755741803
    0x1803030f040323090a14060a0c050705220b0102071d04050111030c03070305010e040c0b0703020a14011d0f0307120219120206090a03050307030f02130b04061826 71
    0x40503142e5200004040b881010014400c4204c2240e000349201c0d00d40c04045a00101c085401794009010001c41c0701b007074068000040b40ca8080d205442c2da5968a10100d04010811100c2803d00d04a032021301040f01c01c02d1044184c054801c0c40284203050926070700e26043c0684010450524280342d0001e400c01a00350080c04110385855516034032414150120352554105913840070103c1e00303080c000b16560301600e400511a5800802290320545400300d807408542c400300b029821030252403441c5e0003040d1b940c007a0b00c00343c1c03c4d580000940c2001c10400d910342d022200c0ca00c80c51a4228216162204800200b6aa510368007c940d9100406203048d0903458202070b500072810680780151603105000300250004010070550702510340315511001e81586070340f91410028040351040c03002c1904070f8481d034402c00d00110800001460130400f40c0140030700c60f5582d40f084900e1100010180000c0d90301040700c5021220380e8010405250170034000c203403080f05100540c468001d0a4880b180040305c04c000d07207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 755744289 1250 755743039 755743067
    0x90605090a081b01090e060a03060c03150b0903100b06040b0c030c060901020306012a081b0f03300c180d050a11010203070506180a2103051803030f0403 67
    0x214416800f40d01c11100004600001ca4082103034070000085503201000300742e10840008210400140c04e41c0d45880c020403e1200744410965540000382c0000c2080c80c00c0000707405c02d25805030300c41c180401003501d01510b01400700f6049040c1032400c0030751b44030307202034030b040c0c40b0524008c4d40c42c4c480749002c1d9440c44c014040301141c2480780c602804810f01043d40214054038080c1c5e82d1102464a00b10a4800100c0e1080e07080500c06c80c200d10390010031a450b003d0b003c400440301900c0c440c80c11a4112038501180140c044c0d22680000a070500b001082129100d6200b1100c3d40c203488000000c3e05400b4000401490f10002c8000094544041e030011191b2244042000f03011008950319414034036599502070108444284816003201c01395800001174131101a80800144030707a6440252000064000d0201071f0414420b860031000000e072035420040d01e009600b8580300d40111104402815543c0103410794100b035408190900900002008490b801603000d00c5d00110350716286011034110801c1e03602 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 755745539 1250 755744289 755744293
    0x1b01090b100305120703050d0b0a1203120506010c0507030b19110a030506040203270307020d1209120f06051005030d170a0c20030d02030705030103021002010c090605090a08 76
    0x1002000c1c00c1c0d01015400341c2c2d01a070100c0340c00100c0e03d0340c0e03452184285c3c6005008540c040c010f050603d002a040288608400307481194590343d15202e0051103086100101c02080600030000c0c8646050f105080d448079091a010142d082c141e159075031038200c2800094010300c1c2c940006441c1c0411010f00743c0050103840d20404c00b0300c195488241c010f42000300420006400c00300443c140d80351500907a40513182c045e0759486040030361800b0f80d00c07100401d055024540030522441001da42d8000c001e42e0018016640d03001e210b801c42400510402a41c0c01c59183c11150110040101c0c0341801c0f000086a4415400501a1102c4d43e06040d540701e00d501c2240c1c1407140100b07182e9801e911121164164651451009042e2140c2612506540c0308903003440001d460f0481003181050100c031040710b00d40005066902e40303101510404203070f0340100c1c0c02401181e00000108110b051001207521022403620007040607810026004080807860302c28181000b2010500404950310054080010461001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 755746789 1250 755745539 755745541
    0x3020304051c0212060f060609010201060b0c0703021206040f0809130606020115090e0307030f05070501051510020a0507060305180102070c030605220303020d020c0d1e02030f1b01090b 81
    0x6040284000b5400c8120300900d012000d0316022180001c1280c02440201007007a0690340d014240007c2d0b801210646046640766000000c0c3e1030081002007400d4180c90014001490541c010f011140d107141c808091141d01900030040030035502c200892100341d00004080c1c0d921007030000510f03072100760010500c80c1480d24500150f041c1d01544000590a82e090058000c290360b0b100c3c080440b40050f107440c003250800c200007000248181410295074446007480c3c3c3c00d0542c540c8a050031528101e0b10004824024a034030203241c540108800620074551000701501807650f85c42980b0384855102d04030a0544070004180c0c1056950100031b610010b1900840d22103d690406a607841124070041d04c2c00c1d850580418011003281d8541095081851884a0f10401c1c581e4128025849076010b9040d0035428841e8054814080c481501d600155540d54165141691903d140c1210200707065020341d03104206c5500c00201d09819520b40540c0e04007600c03101100d50405034058806514001c10741c000c3d01c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 755748039 1250 755746789 755746819
    0x2091003030315050604050f0105040e0a090309121e020609031b100509012c040504060209011805030a110d080a0804031101091713030b01080309010e090c04120302030405 75
    0x90440380a96018040c60882c1400706088500600510790004820441440035083c01040309000c08010700d0501e18196a8070f184001100003a01d111a44071786a04100040c5913000130a5009401d01c0b00b11442411010fa8403400e03a422010700194040b06480c58100c150360b00d0005564181c08040c05580b85000c4a1600b102c3c01400080360b2807183c0382e000640c048041c450000d850b484141a11509000c0d07040707a01544088440c0c10982c0224600d182c44544207490340e002c1c6a00907445150b01589850441002511a0000880a003004c07041da2070204080c0e500001c0044000741c100040c0001510b900021804201c98504040c00c01040001c0400311340d6807040c203aa1256000e40d4a01125504140c0741900382d59032020b0141501102003c51500448540d00071300c9840c0c0341d02610b46c60300e603a0350365500001303000760302048180d040411041a6543c1040d640700c100c2e44102c0c2c40d00d16074501011028190300841c0103081000b54403800d0241050b000b08201c5019201c01045848074003988 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 755749289 1250 755748039 755748061
    0xe220b090a050105011e0e13080703030c080f100b0f0c0106030f0b07020a030212090607020901030b100e010302062217030304060e030a27030204051302030d020703030503060402070c030209 83
    0x9003000b11500c1d86401c00001310303030700150007088111118044d804290382c81c080b0081900100500000e02c1c2c285521104000108030038020305440740b2944011800000810020f006014000c08005c0c46c51124010080c900f1070440c0b5031401d607583c101c0d40c1d944070002d4403001c1d58280200140c0c64060b61914901000707010426400a02e00e5102e00140c141641e03640d13004a840d696070103030080160b480001004880b03204080680403540001d0700c0c01d818031525030001007144a00703a000380c86650b801c9c0d081c0007d500c5520030341c0028101c0182e007183c55515503404aa0b00c1c0c845c80d0000c801ea03c180480311300343c2581c0c1c0d2007280003c0070107000900c00d500180307110a41703950007900d044032901c2c07511090030244079020003952404000c1d81ca0304000c03856544844202100032100e10301400a0100c000b000580d2039101e403600800d01c5640c8403160f2100e51060514200011030548103540c042841080029070000482c1e40c0824252000340c1c9804840c0792146d2040c00e5500000d6021018108000b000d2000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 755750539 1250 755749289 755749303
    0x705030702120f030a140c01090309090c05040506310906050405150f010c02150a02061f030c03030c020a0b0703050a0e040e0705090907080f03130f0e220b09 69
    0xc0740c000103506062003255981c1c0c511019542c070740e50018000741c216031b0702924029502c2c88440c1030740340c5032200100718642112600700003180803451110080c8000c245602c0b030040300880d0303030806901c1c2c1400c00d80014500d004044c20030840072000c0e0010310a00580104080034040452940854641c4074075140001d4001030040c1c038040c600e000d0011780d9160120100d110b50b00000307000c02403405450740046440c20481380b07040e40c1120200c1010b03004c414041005120040b40d540c0604041d04044451039098051485030b0f203a404440c00090010440201140c401c0300c0e498108000f048426102255092003280d10030010140f000c102e40c024076800000800c121f00c4c40e035840c420302d03500700d00402003201d0380d107400940d4135404544140030300c2c28110f01040c0c002c5c5804080702e81142e40c6203003a80c40d0264050b81d480f42d5030404207480c1c0d60b1090851044024150007145441010308066145018000007415844501d42c0d90080c180783d00101c44504900326001101d604283c0303454034410b43c2e00c42d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 755751789 1250 755750539 755750543
    0x9060d09080c0d090302090a0b03010b060c0f070504091112010f090c14030d02060105010e03010b0d1a0f06061c0e0d051e212809030801060e031c0c0807050307 70
    0x683d14106075040c0700b1220002565401003c24030300ba107404449800608004403200d425660303a0018503041d40d10880940f044541010041c541d032280640d645042c0110350f40803d025078200962040010900c07030080d06d01074001e540401140c01d01030707140c034050034000c1064001d2a1409458405008600d40000c003900c0f01e02c4194500300c104081030642d40c145005203440140c11120050240d03600c41c194003090b2200040000c0380392000100003030340c55030041c0b408072000102205920140200a2030044c1e01010040c65002140b0b400d40100340c0a1140300f20f501000c1c003c40e2401d503035441243d44010200c90b0680206c0c0c6000c10301c0e950250190b4802490003145001c0c880901c00707504103586c01ca4030f800350f5568450a580a000070198641c0c100038050326600740c90b12058052502c080c001080500c0350240d40071607030f0306040c1000303422410184c200744108004400041c5158800049440e84241010b03014180382c0c500001c112840c080c4a180200165400101c07207040c040c1c00006041d0740c2c1c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 755753039 1250 755751789 755751793
    0x204050f011701140d240c0c050a0f14030d0903020708070303020307080c030c0a060f0b1816050903120c071415070804091e1d100209060d09080c 64
    0x8040030064030400585a82515070b101d10500603c803500a216480c0c059042c00340500804d0b494540e508a89941038400e0002c000c1031030f441141d103c1103140585071340c00b1407a041055100c0c0729030302c40380e441e0342c00e034800a020900da02c44c01004104440303814010418030101600d0b00e4191502205000c0d0501c03850980041c490b0b1031000c52990000708044080380c0d8160021881d0408035a2800540d4101d114605181c1c0030038803050035205414040d851466100e41d0b400624050920122822220481c0f00180640308000d000720214043c6040107070007168030034025001e440d4200c000c80d924440d8611864140c018030070200c20007107210000d400d12401580a9034007151f22400030840102c0e001300e101d60f20001807442e5402203403068008000d5a80581c5010b4901610781c1c40c10300940340f80405440d00e840f46038480c0f00c000101c510a9010203c040040c1600601c40440d00c1d9a41b40741e110004ca452550001d98195182d807400d0032240302541e490403d008a10300381c100710985800c075003107010340e074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 755754289 1250 755753039 755753059
    0xc12090a06140610031a0415030c120615050a060305040c050312040824070507060f140103140c0f040e070e0c040f140a03030c060f140a1a0a0311150a03020405 70
    0x854000d00032041021040500a071884050ba01000040d081c0a401c00f404440d07550788c0072001c1980400c010b000740103441c5c01034000e15083d01c0d0410454140c105040c0c65071603d4801805642d4400c403140341182c8061801090903115400c061400411690041d0760601c100400603160015500c0500102c6800c1780941e000b100511003d01d03c064942d01619854034581030008200c1030003040580b20050080000007200405440d0503011601d00e1070f40b9000d00d0856400400030498050720a01d0090f0b4088090700c0070b030482c400443c40c0d107908812150b1140b5210303c0c00d072020140c00c01a0b1401041c603202120458208900c05c080f02d0b0b4018080c905103a0340000b0041030452400b00c54080f60880038041c0e002c034500d5a2011200c00801d135034201d4055450b0480103101043c580110b400300c2c00c51002126840c1008001401219008448a180fa101ca100d446d0903da48102441c0308480d08112000c404000210020309190307507190038440d07000c60109014400300d078141d018106843c0c065403200c2c00c0e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 755755395 1106 755754289 755754319
    0xf05070906090f0b0109091a06040909121b0615230a050d0f0f05030408030310050f0d020d12050f0a1110050c12090a061406 55
    0x14035071195414403220394903115864041e505040108910a841e500280c80300001780324060030250f940b19401d0700722007000003038a1120001405156501e440d03404200060290810a45031400f02d1456089458081c0d8000508168a400f9081251455603140b102a090030000034800d40d05400001070041d100062095440d01c6405034490b15241c1a014014240c00660009100c0e80b54840d40304007090300510800c0100780c10a920020005403414080c1c51441194032000c1035200010801072210100003105007078883c125400c2002e001880e04112044104500c080e5014005694040001d0b8103001c1c2c48104a940b402c103c2d08207800038450407816002480d234100899070410203090321348014880c0501c41040540c0800c000c0c200580c04040e130340920115591200e0007100802d00a030750030440003001c6584944180a005400b90064a090f02c090328824042c0469000c040c00e = true := by decide +kernel

theorem cover : BRFrame.Cov 755575539 755755395 := by
  have h0 := BRFrame.cov_init 755575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 755575539 ≤ n) (h2 : n < 755755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
