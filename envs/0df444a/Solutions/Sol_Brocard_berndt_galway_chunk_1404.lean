-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1404
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:48:56.040353+00:00
-- url     : https://prove2.me/submissions/42a60460-13cf-4b03-a885-bed362406a9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 252338129 ≤ n < 252517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 252339379 1250 252338129 252338131
    0x2206060c0309150804060b0102071d0f1807030f14150417070312050619030606080d0504060e1201020d140f1e040308041104020301030b060301050a11090607080918 72
    0x390b140c440926a54000c1d030b0000b80082e100603000101c808022600082d616006105010014016150b01a40700d0454020054840286038021032b544007e100c01d03a505104203075044116142c01a00b54000c440296544003403a2000900c1640344443c08428450300248544140702541e061b100c0b400f800d20012440e14500b52400e8521f0324907851882010a903031021500c69560546407100344011410001d402400001c00d5140c01956a44981c80c0a0640d45141000785200d0840003600d00d00b00320320140b800c0718450b0b0b61003d002c000c200600c02c1e00d07086802d25030403080440384500310210000065003e40031740d00c400d00005003400c0003051900c00a0120900c144164070750700c08217503100c1081414807404c0c1e032110b201c4007075820040350200f4456a104c035402030084e030742c4018421042e00405c00300e900990050f551415100280420f45c902802555003003006610240210703981c0c0500139980d4800c00d02c0051017001c002070300c00b007001110f00941da1a02001000303500707d542e586031f11604480d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 252340629 1250 252339379 252339383
    0x4031413090c120e0c09100506030c03070801090605060f0a02010609020a09080c3106030b13061b051c06080307030e0102160803040b03070e0405270604112206060c 72
    0x16810010120608041c462800d22a0b0084c000700030b0034001310140700001d4070190000360700020034400420300d6155000294050340981003000e43c2c81c48c060074002e04204042e040f81140c1030400800704507a64a0000341c5400c0b49080171400d03640c001070001a4018441d65101c0b0704013034000b03c0c0b1034200e84c2d0448602070803520140142c4e0b10880040c810032030318400078001810400004007150703901e00c0d1440340715403000c0b810400c00681da40c1c40380c5a0042004046450001c44003201d10070038100300603800b851154010075008411a0010a440a0050300407010681545034603401c26200d43d4000341c104030028500713802602d81d070b906942001005820321101c0d003409807240001c0f41d00c0c2061045030b10021100b9101c0654141400d000c2c3c0d0030781c16440640380c402008002c1d0040c00440d5910b11442c0e0103200284901100c0e1403801c504101049103250094501e0b4001904102c041422022002d0070b803402200d0031044091401d490201e407950412010300e0403498440007040c0c07580c201134070301070f268 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 252341879 1250 252340629 252340637
    0x10170108210c19050a0c0902041a07020102250e04050d0206130f060b041e060f06030c08010509040804030503180415060f0c02060d0f02040e0a05040b04031413090c 72
    0x80020310101805200c2d004500b50075038004075108054201084448035558840c4040d58040085900c9660b526501c1d90008101c0640c0080c1c10008010b4405500c0045441c0d1601b480c10200f180e00043e442c0d100c41508100018941c1690452a001d0b005210004e4086000c41c1421810300703082071581c9511003510740001d441001c02080d0000400f0740446211744e840100c0b1700b403210b90380c1e40306802b03803080600f80340e00941c4441c00000c0030100c0120b0b51203080c00c0d03030740c00044040c90a861050078001aa00c01c2c41454548640d20206175440109035054440603078982e070040e100c910b441c2c0c400d8852540090540d000c0807904a840c8864507010030398140b004c8070301348400103a104030002ca138030481c032504001ca11043d000020845c0518410b40401c0d0009252900b015810040c200a44085c0d040c2040001e5002800b88443e003140304849404c4030f5145030400c5289407a65443c000d8042c0a007000d014083c200008181c0b600c240e80c11607410101d0003201100582d0754920100c050030412110f08041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 252343129 1250 252341879 252341923
    0x30a030c170a02061017060c0703021023060910090203060a050d030206070305010f2411010c0306051c121b02060409062903061311030c040e0108010c02060610170108 73
    0x51b00101100a00344003c48001c0c14590701c400c811201f060780b004200300d041d400307180c0c216452200c10f48610032a8035128030194141c00c81181103100920401441240b045581c0810b2020142d8084007110035a1003034800140e5a440c0c490000c0c141d00c02c1c43e0b21180d8031440c640e48680401d5408a1031034010074598505015a903280c245841f070004860040140260000d032907021124100b046091000b8100d06140f041a48040041e5003910410303407070303a40805e071507800411184c20440c0e05c65003c814841075030340c1c03082d2150307668102e11380d4407040304420065003644100004200e9400c0008096006041650711a910100318004c0c21441c40750807004660b084110350031021400220700c140a040c5034542c81c540c0c0b103d00300040f00a9004500144d50340d074860323900c0c1c5422580e00950007120082e056070b444078078040011150a005030031080c09641400f8600b603505400090484e0440d10840d0b0003154141c10348800c6540c900f0148075030380031010900000a12210226021112079980b02040c032038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 252344379 1250 252343129 252343139
    0x50a09020922062a020d020c040501080c0d05070e09150105040203040f03110c0919150e07050a11100504060b0303070b16090e28050105030a030c170a020610 69
    0x18911201c5480094200b4044200c000281c80b688034040d03420b01005254208890a02a0311054107504055400b60f8071146420b024035070100091004500200c2d410f004542c10802c400d82c48081d42c16096018050058008081007001d20140f4041c3c042101c1d0640b082ca800ea25050780c800c01581500340e9043c402001003241e04090017200e02c00c0c5d41007440103032103030724a5400310b404c030301c00300e95164030741c051404201303138584e620100c8502a82c07800f06e07445007000d40c024141d0300300c03007480404c01007501c1070701010410f82000442e03090788445241001c5840b020360040581f101103038400048054010001800c261405035401113024a00881c020007584482100b490f66a214019001d0000032070b180006440110441d0030b541031000500d84203a809070388428981000c8d03001d0315240c0e00309d07800456a0b20f00311303420b491290400c14131242c03e1101d545010003090700c0d14000040541044601d41c1d4a00901986106000034001d40261103655400c00305802511200c05907515500070010040000e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 252345629 1250 252344379 252344401
    0x14091b0309011512020f0d0501020412110406060507020a18020403020a060302030702250e060414240604060525020a141203040b040b0a0c170301050429040902030f01050a090209 78
    0x88a507001d4072122551b4442c1040140a40140c8400c65440d902040702181d010140c0180310702c400d105412507001e0b600440104070548141b5000002088002d000c503101590311240400c045402c80c00303000c00d14110542020010344110f0300301a41000c900da40c001480fa41c03540c011071181c0e04540c01d0707030302d240c42c8030340070072a0b43d101703034000458100060105000d10310f1081080d0360031003c0104001145081c10b015060078a808035040b0403003c074142c07010442901000080c01d02090221062803501e424104054070034090440000d030142404240c0c4100716510700000c0011640003400c55503155514180100c04070b25904240e4082c0742d64040c00c41202c000041610300b034031014101c5508283c24020040380d40d0300052840410080710303002d04404650f07030244441d2203e0303500510aa030303503040c60b0a210545134020707508500c1c02c0002c210b2010600e40d84003039400ea450f040f40c010818981600000b403910811001e607290725483d0005000d071184072580500c651318401e681e00780301c0ea40e584074610707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 252346879 1250 252345629 252345659
    0x30324090b010809030f0a030f0f290901060c02010c02090c0a090807030f12050f070c050108060306070905120f120306030c090405070603020322050a061514091b03090115 75
    0x29802449084806d140342c001400d200c011610340002e8040440d00303140c040d0ba002910000c461a600e001d082400c113600200e8642940364807403100f600300c04400204101c080d0501c2040c081204040c00a411a0301c01c100d0031314043d8004240c0e6910341014810a00c86510103600c08003c02d041d03540000302d600380403920204032a0001c058070540c02544d210914211801162102000020000e12085088100c0031b488607501a030401080c16040ca400035003202406403145120750701600400040c1940080d0f0401501d0094414040310300b2050303921454026210002c00043c0500c040c11489038440e00c1c061031113004200c04960340800c0040074015854000c1e00d000c1c10682200009001c2180650001c42d0440c1040c01c10040f040c001c200002140c500c0c045003143c0c0741e0000034408040c05014001c03403058505031200c160b10f131880c081c001c500c090f18a4049600504688000814050007003180344104c01c40e600741c2507030380d203070480003240285801415218842055040031801c02d03483d8601c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 252348129 1250 252346879 252346891
    0x3020607150e121b0718050406060b03010b071101030b12150c070302030301062303070503040b060f0f010c0614010605040f091413050a080d0603050c09090a020d030324090b0108 78
    0x3883c42d0440e0312161304551409918050850b10900704000b55000006140703120303031348002000080f5400c05280c841c00fa240e081c0c0c0050b04403a800c3c07005202031041d40d01103800b81030b44021581540c641040c0140d0180510b06040d0341c0c4412201b85452418101240152281550002d0020a45c1d40c501c1c0c81c1d10700d4064160040e0040e4000d200511140c5c2c0a1810b501a540c0b010501a242a031070292500440d8011200b42000130781c0070085c4000c210174589419005201241d40b01100e00e00d8501045010318403039601e60400c803c40c040c0300244070329a800910341c100000d060132555070f191240580240d010344211103805540c0080082c40754150f00c90300300c0003240c0c400150842d8407035100411302020b809100f0b8420b4000c9060460010f07510030006c0860300e0304054046012491400d184c0d09018909484a011b10101810031a2040011035071a85860341101d4845229480303007403c40040c204d580c4149040413031004040c00240c00380c09170340c040325034481c030030700c5410005801159030800903281 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 252349379 1250 252348129 252348163
    0x30313030b07020f0318030d030603030206061504090c0903050d0f0f0e1207080c151204030804050712060218030c09040b07031e0614031b1903020607150e 68
    0x103100184a41d00100d4201d1100c0c812180c0e485a9205140e055a12110310303400a240c001e4180750440c101803142c02c080340c1107810300b0088a0703d10303100030752507180090150340710b160140100503451030301c0d038140c5000d808014010840d414940c0005040000c01d80410394451240c103441d00e90181c070078890031400700002d83d94080c1e408070f42401500c903c04030001a503807196048002c030544c2c2c00104011401800d0200041c0100d0f50801c0c2401006c3c0b140e180d01100d00c070010010f4400b480401100783d60499818605000d031a03441b400e289040c401d1641001c003050000c00201e4042c0482900500031650300e412080401050a01c10155500c1e8000c09468110507d5000580400d00e1491a140d0205140c1000303e0385015070403d40315440843c80803c0079040e550002030001030500d40040c1d030310134025401040504400004020940000120700e0702c501c3e401f80075020b07603102c1c0a107450029503001d4030681e00d4921030700c2c00380c100b28100390300004080c1c41c0030802c00c81c032a000a16403140e0601040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 252350629 1250 252349379 252349417
    0xa021c05060901332715092102011e05090916020a020f0402091c06050f0f0c07020d080d0f050c0406050a0302180a0b0309010506030a03050a0c051f14060303 69
    0x11380301c1c02e0201407118100070b2000404281d02c16206032820701d82c07002428981045024142201c0003031100c2d88083c1801041090386007440401c64501409200d841c0e5000c80944600451004941c41c1c0001c180901c409482501c1c2c0c3d0340700b990442c0141c034504034225503500c6990b80300c0c03c0c203603c07940f0070a10741d02c016400b407038605016061045201041a82c0500050b160840500214400054001c0440d4004064105a0042c040a4800d0a401100310300200b034150074442c00031800d4180140c100100840006007031000c6541d2180c041403010741c00b64103251140c500c4410320004001e91400301840070706080000c1d1681c8024030444083c0d6515864075030405100250860003508050321400c01c1da1002c400c00da1243d52200d0310032009049840690b41e9070f1400f80e0b4524255074003d00154001d80c07003940c2d0080005e0b00710040d20311801c1c07645440c511000716410581d03d442c010481010342080342191420303851055030030400314826190810b4040391903000a00d9960b109a610020510391044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 252351879 1250 252350629 252350699
    0x807090903091e0f060f020f01020c150903130b0d1a030601090f02041802030414070503030306040911091515090901030605070c05010c050d05010501170406050a021c05060901 77
    0x1590f0340903d841401200340450b030b01d0f00361043c2c090302290402c401150005211150656040040d000d80c03a6404d0001d41c2441c0307400000907541e10303040700d80800c180c02c20341c00201030410030401c2e03941b1107003a0030656030303410f90351082e0111540c41403082007403071820080e5401e08a9031485503460300c030102034001c0003a80e10b050349200040070007108210000b50200000500022076485a02110700c114600698a003881d15104210701c100240c80c00752500079030750800403070b82c0100649030b128400340c40100300701000c1c2c50090901501100c10701e90003c04141440304c4042c55001c0340320041401c1d90780d0140544003007550303015070040c5500507900403142070040c4001075682d081980c0144080c20304a820007003555406096a822040c0c0c100010004191a81c18030064000e560042800382400c0340308925021369001d900400610140202d80c46070301190110740d03540d0440315061260880900410402d9910f080a400155052441280c20307000102e0581100e04032204404a801c0c480d4400c0c0200d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 252353129 1250 252351879 252351899
    0x5030606070b0408040f050a06020a060c030906140f1f09020f120f04020f06031303030c2601080d02010e0319032a1403090a0f0807020d0c080709090309 67
    0x401864100005000e03440005600916450141c0d01c03400c49283c40350f0421450142540b16a848244030300c00c2e1440811030309401245005800f5003090300420000124001980608140d100c000c0c40d00380317801c210500307034203c1011041c0a90540c60501c202600e40c02c0c10200d1040e8600c10515001649800c104600c00082e4002c4c5091040101c00c03c1c1418940b401b682010350f4100d03603114000200ba4200000c52400e44900c4160500484a03507044d414554400c2080c0300350035034000d09041d51000024501405030040c60561100071078500328505082c060307040c03411028802c0d44410b2180d2480305820030300601480c00180c1102d0000c0d4140784000d1005940500241d03958428075559a1141c8003071600d00040c001001a2021481c01c1140544001450021010810481303d00700b40b0510204900200c0c3d112211074000640c0844200b503814940710902c85e499009500202c0c40724210b0401c18101140030441d0b9240d801d64004035a40c0c170b0400103071001140c0040010303115110500500083d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 252354379 1250 252353129 252353131
    0x1203071403090f0304080607032406050c0709051815060607080a0e0409031e020a0b01120501110c010b0108130201051c09020a0902130603091703040206252901060503 73
    0x904403850451520901d60866110b46c01c0101c0c681c0241041004964050040c100301001b400b0104035401e122200c10f900c02c42042c01003c1c200100001c0344d588071401004450064401c00d8400c20030340c104007181049400e811400c44034240589503200241e07001d4451480c0c41031001400355840c0580d940d9801d4400da204030580418020380c840c0c50403081e15030384510100705121f41c035104400070400d41c3d90040507607402d022000310750001c010480002c0401d49450f0440b00d010310241142d01d031610b44907024052007a601a981311021a40c10684501508810440c00c02a242c1003e0341e22403d00e5101110341700c44010340070540412011a4110f03520fa50441c02c0740c0301e402c0015072505a940000e064056560141059503008101b030300b1007006800c4204000c00c0c80e401d0410107000302c0d945144079440c07019a80101408080002815502d441d02100c15000c0c0803800d40700050890850300904035400c4100780d40c850102c1d07071003810f118654641d264809c5140d0005c0c400d96841c02601311040e41c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 252355629 1250 252354379 252354391
    0x1504020a17010e07090e070f050a0201020d050c03010312080114011209051c0e0f010e100507171c05070512090c060c03030109050604022701050403080a111203071403 73
    0x2464005062095907418034041d01441d080700155040c00ca4000380f088600d500116440540c0c10144164260402c1c0c0002503040b660420640303541031080d0a90090040504801401c0c0c1000108030402542e08002c50503640700d030051803071103088044101c0305c4403801d0040b00c64046900003001840d6002c0e0341150b540e070104620120300080c0c0c0c1d07900d86040980640d00300700c2c0b10000348a424400c54102c0055a403020080d944c103007800c1680340000703180c040748501203805441c6480350341e10301c41d02c108100c66000743c1103401d98100c0302203c11990b0040e800f002c066940000b4080b10780c0d21603c0c090280710b010380740581c1d030107044c0700c10b58811180180006d050743d21948640304a201c00781e20b0b080d000d0980044080051900e85d0315000d02e0300155480185890302c01c0d4810090392a101d00400404900c4a018514401e809904c02005940300d100f140c00c068a80f00d00490501c07007840c0c0c0503180b240c41042c00d105413125000c0e5800414034a02056580768040346070f0380e1014002d507072101c0c003031039003c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 252356879 1250 252355629 252355637
    0x60809100b1c0b070e1504092f0c010c030204030f021c060c02030a170112080c160902030a0c080f070c05011103040b010e09030a0906050a0c05060f070e0301051504020a 74
    0x1842591031101d86241015084500010f00810044030030b82080781c0d03000591041e280b1501c10300e0115841034151260b4010b0301000340e61055200310f96005030485418030405400524000c2e060003a03881255046090500d01c1e56090103c000c1d4820f01c28000d45080f41c1d405401780010703545a60070400c2d1010701079040f2042048030042c00c404070b601401046854007103600950f64840c071004000301241c079000c00300102d1a003994010050400c0c3c030844c0600c03450b0803045194440a07040c40c9642006001c08014403045250302c0c000c5202d0031b45030700560150417030f01402c019142c80311201307803111202180c202034034500c0031000030201c1d4050700400c40550321800c0000b650001c3d0944003043c1d42c000741c60aa9500f4003d00041c010000030140e02c54208000e44015400e2010119008000c0c207060700518003044400b06400300310768000d00c5801c650f190b00c070701682d000e03107080349000a0100d0708452041c001901d07003544080030705062280600030915040c421900c15043c50038040030f5444180440100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 252358129 1250 252356879 252356899
    0x8010512030c0703032105040c0807050301050603030a0503070c080d0f06080c1012060f0308070309080a111516050105060f06071509110a060309030212180906030f1e0106060809100b 80
    0xd1b80040c881c0d2485944100c4151130403a0420011501d404110340119000b80e24140512030155000401e80720382031550314029030780380d544c2401207910b1280e488001f4850311022440760400d40ca40c0d0001130110044000810243d03548201381c030798441c2058100c0760454400308200d40745a01c180b80d0040441d080a40c04a405a0740e076401030703803107440d95009548122010503108109a031015039500100781180c01002c4041d0240c50b41c5d6410a5020201032003003401300c800180700103001d01910031050300400310074580301580c1010f90282508a40441c81030400f00540c401614104007902c40c41c64004110b49001c1c0310051400740105006601a81c441003c45c100c07407150f0b50381240d114050940d5603004903100d0001c1c98040e141441822200307092032000d001544130385141d40341042c511030007100d810304240c80f5400031a062104001c2080080c0c018001c0000c5200000d401c1c0841c0701b015040200941c6036100c2c400c40d00a41d003503525240a0308500c0c02d00520070350942095a0902008101c0520 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 252359379 1250 252358129 252358187
    0x30c010c0f0e240a0e100201060501090e04020d0b07020307020102070b030705040e0903070516032904081e041d25050705101b081008060a090302190308010512030c070303 75
    0x183d40c0004c40c0403000a5192008000c1d40e0030080c004850300d903568002840814145030010303026000b20301a0708240c0107151300042c19591401000b02d42142c101044501505100c20002d441c1e5000c2c5805030b015201c0d400e80050a060070ba0100d80c4110f00c5a13503a1070030b203400c02d20486181840940202035a10042c0050408110305100107208101c406070300101140c95854401c0000603001500000003007a8010310b04e40e11030410040d50711a5024551669541003a00300030306a005a0701c0061417007138042000b1070900b500a1f2125446408200c2c0019281d032001c40d0b15400f06100d030400258000704040704841c08d80a40c0c00381034201d10680503984a0021388103100c0c100e84460140384c0403589100441403a0702e030000482900a0101419241c4031800c00c4402680d8400180089003800e41d42d11140003071602c24407682e101d8111035a02042c40d0801810001c0070f540707081c051a4820b4000d0821210640e90010403500c044264402030301400b4590344041d180109002c2c0071220100315400b0b90301c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 252360629 1250 252359379 252359449
    0x60f1b0503041d100f0b070f0c0f0819080d050405100203090d0305010602010911060a110703050a1b030512030601031413060c050a0512060f12030c010c0f0e 69
    0x805804056680b02070050700da600c40c40c4010001d42800c0c800c3c080241e050001781e030100b800c0c10170358000c3c1e050269150004d243c40040308440100c0038205641401c0c0100c4e01c4242480c3c10403c8480c0102103c4152a1982c0b0041c200b0480000042220800300138907510780031590040350340a0301800a4401540c6076030a00d0342640d1044800d041903801142800e00411703003501c12035015103030601c0208450b0340c0c40e5035600307200c2c1092800307207102d10004103480784450702c120f000301480840784050310f642c0e950360b140c11941c4222201086030034900c0440d0f02e00d40000d81c03142c004c045a810038010001760a8600ca40c518551000e0304044c1059154040d41e000603028004580c042c07400005104a5568076040482c01c460441c0888010050104194281d413580641501e200c1005520001002d0312028001203c08185681040d00302086100701d00a0510100191a000010360028820104400c10490318403180503880c1d00415205010140790b81402c0a051100054035030f10740d251204034600c408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 252361879 1250 252360629 252360637
    0x70603111204061b020f01060605030603030a03110f270f090c0c03090a0e0610140901080604060906120314030103020109031b05031b01020f06270c090a090615060f1b0503 75
    0x4e405a400785c4003441640d0b0702440b0b6000200401e1030111b045040101c002506c0b4070039040794800f0162550a82518001d042c01291b256034045a00e0650350608642c3d070401c641c10b10110824030344440505031050b070502020007042c5c001e00030002c11300c80d03860021750701c896042000300181d144020300c070345c1e03040e0744070320074102c0292421100c0c03034882e4541101007241184050381040108003251029865190109040e9164584e003404c0c40603d9a0300d040204009064550003c5c0003281024000268122244440d00180b402562601031980000000c22818482844002e002401e403c02c00c0004c2001c44d0f0b4248010341140185108865546001030728020402c005a120200b064610389008e603010400c0d140007040030303009400300341b030694802005029120443c11400f41100d1038884a00404d0044a1408800074240c3c038140c101890140020800039030100c8405207400407491820180220710030480d0181d0381d42c030150190841e0f007210300f4400c62800104141d0b074090102c0c00101c3c140058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 252363129 1250 252361879 252361931
    0x5030403021f0b0319020a050d0302150718060302040806040602030c071b080c0301060518040507090c05030105010e091b0f0c0a060221010609121502130807060311120406 75
    0x4500f00c4201030800d400c1107149120154840403d9900e480180c9441382110100c1c4c808440044c2000d8a6040990619615884210300d006403d41084170903500107001c49050050030b05120309090b04c6920981c100c1c071450242d440a51b00c2000000d00141740341e001581d20485200303510381040380719514600c24155052640c22640420303001442a02d01c01c0000c040041c03002c8000340201071510011808003035040300c40d200300d4283e00c000a818800708025110062911680402240844031030080c410f82003030080600107905810520785902d0500c045038081c0c1010031241085100c9410107810640c00350324044502d0320240542c06500505020142c0003500071400540e4035031200503500414040000300c0c030100d540d10740040c807031103910490741c0381070340c85001001090b0400b80c1000c41c020100340d20740703034041400011540021200c01e810841150455421119407a49032030082d4190385114040509070882403141149a10325025003541050043c9030004800d0f02c92100e403001d83d8950910 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 252364379 1250 252363129 252363131
    0x1805010e010603060b040603080d0b030a0206070b06030d03020415081f03050705040b030f030a1103040302100e090702030a0f050d18030507200906060a021f0e0114090c0105030403021f 81
    0xc100113010103030081c07160103039040b102001000e09503a9414907030701481c881c601c4c6041c1d654480245d00e803020064860704580041040d602d03140f5500d08049d0980c030440d0810f00900440071200b140034041e0083d1070a4910140b901d24031410941c000316103d840080130540d084030a400030070505000c2500c8100514050f0700908656800d001c00d01041e2603035494290f020760b205505188142e08040151341c0120008e140a0004403020301220b480c50255401c00b83d0f120301003a9480c504150001000000b030003081e01c81019540e03a5903401d989a000d01705c0c007000480c84555207140031a108000822000001d004c000070182d286070309801d45405162003c40c007045000801c20184a038524904a014495445803105680f02d00081801503402418041c0110b80c003081492034180203103d0041029a04c00c40101081480602c1001038624003c00f4452946009440c4ad52084804000c40c0300d43d40140c000c0522f450041c004440c6a44011b0054045000fa00140350004140b01d4002c50b02881d0020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 252365629 1250 252364379 252364391
    0x10f0e061b0601120b010510050c150403021006030b0c09031005010f0317040815060f0d200d05060f0711010609092d140f0f06010e0c0c0a061805010e01 67
    0x901c440c0740400c1a0040030034032070ba0003100700009110711015819550169040711141d203915405031454082d103102e06070140130300c00084002a0502c00000e109070301030742c00c8803142c00140b41c403401100c1650002425040745030000135800b03130404004054502000d011940d024152084c51812200d0a030004080d0000d155030820a1182001d5030304000040e00790700e076180c40e00c3c224859664041c51401200d0031414140051703402d80d40c0e90050305c1051006042d480d50000340f4a8020b41c0e2422078040c0801104030b004803078520781030504507c0f2103241e10a0084c00f20b6201c030020701008000003445101000300413101e00000314000c0c0610702c0100080b5202080a082c285001080750b40c01488921800752540688804002103411030045a5001002c0040700005421082d0900c0d80782d40701c1c03e40c03510402500f038980b100e00092a50482d4100d088044554484038500c208922490401060550103903600c0004205643e00c07065030b000d400141c51041d0101507913022300b564036a030010b05060350350704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 252366879 1250 252365629 252365677
    0x6060d14061801060806150405030a0614090a0209010e10081509100b0d060b19030b04050c10081609120b07020607020303070c110406030f080304060e0606010e010f0e06 74
    0x800042c10404012010220b50705100004092040003402d4a1042c458980030803699602c00040f10080d11010342502c07584e00b4107041c090090714603c0c044880c5c040c01c3c44001220404042804181e00d44c0c01401c3c100c0701e9103842030030120b480f00030700721594400c04008002040c5504014200564088000ea819246080d40b840342c242503071004c040800c03906041954107103030703100307142184017a500c4a80040c40256000110b400f510020a107102c0c40344a5a81c0802070204c003141848c411442030040b0f841d40d514200500c481000031601c90404540014042000302ca004c403c00c07007000c1240e00c4c00904183d560040f04d80040d07607101d4140e580d4160700041c0241d05505003c01c070f0740b214080c00103601c0c50900440042207003025182c041d008040f0311080c0c400076030302c40e0042001580c1150148082a589080000c502c3d80159000c4420307615004103042000700100b8560700c036a0b01611100705110420005440c0c074400400d20404000c660079881d41ca6036185000361009a0400c42022580045c02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 252368129 1250 252366879 252366889
    0x3150603100305061003030801051201090b0106110c0409030917010f1404050f010603050601091e0c020304060206160c020904060b040c02031801140406051c0c0c0210080f07050306060d1406 83
    0x9424040c4079010700c4021b10200750400400e034110345d020354000c9250f26034003a0707aa004099051380140f04a02d000000074441d984960b0403444c1107030510030ba82040d100300c003c0100300d4401c2e60000740411842030301041801c40c40c034214030141d44134500204040e15082c280904407800510220070f031901c1e070f03130600003807210400100d007240300450300800c001c9045031100340d6190814071900105a40741c5034200401811080e00034030180705da000500000320340150203500d0703030454007900300184640030000341ca00c840c4440e0554500559194140d8400d40d540a01c40c124100034000c0d55002e84500442d502a1601d100d034494442ca03a501842c0c5a8112544002c00c05081084007410086644404040d0f1401d0b181242c040722018100785039034004010f200300740304d1610500c51084525002c2031030421a005000d0252a5100721103400810300d03151425035401c00191260801c54407044c000500361750007000299004000284840e01b4031110035007180a40d00811b92980e042691001449000c0c100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 252369379 1250 252368129 252368131
    0x50606040f09020d061409010915030611070b070203040b180a0b03150f061c20040f0608181c051b0703020a1a070b1e07050307120b060702060315060310030506 70
    0x7006e000403182c402c40000129000818012002030a0744c40480c0072107071035540194002198481010f1007400e00d2030b40c40340d8080d00000000e0790039200c81000510114800b00c1294107907040700103801c1c2040900310740c04003681d01319002113808c2500c1e8100811041c50f6040030b1031040c000b140b00021a110044288881840c0d20203006000301e4040c8105600c00840c503041d0414942c0320f40e000119448003414001184844d60302100ca00000068046a61884c1c41ea011043d100b103922854840c0c7c0743d0400b01c0308040440300d15004d40f50041d82e580500341030051040e03940d014203407501900b88068403116801440c5c0c0d4035807241d02540200010021814400c0c84000201700b06070b41d02c40d003504800780f9501c152003961001001300d003074100041c101c084500b101450640054108a4191a00707010142543e40203032034130404603401410140700743c0c0c1070b4050171000d5100500403e05140603642070000315040513003503500708500300d0180c54203511440c02079440f500750000d042021f9869070034080e09140f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 252370629 1250 252369379 252369389
    0x70501030b012304050d03180f0302061207020c060c0c01030515090105060705071203050703081807150509100305010501090e01080d081306051609050102031c050606040f09020d06 79
    0x7050010050041c0e800c945000380028044143d1040400054915600c41c8070b80d4104640c0082034180c4e440a140e031120f1429500184c407035480f01039030384840079400d560301c680c40001d40c807075800c00c070100812000c80f5080381c1000c60790046a210b500d1b0b07000064007503000341051900300d40c00781078686807a41e4140070f5140c000c4807005010104039440c0c004282c0790303241400b03081d01030b41e00050b0a0082007010000c0d00300620300c1c420a12076001c8103240040c80c40d40180c000303a001070310f142c0210301890003080540100010350340041c0010752800c0c90302c420156101c98410b092190501441d889511440c4e00074115410303544d0b001030b4640c1003000141c9080c0d21504180c01300500e130001030140e5040016010307240d405600300302c00e840e42d4100034034008010708040208502c1c144410300034094018003224110f12620b44907000342d140c80d0f0004a9036802540c18940812030004881c010031110341c3d105903044480070705a5450940c686a0302d103142109580030000c032603400514140714100320b125601c00343c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 252371879 1250 252370629 252370631
    0xc0a0203060f0907170c10050409021602040b060a0f1b0b09070e010b03010605090405040f06021303060b030d0801092304110103050a02040623130f08160503060f09010603200307050103 81
    0xb1500030101507450321003846c00c6015407031000c00032400b07501a0090300e004103214207080d941d40b600803546e10701caa00307405c60803030003503040074a5041c10345000f40075108a82c04594680c20100c03400c220848075040801881035801707019422860100304261000c62281c0f41c14002401d1451400c0803103900248140d1100150403014070050110651040803112031010480d0045040c0c0c65a00701001f1500004400610080c400200850250308020540040300c0c000d220400c4040c03080c07404d140e11441c00b070b2038080000325010018040c448a0340c0c02000d61442d00102c3c04881da440d420074000901e0705030303000c1e55000d0070360b0f451001c0b0390782c18040d01d540030008110a50a140c03610001401b9900310074603961201c0e9000c5a0050150701c0281961026064814454126592803e00c0304681085010b401a00d0040342d40300c9004a541c0f03051001181c01c0503004044940c3c0d041c2c1c0904000b040034062180d1952500d07000404100305032030b4450b11034484c481880042c45c0a108042c40c0c50b190b94403480c10300d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 252373129 1250 252371879 252371909
    0x6040902030604030c0602040b030a09060b03060c160f08030c0301141c12030917040e0f0c07030c11030601090c081602030a030b2704031b050d050c0a0203060f0907 72
    0x6031004201d141c3c10139418185420440c050785480e9000c0d01564200700c0040401108011007860b45401c9050050b00440d8104802580107080c552070f1a03044420726030340c40c03041102c102e000700f0894035130702c00500440399107600208039581e10001358000d40720300d440450084010700c030030485008210b032000801c448100f040890000312030385031b400d00c1c10050032800d00c0c0c07407507100540e019800201d45254800310103a541003100c03c5810080c4c1150017500303140c1c0410b00c00103082829180407240605100300540c2d04240041e6401c0724003200b80c840440e0300c03c40d500c4800342c05403001c01103031380604603a50011078070031240b5000802e0208010600240b080c601c0317900c1d8a0268010044800303c4a03180343c0415081101408184004d00c01c002a09040c4200d2aa410b03280500141c1c6030f010f140309540700c0101a4032440d041003400150a00502180c104101510506005000910400046405440c4a10421340010703043c8101283c40003c2c1c21908030811261140c140034140180000f03091420350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 252374379 1250 252373129 252373133
    0x9020907170a05181c0207051e0d0201170a020405100302030708010303031d0a150c050c250801090f02151305060306041b030906290103050a0e0123060409 68
    0x140361001d0080000c90b42c1e5500410158401c00d082150780e806000b0880b001c401c642440000051a001700c5800103004114000c140c0d860006003c1181540800300046d80380d03542000c02c549030b880681c0c100e040c0804030761008000c000040240b803280d41d8010700141c90f1450a02030000d0305d25251942410984108200007074030b50130040160540343c05103800144020b0381c007443c80901407421032078005445207440c140204000f0446403e80d0018551080c840610081010f036544d0145040c40304054200d560f81e0354034000270004115405242c0707901000c44566888196007100c012440544100600d102e40c030b001c2d0305003110070f04020301500300741d83d162040034425015000000d000701407250f0340c00000300d10303c2d07940c90f080903004141e42907a010500388580030150061030640c3d400c4814606048001c0d505020195190304521081400e00000b0000c1900440040038010020301400380c0e110704000ca0490f01740b260140e1250f0800341c00c02c20b00b8000c9400340403110010a1640325906040c581e03c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 252375629 1250 252374379 252374417
    0xd021908120712020d0e01060509070c060b150703030207030207170a141c020a210e04050910020c030a080603031e03040305301608130c051309020907 66
    0x32044a420200e921952a00101160501c03c0500b8500e461400400d80f81d003021050352002c120318103c10001c0110b2981c62041c0800e20508680003c0400c0f0b103040c6910118000d178000340c2e20200c00402c000391203e407404203450765400600c400e800080d40492204201901080320078080d12401c180e07170b848811004180ba9851005180041c0a1100c43d15030b0b12114504101d52420000e6243c40c1881d89240003a0007582c1c0d041001c002ea414113030491600380d062508004220214015503681005040c442c0b0602010b00006030010007140325000c01003180382c4481c40589044c075000c1d406513039a801503e5004240c0080a80414420f400420104440c2d810810315888600311301200a03480e55501d0800b038995020f0f0f1481078130688504842c03003905200ba01c5600c94078a44032009004191180000203400418001c00030000c5841c0f10003142d000b071401c102c1e000e00a03105401c40307120303145c444c00801e440030342c255580400c064541d00b0500452a0507030304160f2144003403802480c0c200308040d003a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 252376879 1250 252375629 252375637
    0x709090318080d3b01141206040509030c15070f0509030703030c030921210206040b090109060e03040518100501050310081b0a06030c0504090221090d021908 69
    0x19040c440030309032103500d461128920340c4d001d1120b420030382d0b00310203000003c00e01c0040c00c0e040c403800180728803a00401950910180e4031960641c25075121036645e810240801000e014107002801d02c018420240e80c94005c210031503c00f00000300d00849820584409026100f02c0c030805000c0c81002e105190450302c0026000d01160703058640301c0d5200c0c0142c102600c08019540200040000c0b10a120b4400c000005c003601c00c251060407195100e80070303915071201c3d034000103140000507004a070108010508518116410121403000000d04060380d684480403140010090001c5e6007011408000a280481140d850490016041216840c0c440d0840360010114052241130000100100701c80700e4084440e1000b03400c0810455038070061003440780140c10081c0c507a251050842100204045110380102c12059105c2d0b1a5a400c003400d181c402400703074200e210007400300507491000c1961207040f103440703e006034034420260004c0b45401e00000e05100003000c40100000c0c500501c0400114030004071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 252378129 1250 252376879 252376903
    0xe0a030203061f1205060105030c180411011407060501030b0906040b012705090c130b0312030405010906091202060c0406090303050d061503022203030c080d0e070909031808 76
    0x500119035941c0030200082611350070208445034141408000c1002c0054068141c1d03004404035401e1418078010483d5095621a4014410300c2100c00b05000441c18400c2c00b00c4050141441108011035a5448002d078120035000c0d101c1c0340d1108010018000d0380c4039020740181c2401d0140405281503215240201418400c1402d215080000c24104007840e0b04011502035441d44144064180369141c15511507034802601c1c450409421000c000b00445c1c0303d101442e06001d00a055407034034000700000250001801030b2039039501c0348090070010741c45100b0032803c544504044c0c45090b203408402450480d00901d4010400b02c2000103100680d041000340c0201c0c0e03810320b8126546c0400c618190050803d40e8003084210309500d401d11007903900b40e006010b040d48403000c007455045280d2503d0f001c1e40b40c0343c800a0b000c107014452900c08a01c10300010212840d02000220f801c1200b11a128600712456112485907541e40070100d0805910481682054103080198000a801c02c00c080c2e484000d140e0301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 252379379 1250 252378129 252378151
    0x1a030c031b0408060a0501140102010b0102100c0e031e060705040f1203030221090c090411060f0705030708090103051501080105011805060d06060f02032502060403050a030306060e0a03020306 84
    0x441c1800c036080074119000351441c5400d5821500300454548040c200070b00540307a00d10f040c01380801c2154130500c520030840f603050303008084854007601c004004280b44a03c41040281c0c0c001c20401d0380d2401c028103010344441072811403490110740e404030b0818102034461010400100410004c1d10852901d0300c082d941d007442c41c01d443c00c0003442c0c154001d100f00b5442202a400580c080b012191090b5400e5200d01c0214080c1c645002c0c1142c10400141c07000c442c01003070380c3c44501c0e080b40c05090480103409005019104c00340380181544aa074a1500800421521208000703119031440d48c1c58064690810200c0d00100785104920300080c0c10728205015081c10000f0f0000c006945c10b41440e1054018040980440d0b95135000c01d182c000a0002c07070060b40c010401443c0340b030382c00340d10000c200c4002c80d4100c000c0e031103460440d0074a00034583e2224411390744090240000700c0841c5007400401c1c0314620a40740060150f00c1d142c000381100d019075000324443e54100c00d007040980c034040f500301d920103903040c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 252380629 1250 252379379 252379411
    0x61903080d0f0216050615060f0f0705030909090d030f0c081503030d06031b211104020409060b0d06050a06120b041b0f140721020c191a030c03 63
    0xc10b00c0000c2c010100d8002c5200f004815140030301c43d002c5100382c041d500c5030b03807200140e415010510015100d1041d0325261240100111011728501e6000b40503c1131059040c3d92030700b0031540015802c540140c030208865041008107441180d010300c148112003243c42b1003402000c40c503050283c403001000b401c1c08101d111078520356006070b8040c4111207410700c1d859401c1000039101c0c05e00e08005018040c2440780540003203004500c41c4c0b843d031190854212040e002080a07051607484207642544034402d241c01980a010101e0603100e94025074020300708500d1110703118000c0e50795030400d503082588214095070000e4801d01a40340d12020000081da000070000c00d4001c0341c0404600105050f1002d08001c5e02c6008000f442e06500001c912100c1c3c01030f98585028201d0070901e00151311812800030b010b1103080301c540c000000d0042038080009801d00640320140340c0080810100d1906001048071400006014041c0c0c00c9041d10a40c4915401001c81d4118517216410000c00e01c009403803e03002c224448 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 252381879 1250 252380629 252380651
    0x6050913050901020901031d06011811040909060b0111031e0c010903030504030206010602010c050405130216030201020405180f010302061c0c030615020307030c1509021206061903080d 81
    0x118441540d0880010405494480c0300309000350031121020f40040c0c14144c980b003504414580e41d05540140501a21240e4a00740b2500842005103003070303e4030720ba01c035000d800c0c2880964010f40b0003450a40340110304c9195518100c0100c540c081c00703241c140003442410508600c4000b00361044246100941541060300c003c0f002c03920f00400c44603884540c00c0559410401d0b60540281d4000d0348642c0841300aa600d07218203070300383d500c1104c51100242092204101c9031811034244842040c400d04014542040385104284071281a0313401c0d005030390001820052070030a40740310340c00140701c1840328029050401040c44c8058041c403029225400104000b054132203107058003c030318401e6030401c011010310382c41c002d0050840da21950741100e01150035020541d0000c011120040d070305542d881807044040d6a44030300300c500448403008036035580d507104c0f0050715131994040038481071400074402894501d041040703440e99081303c1508181e0360b0104000084071070007650720300f205540000c03da00c0741b90 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 252383129 1250 252381879 252381889
    0xe04022b060306020705030d0b0603010806070e180708070f020f0a061a030a0309050a090c020a021e0612090c0105040f06080705070204020409290a0614040f0308120718060509 77
    0x40d0b04090900b5100003400010040b0010041038200205081800b51102c2c560400145010134444e8203516001070700007440061083c0c80c504072a01c00103100c2d0807113040c086503080070702004591074804264017105208c01640c10180003113207a410f81c80240380755400080c100342c54680b13661000304071640300d0050b4400403818400c81c020360703100507080300e00001603410024640003542c401e031802641a0314001c1356a8002e07009900850b0030a2f0001c0011310815801d01013116141c1b649544406440c111f00d00369595000000c1460b1110000034070101e062142c011030a00200c05502c50502400300000c01086100c1c2040d0000c8814905015075540e65041094070076214403035000b50300c00d100140105044155502545607101c001c000b00ca10034522008003007000744a1b00c0015404540e0b00820898940b2030032088008001c40d01e19203082c40d07a12600001481446d4104881c90400820000115419602e405900007624a01a5aa1084100e401d050980503008040c10480c000841d04520f07292 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 252384379 1250 252383129 252383141
    0xc340302090a0e0d020a03110109110f0f040608030c010e0f0706110c061303050d0206070e04110f03151507030903030f020c10050421080a0e010c06090b070e04022b 72
    0x40c0544080c550740d420002c2d16106c44d142d00b00d012404515040c4d0f031164051240c020843d50100d2030b220303a404203d04100041030301c80c0465a00507801c55020802d604e69020b240024250b900040d6180c510b0080142c3c01c0d90082c07100e02c112079100040e51124000002009404c440560410070884044020032038100f65554001c2d03904a1030026034180d454074100c0c00501164025016a01403d14135a8226102d44080d030350380000402c40c5000349518501036010802e41c61300d103c0350514105404408460641040b00e02910540c0d8216a000b900c0c14254010700c40f210b002a003032483c0070010b40e0043c1004000340005001c011180b580100703a039000301301240b00c641000782103e0488985042c0200542d0160083e03c100040c0e07941c81c0c0138980440c664544002c2d500000305030a01104940841d4407440020344e5034100241800d02c2c00c0400d40f1441a000e07000e0198520b543d152511700c41c080c140e00303900d20045005074410489240032005d103440204140034822612124240c5220158001d861 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 252385629 1250 252384379 252384401
    0x1051c1106090a1e090608010e07090b01020708070311030c0105040303050a08131b0f0510020304140a0b070804060233040213111207030b090412140c340302090a 71
    0x1c02169400d203408501c2c581030085034081d550501c01180c07614041802c9e5010114140140d5100344002d011940039600074030640708040c03049031500c03940d5400041c54000315600940c1c4004100d554010142010700110344903080a0900c00d02e0186181c0d4002c0c51885015054820800030740003180b20708203040702c0040e1058105c030b000e00405d1200c003401c80b00c056542c46900702824a05100040c0c81c14509400f2503a00201d4025504041c504800e0043c10961f11041d650322102c0c804011031215401c03800340c14207070300a01915459a05040e4003074a0310341505201d507584041e41c0031084081c0300801c046103540c1d044031070084103901ca5102080904c800801d03070380c0415081c03102c201400183c01c0e01501011a2180008406841e40c5409404840e03c0d00342d0300d5000b0702a50006008114198500301001080d071030002400440c0701038840e0b154104050200e41c0f500400d120212200b4800784180d0110341c1075002007140100038062694008081c40300034050b0b04440001a0892200d51050040c51 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 252386879 1250 252385629 252385649
    0xe0a11060d09030e120f031614030408030418060f030f0606081b0901121a100503010207060212060405062d12010603020a0e040c0b0f130e01051c1106090a 68
    0x2044900d0013404115410a00b139000300082541039440210010305001c4406c50b060103185050514007210105070394501040c1c0742c040c11014031626141042005000034030031100a1074955003492624040148911000100b00e030a11390b0501001540c3c00b1140116540146120504500f82c90800054040c6a00280840c02164201c3d01319515595403040c00800445480c18160b890b039085201d888410300f0301600e070710422100e0b0038642c141e03000c40d1270304601d4110030621504d980d140086d00fa03034080341048403400e8010810015488032414100e4100e00101c83c24042071134100d010600e8280c0d00b088070725580d1109040c050000011410030702406201402c40c001d16141c200c02103001c0e2056110407400f03814003040000d180124069074a0180f43c2c4400340d005001c0c40c05240e85020340069200d00d54402c1e08008552a44058502c020700400c03a014034070305698503010402c81c1c0303503080e02d24443d51401d45005010000b01c2055010306100c40844840380c6410040303002c11800159904510000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 252388129 1250 252386879 252386891
    0xf050106030203091002070f020d0c080d12050105030f0a0213020912010501051c0c09051b19180302030c040f15091e020a081603110d0e0c040e0a11060d 67
    0x42945600190302c6140000125100b400305d1200e00c904030300c00c0b07140103022201c44810705001807901400e00c0d5491030240003240020342e2610301950608803040d01080120f403098808840c1070a03640507036801030004601a0107021000003e050702c6900707603078009104502c168100307100710074203a058544034800038108044940701507400350b00a103020300a1921540c80c4c07003490080c0d0511450349082007980725174101c1c2d81d03614050000002d0072000c1c081c180440800000200544540f80c007910040303900040c18140c030040303842c024242c41e19056401c502c0880c0c0180500240e1400070b03000e00303000c409540000c5e102200c461400c00a201040882502d54410000001c03900c90b550001c0e4003016414101195900380b18028804034802c040c660804140c80a0010350141a902104225102c580c200800c1c082c004500c082403a5000701040301101741d48580c8140b1521040143c2800b1200c25234040054241c034001c8165501c3c1c01d024000c107440e41c00e560035541030701e4040c1540c901550317607001417000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 252389379 1250 252388129 252388139
    0x20711120c3c040b03060402011202090109030f0b06091803040303080603030408010c230301050d02040f09120c03110703080f030a0608060103030903031209020f010c0c03020a0e010305060109061412010f0501 91
    0x24403280d2015070b501c10350920984812918001ca0b40728080e603416198079481441c0506850301075000702c1041e605000101c4000000b08042c6540b09101030f10445d9258407a186c21410044900d1002d031220f4403119040d660748080f00c2000044400f41c9415003401d54959031117a00081c990b00c02c40e00300c40c20a5081004540c0c600d070304501e40c110030032b0448008086a0b41c98100010181c0002d00c00d19038440701c408101d00c003604040e481620145e00150002c81d1000d003d0302e90300107c00000c0d1910b400500c0440395002030582c050b609039040500007001d00280d51035034491031100e0041c1014603c1002c400400314450002503400303030000304000c2040c2c0f495903a50782000b810b020b4451101f80c000c109501c19020180b4036601c00c956159030b005000d2589580c50000466109240e0310b41212101c0f0040004005030359048003140040402c0310405059604600d4200d00340801a0b020b003c0a0782044002d01001507640901c2c52081c400762191540c1c900000841c48c007420071210002e082524010007c43d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 252390629 1250 252389379 252389479
    0x10518040b1522140a0b03190602070609080d060503010504050307061d0601090c11150106030b0a08070f050f0d030f080705071b03020102010e16140402120a020711120c 74
    0xf010111041e654044ca0b42d400d0261015100852602507045e00030300401c1c518042102e0300388034500e0103461f005040000d43e50f18002203441c3c116090750402c50200e10a06881074030300404014190a9000340140d0400760364983d520300a03500000d10042c2c80e80b0740031840400c180001c040d4511030604039482541e5072002c00300240f81d0500360400280307004004040c800c0c0006000c0a11201c02c0e04c92404982ca8000c04a0040c10341000003984140480c03000140c041c020030a50b00a007419101410500b843c0004010444a000481e640114003550807103021a802a10440e481c407058184619103941c0d04404a80300e2060800080100f540050855161590361807a0303010380b8400e800810560781c10002180c4c1c3c40441c543c0ba810328421884090105404103568210340920260003d07007032040040e00d00398144400c40d621140c030780c4d0116016050007407080c180d034180e407016075145614201800c03800707449010040166018119a20341d4002c641000c0c1c407030518401c903c14003031110412000b4004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 252391879 1250 252390629 252390641
    0x5090316080c22050601031107150c0305100e1f06020f0d02030f0d021602040908030a14010f26010c091a030105100c080c03040b03010518040b1522 65
    0x280181c032a002c004002c0c0d080c245640c1c1214903414425042c10008241d48030090a4000c100604054540001c0c132a03d20800740074040861040c0e40440401d0001c28010b0708941a0500d800e00301418034088c0315411ba40801914142d60724403034082050b980b1042010840c2041c41d44448100c1c4060400044032031703001c1115030b104040801039070700c41114040300700d03030320b008886000d48080c0c0204000d1222508540c01407080d0300810303803009400e0a00790006800c6030406130040d01c1c6d4202c00070402503044014410344840580c040c000b15995414201e8006010401b070050703148101c0c0d10004106a00062003090150408081c003c3c000501160b41c0101106042c0c4280400f1200d0000d46140e2103c0c600240c82c10380702e010303000c84d86440c41400e003195061390a090640300c481d82004205494401400180041c041da0001243e80e94580750620000c9a00c0389a9142c078480e14000780b0000400088013541c00407104440a140c204840c00012212111001c2c2002440e900c0044103918600303540000f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 252393129 1250 252391879 252391889
    0x70503130e070206161b050a0606150908011e050406020714011a01020102070f0305070f14010902010e06071104020904020f0408011b1407120909021303020910030c030209040305090316 81
    0x518011707103c0d03151103120f10714006042401b0503800740944a04031042c9483c01d808501480803a45908590307155401103c903550801d002d12071013840d590035225003290301400181700f2007000b0070031703425900d074418140c5c1c40401e0b08880598459001c1000c2c4225501500c0040f5044140c28648540c4034982d94020301d50021000e0460f107030000e00c110198018800c0d5400660041c0070104096080da0b000c031a60344c05108111203001c0c24408040c00305825040260946071040d000240384951800094182d405e10500244036580402000d000070b411881e08102480702600c0150321440c0001c001406070140a4285844000125000a800c0015000740a40901404040300540038807607040b03a0400c0d88100320b4266120400020001840341750043c0703008d190768074081316119101c01d851816644255a04840c8019000c0c0c1401580b41c01154280c0010140700b41c09441491640c030811015041c1c840070b446007806000003028580580111400d0b840f000302652442001741602000e611014050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 252394379 1250 252393129 252393133
    0xc1b0e0105150d1d060a06030b010b0414040c0221092404030308061f020a050d0203030106090605070c1d190207080306060304032f0f03040609030305070503130e0702 73
    0x105410060b4104103405103444078a032519107038102c2c40000d064403054019000700c8640e07000f2030b200b9051099a02640540d000440e246e860340c10824400603068100c8091140c2c1000104101069140c00e4000664251000320350440e05c1c06040e414801601c034400240c1980c52080503007501c00b800281f041172011a02c94038294550394038117402c90f041c00075030b1001c80b0b020481400400d01a0703540d150702c01401000c0407503c03021465581400c0c1c2e0411003003000350b44147c07201000c121040c4241504100284015070640d85089001881c440003445840d0034131500013201c0c01488840c041c00b5001d48078180c0b04c1603000382401d03000740c034010040f2450070300f00d80c540c480d4524540303150003160041500041124116240c1008000c05684043c1048062200700e1190804034500000d0014011507010b07541e2150b000e801c003a050404284401b19102c98004110038840a0741280982040d2078042c5805625982d0030b10700140381d8400d4541c5042d007141c04c0c07000010b1550717110490512038880e81c0d003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 252395629 1250 252394379 252394381
    0x1e070501121407080c0c0109031d01321327020909070e040b090f150103050f130804170a021017011502010906090b0603010e030a0206160c1b0e 63
    0x8401c60361680d01c0700b10000e1405001c80c51151082400681020460301d040340790409030240c241c216100d003030013200841c0c0314600d0030001d540c02407040f1005a40a00b40004a0104094081030704040341120480500340300e1085002080408140c030b404407140010042c80e06e4652036512014112a080f90181d61b196100b01a1120003500950301d0b400c0024101b5810b0b41c56128095896070003150320380e50419a20f000910760b5945940700540240c03582c40708881d40d4208080848280250410640d060504100c14020070640d540b0b110790384051031008443d0140142d1801c95510b1040b80c1c441c00a40350314000c90700c208480403031724500141c030881d024051207000a80543e612108426605060140311004200090103503c0d19410b51006200005940c4005d43c2c1d2103040f80c092100070b840c9122244100002800e0910602011081500080d41000c0c1d02800080d540c21008007480b06180c460900141002c0c002c0c01840c1501d90301c60500c900145c4d64580107000c81c002ca21a500c54002000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 252396879 1250 252395629 252395657
    0x30f0902061305150a05091014030a0605010905121005070c020307060207080105010f0e130212030d0906060806010e0a0e0a3809120c030f040b030a0605060a0906030c021e070501 78
    0x3c0e0845a405d001350f01c83c10300f80302030320341081032403c07806907820144002d05160b50840300800004600c0b44d8402880090242c5c02c00000400354a007030781196001d40403811030000c29200c00070f4078407405042d0b8174001c1000e40e80c904d003c85404020031002900340c8600c94003c1442500814420156141680200242c0e030340e5003c0306c2519145441041c1e10712100801080d4203009012041003000e0010340306c0306038502c180340390368550340c0800b541060190303441520408100355806243c00501014008080303e5050101031880e200020b455480280da84054044000c041071142004581d0485010b1440084505000d01182c02004458004000c480701d82c1f07100c248401c0b80103000342068802445440d81d0150010900c0e4001d00c1c40354071500c018020036026070a08401400608441d940f160384904020f94042d043e1456500414030a030024425401456401403200040369041d103000b0589100c4080c0980c00e01d488080c0d10080c680a40c0e5288001140010319003044403003c0e40c80c02982281c02d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 252398129 1250 252396879 252396919
    0x14030c0303011e060f050a030608033601082707090f050702010501141201020d090c0501121a1e040c02031b0309060a0809030f0403030f14090a06030f0902061305 71
    0x142c020f06011410040d185c2803440e1092002d0508003045040c0060407a07200c80466256402038200c0712582c1503091119581d0854601c2070300902040d1b448041c1403e0201000a440601c0090201a201091f040103159024040c4030018010200314195001d13a81c031004828050f1206005607400c181c02d01011889461051044a0407580154400321041021200b00802e00a40c072003400255034003842a0030030750781c2e248500e020780e0f482503c019029518141c005800c141c80400b6040f01c4902d49001e10301042081014000340550440b58443d0350842a211103c1034902e048681381c01c1450046000142e80c1c0000081c0041440d140e18000801d0002c6001ca80c0c034400c4000a503044101840300801040c0644142d54210000740c0036a0f040c030b1124100f01e050360f082988264002074100310321102407a005205450100710082d01c25107041d2201c00850410100e5110b06020583d030b581200900c1d5080d6800b00c00b446500600d100d640302609180070f01a0203803801541d200e510444040b003064204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 252399379 1250 252398129 252398189
    0x50403050a0816080109050709090509241b160b070e03010506040603020310090302150f011d0c07110f0402040e0a1803081b0d060605180102010c120914030c030301 72
    0x4644c0d500e4160343e007400c072140042c100151a50051041c0c2110101c4d41000b00c0c042c4c0ba118040c40300062060808504900004502241d4007000044066003441500f0038100408010882d5800d2031642c0d420002e0b208215900b40184064001d0104100b40440c099000c080751003c104203c00a2007243c951404000480b800d0340310080d4154400ca05d81a0040340d203800440300c041c000d005660380a151661419036100d03081702c0800110601100501c826014102c007094400c4922045007030a1400240380704a0b0721540902612140b58088000d03500e544e860307002e0082c40f2001d00f0640d00d8580d240001e1036a9201543c0310101d44bc104281c0900b0510b5000d212400d00b600b40c3c2d141042a1980d40b907030b03600c400b256030a2960b42c62040190344900c9200340608001000241c2e541d80d51402050170000012040815407811179051031445a00c031940704001c002000000358000901240764135120150382c602210155142c000414010740c1e580d00840918100c40003c40001c4c404012004074510240d6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 252400629 1250 252399379 252399421
    0x9021615060302300606060706050a0f060b280c08070305070206070b06040b0a0b0f0a02030d090303020c060f0907060806030a020306040b0106020c040608071e09050403050a08 77
    0x104556a4010660060001941030044100041d60039200e4004c140700c280840b0029000d0842c11020410300b100240d00b0301c0e64814204090b2030503080500000d007051041c0c02d0050f144607140d80226000703110541c4100d600b00c10030b032010451291341d051540d5083e017101840c0f0421000c1099140d0007e4643d446820410300940c1d02d011a40b492541d03401d515800400d02602000000c0c0500b200584400700202050742c040d03d503031705140c50600d080000790341011040a00404806a04202031100302098070184103001500d01e458041e13000c012031941c0143d1004018890034203521005240e01940282090381d0440d080ea0120b0b50b03095480d0007098425120003d482d071014a080005510548525400c0200102615020021900020301e0150203940684140400e00010042c203038040010850101e41960140219440c00c51004d84a01e890720841c618a6200022218501c40410480006e0700d0799172070400490505050040440c3c000e032400d14040303071800b004107100310035003002000021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 252401879 1250 252400629 252400657
    0x5010e100b030c09012105071701060f02120c0f061003120203040b0904020a090512060a0506030a0c0905090a05100209032803031d0d0c05100506011b05031b060403090902 75
    0x4200b50011a14074120001d035540310b02e031110200d41c60802c039000341400b036a425274811701c80c0900480400c6039854103031b10020600906202a9001070b4002c18118000039038000c0e03203900c401d42d0f141280d003000210341505482e400340004221203203d014003a0b03400d883c01141c101d00d04240110050b40e6134413071030044917000131701480300c5645460a0340040c203880358980b40a904c8281c0d83d0020855080900e507581c00356411000400902da01c040c4a0594020b40442c01800700c4c0301c0c1754455100f609418054114060385807000070307804000820841c915503511104a40b03115903103070501383c002d400441215120b80683d0b203100116080b851580d40340b1540b03001e40c45459003404d6400b50700401c4241c0405204d40164000c84800d81c5081c042140700c1201174030750031a64082450a941004a003001e030440e03252500092160710b036442885180d041d1081511003041038002d003441e41ca54099840e03007002601a2050055440c01e011440500851081d00c07064000b0b0b4030398803284260b00425501c14000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 252403129 1250 252401879 252401887
    0x40206190c12030c14070c17030a030f0204050d0212030c0a080711030a020a0b09030109080406050408150108060601121425020d050f0702010905031506180906130305090405010e100b030c 82
    0x5e811280010415140f01d065503280c45503903115541d0b560020000c03072100e15000440c2c14030000fa0580a442c1548034007000c02c42c9841d04080c00075a0041c00040c1c041c0c001c031850304500c40c45503420030031140070100e010100c8001d56218508040300754003c100482c0d1064440400010b103080005a01306145d40c014403580d1443d003441c520460075003144580c1e990541d2581000c2000c070344400001c1c40648000d40d115641c0705e0030030890b14034144012404591403001200100201c21020400f42c3d008402403a120030001c400001e040080c000700344102d81032142d65814090f0400c0c40184a0558000860748068a901026000c2e1b0f1145d01c1140008017013901001003d5092400c14004c001b071030b20504003c8090381d16400440d00e80316040b03080d8581d00103c00c05205061404c416007004607a00815000400d1428445050319508003034480d00e03100100b0901030082500407000d81d03a101c000900104500c1d86c2d6404c24440c0014290381403090404420404070745a01000c040324490000c0f61280d40c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 252404379 1250 252403129 252403157
    0x3040c0314030f27090106021e06041203110f03010e0a24170f070906090e070f03020906040b060d0c030b0406060e0927010207050c0a031208040206190c12030c 70
    0x3440700b080100110102440400d44c80c2035a4980d80c0711701a04155004040e00c40984082c02e03d21240d000001c80154043c0c0c04000000c0d00ca034000c651a0300c01480d021503188100c503424072460044070401c00300c0082c040004250440350360303210391203440b0070802480400c0700c010750b0415808110789000e0049540500600c1188020400b00b000d00c01218100d40b00000c0d00b04090707003405042d411a150440c1c90310b03410130004806000706a91232502e04058503545141c0910035600c564503110090260a0100c0010403d03079495105900c00c1e803014020302e641e46c103c0544103000f461203600c02401700b4903041040c4581d003000d1090b42c040c1c4000e42c17200c04941c4103000c2080300c51b01d801444013080c50030650110807280c41d489501408401c45000243c0c485800b0b182050070702200024803806918000710400100720480b1100001c2c0e142400d100105440f1800415101c2c400d000710801c01e002003c6000c8a000d91103c507035a8000d00802c1004003010a4140c100c00307884110306c001c800202c3c400c5241301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 252405629 1250 252404379 252404407
    0x1407060504140102070804030c05030309010f1b0c0303020a02090c0f090402030636011a0318010e03030702150f060a18140c0a08150a090e0703050303040c0314030f 72
    0x9000340c00781060159001082d401203083e07038020107003107840702c01c0400e0400c100401242c024002e060304401450800303100c24002411000e140315100200301e072510b00500b9018029801c11070707250300b00c00c50091607516410069620740301c24100703c0c00359000c42c001030440c414050a41e564026001402440c001c80c03c0c04100113504050020383c1c2c000c0040d440c40c1194207101c01c4d03542c246240c4d08000ca01d40a0004540301c220358050f8000d05140c0e40f6003003058213903000c0004403a0700049100301544e0100321140c003240184072100001c1840d01c000028011035540004a0203881c140081c0f50000641e41d0204100c94200c040c1c51480c0c01c0b030861842070042c0c41c0e031020000d426000c00480010906e50b0248031000090003500c07102030007000010b0854070b03594080b84042e031205851600f50352503082da0b1b0200320082c07124807400c5141d940e10301310303004451001c1c40050300458100044039184d043c1402d01203603c5200d88004c540c3c10422400b5004550300100507240c074030500074507050401c0e01c0540c50320 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 252406879 1250 252405629 252405631
    0x311090103080a0f2604021005030601051621030e0705040b1f11010507050301050f0904052508071716030b0408070611030708060111011802060703110703080c010c14070605 76
    0x50500114200341e8a04107864040340307145c400c16200070307045410f1a005100c8443c009013600707010031008000b0058075036040021540016490751a9250007401c0f41412503c04a042c000501c082081c2900c101e449541600980381502420043d141155952010041100e101c2c0d45001c1e0445a1080100d8241034064104224a441810700201035003084020508440c011030708000821030100051240c0e052400c8a1a090141a600102c16040c00d441d4940d5820000b0020741070b603400145c1c42003240f1842204034006140d02c200b1035408a4541c241c1d10f60550b04030030001c0841c4108030364002038120b80c04100381200e4201c0b0b14a038064907182c64414080d031000c041503030325a80324000c1c65203041c2020004c1d0b1168245658045241c10510f000414131142c40c007083e840c42c0c3c10581c0f01000041e1118524070440c5c1d0444e005591010146800c2c0c500381d510703c04c2e014603402100c00010502922500500856441c4d00003000600000d80303080d24815040001003030002d0b818041a0005103544d8046 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 252408129 1250 252406879 252406907
    0x50907080a060c0315090606080604021611062a0f060709090e01060e0106120e0102030114060714061305250303031e020a03021305040203010e0403080403091805010311090103080a 79
    0x100302c640400080101c0d21601e030741b10080d0155120410842260301000b480d8200600319815440d16030b100c10107581d00400e03c80003a246040354a02441d40780d0f030314011100c2060340c51603080f004000e030301313515910004c03e10901140d0340180c0c0011000d042001c0340092107401d094540e00d903e00c0c1090804d0000f44860f40a01c485590b84110100b003048442c08100d0090400d07542d012400f500e4072001c64290741c92004c02441c00d81c014070050080340c280b81c1c1280e0380110152101c5442d0006820520044005041c80d010035009031001c0c0300203546a1101c034100c950044040ba56160070304208501486c90700d144091000c03461070410300000344260410003684443e0058a01107064100010049901580b01e01c0042a400901400c3e00e0402c129110020802203c04505640c0340450080510030001c000604020341e03800014200340c02420340c0ca01604410549944c840c801e00910001441c00780025121223800c840510068035110350700714103980d480700c2c00f142080014203064a52580c04121 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 252409379 1250 252408129 252408131
    0x1200c040615020c03010c0e15091305012102180a020c07060509040b031911120f010b13090f15140a090303050903030f0402190519030501050907080a060c03 69
    0x10154956a180240c2028002d1030181d1902c0c000d030004081d15000e4000407031402079040070b081202142e04a03240f241ca9090564212000c01d01540e000c120a03c507070054a40e1000944d007194109404591007a4162004503804c0c0c000300e140303d91813244809080d04000e501c05c410311220141140c04000c026048400644050b05051441200c0c81c1048126041040010b02c080380941c40340c42c06001d20592203d0070390203801c3c035403a0101c803010b030040d5894014040034203c0c0c000c40780c1516940912071840c041c00081d603000c0004910120b0103405503188045c07181d00001c0032511041203034481c4d103030800d42c8065517502c40b5029581300440c014885001d070b27204c1552242c84c1001c25024039007461080c03280c00c900142d00d0440d898081c007104c1000e000000c5035803041c000c0101d10030048011603005601160802990010315103000f20700001c40d001607801c560054808030f442050300d034102042e0b038407401c001d11240c0d03580c181c0c40c2e50354001c45c410b0301c240380d000c2d14525012442680c004004884a450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252410629 1250 252409379 252409393
    0xb060d02010e0607060b0a1d0a0b030703021806180708070804210203030619050907140d090b090601060f020a061512050601030b070504032406030b01090b01090b090120 74
    0x4000f03002e6800807181594001e850b00b03800d0255241c00c0b00844098040700788081d60007903080c280c51610341c800600d112951a80c91520b03c3e030590301005804001c42d402450f0482c40000d55814103076101c0f007540c3c01c0e400f480407032940c2401c003484140940d128680b80e9603658025a41c10604440000000e403060781c445680d45100c06910380b061350f0a08848030180c00940d600d04240b01881410309444804454070051034100380581e68914650307607082002850a1a1201e037038481e506183c2c4a40c103a981012440c004d5050708120714039105511894268040d41e42c0c6a0365200c1c243d07500103503003000320016000440802e001034542da211031550300c1c4404884403450b0301c804e9484080c440c90f40c000c5d40c03554049401042040050440700361300211510701705081a2440d03550801007004a5400444400300b58116181e0030060340c044002580c000509c14410350b510381c80741005201500156000500700c0c0c00c00321b80104100d046504200d1f040e540c40321111401280300c021425501c003000041c2c003440c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 252411879 1250 252410629 252410657
    0xf060f050a0c0f082d070c0513060806070e130e030a0c1a13200a03031409040603030e1009050604030b220501151d0c0d0905030c030a03060b04030b060d0201 69
    0x5001350050307401441401c404c00000c42070b04a90320703c2e04100301c5c014010410804001811440038002201d00980e03000180c0c05640c10008007500054000080b54401e0904110340031703521201001c0e10000c2542c924001c402120710007030964154286036401c55108100f01003249200ba101214614010210510211101d6002c0550038030161200450195002404802c0c4000d0f040f11101007121814034624607007040010500a82b02c1d0311000d011710a024481c074402d01c080d4012603500d500f001b4010005140c503460060b01c503402807402c060140030040c406100aa0140d1644803c0e0380300206018106031a5584010b1840401044031290761010744140880680220140854500c505c001007072027400071907902c0d0351041c01d5001100d441c032080814078000414400c1d4580000c800c02039560350b134114002c2c03000a081190700041003444000360079224143c0100262201aa841c1d40510080d50fa4107140350703050040e1b02001e0728032038000c0081145807404484a8070528810305200c0040c02c200c0e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 252413129 1250 252411879 252411893
    0x15020708010e0106050a1d01050904150903110d02010e06040f1110080a150302210705180108070b030603030d0515040609091214070204110d05010605040f060f050a0c0f 74
    0x1c0c01c4030b108540e44900c0280018600751a8500c06454081900006e8203940c403241c828a500608c900c2d801400100301180c20f1110400442c4800c0c00607001c280050300140c60018101c08002441d201c45005281d401c0f00b41600c10b000302954480c60800400c855115a100d000d01d54442042c1119160305665403146652100c183c5001d0482c503c1e150100e151038141c603c0c000b6aa001c0042010740501c003582840141d0f141407889800080c0d03a945803694507503040c6106d00d46441908019400310034281403800803014102a60b0507240c4d440f05030340d042d5558043c4141e65000960b00282e0640090011440c1c10b011b0360b0007240d0250301c0c0ca410707801a05640f400715003111801d4201160303154642c150780f4240629a40054000490b500d0300f42d00ea111644803035429401888030003485980c66000b1000065080d0f01900d00c03811000d01d08101650b580d4002500d0340e440741c82032501d100005000064158060700700ca41d0118600d0716507525020740001c0882d00c00701288402c403911500700355540081011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 252414379 1250 252413129 252413141
    0xc080309031e0d06080a0308040807050c0307090c0207090509030a0c0510060f14030d09050f04090b0c0a1103090a0b0a0c0c0305161e060507050a0609110a060c0c1502070801 76
    0x82d4041c40340d5503d008a18510507181c80e90400039455000d0144240007903400031605074490b4100364850b403100114641103081500380c185966151240c21707404034041c4d646500ca840c44030696001c465002d0390702c81c4000251041241c8240d00c40e00f052210071003031030040351620030440c4103071305451400c44a00e0440c8101e4169400c0350755104400c0c442400b0362101545480030141044008104815103004004d000211038010280142e090701c500e50751644480d000701c501c7c1c41d0b014030b2007451071a0441d500c0d000340c4c1001e6000000901001d00c000904e101c00301c21070303100880140610941c1030400c2d1904510341d002081c00e03c10031036880002d501103001829484091403040e00982601100c40380356410070000e5030070a42440f0181c880c041c000702da0048000040301c15a0402c180c0b50701084c01d085003090074044000d400141032003903c50411000d403c0402031a00115001035000d81c4541c01200c6589000e50000e0881454000074086012914808008080c20344116180d5035203d001150940324 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 252415629 1250 252414379 252414427
    0x402030d050a020a0c12031106060307030219050d08210c0703030b0a0e040501090c09060f030b06011407050c0103050109020307052b0c1101050901150b0702040b0d03120b060306010c08030903 84
    0x90f51b402d800100743d4040300f00070303219001c1c0c0700500441c00c0001c0008e444562a20000b8450407064181c0300c0600030b051205401480010000f4451000743c1c241088254000c00160b01039007045240e031480d1095445001d03000d44c0d800320354136091081607542600100980e1203003d6000505140005002c3c0d107103040144954070071800810600d40600d020003180d460381e0050382049003000c40a120f0404001a0b05017140c1d0490140707052070b296000162031f81c9161840722a581e400c00160007007803010000722010044800ea038104021380e83c441c5080101d00040c0c86190000317004100d001d0b0031503101e00b02142c1940d80d0703c070000130411000c2c80f544121104c400021020821611480030448403c0c4603a40d0b0020040c0c0c000e00210503d00c05110998040c0d000d845c42a680110742c000540d00c8940c040b07000311601500c49122010319080181c51041e80d10351a60540741840d0008d0f00d103060078000c1d40e00618041e100d40c9298a0f080e640c050031078000030f0506041d03110920465419059030900c80e140c1c22 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 252416879 1250 252415629 252415649
    0x9030f140d0603030302071a01060e01120e010e070617221a0a090201110f1203130203031305030c0103060e0a1109090f07081e0f0a09050604060506040e060402030d050a020a0c 77
    0x10031350700d40010210508e6180041c25050f4200400c500354020200789510b5100b442c12024411003106850001c0a004a04540c40c0d0f10f0240d0040301a41d0000359a001c1d181c241c0c4640c4210100d8500c0d040c10b5010407904445524444005104800381e40411020030500c1201c0e1070044c0700d0009426842c2100807110046a6070f1903169003005d6580018410881c1480304014200e001c420b24103040c0c5d550000711f1004c0c070346040000010f800d2025420350315041680182620754401e06124140030091550103200d201340181464200d8960203403045200b16072595101d143c4030b41d22030b010301005021288117489008010404100e050b540c00b00c1103032080007411020405400c203c0b000400d4443e0042c0200d41503240c0d2140c040ca5444040c400560280c00b51603480d88541e50504851b003d440090b00c014014807441d0103110070003c0ca40c000300d2003000b081d03c0411000840182c881d6980d602518040e405400000c1014441c0b40b0450007070900400b580100c1c2d002581c256071320304070010300c0c0d07201031285 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 252418129 1250 252416879 252416887
    0x3051e090414090a0201111213030b0a15291c110c0304031205041d063a1a07020606011209030827030c01050114010309030f140d0603030302 62
    0x68601441410100b08040b40200180c1c54289685a500c00302d25070080e050211503540424040410815144045080300c0150f89a1854480980c1e03550305c02d000c125241d080020001c0c0200c115031160641c11815803d05e1441180380a600c0c41c0e20407041204542032001d407499100407800d07500011314900c2c070054603400220340c210728482d00702c80e881800c41880100070001c100c01d0000c000203403010b1320342000000c5000c0c100c490042c0c0703c9220f02d40c001c43c0201003402440038240e07403807040d6030300c100015100c0850038404680b100d4a49020008041014591400558801346100400341c203030901c500c5022943c0e00420018480c1c3d6a800c9a50000590280c5d042140d0355a02101d82c5031203101c500e01c280017010300c0d55001340c681c013401072689041c0d9900b0f075500700101140100c801d00b8140b4038005c1c1d90356441140d0105010b00b1090040f5080c0c03d17a400980754840d44284540c25203582c040da582c4001241c007000403200d00518101a8102c42420300080110700594420300f0f00641c400d03100140e40d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 252419379 1250 252418129 252418147
    0xf0d050603030301030c2c0a020304050c010f0f1b140d030b041407080a091e02010818120c01062c0a0c02120c01020408070b0c060108030c120703051e 66
    0x6442005000c01d00a42042c00100001a6125072000c161000c1480200c010001214480c4c41c002c0da9805004254142c0310074071040c060140d0003140228021420b441014501400544081d502c640c4500001510707519803086941c800e80382c4c120040c0150307103030400b41480e0f9225980d00d6102040b00001c19000400c1800b4001c0c4c0501c9180424041940c00b4080404401c07115000040d00424150078460008000340114140e68000f9040070303409228038500e4200c207a00302c28450300e0030700200d012412000120306104903409107078805006000061990300c450069003031994108550106082d0348814003c02d510550041480600c102c52082180748000c0c0440142c40140c0036160a445600d458000010039a003c2180c81c103190340c40e101c040d568100359120b540203105540c411415401460307000701d81400c403000200504a00081101d49590301c61001382c0c6c503841032000300c151551001c1c0e50081d88549201c040d00485001e800c1060500c509200440224000003904100d054000140020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 252420629 1250 252419379 252419381
    0x506012c04090f0303151202060d020304051905010509070e09030409090f06050f0609011205060609130f05150f0906062116090c0509030c04020f16110301050609060102060a09030909020f0d 83
    0x80240100542640446403a4000c80e004ac8948101074001c20340010005007400020040d40d010220100b00d03140c0701e4121424031500906082d908014103004481000071600303403160b0100d001d050044003071403400c2c0c50000e001000b000c100c4421500c1c89140341640340030402a210307041c400d51312007038040c6452504404101071303070205030807034400c000ca90412030001c1680010300c150300c424242c5400000d0340342c42016040c180031301c0100800206544800608008000c28000500120b04050075100d8440034808441c25208944c044880c0c0d00c54400100c2038a018031207180f4944900b1031400c0c92801ea8014203041400341030011810010440c010001e1025603c05c0b07495038816803800c2424120034500003030310384003903c01651040c0d1b00442c1844404549108036810a00c4895140590604625140c030311290718001251107546003600007480e0742010154035200c2d65050340500034a9607024084802010048816010003114050124000c21140300400c5c5021315540d003e0348a0080c495a10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 252421879 1250 252420629 252420671
    0xc0106150e0f15120709090e0c030105010b040302030d03050703140f04020306010b1e07080904140403031b0c03030518010c2304060806011b08040b0d0506012c04090f0303 75
    0x500820001940d50030701c076401c0d0240c421020032141341c00c10507200c40500f10f51240355038001e1102540340c8043e2020a070800a03c0001031f16083e8001d00c2240c0c2d032150824100d02a900c0701a402d90400c050340e0400301d01ca45d00040c0d000c4418100000c0d0200801550101007004991881168003041c0031b20041d482e04000441c01048015051032802c00e100c00c0c0031100700c8001c200203103201030205a403c10001c4030001d60302100783c098001c209208449403003840091095405a01184c603007010280c2040700590040211801c0391911a52012555400c40043c10020541044219205105036183c0d03800e000740d0100616aa076006440f02c00550040e00c0341403403164099408404200c1007100c1c03074000c45665448202401c03d143e1400304542d1084105110040092131040700040119a80043e03c02601c4000c5031400308000d00d030340306401950f07490006c0c200815480c408a039040c80310344855049124420000d8004901007519544240c1401090b49003140403a4440c07600c140200c502a00c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 252423129 1250 252421879 252421909
    0x11103040c2306090d050a051b100306050102060105011b0b0106050d0b0607020a03020d030c140102030a0f021c020c1005010b070203060714040905042d171c020c0106150e 75
    0x8094028503000240b80c1e100d20341440e40520340d03c01005e014003109101c80500303580c100c0150b84001c12000c450801d058814801c09110380356900140145c54881d20619080d1a010303002460b85074201001510045502c003280303d0302c1e0302840000710002e034002c0c68550003441603494280c1c0341c200d211201d03829a0341c050001c03405040f0600c490000b40c5c1c1ca030b940c0350f002c40760162094041c8613814101100c40014454000c2e01c81006440c000091410550003140702e1112450300700074104a028021040c2c0c0306d98095041020101d00206651050941c02422000624800c540060321850318660595009a208a4440390701060308d1042d0304040c441c543d0300020314504401010f810850581c0d0501540c014001907071b544100140401203290315160802d5003018003104c10a603490008000001480000c441c40d4010001d09484c00c0c1000c001c1e24913040380a03203441c001c2001c10103040025080192040400e640318100050310f09540c0040041c86a0140e4136010000d9440c1c0600c8100c1d544030f080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 252424379 1250 252423129 252423179
    0xa050105011e0302270f06010f0c031707090f030f020a0902030c03010e0405150f16081003020f04112802060403051918080a031707170702011103040c 66
    0x400005150b1004000c05490781284c600b08000c1d43c0c45000d0300301d407115034142482d00b02540184007140703c108080750f1007084240c2e100342d51180c4450013181c0e10f4000c0d4034010040780401d130000300c42c11408250b0075440b045134a0a540406c0da00d4051986405a562043d16000b0a00d070325042581000381444010b001002410740c03940c1440388084205100500c00c1c0c2824107080008501000f106000c140b1031000c80000c0390748941041500070080e95015101d000c041c080d109182d0450368010b0900c0c034819070308000319030890361450b02888518502c115189500540d00e24100100850b018054400641502c414000c880e80b02109040c450807000c80380c1056602c00c108000c0003a90003001c44585801c0c0a01508252a54140c152881c80400d1079600340081c0084022032031082c00204152546e000707588080b961107000000c020b841d0b8054401000050150280018080b10b407000c554100020b4400022800d0004a60300c2c0b02da0820f6030101c41101444000f040094900d41000302c2c1160398440d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 252425629 1250 252424379 252424409
    0x20105010b070503030705070305120406060602010c030e07120507180209011b0b040609020d02040501080f0c0906091f120501091406100302040c050706090b0406050907181503080703020a05010501 86
    0x10340c3c41d0707a40001001c0d001004000140181014070517000d54010110001400c4010b0400f0300d800c002414040c003c0780c006618048020700a20f200b03004034805400343c90041c0404904260490b03009400340b00b0195290300c500f901c00203041c841c8420001486c5000741c0016100d03510b50000501070744106811220b0b4490750140c180100d054003120b00e4200d81c0c000783c0061041d0321403010507840d0380403081c0650b000f8038050001900c007401290203c2d05d201264155038081842c0410860064401d031031aa03082406a400960f03007882c0e01c015003d00c1120800ea48024581da140c0b0305c89a6000140100c0d1503035107902003142000703501403080b52489052400b414541c030b0144000a5601814440a031203640ca82e8441c00507140074a04860758140c00074014816511035080007045448251800c035021454a000142d00310408503e5505641c1c0e06c100102d500c1e0800c07081036014100c051040750307041c0c002c00b03000400105440c0c018001a80319401818640481c1e040207030031614140d010780c002407100302c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 252426879 1250 252425629 252425633
    0x20f1513083703091508010603060b0a020307021c0c08070f0b0a1e110d110c010206190e1e10050609150105070c050901080f061b03010311120319020105010b07 70
    0x240d810301020310032084601d10303090f0604440c0c50186074441400c040300c0c0c210350310140381d010304020706840072503c0078060300c1d655004030381162080d140c0920068100f07101050040c07414258140220041d624034419500e100c0d1130f214a401000c5d03100894a40c400d120800c03038401c00030a0b020090224680c1542444400354005c0d0036403c1040c1c4498904010300c030743d0f0800600500c28036101c488243c08540c0328a03c1660301a1058851030605a02c074810310700800b01c1e40d1f200242182c480d500079086040c0754000c1c050200060311070800109000d0080240c65054002001c1092511450007401090b81c00345d108900c404a800240506020300e44810030070500b00f003a040b008800020a04c1c0442d55400141015000710710701c1e07003050758800006400041c162400180a92807141c1407000c2e0b46d181d860320042084964100310384125482c00520040010450715115403c00c1500908405094464a0340440c2141d02c0790542d0100140703c107000c4e0107050307424410b4a02500340d000c0440d10713050081d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 252428129 1250 252426879 252426943
    0x206060a0317090415060e041b211118130b0a15030f0509010e060c070f060203090a0f12030c14030f0711030a1d04020313020f151308 59
    0x104649054129001805440359215540503c2600c0e40515822082d10b440740307001043e2202e0050040d02c0780e810b1507003180e0b048013803401d5041c40e410b02d900c1d909210108200c0f02416020b0202b0072480d250307035605a40c01c4d01d022002c0146184103c0c4503840d014000d08074200000c201e074030142008910b103048114400c54590345000030544400f40940b03a004070402e40118050724964585281c80b40c00c20b410b201d40c0b0031301500f01141403030354001620030b80c2d40c890040c14107034021000c02801d40d84100540c00b011440031f6000f55000b070790034801d0301c0281e0020b80b9503103080400d40ca412240c03c91f800031603c40d95036242c4a00091448186050b05001e401d00301c12032841d0001424404a10007040042901580548a1043d00d88009010740e5112030050394040c10000c0e01106c0040040694005405545441d00c2144d100d18042040c041101115800384101500c040840c1908040165460504d008100c000b90191440491310318200350b051400c0941000c40e07a5203291651912403000d0746181c40c85e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 252429379 1250 252428129 252428153
    0x50112020a1403070605031012110a06020d08041506030609030c050601090917090a050d0503281d04021c06181401090507020304051e010305061210050606090315070206060a03 77
    0x41c1b03180207900c0362200c8aa4041e5030055034441c1e0240e00702000344c00108014200141040241261148a030a5032103200346d0715801005c80c03440004642500150000703400024050f4802e0510340e00003520303926595540e00701c508150050340030450307400602003042820802c5c1e070701409003043c0c240101215035940300c1c40114000002d07036910101180c50b130240e4981c00c08440007071030004c2030312044250a082240e240c3e400210f1081901c100409034643d07146841c42600c034140300a98a50070000703202080c0046440e180d40503150b000e6020420383c11990483d0846014071001d008001501d64500fa1040341a01d000130f500034156810010b16624504c680c8044504488a880010070540d0f10703490120b003144039941169a0048034071010700080b10001085041540d000c1c0c07400c0140c0c0c0c40d50810060311008044600b64241e1040c7c0351520303032003000d400c000e0b08102c0c00741c900340c01c1007010000641032000c00302000c010070401c2020403640960412034241c00c040250f4400c40000d042d80c40301c002c1450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 252430629 1250 252429379 252429389
    0x3130501030b031f0b0402040605130f03020f0607050f0303010b12010f050d0f0503090d060501060e0901081e010204080f0a0512030f1b0c010e010b130509030901081801050112020a140307 82
    0x111560801e04e001d101d80c11070350568100400466950340c8500010707029030004107401c03541c0209039201046040c07440007510150781d00182050311100526040180303950141004035414003031070524040400f01003018601903c0c2203d0015200c40490f0703109d88101805a1010071403413800c80d402c0203c2c2d03c80380550800700780c102d8001001000039040091443c8141c42206400c040b0f20b8002e4414081143c0c81941a180740741d1381c00741c0b0b4255620410a04070300a0154040980181024180c403e100b0135a2500c041c440000141c102503550420300d09001703580c19059891380048400200308a003c0c0809060121004910303410b5040411034010349900c01000b01000c00010070035015040030302010340700f601c40c401000384450701c0420b80460180c5040706030180180301900409000c40014050303140b141c0c010740c00460901d009035004540c40000a04a1501d0b0b0b0a90b1243c9070307040c0c03001e0103414080c0c80071440741d501041c1c80340705000c41c000455000481c040c040c01041c040c0ca81d404031b00e00040f20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 252431879 1250 252430629 252430663
    0x1a011722020a08060106170a1b0320120708070f0207090b06040e102603030a050c0c060702160f0b07020d170c010b1003020c0a030507030c060e03130501030b03 70
    0xca5403010841004950b044541548111000003589560001000002003143c400101507900d4030302c600d00c15105c02d0908101000d240c403020164061003541724242c3c4107044075641500d2029042c407103146034080740382d00030b45104202c10824070315080008590032501d1803500c40d10710340c45901e00a440700c0c0f540c0118810b02e03403101c208031519514007085d41d0103010612010701540c240384103c21850701a600c6010307140a425130740e4134809010150f1240c0720f0f03261080950700c2d42e550b01c142c10000740001403103800104021300080d080740350100000c82c0f241d400d40d001058042e050140e480400c071141d0b4407684e84159403d5061020b94028416100b500e54162601005400f841c94054a4810b1a0030010361882e00410003a09041c81500548541c40054400d05c0074040c030303440102c0036441011b600c144281d001c034007080e00282c45800109542070103403400410200b55551148203551440180c1a90b6030b201084c03440c3c54940c580900c100070030003424100000c51900e0086901d032451a02c40210305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 252433129 1250 252431879 252431941
    0x3150103030807140c0a0209070207122613060914010c3302121b0405010807020102091801060e0904110f03010207080409150e06010e0d0203101a0117 66
    0x740184401d84c01000e00080b190b0719004804481036035000e1014082c3c0c4260034032000319105900125003031007074400c01401c6020000c866116a4011506510b01070710b403c130030b54495045130800034040c0412403004080d003255030f86024130086c814001b40d00030302d1120500c1400d10703019a8001e40304031006940401080c03644400100d04c040ca81c2c83c00241c00c000e040c1d0400000601c400141e0060805541d03088955946848030a45030a44400250030249000e00c02c000c1882152700900880361301c02e5540c40003600d0030300380740081980d0074000203050354404c039a01c1c01800701e142c00c06c160315020601514800000c0c0f07000c0d120151b90a100c0e0090714003901417466a02d0b01a2020b4044861254001110030340d1950345000e417100508c5c040704640030b408085000440d060000700b5040e40034400c140d64841030300001104000c4404408041240d051003401e50318880781e0058050b14200941e2501d0521046484400151140600b5980542c0c510000302c1000421880104032800e40001e410300c44403a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 252434379 1250 252433129 252433141
    0x20406084f0506010608160819050615040806040c05030105040b071d030a0b07020606010f050a1d030a0b191808070503070b090d030615050912070504090f02040605031501030308 78
    0x101c040607003000b501c907004a50003c82c00941005100340900742d030340d0314500354003003601d021101e181d420b44501c41d000340c100f210f070031505190b50444ea800880040c01c240700c50419400c2152240e0042e0b0140c08290005800c00c07041c800c0c4010028001c03e819030091041e4641030f51007031f601040040c032400900c6a2604d0301032255640d407000060815001d8116500c210040c2094261200101c4603440144101c02c0040c1095100e40c40e9042c07401815100c0c54101440010292540f10b200b0303001d824140f1460f001080e196400300312070b80003a8001c0010340c0312802c1200044d404c4001804018020b1402c220f140d50304107a45846014519030410f00107501d4018914100d0704510030301d80041c0400c121042406442c6c0c501094209000b510381c0c1742040840d81d108038003038041010140000c00305005010241840c14030000804d0031a0503041650b401c9e9450320300043c02c94086810503100c0410040741d03002107040912480e80600000c500404100d00c00451041500d1700500000f02000028400320751 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 252435629 1250 252434379 252434521
    0x1d0d020120010f0c0309060507020703050703030f261e0903040902370e04110901050a03060b1303030e19031203150303050304021e09060f01020a020402040608 70
    0x3c0343e0f8510f0101440402956103004026144020090395201c1c80c203000306060307600025424085a034010041e1003120720b142c4083c1c0300b0549500140090010800320f07010344c4102040c032412481011200f038865410142e01d0013010031160700002011440e541c082c04040c4e9000400d68049811001c0c0150b40c40f00310030302602500615082d07a080060308008407101c069956406c1d0245c040582d5210004002080100003e0b980744400c480310031041001451760740e5201e40d0040c030710003900d400c0103e1010342d6401c00c0081540003c104003640411903800340304050b407003908012869801c5604040f01c5e011042002030862041c4402014401d4000d45243d851380aa046030740c0c03d00c0c2800f070703842480c0d0b42d81c200900b007a03100722000c03071044510100ca0f884000c0f200c04000040070b0082c2c20341046544078828402542542c0c1d00d500c0c107522a95074000c00590b90f900040000c0d00d0103544116460421a080c041414182030040d08035031b0111481c44000c034407440004813418000000040392a102d460416 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 252436879 1250 252435629 252435641
    0x903020a1e0306180b130206040e0915041b05030102040807061815020606090708090715230405030c030607020a0b040c1d0907080f070b180604061d0d02012001 70
    0x10801c905003490400c982c0c13403a0080e20040e50003050300d0b003490350301c02e070741c4c100328041e160002944004140814400c09600307800780350340601035000304c50301503042070354000e0049000c807030485540c0e12003c480c0d080200c924007000003d000560083d8107041c14102c1041d107039481800742400700803904403030500070305810310b40c000200040c8021481c80c7c60040d100039200e04d012036899002e035120740085500988a1680f6074416803400004d40803180c200000341420b1800d81c0200001c1005002000101301e007500246054421036913111542c6618241c00e041c20580f042c000d051190b089003041213504d503004502c0300c0f045540308034035a80341d070303518074040d0400245174102c50400201481485900c0e040e85a040380160401b43c00ca402c81996007100301da462070324007910b49458200102c10005550701c00080c100d10161404c00e04800102c40c00072964981081e404040051402448002d0000c0a84849203205d003082e0740d0703960020600d40001c5c00c1140c2102c10b410441040740079061444d24294020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 252438129 1250 252436879 252436883
    0xb0603070f030c080105010b0301031e060e0d03050f0901020a02030d0902040f09080d1b0512040f060e0303041205280c050613020405060d030e1003060e01240903020a1e03 75
    0x4084856241d09103043c0240b0305000d10703c034542c64403002007031259611003524102d82d0700850104503030b003c0b40070306080d203402c030841120032907100c22168030740e0030041c843d2504141282c0c3e0001460725120700302c02c80c00b079400303000ca00c0c10740d2041094419243c0d011007190383d2500010350102e52005a031011800812100b00c01d026501c1ca050355220410240c0c4000308203440d010350040c402406118805410f00b5600e0705004049002000240d0034040c610580316886801140c100d100e614181d101c51003903400c0160001c1407034000104220802145505081800708240b0301981065070300c0c2410140004174044507410013603c1080d01b5161803003441d800c07400ca41d0010a40c1d19134104100062041c0c1c800440c00c9100f903081c01c00088a60400c003003400500d0f6010307990600b0000e101e605000e0310010044c501c40c201500ca203400314600403100c05d407038000c19a8904080d000c80404603c07000350a0302e602c640c401c0100e85842040981e407004010002d541503c00007454062104102c24489034040e400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 252439379 1250 252438129 252438149
    0x11d090406060905061504050f04090602070302060103170309060c0c1e010b24041710050705030f01091815022a0c010912060c0327050d050702010801030b060307 71
    0x4010400040350450b0b0111002c82c0814020354079004100301c1a4034206040e081001e0090000b00b019280c680000405010301500004010046480701c074140d90210704158090307807009004200b00140281074401c4022210741440c00c505054011a45500c005030003503900f06004140d942d1040c00521440e08413100c0040e2000086014640d050302822202518511604030040100c40000441140e0a201702282010030301c0c3c01e04103051800252840700c0700c80c840e881403200c0351541e283d003486441e009100d40e8691f113480349403400b1204814081600040d401500380810001c1c1401f407401d40000090f03005d820025841c0484101e50000d0180c0103400c4014503030359040c404c810b44006d58907118141d0390826035a4490406d0015030311481c0900c03ca107440c1c0c0c019040c0e500810017692040780d080b40d05280c041f40302d245061030401c0b41e054050084900441c0d058014041010400c080750143c0201d09002d810171142d40c00103402d14805101c00b42003100101c1c001281540e0074001540a880c80c004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 252440629 1250 252439379 252439381
    0x210f14090d0e180a090c03051009110a050306190f1109131e090501020f04141206070509120f0303041b0504051302010e040f02030a2c0705011d09 64
    0x4001681c4100003024000030a107514180089801c103540c8000307140d014044100226222849910010300782103074180e5500c03454000c080b0000d101800f11a20b40d0312803c0005c600400c4600f440184a050f000c0410301c940000da034104925140801c0c1d0542c0144200d202c02e2226018203000c00c080c2c0020b000c0581c8484c500306203418441034010140040110682d40a0011081113840c08100c800b00d405180020740c3c01181003d50291a80000003000d01c02c0300007600381410b14040302c4554020303411586031144c01900b14515410f200b85030100c1a442c0000500041c20900d101401e240305054680f4040c0c10b0414113844903003803c0042001661680342120354a1038a82006c604500b03809081314a002d620410004981c9028040d03030b40125041c0c1041c0340c00c00300d143e0054a81400e0002156002602c40e418000e50300d40030703c0078522414440703202240c0b52040078403203002454030942c4266001005940c46015403000600101961802c3c00d00b07513000003540410003d05102220043c0e44003440034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 252441879 1250 252440629 252440641
    0x3070f0312030b030f2a0f060f1903060801180b070507020d0812060108070903020a090515090c0d1103010f09181707020906010e03060a110702030102180f01210f14 72
    0x626110314494501900f01c032a83d1241640e06c4288052812503020401442800c02854920028100d468041c00110b1034841e8095104421100320340103500400d684904c100030245003030040c2210404003a421070f685500550398a244040e01921050410801084c041d04544400191044080d004040b46440e6800301e803034500c00380b40464989001800c01004a800f850140300c5050542e0f600900d1035501c0303824800140000d000017407814611840400c070f500305d55181c4d25601c80c0a05050390311035546001c450411000c1d5101e421290f40719150130001000034103c032810310401e9440c0e0041c04543c10071000441c605082520070080e00201c0380004800a80c0e240728020860b07140300343d62807191540c84400558005165021580c1c040c1c00c514002043e10708560710549484642c500494200101500802d007243c0005400e41c100c810004910542842c01965000d080c5000b4a09a82d0300c0940108200c0c2c03099440c10b5020342c082d192444400c2081041d0888000400e020028040610b096 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 252443129 1250 252441879 252441883
    0xa05040b030a1d03120a1e0903020d0201150b03060607051204061701091107140f07080f0c040506011704020604030b040f0213291807050a02070503070f0312030b030f 73
    0x182100c000b00301c6844241c0f8540007000c4252030700e456101e0070070504d99441110803405058103040e201c01c3c44003041e5280004044c01e2080303010300c5020364001e0004c07079104e1b0406421209403840d55049031100183c200284c04030f942c101c940c418070a4400303503218912407030503518001e00d0a958480300c500100f030104215510480510380a0140e8101e101e250345c1e9902c154085840042c00b841e2061010800703980171540c0f0a105904034808201265007030030203500c03902c1c20201076410103000c5e6000012b200c0f00d003440820078504079038001c84003001141412000a0201c142c0b10900c0c48449480034001002d55a609090b6401140c200000681611f85480c1c199020490310600320322802c41e0203401102a8210b101d1403c0c4200c0b507840700206400155401c1c0000e8207003810f0f1a50110f01725a641c5400c3c0346921155000e003071300b9140c0a41b55900440702a00307100e960f40001e4025032060000300410312442c090300e411690800200d0550789e240f400c08801400c525141c1c03540510894490450003440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 252444379 1250 252443129 252443141
    0x1030506240d11040b1908040c050105090d060507050703081806190b130209011b0816020607080c0123060607140f150a2007060e0f0105010603140105060c120a05040b030a 75
    0x19071441d11b070006103c403500751422402524042d00c681e41000c0b052251b0b5000314002c208051005040c100b10441907501c41c42510801c84000d40082c0000c80c0c00400c05801c0070020744c0214043c404c8445c16070442404940c1c13603100402c010220007506041c403070301941c1c2d0b50100b0803d02e0050005910722901c1010714002c0d500c011602400100000d010542e901320700c0e4080c602440c0c1c0800d41d1840d00c62504051030345d6680032242a40e000e0740c1000300c640003c682800400600035504000f14852501c01c0201110051200c20f101003202d4281c00c0020350754030042100c8690b40c3c00050050043d2074540042d280c8001703070340040501d00c80c6150514100302030010f07a03440313a19600418404284603111680400346242124421088140061400500e86400c584030044102c0c04690554903034242880c02e5401c00c0c1e110a02003662454000325041c92001c03000d025150a48030f0030b18204040300311560f43c3d4400451200c00768404101c441400c2c1c444c00440300100074494120b6202d0502d50803600003400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 252445629 1250 252444379 252444397
    0x50907050108011e05060a020c060409050f01060f020325141f181101020a1502090f01050f09041505060406050c0c010309050303010e2d0601030506240d11040b 70
    0x100500000a0205660520348000d40f550500f50341366130320b0705040c0260740d00540d040e030080d800f951a0f14100380c0c460b2405080100024000844d1030700b4031141a0703ca84d1410f811110400072004c620b483e20a40010459001c50b409505800d010752410850800441121800030024426038441030100b4000164081048014090b081c0b40840c07a5040309040ba1203104a400940d4648071420300841c2440c950008001c8060050359400460b43d81c45440c0e2214440700b0b6030200d07501080c0d694407801e120030071589445003801c1562520344c1240c0c04040d41c2c042e5903143c0d48a01d8071411182ca140440c0250704000781400b0708859100e64a402c000740c9035401c50081c00b4841c0c41603030b00030401580b0034012680f0294109000d5803941c3d003010342c040c0c01c0304001020781c0610110024100e0038100c1103071b4900e41a594a0303403040c01e0b50030080c00040507100040d103170620800e41e1480c035510064910074000a05401c100b10542d44800e01d5070780e40c01a0015400c804511000441c0c00103801e03420034002d00b9518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 252446879 1250 252445629 252445637
    0xa0504090b160306050102120d0612050a0507050604060804060203040201030e010f060e100f0e07030603050d0305010501120603150b010e040e07051c051b0f123a051b010509070501 79
    0x14441c40c080f0100e407203c0c410140142d010b040c42c15a2810441e0003004c0c45205101d0110740709032141c102c07019040c101001111300b036025403800230500c04140700940c0600b000322496844c02d40b601d0701c000c00440024101400190780000403a085a01a5001c28015002040244214410701100c500101128411018400201c000042c04c04408051030025079511200e0328030054140030b46a8070038140207103c0070601d5619000400410010400c0c0110b8540982c0c01140642c1420001840000c00c000242241403c0290510004290f130040c81c080e10b406200c0080c00e10039917801207400300480300001e50080e260000800040401190800070340344103440303498451281c0043c0c14520b10003000050710540013078130f0002e00211803c6c00f0115500004103103100000d4480c3c0000c00340074001ca520b241d1541721a5a07450b01c418019607100341c9114210b03e02040444c044a101d5200855030b002e83d0801400040d4540100d01c03803984900130f061000c0c000c2050b4509514000e13903c0b052800f880b03000c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 252448129 1250 252446879 252446911
    0x12010212240109050907030506011b210206070e060a020109020a090203150d030207030b070e03030c0d1d0604030b04020d0b10060e06031e0702030c100614010e15090a0504090b 77
    0xb54094040807040b01d01c003414000360356442e41000c40c0100000383c600d82c100002d821142400c0c1501e030080c0d55440d0300818440311103034268007440840d01010107121055412040030020390a8001003940c0080c2d000351202e5035100c0c0c036440308900604810300c00079400f007038440300895a0900f540c00f562165aa038034140c3c1d400d070307044404c00c0b8001e081c0c15001401a03000c000300f8000601c3e12590782d90001c0307960522002c210280000242181c02511030f1541f198080403024451640c8032080c00103011010f42c0203410308203900041749a80c03145000c041d03e107610020100d011512940c13000c25003980c20000b400c610741001c4155850081e0144281c0002038a0300210359040d141c080201c03070107203000781c0205172030032066140030f07840e070360028500d9040d03000501c40c0502d2141c040c0001d5120341210000047c40900b4000052580b0100441c41d45c104480000f2414041c1c80e00e11001000078503080c1c800e0344602c21440000d285032540c2d0402c0c1d401c40c0c00d1800d044c08000502c0f507218000c1118a40700080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 252449379 1250 252448129 252448201
    0x1605070503010b0406030c14011b0b0f06150f03090304030503071a070503060a05010e12030d0b120115170a0203070902071103010c080109020a230c0f061512010212 72
    0xc5d11040e01010384000b00135441089a00c6450801016406040c10803070980000c0303000e0516002c98400f020350b090300c141d10821a800700003201141c0d001501711200450401c11244500c03541c05542e1600948a60010108030041030400c140d0b00156400000c8035a10001d602c0c050900600500000340031458207008103001c0340c010800e0301c0c4904005000d903040b091900e00115002c10050b4049a0024100c2d040c110361013900307000030108400a0300d0301040c10000c01d01400b07200c50f00d4648001a40c0d2600240a91003291071081c10111280e40000c040402e802040c00790a0050f0403038000d5042c41541e03c0010380d032113250050071042d801142010305140c2250b050500380d032201c0d40300e100020740340720040c8002d40b00c0d40d000c3d10842e9854074059075480f004202c03020041309070303581800700c0e04e502090285c284401003161000d840c2030040508510708244500c24110801811018401d2100000300b1042d103000354180c07840705c1e501c103080082c0d500f07144680e80050705000302c942e690074018000f6260 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 252450629 1250 252449379 252449381
    0x3060f080715030209131806060b040501090b13030f022d040b060c0a170c010204030501020d2711120102270d0506041b0305060f09160e06040905031605070503010b04 73
    0x400e1050282201b07a2081c010000c0e98024994117581100d14120100e0000c04941a4460700c0d02400569181c56a6141002d0000d0014284c03a030040640c1c00b010408800000314807a50402100e0340290745105003c95840000c070142c01a402c8803240030b024402a1400c68864296a44d606405440030010b61080c2010301009120700e041c03012003548406143d00020707269002070045440075078070141c10241940107450036a8896442645e00ba900410580d01064842c400d00340010fa11080115601c0150179410583e0011080060722107107040030490300302e403a41c070a18a50041c0c1000215034541807140c01c61955115101203001400f80d46c0d80c0c440507424003802040400341c00800070030703041e904c0b0b0f5207041030a84007491462010903c24800800524204040b9010369200300030f0703400c54544480e00074502410001c0380d6003207200c4280108620140b151056401c03aa043c0d4010034100a1414041d10310b01c41c2d9401c0e48101c94240b0702d01028030001144220554800710000d1144079040f104100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 252451879 1250 252450629 252450637
    0x6031a0106081810240b0405031b01030b060403050d0f020601060210020702030c100f1b0b01050409030309172109030406050c0a0b07050c010510150f03060f0807150302 74
    0x100030411141c0030501d40750075180c920304428941e80c2124050480c52026130f003940c2810900300c003141c03191000102ca002c41c691a010261006520306800c2c03e15000c0000d40d644125503494814208520f151712a592003a00088100b4001400742c035a101e940c4d18000b566100c0742ca4801002030041407650f10503d20201e042c42c100c804a600608240c82d2003a4404000c0d80483c1c0201ea040c0704010030aa1140c40e80980520b02d08407a859415030715442d1302c40900000c01214205040c0480110410006000f007008581076810988000405403010324064004000518007e0484958101301460301003644c0c00030810044c80280c040071509030040c41c520582000d90b04042180c2041c441403002c14410401341003806e5035a0f0440701c421a26407600700d11508149e03002000940d00040da100c8200090107120f4004150b0140d14941510b04062046687c8120081204200f011070882d60050f119030030202c05010400c40030104144d450421913600e000d01c3c810110007a01a06050000501034400d803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 252453129 1250 252451879 252451889
    0x1020a02010f031e06030606080601170709051314280506040209040f080a0921030f05181201050a14010b0703050d0e0f0127020609040908040e090106031a01 69
    0x82c40d49401c0041c42034002d86800f03086070300041c0580c00c01c3d103071000143c007030880158000d80001445070b007411101d90400340142c1186810800c1005d52800c2c00f80001000d00c00c481107080d0000c0e40e9100c50486008525402002400310b810342e0307051000320000428441780011541d030b203015441603224164043c2c401800d201400c0e075008032000402508003610003503403040c442e82c02c0f40d885040d2950781900304e41081a000740094495007042c00004a52203500382c4103800400008260040c5640c014031000c5494503500820001203030307842a1030b0000d0103103008203a004000004200040c8900790003408111803411400d0b003004110f41c6000744c0502c0c5941a0340740341c50328605d0250a6102030320345074030171036200740410b5441b085030004100922039400502204800404c006200700032807906546c1c1c200c8132038050641c1002c42d80040e501d001c221940c11100361400300f60041ea03802c18600c03038020b42d0701c4401d44414101c2042800b403c19400501500c0c411100c12003d401d004050743e1070350b07000b4014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 252454379 1250 252453129 252453137
    0x50f0a0306050705070c0f080618030307140405032a0409050a030f170705030901050106020f21070804060804060e07120201050304140f0706030e010e030f0a170f1501020a0201 77
    0xc0c40825181d8000369840700207410f1035481c003007a5569240c100102544228414070102c1800d2200c0b0a007444055000300540ca60444048440c0c10084d4803880301a00d0b0006004580c803140344075240e00020364004181c01001d0b03981c1c10020424600b02d9a511100240b4090701c0003400c00d009180c00c0c8203540640da0041c00501c00d014003560250340401c3d035003c800c0c040c06000c51204400c0384e41d0004d4a84204030340d07514103443c1d0400b032000500303484040e0448015034122041041e0315420019504401486280c00c0d908011440502851203200d4100003034051540014003254840d0000d80003405030b480340c1010002c41d4801e10b10107407104c15a004510340c107411011000050b41c03007a8059608140114072030400c0d1041410301c43d107024082c4607071504980081d0f03003c0040d00d03014810707101241c0320309009001000c11a41c01c66200d100340a107883d0300031000305045150b5442000c608801700e0295150180c20709000c04401d10061b0100d4410600c0a140703106600c10f5440403582d01069507068403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 252455629 1250 252454379 252454399
    0xb0a080309090a0b03011506020f0c09060105210c0a1701120605091905011b09050303030a0c09080340090b062110050306091c0e04090615050f 63
    0x1006450034018100c40c0c0b08541321540110155401c5c840c810087e80d080840d80b000da458504080e042100351528684207411198800032540ca40c51080ca50181d02403030010707a20845040000203184d2403585402c3c1c5803002d0307820800034201a83c01051003080b140c40e01d40c1c90310800015000d800c0002d0054003440c20b40a0100400140990400d80c1c01803040c0040d54654440381c43e005440380503145080e52269140c80340307615500c0840400900d0b0095a20701082c13400e00340008642c1e00e200c050203542ca10dc1d139680141954901c41c020f240050000740c801c1c0c0ba81c1d40d12000c0014195070b80011704142e4400e100004090803100b03030300140c0c5280000e22014004500d4400c00c000100220703011300d60072a0b420171001c0ca034440c000071610400114034411280509240018204201251300000c1c005e6014405110031100005004102d07004c000d03090180300048103004885500b000400c00c0e41142c280842e50f020007015401242000510030381000225640c3c000b00b001d109000141aa04140002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 252456879 1250 252455629 252455647
    0xb01080606100e0f0d0210020114100303080103150209120a06110903063408010311150d09031701060809010f0605011205040204090f140f01111219021803010b0a0803 73
    0x1203c5046424018201c51840d40395401185400581e03807e0b200060355507614102881c0c0c4401c2a80350400e048045648080341140c3e409880100c060002404440f01c03454102110b51480c4c04641c40100080c0a030410b141e18140010303500c0640c0b6404440c3c96003072200800044242e607050702c1c1c14102c01001403141e03494012200358141035007084000700e2200401c05041c540802c034600d800c5958640d0328128550b24508140c05075101e4005c510b80300384c0040c0c14041c0560010010303503d60803200c00000944170645d01c0c09032400456400c2d110808144035000040304d5400c005064807500e42d000080c416550318840040c221032050107100e0104004240050320105243e1055a000b031000d0000164040303e41c5583d4040705841c101104c003000089813000e0003d10074404012160101c5009100019103a001c0d03d50178002d04403228010198400003600c4850040c0300740180090100e000c540c0c0b600709240b6020048d0511104c14040e40c2481d15100c03090030403291040407500d80c40301450601d241ca03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 252458129 1250 252456879 252456889
    0xd0b070e0a0801050106021b090115050d2a02010e010902060d020d06050607080702190f09020f0d0e0303060a080f0601090b1341040308070216030b01080606100e 71
    0xc680a01e410004880c4007003840842407041034040c0101ba0014400489800361078024002044200340c0111044001081601014000001c07144100d040854540940d1080100103200004400c806012204c140f080c9800d9600381e1008a02410380c000e0081b03244c802d00c42800d840400708002c2d086032041003500c1203214158050161845c0392080440c00e07030358410000d82c45400c4414240e07020382c00012540304600d08544090180800000c070803640910b0490031802c0074005209440051b500051241003618884040b10f40c0307802800c2c020003004100d1000c00303075260400c58400d40100301c049400714100100085441c3c045012200500c4503030301384068500070341040c44400317801160380c403070300000c3c9410303401049100d242000c80c0a001d11b610031054031354401d182c00c201c2d189000402c03040c040007612080c1e89a2090b010700b0010350315150154124a0025180030508910b03000740000f1080100c513a5109040301d140000302d40703058607402c4c1001900b420884810b80880c0d4890611404d034100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 252459379 1250 252458129 252458147
    0xf201b01030b04091211120f0f0d090c15050c1905011103071d04050c07020f06040902120a0b060906180f1002010c0305010605340f03080405010b0d0b07 67
    0x1041c5404200720302690041010303140440c10031902d1000035071041403016448041466031310800801002c0508216044803000d00ca40c02401006c410006108412441d19408036005100d1014080140030342506240e00e50320654050008000311a114020b0341c20320a4080d01c01c000c9002d030150012110421500200d0354402800311615501c1d05030844940503c0340103180b0514280e1641c418008805a50550007150b80540da48624908400d001e80001907805942010703a055440e00498145000000c1c0346006507446046590700000780e407108444010303c40c0380140c0b10500140310b050b80310010420540119842c598001409010080b0281c00030350010680440240c901e00c1035090100c0800c5c090300c5100c081e070000d43e44131190395038010f60510031540186950310f007031030801c144650300001e2503607450070303c640c0140c94030301081e030190090001813a21a0310080b004071910307417840c000d80381c0782003140d007550154a000c00c104060f0401148203044150711000d0b40c40c403075544020607100000c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 252460629 1250 252459379 252459433
    0x2130b060426030426010507170403090e1003060f140f0a0605100804020f010c02151c06081606031b11031909051003092607050a030f20 60
    0x65114502e0000900b48018409003401025040b440816040c0354407403105e41c00050011a07150000b0008840c0c1e1003104071414807542100245240c80d0b500b01110f2031801d90f0419100b0081110601aa20190f07034040710883e0311940081c08410104030700c10003110a54015010300010b0840003c014400743d41007140e024600d803900040c6143c4030f0300801e0500c044082102c012840100130321040d071600101d00d0a190b0802d203031076074121845501003041014202100600f8404c0407030303c1c8504008860354003c61b07641c0004100181c03940e07140050307600c01160306e800031300441e00380c0007080c09072280c0100303010080320807020500f034101c40e03008452048450107c2d80190209001c0c4008006102080d0388102d00150341e41060982024100080070485a510b41d081c1440d2424000009050b408508131104003131040101c18480c100b80c082480c420400300412600a0954500826402c12400550018555102602c9400111100090072109900c8a020b980403040c85034102040c000c5842e2208 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 252461879 1250 252460629 252460679
    0x30906040311070b03070513083708070609060c0f02030a0c022e020d02030702130504050c0a093612030204091a03160518060402131202130b0604 64
    0x4d80d21025035020760820341b0007100183d8001041d091282c0501d4140c0007801c8000023520101c10740a96109a01200c0d29543c90750200c858440000d083c0c41d001c1c00180790350410440c1e5038034011454000020441103c00300c4201307181c1018510664842c0103c0055401190021413403c408103e058030740040d02c1c1c030200e9000c0000c1d100e40a8070b40c00240840d4040c402103844252081c4020307400703424003000020880c1158000e10200c009a0344003076144201183c00360b4001600d842d01d040440c00c1034902d005080e0484000400020380140c01d03444941d9240003000705000c0707401c561007800e5055200e200004e068400c8000c00c0404150070381d001c2e841000789410010b244c00e1752002c1c90011350300d4180041d2010f80e10641100c1d1141000c0c800c8406840822038080708032820b100010b45101003131058240e14108820029145403103642c11648200408484a101680d40700c041c004d103040c400388101e001d128418103c500c49200e900410802503002400702d07003428109000043e041900501c004428 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 252463129 1250 252461879 252461893
    0x61003051012030513060201020f04050f03100c1701060801051e12010e070f050402130b0a121401150206150409030504030204020708091206091218120706030e03030906040311 77
    0xb80e2034200a145210f1384949455a01005405e504084e00c0d600443c02e5900401824511502d030408a40684408039007a0440e4194940801d150842c01d02030b02c80b4061400894040494001486040c1240503511107491a1b032a180c08841603103080c80750a8101034924000403142c80f050400c040a624082d01d0034a0802d503800b070881c251048a9008c8049801292060140c5042d034136200c80600401d403800d44c0b61202c0c03040508030200051045880200380812202049842402d80300c541e01c650303910500a44c0d0214001482d02d030300a104003007145405144001045001103010b40c82110022400703c0d0241e251000d00000c5d0141c0c010813001c02004020200040e03440e4800b824106010358070458a030a010814000351498120010140307078400020012125000605003038042c0524115948409801100d441218032542c0096071007010780f0541c07040700c540010f0560445102da41d060000c5180704100c103031a840182d604080d135422500008003c01d00034010303401240c9030300040b6512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 252464379 1250 252463129 252463139
    0x40f0f020a090c1b0804050405090336100e0f18010e0105030d18030201051305060a0c0213020703020a0b06030a0c060801060f08011809110307030305070b0f0610030510 74
    0x1c0e40707420008215649105281c6020b50254600c80c0381021840c0d82c403211045510340d2152405a4800c0a1065446800080c0d00e40740920a40f071b207003811200c403480100300010740d06441c0c10508071103115552102c50b0000c91485c0c404411080c5e05095116015000a00f40510607004030780d01e00c490f00059101000341c03800e01c0001005008000800408100354140010541003080d160ba0704400c2000b46041130160b000004010012603509091290f580d00f00407408407143d034060343c807260780300720045124203006030082101c6215510841e00384070100c0e21954180e0881c000c072000580140c0c04024500005044c00f10b8140c0c100d4001002c4440da6a01c0e03503200e00d96020184c00000003d004240100049500300580d07030401d074000d051006075581090404451901d50100c003040c026103a60740181403003088541440c0c0303c42c01809481000d0303120708010b44641d00000301115061150380c00039840d000c220a4040c000d01d40100201148414248110060a0090b0080600003040240040c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 252465629 1250 252464379 252464389
    0x13020f0c03131706191d0a050606011805040b0d0204050711060915070806010306080d020a031e050306090a1515020115050f270f061e010206040f0f02 66
    0x42800e118500640d40e40007107885407072440b0b060f58008031079810b0114107500300c9000440c03540d84c4a030301c5011a0004c8450342e54038201130284084580030503140502004600c0300013086024549000d201100c500b9260000119590032800c1c403841c3c1240528001401649415004462444801806440c4010040c0c000908880080d41c84a0120b07550051040341035105003d200d51021040e4040c0004608241c0d10445020004000c40d0800010b2000900070342e010b540098043c061040490b10030301041c40300a0f42d00c501102c020390203c0c1e5140c41c08284030fa5074448020300c07c0000e030b1710342e4103507100c490600c09500d81c0a003020002e10b8581d80742035010a1001e4992000b4200c080c80703210301615110000c1e0071100325442e0030203e5000c0d00000d00003600e44074810300c0c60420a48507103400303220303142e40031050200b80344100f01401010700078400b4064a45106500412003114849921103d8880703a4038440e05080304a801340c0c00650004000ca41668139100025001d51814800d265407540061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 252466879 1250 252465629 252465637
    0x308030c0403020901060305100303080712060f05010207090204050a030206131a18090f010e0705040e0a060333090c080a030c060b041a060705010e100c08060d02090613020f 76
    0x89010034045020020340c507000001038010301c0e15044c10003003420510314040d0041402d0002400b44404000441c1c242d51142161040790301245104110305a259007100000a04600c1000c1c010701c90a0700c0801d10010900c02c68044800003010f44000f00e240d0b41c240301d20f07070300109590255032110f890001051548a0044840329500b5040769940d131038540c0b0320460850326148400d0052020f10308002c020003c01d0340140c1034a50280380b0a2148e5640c10f400c580c24821904205060010301e402d02c00121181c2c0c0013101524402c1801c800321000e110a03203082090054101c040c0c04540030040c0e00d0141072948003a40090003083e60b6440c0d0b80e111502e592404241d100114005009140ca00041c400305105100b40190200c40500070f6181d440002c805000502d20f0492040900150762810042c1c01d510020300a07100034141c80c45003e49803e480010206c0d622a54003007031a140c0003510383d01d0038002144034994024012807568995000340300c4800000d41c88440480da0812490795400b00f40c8002d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 252468129 1250 252466879 252466891
    0x615050a181b1215080c01120f0c0e030c0301090b010b0a02010204031202060a050f100b030613180512090a030f060603020901121e03080606031f060c121d04020a09030803 75
    0x40b40d02140404024012204040c02c03129507080c507040b0074441d17041e002c5041007020f582480c18a08505034844508020401c003008196004d00e0100c24082158000d043d03820380100482c141c40d02d03e1805801c0c503007a1a10400d00400e000218401407180340e2012000d058140f034548001800c1a8032076450b071865092a0300e1000259004004000a000c05401100c3d402803011a020301c60781021642000225a217000b520750070f00307001c8000380e019225949025080c442c4000c0901000021410402e50881051000d440e240a05000303c0c6560a00e10103c5507280070161100508500d503480718060107035081301c01c445080d1152000000f590710203034a00d0207441c0b036818444010041b860402c1c540e541340400413260320000008000481d07000320700d060b4400b1090b5410303030362665614802c0625110641840000046000300421607036400003444040c240301e54100701098104070b805594205081c03d803408202103101c0074220303a0500c2e401a00307840ca80b60134143c0032541c0305d035611100d9800807190 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 252469379 1250 252468129 252468137
    0x4020310260d030b0d120c0b090724020f16060e0a0302030a02040e0a050a150f0e060a4709040b0609040c1d040615050a181b 55
    0xc144903406441034085070004030003203901103801031004030a40341c0070101c076001c06040d40c0d084041c00d140c4440d000903240faa80603c0c184010b4070055405005006810707000c2d034601d400080051504c220001d8004d096643c24414020001101603400e00c41181e002980d00450140d01c140c0000110100301c2501e0031810510000401070403d50b005000454410134680f08a0042c2010800343e2000300b110180290185c60101e60002c02da04120300c1c0081d118001400c2d445040003007020b20503807003009280003810700018428030654148402c2510b449440c144941d07009080420701022791381c1c1c0003244480380700b000540310f1081c0500d080129403810203012000030748185140e2204c418041014500303042101c0000242c24071f40c0391010b0151006203900e0040c1d0302d04000c24103002c400c45800000f80540d1075580344610b240410549001e10036a821154581400401510f0f4040e482e0031000f03445010b08010704a501d440420050034040e521310016190b5034030a4015005003049403c1c0c00249a80c403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 252470629 1250 252469379 252469411
    0xc0302030606010212030a0c02070b0703020606090c0a0807080604230609070302040e150d02130b030f0c03030f090414010b1308030f0d0f290102100b010507120905040203 75
    0x600d814010300428260464014207440250170b03403594280c3c2e07048010f60b2000a00703003200050a0385030001ca6000300d034880001013001d104060b800a50548149001e031202c0d40b00f0341b181c2002490340d0190441c0300d00400c81c1c1900240300706205100070340d40060010320106200501c0100c0c0482c00c141d86689100340f003032040c10448541410500d0329000346c000d140441c0b900713182810ba000403203c003030b041840c0c070072444010344510360314030190410498000b8140080303080301c181c0b220002e01d0b08001042c000d008007a400709c601030300401d12402540024014501d062202542005190301c41400d00350320698500c0b48001303500e000c100003400380c001000061fa55006c04c100d00e1158054560102c01107600410030b40d0b681d50254002c2d5010000b1000300816400c41e40d00600c4080e111000d5034a40c010084e1034010340c80d000030350040181d00020b03000c3d50488110306071900c0541e245441c055010800130031101c000600100300c407084207901072900c0c0c070400f508c41c2c0000c4d090f80d10594001c1c9070304456034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 252471879 1250 252470629 252470633
    0x6040f03020405090f1207050106090c080108161401110f070909051005040305040504020d02091002100c05070c030b09030412050703210f030216020d0804090518060a0203071106040c03 81
    0x1224058004c141c2400802080060398055a5960000c0842c10609900401d130001001800d402600160003500401d004070382040c000146884400d01c1004064441c2c0c0030f4000c04842207060340d00607500c06811407000440c6450066600c4d0b080080307400344030720400240d4030081d0300a021900250031002c4000c1b403015441e0400510b064410a841ca291170320f05414440025007180840d01225000e4030b01580700c01103a10070070300078040c00c10402e411a1701d40610944296001c0340360340b0529003407402041a5140c00e41c04880602400000501815003600300380041115100314507480702001044031301d0304d6110108d00d90704404002044810343d10040e020702c10409160350348000b100c00d0030f0b40088400101e640080085101c041d01c1c0301070540c00100e0998001001d542032405540180002d1220700d01441e003411140d202d8402d00b06031031314220100328403940030721b50a50800e00e401c00500042c2c0350803690170020344c0301509207400e0040700e0811001e810814000c10380703d2801400c4082a42d4614 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 252473129 1250 252471879 252471881
    0x12040515010b0a05031f03050f07050901081f110c070b070c0e1e0a0e120304110102070b072d050102070b090309030a030309020303071a070207050f06090603041106040f030204 77
    0x1030b0096418001e0500010003910742c0041030b00d0f40404070450500c1c1c45880e0303120098042c0e403150405001070090110059101c0d10003c0d41008582c01500c062301e1582c0d03035141003a168540c106400315601708480d416a1300d40c00641041c10002071030141d09142603a10710341103242001960101440d140e012822005200228074407100805a03050202d5241c0740c405241c26140300b00181c030144ca40c420380e001c104601c546034031080d0a501c005040314801c03507466441c5145900110703401c0b204c40c000007481410719480407440700c0403681000101c40c242020f40e40d40003078035010242003401108070070344c142c8030b594080740014440d117000e20001640c0700d40e01c0c1000f004c58000145100c0242d403081201911030380780010b058640c9078240c900080c00c0803c51002074154800e441d0060454440101c2541c0d08190680940c1e004034056002c542e2000e03940c0b030901c07408841e0080c5003a4003520600c6044501c0c1440c030011980503104d0000b800d41c007218070340010116006504241c4402c8041e540c1031086083c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 252474379 1250 252473129 252473131
    0x7060609150f050d0b01062d054b0d0513060b0a03080313020604080a030905090f07080c091c060506040c08040b2701020409050403140a020607030203090312040515 72
    0x1604d0220040d00140c48403e082101072040700c0070003003413040c22000c0000750b030f01081101441f80c5524082d07c100000003031068000000d00800806040c03000d814881c24034580c00c10440141e0250304000e1140c4260701d0404018070b6021002c41c20800c0700c40c2014000d841818032424409584403202a26407d02c001154040324041c0e000d00e2250009202060440003170320f612100b001300996059a031440800c03c070b40602d42c0082c09030b10038000380e0783c10143c00000b005c094a200b44d60740c485542e40c92105240040050340d0600100e40b07030300c0100b00d421328000000c2000340741c0945902040300030030001000300ea013640411342c2d10960702d10910a0b545001c0c000c001c1e07102201d2600407a40d01300b98998401d4498042c01038007550040b45003c20084218582d02808914074400854803643d0b01c00c07800c000740c00308480807070010f0b0f1024607042d22169400d0a0b00c3d06000503500511803a560f155041d03000b0760029040d03060030320090010046111900607168442c86c0300b4400f418050303049142e51340700288 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 252475629 1250 252474379 252474389
    0x50a0b010b0a0207050609120115080606150906070c0b0c0f120703020c0409051e0303010302040b09070e0906010e0d14060105010c0308070305040326070206071d0607060609150f 78
    0x1002620001c2d54009150400d41da0200c41c05c03659a0464400680d0b1161640310000383d9500f0f029140c112005071a46000484590b5000c3da1004c0c4e50355401c0111001000038094901c0300140403605181c18540050407540f4882c5010385001610341c5600300181d00034211040059011a4000e032050b030090014006605070600d1580c10b049103581c000c0d4039829052140c070b0140b55074100160071b2142c200401c29101c800720b6080c0705201082010305440e54000d000683c00b46080031082c0c08241044070080c0c0c800e41c0150f54900e4140f909804203c0e10180c068511810050060910219941c2e241c5060804a200b8040a855142c42122481c203240050744164103020700480c2c108082a0461902980500179160003e0b440d582c03860156402400c03030712000a07103890031404401010800d5600c501036030701d43c0c089441035070742c0c140101d40c03110101e048801e0340c454080b000d50f050309240001e000c1452190300d0200b262034607440124200c80405400142c1011100f408200303904481c4000e00c0a48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 252476879 1250 252475629 252475649
    0xf0c061d0402030c0d0203010605070308060607021c020310020d060e060a050a03121e03020301030302101104090e101404020a0e01140607031209150b0405240109030f050a0b01 77
    0x180d251200190646111011402560000b000401e40c562583c102c80b2490b650800c00c54803540c540348001c1158100c080c040b80810f00d520b01040c0c8502e4100305407480c0c41da005184038501e003081805824501c0034650708030303010700c995020301c40a10a180050300300851100c000003a054236211882d009481c001e01554001d40201c1c100b07108030780315400c91a05aa0b0080c58016502d01810401c0740e40303418900c80322807502c0c00c0346014440b03a130307160300110304032130099003100d010100800e8600110394100b1030980a00c0001c11003080901402e420108042c188030054074086c4040c2144801654011060141c14441003410001140b0301204000c02410030110050015030412078480443e05058045503c20440800c048007018464107004c40b055000c140284000d8109142000358034002e40808038409090920717600c22400d261084521441e1540f0810101800c0041904420000d01d448d150410004500101c041401807540b5144584180020401a00d450030000380c00b0b030068001300d00711 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 252478129 1250 252476879 252476897
    0xc020f0904060b040c03140a050907120803070305090118030e030102041809050d0f020601120c03020409050c0901060e0303030c0906091f1e0806010e01110106060822020108040605040206070f0f0c06 87
    0x2000b24240048c0d482030440c20f00040715103411078051328261a5074030207401517048101b03a608003c9840301440c010b2586890034442d1b46c80d411130240c20b94800e601040540100740b441c642c003003442410003040070080030f00010b180944404104500c5e044003e003907026203071120198000c01c1801c005580000c142850070040b06500c20783c00035200c1406110350780c1100200c00100c0103014005091034011b5900070000c0100a04038900a0340b0b072200245018451484600000f58084c001c440030140a500203002e10300d99070741c00100300307000c3d088141d03055044407040c8241c44642e00c4002400d480c08240000443e201c1c161207070010055202c16184194105008000209070341d0400c0980c1c0c0c214009080c00d40c05070020f00c0049940410015030007600e503080c000c0c0098201d401ca000c80d07003e00741c401da86003440c2c111070034412000c6070000c03c024001011000040c01040d202d81c03150340c0181c4000c04461030116251a6000140e10f0044191784800e103103a400808c0002d4440e00400074072840c00c0c41c03000c2c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 252479379 1250 252478129 252478151
    0x3060705030414030f0d1d030f0a0518060703120f0209130c0e0301021b070b0c0c06030406090807030e01120527010b03070303090501080702030310060c020f0904060b040c03 76
    0x480c00040c00041214403c503c820308900814025201e04078284000340f0349541c030400c05c0340c0c0034200c4a90194040401aa5001d41c01c4801204590144030301c91101e41c40d1500035941140c0c15030220300100d001040240030f0140c15600c5d000100081801303a0344940c106107a980e4400100d6640c40c1049414034030401503841c1640368900c91020340000d00f02c000420810280c419184500101402075155100081c03640c07882c11840300315603008410b041121512038580c034003045103105400101c034240e030045e02c0c00c8000d031a0420040d42d22611440010444010b181d41c5e040903600f000c042100031900822148865581c0400011400444100709010750700f0710382c00d40e18119407050f865104060384200c452001040940045000820240c11900300664900f002000401e80d030103030078009803081003c41e064034030005c2a680101d00c24001003105d02c0c40c1030344c2619146035006080340c1200714010307499042c0ea2840c107160710440c0114030200303100e904001040221083c0e0103415041c10f140c084040342d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 252480629 1250 252479379 252479387
    0x8070b010b0418090303020d05010f0609050d051e1608060105090604181101140d0903030b0d11010c02010309060f050103031412040f050705100e0a0e04080909100f06020c0f030607 79
    0x3da0141c12000041d080c24601701100a4855405100c0d545824000000f960360040020501140c41c1d6503103d648040e00d80e0208010601c0880004d0929407001d0030180703440d81e84010000003560003e040741d4401c020340510101851031540400c007290007400040142d130030010100c07607209004982c100450b4180e1a90b12221800d20301c40074022110700c0002d90442d9024546806c2662170180485881e403409107c4130000d488a000c0c100c000a051100d22209420b100d507201e400c3c0c650082c01413605401d600f00440e1250b0800340b06034105a1110350b5600890498480c040880f441d0903408503a40d8150704001c0c200030519200301d21400c0c41000341070484000444d040790015809044004224580d08081d8606101c503080070380d2051641007100c014030740081c10001850001d881fa50449659290001041c2008482c058005d400400c02c007903080c9403141c0301c140e1014200d1130f9004140e803100f50303441100701c4a803c40030242e480442d1080181c50526180740500c0812001080c8500d002c000c010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 252481879 1250 252480629 252480659
    0x302030f100b180303090406080304140402130e130c0801091704080d050d2301030c1d070c05070e2802191b0602031015030e0303070c0f0c0308070b010b04 68
    0x280f05005809204070701a681030044a07100c2078028414400c058503001155100d602038407940300c0f42c042c51081102c20b1706260007641d00035500e5200b0307022468501041e416941900034403400c412554a080341d000603440c410140c6c060003200d8000505103400e0300c5c180062540100300805002c00602c410810070b000000c909186e20003500d044d41d15486039100c0d8101038140c02ca80c07c10798508062030a100c0d0102030032094107e074000c419840045503210a070561403000d6001d005035a031400d0000a01e454094050b43c0780c468440c004440d4142d43d240100c454a4500381c032001c00d10301201c0d5580c40901040c0c4203010a4041000085140c8160100c00391814032341e16003010103014400b010044a40220040b01d01e409401240956980c81c08401e1000065440e015500c403504071000700d030307500d24424414451004c001c480294515103c0020980d0307007002c5083d0489590849000b55800504004115001144a2801e96488030010f107401c00102d0b105800c001c503170a03401d1004003d015815070501c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 252483129 1250 252481879 252481897
    0x108060306071404080d180f1206050612060f010503010b010e100809030d02040b130b090112050606040906030b16210203070e061305040608031204080a0504080a030302030f100b 78
    0xc50030340b400303203495240302d0207103a001034418003540c00120112900501070110b411585181e40c1c1e41203403200d00e0100f0700c05050154885009c0a81a80390000703a1315401140c021400520010b0300e89050120b00780340c08011104507200e030710700100401213402c09006201d0358004c00d08296600c64283ca0125004441c011100d008100c401e001055034021300344100c503554402c0300020356903035417114020210341d40440d100191481002000040c4050014181c1e6500c800c160b58503000050050a01c001500001e8516540420100000140501e03184503d000952203006c030511b05107801c100321614000b80d80700e140b092043c0140320408160f00c2500d048950341381c2000040e12a2190003080398007da40116150300301200041005c1808003000e107190440317408171018040c0a0b2036003002034030f034040d02104806004036040401c0000f003c00300230b0301d0146c0d190b00d0801e08050f40c4548162605220340d400707a001c65400401d20800c0f1140250190703200c0303c2428505015440c05103402c0340c520400444d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 252484379 1250 252483129 252483137
    0xc1f0216082a0a15230c0405030d120e07051003240602030c0609120f072d150203060f010509010c0b0a0f1a010f0c0303022109010506010806030607 65
    0x201d6803804004203000d1880780c0c101100030841407045400c50f9030380d04611403d54100403502044000c07041342c1c3c0101c0c4c103020922480d070503189610392054104030001900740c0c0340c00c60040c880450359440402c2401044803980d562242c0e03400420310780d10109da060f100490300e0390704910b4052115032140700b1a000d21820b030f03150005a41100d026140e0002d041d4059060010307482c84c1000962950000c00b0742180400e203015038400383c80d840801d960320588030360f42c030360b51f01802d000ea003080392a01405403c3d000d0280c400142a00d1038041225489403d001a110740040040740100a01089901e9640b840c81c5050085103182494000104003001004426040140000e180d49843e4840c0c28444030aa901c1380e5071076010b0a16400c601c1c05801e214607904100742c41d090380b40b070407145d07001c0b00445a40c00603110070700d50030f0086c2800c03a0380e4109a6001e0741856020080d00f0070f40c40200400142c901040720803010603007061402942512005051b150421010806000c1140d074040303941500a403035420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 252485629 1250 252484379 252484387
    0x1103040807030306050a030606060314010608130c0314031c0903120506030a02041d160b03180715030207030e0405060a090b03070803030c040305070f0b07110103020c030c1f021608 79
    0x2070201c3c003400c1550042500480040c40010030400603412102c10380790305440a100e184449000e400079207600744140000038286a000c03aa48801c450741c4da005041c00f032030600c0e00c0f06807291191b02030102a0b6040e6036141d4400981c1d46410040c0707408018490707600013802e222103603040e10001c00f204040707803100201d9580c84010940f140e80c1048007032490313503000d0003d02002400e40314468000fa003118030301301180240f14500e00c1f6803c106a030001980c0d40b0f03100c0c25003552105030034a044402d0b481601040c510a200000c61034103141301011103150084e66001da5035049074a8020310200203550224010350800060219503a03a008846060303404103800003d5180da80307030020345454150380c842421801700005004d9441440801401a02c0c000c3d8211100c55950708032080381c540b0f0511916003180010301c1280002065505903c034980c0c014075000d4205100f0804550455200700d00c200101c7c1c2c04a60501d804200c4092040c034030150074507085013040c28121700c0f250300803010100140f1400e4001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 252486879 1250 252485629 252485633
    0x9210f020f0c2b0303050109051b04030f140f0a0320031b0102130e0f060105160605040302010902090a050a0605090601121104120f0b01050910270e1f1103040807 71
    0xe55031496612582d4036103c00391183c14040d00070702081c010031031600d0500000801d44400d203d00b6403529242c41c0c1180c1c0c50030349142c5540340c2d8461102400c50b8208860301d04c20140c00c0c410003c4240000f048005040706021500d4045d0003038040152607141c80103020801e010b0800b01205450303038040d58400508a95007428902c5009205203000c60884041421010a101c6184500144030300c103d14006d1046440300c0c001590383d03008500503080800020607074280001e9840c2c1140390020710900010440c44c01d1039002807054038088958104503a80d038400c01400c1491401440000c01c800c2d80c072081e843c02c0c0600007c020000c40b411002e40241c0341c2101c14800144142107070000c2880b180303020030700c0d000e51409103411080321100380c49250707110001081c10f01c1d101050600919032020401110740c42c00640c642c60f0050200c3d81c19040720440800050040d807400b40f0b1805040200c083c2515000d0056010188880c061199030081d180c6030003100507071402c50407a81c00ca604200620340780d038114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 252488129 1250 252486879 252486919
    0x30b070503070908030c070503010f0501140d170f03040308180c0d1703010305030717041d1305010903081b03011d28060e0601230a0309210f020f0c 65
    0x2d84c0c080003151200241c11001d07103001290400c00c0e40c20444c0240594000f80000c00d060b01c10a004c4e0340c080308248803030001c2a02d49803001c441000d10a1070303080940b82030403481b12038a4200c06802241064008104010550300400e820f50000c0070411544805044a07440c40d550f9003074207191030003180c4482151040c041000c61648010610940c955a40e6031a1300e450743e140d800ca03030703011a41c10050b0840b81c480d802c100416181235415581440500407003c41e00c0082c50325000e403064105400206121020903c00e0103158030081c040d44600e901801d1540900c1c0705004410040c0d80100ca0900043c40070104015020424820103c940002e54650051050034014a0340070354040c0340100210245100094214500300c0744c003480c107541070399100360040d01e00e408844030031840c0408000c21070006514480c0545049035840c0707000220b002e055030781d001180f01280d0a000e012403078203140400c440d0744112990046c944500c017505003018501046542d4044081d880d0b44100c041d1024544031640d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 252489379 1250 252488129 252488147
    0x40e13050706051606050c0703230306010e0f04180b0c0703051812070303020a11010302041d1f03051b0d0302060403030e0a0804090209130b010c080d020408061008060a06030b07050307 81
    0x810401c01147c28441300f1030449901c2904102e02042d0401240003034040180d030812401c24a03210880d00d5a950320004480d0b8254250001e540000c5428100170191036910503440c08a00d840d803036400750412810900100c1d600205040541b01c000c01250700060790040640d18400c210b080c81c01c2281c106500000c40c5046203020314402c030302c03400780f0000906d40d00056100025000d070000e44e030340600c540011001ea01c514010071216101403060542ca1003044860340b503010618600090b254640c0060008143c1116481034a00350702c1003081c00380e491540a4150202403044502101404032560081e48845c03004201a0905a03510b25000c02a0380c140301e071201c0203510231140c0d6138468036002ca0307030020b41200a455000300404d40541040d00300921071058500710584940f04614102c1c0c3d02c400c00c51b0311550002030380035000c0c000060240400c0110314020b0700200c803c80501424820014500800140030040342c40c20003004101007500c0395842e0360440c00074030345140d4036540e42c50103640d4501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 252490629 1250 252489379 252489383
    0x1c06030501051603050601080402011707140d02300c030403090b03040c0e0f090601170708030408010b2701050105090402221a1305010309020a080303070302040e130507060516 77
    0x100301810003450301c5a00f4601c805803429924100441d0f140d08004680e041c2003110003e01040c20402501d1200703c000595aa100249142c43e0910002000c0316281c25000701d02c0d2418040d80205129200007039080c02e220000382c03007210203c181420781e076007506c04c214041c0100c4034103140000810300f810b22980c9031030003908007694095640d04242c500000e1800e41445564681e5002102044d80c1c160320203041c9000d0000c000c002d01d410703400d140000b00ea500c10001c1c0f01b850307881209000142c0300c7d002d00c0030380b00070040b0000024507181d06100780201c14590504982101242100e0700c03a243d24010705442c107461003072070415102c1e03022402140081c81501c4102202c2045008000c50116003070001c00140d440c1f120040c0708070074038014091414010040d2940c05101800b00601640d4800c0c0d0000064500080095858681c2c418000c0d04660064649200003a0001004e1064000c00c0d007403240c10403a038280c0c481841d442500ca9035194901c5000751010004006070711458022040c2c00341d20906c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 252491879 1250 252490629 252490631
    0x10906020c0319020a030c2c04050a031107050a1706010b03010b070312090602070f11010c030206060409020105040302120f120a020c0103050408040503011505040c05040e0f0604140a150b030702031c06030501 91
    0x1a01d0715018488c841d1406445082e110003074000010643c926811280110360280c02040d02c64180d9a0990b040c2480c0740003e082031181001c0007038030360346a20b1014010594480d4803000c429900000fa03081000503045245600c03000c000401c0a9813089086a080540526240c41820600c124182c0031b045e1804015201500100342c4c5030078031401d00200e0030814400d403e0301e81003c503500015189040c4880340900581c100e40c0000d080ea0802c3d41240d84118030503d4140e2030691268006414126000e10410451707000005c1801c3c21001006640c1f52031000001719420071068900c025520100551141d0401d40c0b124045004c114110b800d0701c015000003002030040f00107034021111742941d1880350340e00c190308000500c89518010021602a10003988829443d50344248402c3c1e241d14005c0d000f50f411a031f403140412045099899410b0003486c425a0100742115241c0c52041000c445030010f03450b0703a00c00c206004c0031039000000c4454640300700303504030400b90440e03100c0301c020300c03807135002403c55 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 252493129 1250 252491879 252491903
    0x4080d05090c01020f16090f09050f03040e0609010b0406030f060302040f0c0207120c0608090c10170916120501020708070501200c030d020903030c010614010906020c0319020a03 78
    0x840880c10b42251a403c0c2e08070b900202d005980540e4400098040c444112004c3c0300c14041c124194210399140610301d880440d19017400e0359902d217007610303140300c0040390340002c18184010b2881000c510b8006100312041545035060640c55a80343c821481094145642d5111100d1068810f420810055800520800520080200c0d0348003400e22900031100500514002194041140407443d40007900400e01c00c18190400109840c124400341403500c40348182c01c00705000d82e650402e49081318140d079071840d110250b00c0c50703101050900580028074940212003106003644031585080c0031154050313081444500c46040c8680203118583c40640340200c0002c500c0144003054101101c044004800c008542520380050003031809820300d0074446800030020f500d40c62103640c010302982c1000a00b5070b490000c0381c1c404a400c4a25942c842000d010550141200a68122824038014816400034040725055400040e4442107080400d0004000c00006030742503407100c17540d90b0040c5031310000300404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 252494379 1250 252493129 252493141
    0x190e0a0213020d0624030b2b060b011106070e060721080108070e0106030b010306050402070c06080601020313120f05030a090515120406051503101e0c090b0304080d05 73
    0x41d41c031208843c4442c60401d04000346000c094074000600c1d00c0003070492003100300c0048040b0090f006141fa03095101301c07580b00594204002103160b0410241c83d83d44100d083c0d905140c040143d6901e0a9000e051041c4025112152400492100da00c5921498107811010300315001078024020b01201070041d8540e0242242801e0300203003100c030075014649801409a9075074603c1507441449000724402110074a0040004074001d41000c0422441414007103421a2140c001c14100d0300808000c0c2c650780faa00c0c07400c105c50741c0c0040c5401c1d0081e01c02c6c4095458500002c4406070392020501c20480c0a84c1044489000e001505480700042d9500c00c040c2caa81d0100f80b0750040c46054a8001c7d039100c4c101d09501c0c1c3d0b4601e1207900444004080042d038086066580761600c1d8001c00004140302c241c802c1003242481030780d070103002c0c030446100d81103000502c1f24141c3c1e000c80c4c0e42181510307084000710f00e07104d0004001078001c10140c04940055040640d20707912450a00c541d07000d4a0304404615040c4401d00c0a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 252495629 1250 252494379 252494381
    0x2131b02030304020910080a1b050d050a06050a02030c070b150a060801060f0c0c05100909020c240105060313060e01051006020d030507050d0f06030b0408040302100503190e0a0213 79
    0x3c0202c3c003c88451840e030703c8180340e400c0100800e1181011503402450308034002a801c10701d4035504890f40d0100c00403107a5450105013800310400d8103d82a4206110700010040e19101e642c2d00401441011421403410745688039062041035000b0b425102c50200080010000b040348441444002c0c000c10311842e95002e0141034450280540400b0550402c00585260b108801c21145590007070024030006d450101402000ac1d006580181000304210005c142800640014561320540d0401802c200343c100800513080300c0d03e124401403104070000100320725980d0030140da0b08408050080e244a001c949010030040c82e031140e07030010310750826007001074000320300f510401220721039000d079610030071840e504404880f070440b01d030404550240510316103440d182e4004514010156070024601e5166160b00020315412038044600d100e00240500841c106030380f0076816514075042c0f00342181494070428038201d02d40400202910343d50001d04032003920030020015070540140c2444080f828802002c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 252496879 1250 252495629 252495631
    0x20402041a04030c062a08090405010807140616240903030207062304120903140604030306050604082109120c01030c02070b1204081b010606032702131b020303 70
    0x10f07030720300081500001c0301c40c0240041c0c3e20001910544515008211006031003071ba00c16a03059070340310400d2140905944403441200d0181180f08010308566140031069003000c88400301031400b40100b13104110040380490345509140764850800c00001040c000d160f010318403003481c07940400781014030986c24035030980e0003048118081c0000740f102c10046803944029000b1050320000b610380f208009400b00d00311812482c500c461500c1c04280340b55494883c0e80120342c1e80d180c064030300d801000c2170008154052140800602d0281c0f02181010301d480c0c00d0a44444000c148400b00314804e0554208106906084070341d45600106800014000000801d64134801c103001a0302292911002182807400000c25100721800d8210040c43c22001420011580d01e0280c821502c901d428852050800f05504500c40703208800c40001a10f645003039801803e5481306007210090090045901d5162000061131001085d01074805c407a603035082d0121380000b047c00ca910040c00301101240105032680c040021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 252498129 1250 252496879 252496883
    0x90812070206060a03080307080619030605060a05030a05030d09030306050907021006080c0f010c14010e0d0807051201061b0206160203060115020312091504150c08061507020402041a0403 82
    0x220210f903990340501194994500001d0728000b81031001880301c80c42202c42e01d84c803440180c442c90080084080000c0c150300c0680013202c2054032541003000d03e04090b0801002440118005c04207a1020345400c0c3d241d200340501416841e4441094400b03050081c0c228600808014115880e1441d0040c0c009441d40c100100b148441810608000b40c2400300081d40505844018808113104614034015110310019107011182c603600c0c500342031942602882640c850302021809482440d0810000911002d4000d00050500c00280a0765158541e40b000c01c0b810354025041030445500300c545125174440c161900254058030000790448000202044031032824800d80444416907242c061080280c04410070030801a80309101c641c107055040841145c011081c0300a841420758440112812010222002c0d10440c4c01c1750a550501070541c81483c1d800251844c00c103403142801d100080c0b08101d460b4041d00f08100100d9a503080d0b5866904540050202415500c5055181d8038104003130380182c402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 252499379 1250 252498129 252498133
    0xd0506031b010203030c1b0303090a0506130b0403270b0c100b030307030509150c06061c3305011701140106050d090602040801090b060406050f01080115030908120702 73
    0x107030800c0341c4940c180720221101c160055400c503540c00e000100542c20006c00403110180703039640440540820320086011383c408401801140d031090070264600a0003070503242e51030140d007004030080381090a0b0180c12070f80c18541742603404000c441e2010004140020b40704501000354001582c03503ca00c008041404070f54041c3d6000d040181d42c402c00b00d80d0104911134064100b00541d00c0024801c0c030040076034520041c40d010034801206800075550b000001c00a1041c2d0001d07003440304618020702082400054400403407180c00c00c07076440a903c03800b6481101404036100d2a400d059078222900700d1300c10340c080340d003c01440da0364045c80c1080c0701070550005a25482d11102c5802407a1902c40207050320100d45451303180415070f5003044020103000c80c0c1500d1450382171202241c07441d0300307001d6840f41a000350340e0f0b20110700700103041008903441c1d5401a071040540300c1d20314155982140300705044520b440e0840f40041e1204100703902130705000c00d0081040700006007410310440b050f01e09038002c4c0041e070300b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 252500629 1250 252499379 252499393
    0x210d02060601030c08010e0705070c0f0911041809050c1c0605070801150e04021e03091513020405060d0c0602030703090812072418050f010513260d050603 68
    0x640c100c0b1405404d4100007030300f60006000340d2040d00d0255421203060b01d4014501480350319400024000343d04000b030406249a4100700382da409c3d014585400c010150744626040c500010401030100c0804458400c54640740224180300c01480f4030202500b0203085940c006644158401e041104910101c070380514003004030703080c41d01c01c40c9d510b81658134080140b11500c0b00c581055407070341d100c00b081907402502040a0060401624030840c40000d408015640342d060000481d030805c540c00b000048480d008200f004041c6410100000d9015010b4800186a441d46030100300d03540c81851015060500ca1800002e0741035000000b0b00002e07000340d0b20100e110343c5070a0855116082024020202403080c0825000f107082820150480e04c50000c88001d90f05400c29044c0580e4840840764400502003a840742c18800244800c0187e401c07402c0080103c1d00c0e00550750306802a403d480903045035400c0700401c00b00042d40c43c41040100200c101a03440b0b0150a0709a0041c000846c1d4040c0203001d001307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 252501879 1250 252500629 252500641
    0xd1d010506010818070b1810020c01120b060c0712021905030601030210170a0c030b2e02150c0901030b03031c02031513060503070f081902210d0206 65
    0x88909809500160b4030300a181c2c441c500d03e00c1c13420384114840c000030b001c1c00000280c070ba090600100382c41154030002416100c0c072101048200003071040c003142503401070181c0d06550380c1d1121089100d080040d200054820b180404608070b401900d1080199204506000c2000d5000c50108009140300321221440e4080c08802c840041115100701354140d8003140061005140c6003120011420040c500100ca20610746030011540700140ca101d003065648202030004a23605005048810000b9030341d0032428207886407100c200040000109024180030b8484c0040c40d407082c0b140c46101107034201100e20500b005985404164080501640030a190924039081c9050200595250f0402d400601e00c00800c0302e1200406540001d2071000705000c1c91501503a03603030301c942840f0303044d00480d00c00282d03040c10502418901141c40c0c0182403000c2459000b00007080b07001a2442c50444240c04100c081045440801d04110384110f800e60030f0007406060609244000400340700a8a0642c04c96000d51501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 252503129 1250 252501879 252501881
    0x109020c070306093c061806090b0a0c021203011811030705030f100b07030e0102070b12191808070201020c0d151a030a11030a08040e07082805040201140d1d01 70
    0x9050040b0746403191205c0300011031843c2d0b0100d414090700c80380d50340c030b2030042d03642e00300446001306c0c0708480c040000c80078040c0b100c0e4a81702d004d60700400c1e40000d0012900804080110380014843c81c09142d54a40b006480312040c0d42100285502c2241000d480f41000d8401806c1904121032011440000c031700094003003400901803070f084400e10003d46207400701c6900e0440d8280c204070340c558154800d0000008040301e01c00e00520490f0002c00081c0c1d21400c0c60a070080034805400703500c4400904001c128182900380301c0040d1030465110301010396415080c40142c1c1000103505440c1d9008044c00b03410030510822100107200403440280412542100c40103031556034144990305c81d05648000c070300c10000740140c3e07041c208104006085560071462070b50f843c0c11550040c0c00a070800c41c01c210030711118941000d8241d40003075a250403195a0480c5a41d0881d00c64040c5010240b030b103480b0340220b41036900559060300081c28156000da40c8000d01c4640308042c00c104085030868000d81c1344400c41d01141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 252504379 1250 252503129 252503213
    0x3060c02010b0901030303090f05100b04060e0c03010509070905100e03060a0515060d0615030b09070c05150601180603020c1002040b040e181b010f080702060109020c07030609 77
    0x700900d140004d03421a1000c500a02c5104800c0b50009107107490745001c104208408900d511711500045243d402070028041560042e501c103801440c0d4010600c80240309101c00d82c2c1c103542d0143c035016025035401d4400c840e07401d0280d015941007100d5000342001150f000b00b0303101590743c0035021101d240d1a068005402c4910071188007821109100b40c2005524110b801080403101034040495115142c8201d0a01c0400f01c00000000c255100f21074106400c10454103035001c50b5074100086240129201c543d01e500d4001003c443e10308181e00055240c5e8040e045551180901a1086948039110f0300302500a40c4040c2c8110801e1058209040c99444680222410740d210320001a090070b00d481c5692030600c0e07020f8a00203060246401011003460100007010314513062000e0310f810004824005400d09a07942c0400c01003200000400401d1078000070324904442d8410001a038500c0300c040514284820307604020030480c00d112000d0305100252542c04d00d15035600110a00021000d2048010808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 252505629 1250 252504379 252504401
    0x6030f0629060a1103030c0c0712050607030513051e0f01090503190203041a030a0609020f03060d0c05041104080f0c0102070e0a11072f0307260d02030403060c0201 72
    0x4054141201d94104034029081e02e1142d0300b0207001d2103052406050658000f00c0b05041c9100c0c02090428003e981045501c0003486180e5507050500060307196103031202c00c020010385c141511074000c6180c000304441102200c42e00301080e50030107030120056031034104c2012190f000318800c0800e14001c1c290306100d0260011f40c410006e601c0c055104418000791443c0c9080881580070902c00020038060b41c0400c0134012446000d040d030369242410002c012140650000058a803050113628418041481240c0d000030040350340a03140403071b5240094402600b44c0043e0f070040c4c01c204d201450b003a242c90140c8240c0e00c010060311100c00c3c02c09505a40c0d116000507160050b40304030b000f040041813140c905600300000c4000490104121154084140d00004088a50f0b202e410030030100f00102084044088145458400740c41c0b2040700000d996881901590030f000802c1c01e003032600850070703010204004680ca0207071902201102e4000c2e440f90464442a2241410100410796051061080400301030b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 252506879 1250 252505629 252505691
    0x304031106070f081e070f30050603070306020f04030611070515071101140702060a05040203120c0c031b090703060b0a20102004030f030507021306030f06 68
    0xf0642200071100a00302400c03404002d00a016185403e400c0d031198240701e244161161000031400402c01030082e43d49400200f080340581500010700d04556041c080000c00e840740c04995038a4000000e1300b0324803103030b1005002c0b92000074820b090305101000707402201d0103024108175020b1a01c02c8107426200303040004007281c000b902c82283c410084e4000c1a0132683d82d00d80384001c200d00e6402c0d80d0865100d10740149440e5007002c108502d5a6040003101d82c40410903400303000b10f0420b940400c1d569075991010842c00100480c080b20750340d10800401510781c030002c0c100c1c0d50800612045d21a44544904118041e8a00c84005050180240210400c440d01822403926008004400322000001c04000540d40c1d0140c0000004070b80d000c0140c1e02042c004c0302000146060312041a40621139512280d1103101700610040010502c0c0c40c0102900640509002d030351030f0524400145001c245106500201c1c0c0b52110220a03c6405c13002c1540a07480707104200031488462848041c1c905241640800c0740c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 252508129 1250 252506879 252506897
    0x90605010e0f040905070305030d06092f0a031e05010501021e0703030f05040506031e0105010c030507120315030501050a05132103020f0417010b0a0308032415030403110607 76
    0x1810f06510083c8402e000ea41500c811310b8481d039a0320706550108003130b000c641da190f40c020b010000861103810140c48002a04c08041c00c090314034011200c040081400d050140450040021400f07a006004030410810b082210026a0001003005100a0160900500c1201141105150010750358408005640d0003006480c0c80c0da64211120064038541404105003070100145548900000d503000300c3c2c964141e9070304585000042d10052005030710040c1003246881c410008030b90024119402590819151034808a106405401038a40c00f1000880c83c8004030001007485010b5010b0390050303540310703014005605c03012200c0003030407203420014141e4544031420084114101c07019580390345480c100541000d0460741c00c0c4030540c016a00268152601c03001400203003000303101d0148500000c4400340c1e01181580c071141144c2c000140002900d9404e004c01040511340342e0307240c1da0355010040c40e145120b00e040111b00314640054400701d001c0b8101c401c0d000a00c20000c200907115043e1a07a5031108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 252509379 1250 252508129 252508159
    0x150105180717040f02040c020313090b0d0c081f050c091c050105010609140301021e030a022209051501080604090813060801030c0f06050301032316090605010e 70
    0x4800050409014840b40e031142d00040c080ca500c5042c440c502482105110309602d0052006990070b680700c00c2e0454008010701400e842c114200071050322560100002d1324044071010910300c011408026014003201c10b8001107030a000185c510401100c1480d0758400c1c1c580815102c190b41c03094800d08442c010910030f1a41c0c030304042d83c0b6807100032400b8a550901c8402c1d500c42d1421900280c200b200000c2001005000006400400b0304204030260000c500d400185015402042004000b800ca16100040400c4600880742c0594841c6c08410019181d102d990b16010031311845035100d20f6044904010000d0b07224040540c0c0c003c0140310603120303c0301c56a81c6204120007003455910032641c2c0e070300c02d00c50303058036098806007070015042c43e4994007003a50450400d100302102030761004101e00030280c02484030350791200c02d80341101e0740322071110110300b01c65005121124203d500303982f051081d94610b02071400c1c2103094004403440e02500300005600c42e00110303110381c0800c4070250005200402c2c0f8034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 252510629 1250 252509379 252509419
    0x180303020307021e03040807080a0b0f06060c0d03050114010f0f1202070602120411060415080c07060f09112b08040509090115050f01021504031817150105 68
    0x40e20101c10310580c0d20943c00354141301d220b1041403d4180180d0f10104040c4006001004200c01a00d01c400043c0340c20f0026684030800300c007000740181c20312200c00000c01d0300c6440390701c207498841da402c0c0b00340c0c0e03014a050807004004000c2489441400f07044030324412800e5001c2c07951510079114650f00c1d8119070901c3d4005848a420212000c04070503030030440071002c28814409411042001076002041e810503040030485040980001031007002c003008200502002034007013180c484154100200d00341d403000d800c045540694000940103e0402c808200c154034a64010301186100b82080100401c040c1c0900c6400d004000d00010549501a807030000c10000c0700d035240005101e03842e0b823864541c4803000f05030909402d07200c010050b91200020088000d10b0f40410000e4501901d150200d001c80303000003075988298503203407201180d005010806240c4070b1000920403000c00350915107810780c8e403c0021003150707140c620b2040364090b8444621a0400c0503202e64100e6000419004080d42e607034595107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 252511879 1250 252510629 252510631
    0x3050304060e0709021602030c0414040f020f04020c160e010f0b09150a0c0623010506130302150a2c06132102030c1008130302010902060714101803030203 68
    0x90b40da21440034000f8056603540024010070400d050340703500020417032051610b02a11020010700c01e134100800b20049050f045d801e140c0c841d030001301604403980d403400030600e1404040c0d220341d00a03000007100329501100103521f0381c0d0351440c401901030f001d41d901c403008034170341c401c0c0541082040242002c0007261600e1010340351b000c8005103065410228021400d10951190b1082d002007000002c1600501c402d5209403d8000340319200d01c54603a0303003204541000d1905003c2d45125110204d2a101d2480030964803401a550140444081e030b4042c440c2040c558125540c00800296405030003101d1008080c1d845540454400407014110705070b104000060304041c2e031004602417032410020b45140040700301200402d1038002d0540d0b0200360b00505050045084045000d41c5c44c8249414815a00c01900c90b48102818078a0b2440b0030700b481d04034003418514001a500602c04905030007400214144400c5c0c003045142101c4560b58490720010556059004a031110b4004442890109001c1e40042d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 252513129 1250 252511879 252511901
    0x70e0f040b0a050306041a1f031e0507030302031e122d1302010906020604021020030c100507110d031a120706080a020f030c07020a0e09010207060b0901030305030406 73
    0x400d04903443c1c0700440d2810104a405a903040032807111079894500204001d030301315582d8603102c2c03450b4806240c034100410092200038140ba0303460108031152a864448040680d034440c1c251102d40d83d903428001d5690300310000303400c0c5202c03900034200002c00c0000b089031048174140364590290364a0041c050280c008110390f5a40311022840070145507000b80108910880c0d0b54104480311314603c1c00014030703002c41e07500000151741c0801c0a20016076605d2111003180d44c003501d0b1008450a14904050210000301200c202d90303c000700b0206121480807420311010200750030204059951507000711407552203950100303a070b6040002d861218500c02d41007070701c050400740e0325000d1500e5180d002c1503516258002034045908100303c10700c809544088825040558007905504103400408064002e00c00074151981c0300710005051021500d81104540c020480c000c10340c0380750b2030041c250360301035840b80904072101854188183c80c42d2410301e40c1c442c107036900342d070317545040d0f80c0c80d44d60b044010410b4440d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 252514379 1250 252513129 252513139
    0x27051f0b090f03070e0f0f04111504091e0b03031603270b070314040503100902040b04050f0a050705071502130e010b04080709050402060f0a030207021512070e0f040b 73
    0x48030b00e510100320134001071030032101041c010b141c002c58001c014480680f10300050b1102100340000b0505240344072501c1103040300c0442c0300c0046648495500d21030f55100900320f605003500780025086044c1b200920700b10750281403001440c0b010406480303118152461126601600a030070102e849500800340e0044040e56081050300924501e40d007403d010342c0080c0e048240010310b00e00701640400034001c10350b400c0412a08007070801001030344903540c3d510b402104a940d410154290b40e500d030401d640209000c0d000704200d081840f20030100d02800c45d00040d0130390a00740030070101840307201129a01908400100c0c0f1a0040d5680f060282d404080311200310100010003080d13448542005500030007000407555501d910b40804907080604075030044032010b281408010150319208115802051403014080c0c1c2d0302c5071800244e00a000c2d07a030029400c94034070100d604444100e00010b10940307021a051440750341d5000700031a442100310310384039040803035007104840c0c608058121803003030f00300105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 252515629 1250 252514379 252514399
    0x130f0204020d020418060302011d0114030f010510050c0a060b0301020705100c020106060801050307030f0812160311031302040e0703020405160e0901030804180627051f0b09 76
    0xa03040e80c104042c1c041c40198005030801803405101c81000319110b05100a01c0b4017071450700060070030b180b10b140e944034410b6180ba05001a81c40b90707030344a03030300c864010304261a410b014219029640c424052940640d81c0c1908414a20b8003540c1034582c000d898600400c3e42015559800c03002e0011506600e030959024445400028420300000c0d4240d840d030301c0c000030200602440242914034130b038090020f010802c00180f2484c0c4001c6203e10070750782c00030042c0411b007607145454050b82c42140001d500840e8031505100381808400704621b031952190354244a0529005242406444144c61007050140009038920060805800118035524401d00b55404280e403a00414255101190242108903980700f50b411155003000c01d44070410740581398410fa66046507129105132140703018000300124a21510300360000c0c0e942000d0090700e000c044181d40313004241d010707849442c901242c52100324202400036110300700401d042c015a2008003000003c1c24942410329416a201d10030042d08008240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 252516879 1250 252515629 252515633
    0x1d0c1806070605150409171312050d020d05041410021603210804020303030c0706091e0c05120309010503090a140601080105010503120d0b0f09090c01030e07030803130f 74
    0x400a081c040340608004a02440c0548240d00c0321001d050710b06101d00d10b40840708001c2501441080c00134100c54850302c0e50b4407070300158007041c240180e2005190360030446800042207400f1031070704422100d03034003141c124007000c100035070740350003a030107403410340505c0d805451304510f001e07005000c4810b42c50041d104800d411740c5906030750210320341007558400902034021540245892265000c0d00742c030b140c000c0311360515900186d101c0c40b000c1d1180d8401c0901154003014040300381c2c8134200040c0d02c035250a08801c1c07a424002c0c030f1301105000644044904a00c00034071410502034503e11a0840005145850f5040c0c00644030758102400c03800382841a0206080001e54082580e200303d00d0100c0141015072425005500b5980140c12060082e0090559030560044ca0019104001c04100d0b01140100041010a040940c1e03010325a1740145807000344101034001003400d4641d084d0a0340e061000d1204140011754416a520004002c004204005025840f0b41101d040c8018414111106413005907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 252517985 1106 252516879 252516889
    0x504081204050d240c11010b03072103050d020a02030403020901081501090504020f03060c0910020601030210030b27061e03150601030221101d0c18 65
    0x320b10200b0074130088400c40380f95451070700c000c01951103002c50060148800a8400b0925441d201000341c2d40d060128802c019110705451502460b01c89501541c03540c8080241034003000003d02c814050400140001c0c020103841d640299180c3d4118010444a01c0046e0300c00e0302c0c1c80d84100001722810810310607480c1120124100029195618000b1555808002e038820398140521001c0108807070040003e001480d82c1550802030300307006500e050b40d95607800e01000c4c3d0312130007025240342d03564403940101410030380c0500088110801000001c10607010042c4020461200d4001c00c500760501c008500b002015003502d00001418680219444214900e401d0505421200003c0d400b80d019030102c81083c1e1a8030204241068401c000ca44004029038034541c00e481c1c2c0040008180c007480180302084012508038400e680c0340c0c03460340c1201d54403a0703040302203000d40b0f0504d680642d45c407 = true := by decide +kernel

theorem cover : BRFrame.Cov 252338129 252517985 := by
  have h0 := BRFrame.cov_init 252338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 252338129 ≤ n) (h2 : n < 252517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
