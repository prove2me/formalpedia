-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4831
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:52:43.056373+00:00
-- url     : https://prove2.me/submissions/efc866eb-028f-40d4-9450-a116b154c4b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 868705035 ≤ n < 868884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 868706285 1250 868705035 868705069
    0x203180f030709020c0109080301172517071707090506240c0f060709060315030b01060f0e0301021902060a020c060c07020112060603060503070902070809190b07120815 74
    0xa1785410780c0030b699004080c0700000512220000c0b00018810400c04114501d0494940a6680d03c003640c980c1985041c2e00c0c9814906048800d5a003844003040d403032204a4944030620448101a4944800b854400004aa101c255a106100c05c2c01181c0c02c90048a4101034203640c641d4840807589920041c1d0301e6101d000c41d850800124442030600402c2020b072072030326480020b07200300b07007080c43c0f0060501d04036014100c0428105012582c803541000140c400301c0e500881103005d16400d10b02e0848d076040781d03000340d40200440880c2911207a9020b1004100414504c4480b00100101c16406802c14500800341621244148a080300c0d405c00071400a80c0103550703142c2e190740d0315580d00c0140e030005a603805456034149000000705203242c0552001050702e13412000c480e20742d90740d003407210306901c200308000300020f00c04d104000c1181080019594116061144030022236110000c013003d580140d0f01c1540c1203604042800c0415402641c1c55803c0700c4020f4042165130f0700c20020415800e41904582 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 868707535 1250 868706285 868706287
    0xf180105091b060708071a010b03160806030c060f03041e030c06050714030a06091b0c0b040311030a050301060f0f080f0402060d1404021003020a020d0e0409120203180f03070902 78
    0x10001e665454100e031210390b4002052510b9910038100347c500004c440c040742c801481d4090001c600c0c0d41202003500c3c07080d200c032505042c1c0b05c140410107c8589401030415901403080c101d4182d0640c0d00c010207421195800c100c0e450b180d1420741040c89560040700f8400c1101c0400510080100307900a00100c1d0144c0c02c414041800d4456490441d06140d0006100d103170501d02105000e1054115005070041341e000c2c0d8818440b40400400000d41000a01c030f880d00814600f518150005100d00300c0140c0c0240281003031011440b000000a0442d840100c109000510010060001542103030303100241c4021481c000c9000ca810b240044e00342c2001a040d181400b492000240856a81100b15807034402850740074444d02010740312a0400820a4904a1040c09544030008806209201707958241312141d00500045200c0002a1503142242c024581c0051321103e403900030988507030f20101c2c1e4081c1c44d4021580c1d0703a000e22040c03a1070f40348582454880e01504d0000807199400291500030345d04411741c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 868708785 1250 868707535 868707583
    0x60605030a0c200a020a0f050d0f1106130609080307080a0315080f030408060a09080306150f0313120315060513030c0f050a0f121112060f18010509 65
    0x1d5512212000000102858110000c0b103c81c001140600203188251260601c640d240c00d03280010344202e00403240c00c4142c00c0d050b94003051001520781c00761409a1030a078070a0b800d034800329215074041500700400c028178060422005600ca00341c0c00c002c0203074401941c200b010fa6541c00e5034601c0740380c46007010182c550a41c0c007030f4140d80c80d82900003801c000088440b0010a0100261a40c0244c41000001d000302030000702289540c1c0102200e066120041a00c3c40d41c0314410440008210302c0c1000f001002445a03004500c02100190301070700440e001d8100d02d5200d450001940036400e00c04908050402d400344901c0c0d081d400c1c0790011359040c4d08200351100762185070b1030500205584050000340f05014005100311031210600284da43c15250802201d4403000415100e40e242c1c810448a140f07006184c0011401220051160000c02004050b0602c070f03800c480f5181032020350360060008448014003100c540024034602c01000210024801403801c0c0d03100300e46603504a1160400c484d4580d0301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 868710035 1250 868708785 868708787
    0xd05120c16082a0d02121306050a050d18140118060b0d0b010f09150305030409020d0b04050f061e180402010c0c08031c0e0a11063604060605030a0c 65
    0x2c50304060489640490050501d5100c0c0b5130364003032505004025015004c3c0200d000c5046a040740c0194101d414100c0550340707002000c58007540714404040401c0020b1181c20545000c40c000c142c00003280001c0300c0c05030130540c240700c1061100014103811030383c508505517845440300001007001a030001e00c005140a200d402107007040307d5141c0000c1030a5070078000070400010006090050b1401d116003004000c400300c4030b494140d900781c00301800960040c40204414421600180500c0d10305a00202d9180e0b08007010805441c4180d0f003544402102d03804000c1035090002d070280e44808140030b410b580c0200f03200403c00403144244c84480d1015614002000d6901031100c0103140c07588147c4603c0c0740ea03690450f49450760802020394080301d10101a81201034554041c0c1d000c0c10983d10040c01c2403400c1540e070543d10103071080220b6001790041c40402c1c003080c0c40e500085050791045400300c81000356500e005200e48201c04400e0301c01e40c41d00009000c11a840320980c1c1e840640b0a90010b580c0d410290 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 868711285 1250 868710035 868710067
    0x20315012405160b01140d0c03140a060912030c05040f05120c0918070e040b0606030a0e0d030b19060f05030a0f0912020115060e041d0d05120c1608 65
    0x4078105542c50480c3c8010308020f200801641204d5400c8002900c810045003044003291030030502801e4140b50140c28000704412041c1c0a5601c1400e1040361510140c580c0c4102c10b6a00f10380c401d54400503c0403480c0310558250060103e5601c6c2c1b488c08034034081c20000300c528940400d0181c540102102040c40c2c0d9030480801400c2e200001c0140707440d405141800341480c2da41d0024220100e1401404400a00710000c0002940640d60241004c5096581c107010301c0310a40009207411b4500d52155016100400280200d00001416507000b10301c075240c030340c1805a5081c03075a0072aa00000040030411450340e0042e9007415007011841c00f10364075200e03648024007502a111104410500c0d00c00309008110341010310b8480f450325034000b8045035072080000c4188203014407070100414031104180c0814a082e500881c420050b01e140c4846101c81c90101c58a09a01c5280c103a021810003c0d5030003030122818011035110400203c03040c0b81c40c03c0d40f140000746500d007000047c01d804d00402d411300601c0c1200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 868712535 1250 868711285 868711297
    0x1b0206220609022808010c09050d05100507020c01020111041d0c2203120f0c0201051e0c010c09050909030d110904050a0902120f0606060c1501090207020315012405 72
    0x14044401c005038448140507a500000c0f400307502424070a800210140103003d015998031858480c4c4484601c0c00c1c0510000900ad404100e50034000e10502d00490106407003014003601040d8020818070070003000290031680348060b2007103003000900c8104016105003003901401425a48410003a4540398241034070350140310001d40d41941c40e44a00c01460002480c0182241c1c01050300d0310b0f406052580c180c070314542121848000640a81402000d07500810040072242501c1848404084030b01d400701a041e0002e00070500e0b10b0351101c1c03400c0617441c0d0000440000d44011a8002114181004201e54a00c521540c945d0419164a200c0c00c50306107100a0f9000480b001c2c00901c41441d058410100030881808102c0c800c200000000000f00b000091074803444a048005200e2510381070100300d040d4220b49482c3d00e0314460420b070f960143d1000c04405008001c1c140d00985c64049500c101810101d66410701f00182540c000100000c1485e100e10185d00c000e5800310381c0401014040c1200c2a00c0b400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 868713785 1250 868712535 868712539
    0x11100e0c0a06121503020d0609170a09050909070e07030b062118010507170a0b0a031a1b0d0b040b15042102012705030a03031b020622060902 62
    0x1200041d1141c0001100c10308043c100d00c100401c1007501c01c01d080294a074080030703422084881c180740028040307602c40c99015019402d0406d0000141f40d00702215800000e207400012500c0c0010400b80c10305448484c1c000c240500601045801d0140f441c000000090264041684441d5003401d1130312401c1c00c40e4802c810320a0030600c681f0b1102c0320708001d040159a0054840d0081c0c0503800e000c00103214141c003818031030340c1d00b00d41c2d09000c00c1604028180034018100c101d5851001e0301e42e0355071310140311000f03500c42c40e94040c00c1520034030202c94009004024449507e1600894801d6007144400c4428283c01690006070151075030b00451b000301001c5180382c1c0c0000800401d40085040d007005001101c01915941600c5044d03040e1804440c4001e00c4001e020038160381700015a030b6142c1c03040d005111030300751410ba9401d58400000e407501c01610000e8022075078500031101030400c0d5030a100c0107a40300340014241c5040100c214100809010031072228007500920107030070001c541c2c200d80e07012600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 868715035 1250 868713785 868713799
    0x10603062d0b10210534080115050c0d020109050f03090a18141f0807080d210f0902011b030c0212010f060305030909160c021c06020c0c0901050111100e0c 68
    0x709030400c80e01c1c40c2d6110480d2803101e06c80381c68445a1069038049401481d400da1710f41e001c84c3d02e40131031000d1b5001543c0c0203000b03101d03003842a550030300401c000c00341d4603010607070000c140030046051441c180080202c00c10140d4008100c600e030b180c1c44103594002118528000c40c031a4130f94201800005203650702c0c590341d04040003014000c020f0313480c0c401c55900310300c10055441501e68420b140750b6034240d01e00c0384111541004054606d018000c0c0081d05c10340384e203d007440d1500040303900f14008070f0f10884038035481556900412801c0d941d100403100317038200c10099019038a449545000d001e003440c00000902c1003610700e1011481080a402215418032112001e204035070301c1c0d02c0c00703076100d41090501900034600e0314005403110801c84201038000300d0586464807a040030381c0900c4050711058014421141001c0c8240d00050300345d1008100001c81d113070146c00b54260020400c0a40801a4041e60400c500b0b8010000e04107808900540b2440c501030b00060b1240749031440c87c2c01d240030354003043d40c0410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 868716285 1250 868715035 868715041
    0xe03030403030b28140d020909160e09030910110a0809031b0d03050a0e09010905181b1c02060a1809020a0c0b09010603062d0b102105 59
    0xb405402111808604640501c80c240e00450b5543c1580c1032415104006101140c041024600001d80b141c5a901c0146c5240010504c0303130045100d5160035942d498503584002c01c41c02da041d01c08803a4601030a02094200c01d241040c0e030f040c903a24010300d500c1ca0310030b03132400d24006580c9005044c0614000035041c00d44d9200f1a881c2481441604825035550180c000c2c07175501228001c2c001090000c0200c0100080d5840c03080e51021203050304284225018080000030170351050351100c1c1d8442c000c2036826400314081c0303407151940103070a42d010543c4001c0d612600c010b00c8080c030f00003007401c6000001d8400800b0310300c04d1101c0c001d80e0100720b0006074100c20002294a0419032050741260011241c65000c200035a88280a00433845404c100c540010b422103102e00000b080082140d4004001100100354143c40c1d4443c1c50480d007507c400148143c1c102040030100d01d0011038515260282c03503008124888a25010483c403281419910b810031000b044001030b042c2400002c900254000d800801c040d10f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 868717535 1250 868716285 868716287
    0x6030403080711011d0606030f1e10060b0301150215010b070c0b120414070501020703061e0e0102040602070503120414030304030611030406140402130f060302330c120d0e03030403 79
    0x10007150b1749000c4601400000917914200003a17200c03213030041c4d00020200c01c21040d911180a807250f02c44880c030f03800340a420030005602402244080c010000c01982e6035450251150f034503c1241d07140e04159000a515141d02d036451070aa00e04651911203242d07034504241c58402400b0303a103034100d521215400714000288550b403140b020302c900d02c03507150030f4aa0303410004019560301d420f100f054010b034044003052000400681001d030303040500c5168080c15500a64000c0140d4083d08000100d0360743c0403508003c10342d410880c40300100f1041d0050308001503040842c02d6a441030f4010600b51881104031502c1c0da440c204125401507400000030003102840520361001e0780d2003601c05aa04270b08100c001d84101c041414800d0103a0b038014224408003058490300006050f0301d00f04815869545c00001026071180202c6000c2814105610410103c80d00300740d90198100d120f1300d9210700401d00020344010741c002030b8008802d0509541030345808000e6021400b40407486200e0b01c0b1800f000c8113000c101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 868718785 1250 868717535 868717571
    0xc04080319090803040f0b070201030204080109050a03021e0a06091e11030c0405130201030c1103130815010305190203010618020a020606010e1003050c070b0103121107050603040308071101 83
    0x6041d1550703400030b0300355504010f5940740203c0c041c40300c4891003c0c000f001000301c681e0081203058410305025050a83ea42107003400c40703103001420354140c3c00400d000e4040590602152100304921039001490708110340c86141d8403034000100414141d030300d411503428001d0f0a09107000c02e01c220703480b201c0d1040e030b00d02c1e0820311151343c00141802480340440c440090b20345805004c0c030410444c00032004e00442a00110090200103c154081c09140005e12101810078001001d201d1500d508031740c0414a00000c01e4a40905511070b00f03a61841c040060000450100f070281c00d21040c0108450444d582c0d00000f4018000b5601900803a01c2e611000e0042c070307689402420303200b0956000d60b1103507600c1c4070054440301c0030a07011551144003004440c0302c3ea80280d0080e03070000a00042941440516550b0b076403000800c0c0c005891089042429141c11940900d60240040c010b0740500100f51820340820740c9400301030002401d101c001000285074a100f8160113583e04c80c020000d100259031400c04c1421 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 868720035 1250 868718785 868718827
    0xc21070e0a11280503010e222a050301091e0606320411090d21020a0209090703030c0b15150d0606030603020d081e0a090e060405100e0c040803 63
    0x40203109241c0d5883d481c040c03003d80e412208107101002e060340e54a001c44807262103586c0c0301d2009121403e0340d48007054980081c0710340020080c481e008030f40c1900c0700400e0100c00ca94001480381e030601c1c5909001030f01002c0c0c80039500c00c0907200c190b003500b410701d0040c0151010390403002100c030380d2000b0358603400d0a250030b1901203070744210383d0456a912107091005560b10300c074140ca42000100b029207510f05241004010481c010b0711071240c0c0e1200d0084500c5c0742c0402100410040e40800342d03030f400703518044041c5600550740d403004040e1246550b5014040c03480580004c3c0c0030740a08030008404800d088a42000200d004002440e1311a44440c1c5d50342c2508a90586040d991500d8408036140c2d0083c403c00080c0c90f001045400c101d012551500d280b5030000d142c240f440d41e000c030302146201e65a075000e441004000d0302c641e6409e07800c040200401d100020a00c51040e0b00344420b0104c225031484d00713101502e410b240e980000c2e903110307040e01040c0d00c1550300a048510000410703001e168062256001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 868721285 1250 868720035 868720087
    0x309050109140a03030e010e060d0b040e060403080402040515091303030f020408070b070203281104113907080d030c090e13060903020c21070e0a11 65
    0x4101510b03440c10484465032281c0c2c0b2500030503040c0092001c240510380c1115810b41c1450b00582c1941a032004c01d0541d040b94204844880c0c0303036418140946420b000c1c045146008000902d47c51410780c500624100b005413029010b2603880021030108a41110400c1e803550000d4000b400e07d0502000c0700e52002909103065000918141d0717000700750b0300f460017160101e0360000b000300700060908089030601e5010a40c12a4076104060f9036000f28080c0190100200011401c5240013441d40c3c2000d048000032a07900600c65864100c0b401c0368104d00406031a8005811820741c800c44070340046081001d0480c050103100f00c0c00e89003403580b02d040b000955905444c4140f06a03011410804026030650366800410008101c1c44003040c80501490140c2a5000500c400e004502c010240c40c0c010032103906180542c0140c000c5480382100342070003201c0410441135410301002062850384507a1312039189003e5541c184100d100821038004450300104415441c460350b45a0b906109003803980c41c001850f050003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 868722535 1250 868721285 868721297
    0x5010b070c0608010503030d0e1e07030c1a0f0306041103191103011d091c030b21060601031e050f060306100f0b03041e030207060e030a05100c1b03090501 68
    0x100d54944a07010710f0b0304844018000710700b8105800b030064042e286a40c5445150300c02c0040c201c03480000c503601c40c0c1c4100384942c0680000c0b0304600b48200c907120150000c030b554107403002e0484070580824040342c000ca00054802d07600c03602c64100003406040307903040a50307030b864000c024000c001d00030310340c3d0b64116020b15074100640035821140356040d0001348900650700040e803c2e80b203000030003848502e61000b416020368078070074034a680c1c01d02180da01c3c1360f680000139a96103c2483e03d007419181105005a1210300d80120540c012003150f40310001004181003584400301d6604e182c001e44901c0094071080e0106010030724190b048031510718001c5450601c01c0c41100042080958100310180503103a07a0081000700b02c0c18502408415070010f00f048501003811614150120030200035140c485210b98094a00186000c1c8000c00c2004000c00251003504000124400240b0004404540f516101d2001c170354070800c0002a520004400c100ca10007a442c2100c0d90105503101640b4010340300300f6200c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 868723785 1250 868722535 868722539
    0x31d070e24090c1303050303011d0106020c030c012f03070b06060f041202010e0301020c0606040e0f0c040c0509030f10050a09050604170d060f140609010c030309021305010b070c 78
    0x14481c960740074942600407045070041074484001c94024860003000059083d0307459640da64552130742e03000364025500f080c1340d2060400d0903103540c0e2000f03004051070b20080001d290f110380040c0c0c0b00d0b08031904840c144140140504504c00d62002d250b0100030100b101e20100b02d03400300d0282d4032640040310858180030740d100060f449240500640d8400c10302e10300e074181042c0c01c1c82440452900188030a90600014013080304140e9001d00007400f201c0240c0d409007030503041000500042d43d90382c0032011101e4000c14905849007400107184901e083c0200c4000c0b0381c8001e444070544d0b0f07512135141c42a425000344d400646040300c001884030000e407010001082107964101d01c3e4001c441140f84001d116402c940046804111450900c2001c40070100300c0c02d26000021070329070102e5400340d102400303103c100c400402c5503480703070347c040c1d1003154082e118503240c2005000020801d80449100509042e80c2e51851801e54490490303181204514220400465846400003507042d000702104603039280d071403100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 868725035 1250 868723785 868723831
    0x1a071e020c120a0f08030901140a0f0605100f03020d0e01090f050c15030a1d0607020c010e03030307020607120b09100302190501050913091b06090905070f031d070e 72
    0x346203c0d40d0040c0603c04800342980d01d0300000d510140001e0748541d01c03911a40500801d46201e0341c011043c0d030000084040d000000703001911041e503c0381d4401c009100401d0107050f0083c0d0303180408841440c0050392800600d512703200904010800081541c0b0b0071241c0c0701081010050b000c0c0c140e01640484010f03000c00e1040190203003949408030541c0d141440031a1090700207070444054a144101a0203454000d10381c01c0345070034001c03180c200041c0e02c1103505507080d503000390325064021802e40242d0b187d840d0401000c1c1d40c0303917005407560041050070f003490080019160305c140b0100c1e4000b0f004002a0802045400101010340026403190000030801c070750800c00d040341c0300100d81060f125641400451400c000c1c072500340c0400700000948604820000514208603500d43e40700c0134288403880c1e0700b4101c000388145083d410400782c0c40d2401051058460308076030481d80400c82407402082d01160101d1b011440d180c001c142611501c01c801020030800703410801144a5041080032002c030688a1103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 868726285 1250 868725035 868725043
    0x921030a080a02040323150907140d110d0f170306040e0c0d02090c0403060906021b0708070e101707170c010903060f0b0604090c12091a071e020c12 65
    0x100040804050b862091a40c2121b6460900c1c0b20110700180d516501080c629407088203030465040c99103070010042885100d8861005081808050b501e0300da003c41c1941d02e0700030711b904c13001549100d01c0c10024444100048030704014141c0754003100195284400080900301c5401c10303104a803041e0f05052003501040d07400980200025401060074588031915000d0080c407490140c81040d803d802000040045220f9000c0c04040c40c0c803038000161b81d128084080c040848240d02881c8160300329182c01c00c400140065030505599031042c04061a417140c0e140d41207000c059500c04015466a80c41c00d00d07040a022601c80308855a2000d141043c0c40c0d00c143c5191180940d807030303190101d01345607414000320b200c13a444a0381320a000c1a0002d55005001d0014070160095846030012a8031a0b0080703105551140c0c88c8131560140a405222000d1995100c040d002c1860405180b121301000000b01820720449030b1703440c0c0d604410211070000e03c0b006002920b6410412035140903010060940c0c0c41444001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 868727535 1250 868726285 868726289
    0xa050906040e1209031e1e0c060f0d0b04050c070b070201020d050702061807150e1206090a03110d09030b040201031508101a030d0c050307050d1d010201050702030904020921030a080a0204 82
    0xc00360144011f07220b02e503110140c51030780d1141030340b050318500c3d0340300d03180e900041900d41038074108142c840c08020000001e43c0c20894005000794200700c248800c2503850303015211880d80c030032100410b5580f44c0400300d00900941818100302400c1000380b182e0244c0220f0341a028504c01d00d400f640d40c162040741e0360713070700c1c8407911583d00d84e440c1500d1000d2200380f00e00c10904400100501d00c0892116004105113020703019208594603404c1921032000301604000300070a024185006040201e00c07481000e04520401d1002138001e401a00010341107a1190b44110f00e07496990701640401900d075044241d854400c00c1c0c8005e40585821060605501c16404414400c1e00045c0140001888100201c61101c0000c0044426200c1400a58000b40c01845050f444040365503600c414100c40300444400450851403240c150791524060042690b40070089582c400703001d4401503070b241e02900c0401e01c040401007540418403034500003000c0d4000c01000511302c4008541d242d00642d1a04198801248564 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 868728785 1250 868727535 868727593
    0x4030f0203010b101209020a0801050c13300204020c0f0303180604170c120c0c100305040507050f030f060c09090601020708031c02091201060f06030b0a050906040e120903 75
    0x402045d0886900c1034000c1090b00d44054541d00c2c4456551000702e003960740998201c041420f0110b011840030700c08118000003008070352009502841030b1051030025032220b13940036030702009001d0388805545854040302c1692405408840e100c0d42008410303501c0380c0040d1504561001581452100300800182c101c2c010394018500c006228442014105a0340c00301c98221a05d000d00c103241c0e25021241000f8216000d41e1501415a20500f1000c01c6011407024005000741450403003440003003500050500c054440a40c0d5a00c0b04034270020010b81f030443c0741a41c0d02c600f4801c1e00100701d0070448140150461600c10345001d1206d4a1f200e0059031030f40240d005030030150f4018011348203c240028010091110b688800525000000000c686a80c0748201a00341680d1510800c1004180b043c81803030003040e245c40e082200050b2070000841000c841c2c0300e40d074414811034010076419641e942c44602c10070060300031144102052242c80310180c006075401c0c0e209000d018a0f814002c615031810130111101c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 868730035 1250 868728785 868728797
    0x1204051305151e0109060906021b010210061e05030c061813051302120303010b0a030b0613120b0f06130203100e07090305071401050708071704030f0203010b10 70
    0x8105035440040c40d00410100a0160312090781000d52280c0030502011000780c0d01c109090303500390001400b140b035998803080c108100400d003041a240d000c0742c1000303002c500d0a2910160111480101d14081440e00f00d280914542400095410030400840442000e54145419426075a108045d16114003c8480ea0440c80400400c4007003c1d0502450142d0400148059080b0049040d0401111b800301d440c16003c041d070381900802e41c5060b0054207001d000d19401545558100728900d00e50340141d95103503003455102d001084a603524036066410811951512a41e400d60707420381010300c51903401c000c0e21712101010206088500c072070841e5204d010702900560001c81c09a200c03000951000b84002c0700380c3c113245404592000c0895a96014168a85d610100241582415400d140441d807160525441e06140c140d41660000181d440180e000781c1200d8a50815083c1040c40c0456217400c0407040c08001070200070411141c081040e450f000b5802004512042c00030300804a909105040c08181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 868731285 1250 868730035 868730059
    0x9050409110907350a060f06230c06012102030d050c160801050702070816030821271605090a0f020f040812040e07030f110703080108120405 62
    0x1040141d00d074001d075851818180008103900700741400002c0402880004224580f520002030807080256001170406008001305850b155411a150718907100c0c050900c0b0010312a0700100e000c480304012403000c50001c4a54408541e280c0544401003401014241c14070550b074918082407030042c8881c0309501030000c09942060460644e01c0d9084082030364003520495900442e10741c40110640020074001001103202d08140201030b0420851383c0021419900032000c45a0811039844201e0480380c00c481c0280da00c5400c0400e51700035005680300591038040c0700c000d00159500000181001d40825103d4540c0d803800543c42646461034001c0d07140a4a40303400041c00b03d86490702480b500700440076800903040e1868415442643c001c12150f042c98807005c5400c00000c04203000307074103440c103000345810328050811203028004c90300030b4000e03c20940d40e00d501d0089100c1d41d5000d00c50714991f25460f151207103068a0028a0310009000308441401404184102c842d104025103094407030042c0020034582c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 868732535 1250 868731285 868731289
    0x106020d0543020f060c1005060402090306150915130b03190804090f0506010c12180e1902030c04031403090a0e0106020c01021f05131b05010905040911 67
    0x1280044a024940040e405078401c49031421041d80c082c040300b00c1c0120380701c005070040042034030729042c0541c0540780420490840100200d01845075040070b40e0001550b03202c40c2c0201700240181804070340c043c49208280001c0d44010040004032090840d0520842d950b601254500345242125a6410420907841e2106488e002e401205000d0320103811109801c0e040d0318012103c05240703206540b00f07a00003034280b0084140380203440303401802c03460503c024140080020181201e4100203080c03890310306542c503d214450007210500c01c200d80700c5104ac16480c0c0310305d40c020100a84006049400344ac4065a0148079802034900c180600082241031a103544c0752401400f4204034050218002001440c950b81d0354024044c0240080314074200c959814110081d01d000c41c80c440c800d041d58081c1c4a0054840140e0081e100e41380780e2400c0110f82c5442c0c0345044001d000e41e031136000f45035200c4590007070380300c1301ca28ac0003030100c8800340d0b0340e0100207a50307100740000c076080c13240090480052411090154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 868733785 1250 868732535 868732567
    0xa0305061518010605031323010605040603030818150a0b0f09060112020a1709070305210313322401030809060f0f07060c0e09190e1c02060106020d05 66
    0x800c075000c0719181407107203d031744405c50001ca10f1881c1d00d00c0e010407006004070323600c2441088081d140036078003084a0350454130b000d01070020003800c2e82038504a052803a1684e10050cc2390b04000ca03503410220056083c200704c2000504502844940900803e47d1201e11a1034480c101c68002e0f2410303103400842c04030740003400020b5400519460300b4040c50020307213000c210f28000c1d0103210385120700c0070b00140c40c00c41c6403985c2410f10444c00420310002c00036800761821008011240c014014080d907000070401454880902c81d0460300c901a51155240703483c2c1030a426a616124045641d805c2d0b9607041b00460340040c0c07000c00120f0442e07500d2008001880000c43c030078000c011a580003482d4508281e41032410904940c08140d82c00e181c00c01c003094020400856001d503002c07800807410800300080d5aa00403030314008004120050004102c2207240d2400d080d648074009608505003500c8122010030052580041c494000c04c005101c1c0e08000110980b000c100c2c1030108542d42e03241494100c6000d0314204c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 868735035 1250 868733785 868733791
    0x3160305060622050415080c0f0109151d01140d090c030203070602070306150b0a0c020406090f050105031504020904120219140106090e07091104050a030506151801060503 75
    0x28108200c00f0781c650000c054400d030b80c400b43c20085040241000180300907603080f20765541040f86d942034140a15180031907030340e188080555074a0f28800c11034004032200c41c074aa111440d42c525080c412a100390340001da000004c11681181c0300000c1d01040115a90032038080e8040b41e5010602240080010301d070804900e02e03000f08a807200c03081d1603400085c14002c0a5111401580c04640104100300080c0225002c445102d0002820301f444d1890381c070102e01c5005400020852104120000c541d141d501a8001c1c0c03403a8207013000342e00d50104a0000903c0c080c06014401d01c261803114000c10540c0a1182c4103d5016102c1041511b5a41d10b810510480c1501c10080d400b80510740c1c07050185441030040d0440c007030321400c0d0f101056845850308454007500b000040a0500081c000040000100714040b40c1081c00b00017000402100c003640b0b42c0c015504030740c0d401070b504c56000040c04000604540191f007940c0c00201043d02142c104140400070030b003100403001c000801000a60b00030805154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 868736285 1250 868735035 868735039
    0x61e04030506190e061015020f010c030b040b15120702010612030314060a2303030f041512090b070507031206090e1e0309220f021e0316030506 63
    0x1040686070307521542008402c40b80184401c2400c01441ea91065502448980d00303e5100070f0b050728204021011a00c0b4802d000c2d070511f0f41c55011144059610802486c1070040480000304942c4140c0c2000401504c004411903100d241011005900c038030703040400740070340c504401c0014608141c07c00354440ad000000c0000c01503560302c890005804800c05e05a140d86072017a9000034490300c540c2030400c01e0b00300141c499400f030b003041079091101a450701a448451508031001c0e040040c2440006403442c815042003503026003000c18001030b5021500c1d480340301d22a039901c6913601081246150b500301c1e4904c860203045046450085180c0900540007803000750702038034001d0910080c000c880000c1d141c2c15444002e00c2c5a985089698810052200d000340b1194048103a1910043e07050040e40c0b8095031248520030019400f10140203110418291403842c400309090001495040d2054020341003012940c07482c540314103842101241035005c89200d01103051401404001a100c218014000141065 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 868737535 1250 868736285 868736287
    0x7300c08102904030b240906042007230a0825020d0b070906110303011707030c1e050f03191e0b04021017041205041703090a14061e 58
    0x100300b005184001c02c040e5018090032410b90400380c28801e10803442100031301a0f2156544504d0132540c808003c0e0341c21450484000c140d403811200884840c0c0000c030309008001200044000401c03c0280b941080320032000714001494181081554440d07841260051103c9010000c01001035002c0003903412442203812074800001256000c03a01d029003841c819a500300c148000c0140403036000c40b0700e10140a940c50000c564480c5140303400c1da07a000c180554501e00d80c085c16600b060310400c115510096030400740c0c0c01c1c0d16070360720000d012030b4001103040300031021001c1d44007040c0ca0500d0140010355103005401400d504002d005d4038100307113415140c102c0b52800d1900400c0c10440c0e102c140c115100b8028034420995050030703c10400c10030303210b0b0403030424841c082c083c0d440890b0400c50390765445a001010000308203240c0c1421500d40c812600448801140410b07524040080003002d040c002d20182c2c2c10f081d500d1345401c02c1c0e45885041c3d0320311540c051001c100124600303040c852045607020032900a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 868738785 1250 868737535 868737599
    0xe0c1003050c0403140c0a180522060506030c0402281404030b0601110d020f06150a0302100c1b0302090a060f090c02070906082109010f0807300c0810 66
    0xd2104150754030007980e00300c1e291080d89000380c50f42701e055004460300401c1181c5104150170b48024014400e00540000d940c0c00024440d52010310240d8807692005000b1540c85072054040c0ea60000e61503607002c0d10304080c1c580319000600800203a448a0000d5100c2420f280c03640d90340000c0e90a00030b020348d0400c0714801c00300e85240d50400074210040e40c0c5801400600643d52001d13883c212008100c00c1c006408280710300d036161645800c2809603501075800007100b4000b00390039030301c41e0300d150001003a0340002d2000c049442c2c0036580c43c0b01500c0c401c6408005548641d00000d09448040c050032200103007803401000b0008160b48080c01c035044034015943e42950720352407501203e2455100c1012500203c8501c0405803c0b0480d961452135512790003820400004002401c5a0080c408a800d000c030b483c022950aa0003040b0000190581020041e00c2071020030024480c0e01441c06104055410201d10101560150742a240b00da80e011881c50b0015251010100d40b0803410a0010a0b144014002c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 868740035 1250 868738785 868738789
    0xc2009040f110a0f090c0806100f0c14060402040b0303070c151115060a1505090103021305060711040c0c0b04110402130e040512210c0d0e0c1003050c0403140c 70
    0x14009010325510300e52501c0ca0300c4c0001086d06c0079400c40d001001035040800803140c0d503078150440e4551491610340c203101c5002c070050341d003005104406001032200b04c601440000c00007401c1840b407842520180400c42da03801c140f569034001c1c500e00a00180d010314050007006042110740c1d018141c0d61a2403540395200446440c1040d001081d0110490010401c0054034100381c40c08000518a240f84000740304102080180382d4090f2414540c1013580000b503001e89180e8100e00e0340c015000c0103088642c0c604180c600b050311070020b01003441c052402c004d0800a0240214241e5003010303045102200c1683c0ca6030384454062210790440e540c07140d0300b404032460306d8011909d0200648414508071100741010306126140c00c2d00c4c864481d980b084108807a010940c101c07450700080f48ca00c8000f0483c0303611022000d00036800380c4039182103d10711f404a805005540010000320480090358450082c810808003142506c00403544440718003810401080040c000f18071580c4070014000030b841c0d1160003580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 868741285 1250 868740035 868740049
    0x913060b07050303180303091005130c1202030d080610110a051e0c150a050a090503100902090f04030509120a05070e07020610061b0f02040504030c2009040f11 70
    0x20150342d542e01c040200003120b00708000408401044100031030031890300d41c040540d103941000c41d08103060344072404151000e491007040710702183d02c5044da550264607404c0601d003500b010b180a9219200c1c9103030841c0c0550081a5071801000003624051490390607890a40340700d005001c40042a00c290b01405001c10b00c140001d100e00c0c01ca00205900728120110803a24084d0ba481c1017502c0303000c0142e014443c00c0112800c07100c02188a0509648802058501ba102c0c3c08140e4400d58140c02103000f810408001d50340309000e818801c031018041078494140002010307004982c02404078030104041c284520386038400084210b445002c41d10280c109a950300e042150990080000400f10014041469010b214a07640540c20641030300300f032850040e0042042881100c00401d5218100c0040c00380070031180070000054010304103002c5400c1a2900409080310a41d054840d1900b8690254488011007411501c00d0b8004080201c10b44a46d02c41d89140041d0502c112941c101d40401d828190301d80d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 868742535 1250 868741285 868741297
    0xd080409060e010303090b03070203040e180a05010f110403080703051c09030c11040e061515120105010f1704020112020c010c031415060720060705030901091401050913060b 76
    0xc602d1041c0741d45540b0f005040380c46242c10143c01d004003841000310b0f00e40c0c0003056408682c144084485107455082040101d81ea0114007415280507180069060140c150008146045600401c1100283c54400f40d0420b0045010046c801a4200b05240200380b1641c064484844080b0520b0b4890500c02da04c0811138154200032008540b00d004410203000c00030490003499401501e09101c0200141c00c000e03212100100743c0c825000c8081002c4c11981c8030840f6900142400065040d40d941011030300c84a00d402c00d10a03140001d81d40310182c4441c0348a42000c48610304d51085003a40758489a005440e240c1041601c400341ea64203201044043c282409800d40e507000c5a100051080a40c04905d41c1a107002048400c0007a8143c40100b407030740341c1c802118140d58221919880a845d5010420050310141c02c400ba4050404281c020a1000100050070011000d80f100002a969a03071403030912960b080c4aa804103200f0701c2410380f10304200044400460045500041042d01c680d298403540d0049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 868743785 1250 868742535 868742549
    0x619020c1006140a360204120c060f02060f07050702060a030f0f0e03040302010809031201030812150609013f0b0913080d0b13380d08040906 62
    0x518401c0000650900f14030842210075034040110710704048048620600c460f001003203d00441c4502e0101014264a40d00f200c511082d080d95155079801140032140b4840d642640d8074201d01000140715800f41d440c00d11014407903000341c206603070b80010540d540c4070001c2c0b0000c24000708020110041c0c2e651001480e02c0c004a841c0001c00602500841040f642146080116175240c81480c0e00e0451001080c0d400b143c1d030918200f001c690b1240c2c0c88034118040c041081161166a00000c403c2028402c0901441d0501c03207110b001c159946030300740ba800f0b01888405601720784100811181d5504c5032801e44055490554400e5803540000b1030000d400030000c0041d80d440b0000300700c42506241d40c1c0140300d842c0710708482d0300c150b600b041c06003604a1010410300402c408400104201403000c1038000754030005008056002103034a4600001c05810440c55450580d85c8ec800c80308640c000d55582564000c80301440c070300140c07c14a083c000b000031018800d8130101820f00c000074540515000c1c4101034811 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 868745035 1250 868743785 868743791
    0x4090504030f0305072d0c0203010513050610030209011202010302071202010c1404180513050730030e1203040801050a06050a05010206010308030406092904030e0a080619020c10 78
    0x40300b40300804445001c1d011504000c0039103042a80d00746038010702040b0900f2002d00b56660945003030151441101300703000079010750030302003080000b0482e9981c030040c00f03009505441003940c40c84070310340f80d240d042c2c00002d6100307451344011b10041c0391203c4401041803040c10010302d05100d0f038844050903541d804401c00143c0d10703821501002707544209211054140900028202400c1400e80038809141120700b01440b0365030703400144508005820407000c40c0d040070545012035140c10780001200800780140045112080b2210f10012018140e14040c98240d43c616044051010030402c280000f840d40e0380151006220215200c0d9080c07040074040c0300c8541c00050440e14001c1440807882041e4031960540d00081300400108049000700c0303601c9a841000020f80c05058600780f40c021502d0f005100c7d4442943d00c0c045503490062510318022030180e03c0709100007100f07034100914104207015201e040e411680c00b06408600e00c0441001a483c01c500c098100584015100c0c074108000082c2610503403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 868746285 1250 868745035 868745057
    0xe0120010b0307090603030518240304170a0206040b1005030f0f0609010605030d0c020d0602030403081f1505094b1f200114010b030f060d080409050403 67
    0xb40800800000700001401401080d19548014240e4010420340e0f18918005600440480d55004004103a00400f6036040d04c2c038240c6042419901d400440d400c680320070110080c000d000c107508c820345e06260103550003804165502e03075401d981140c0140400d080300c40943c80c0440c49940c284102c03c0c6080303a1800800e00c0c00361074814507180c910094454400c0707034500b030010321250f200440d0003941c12240c2d04080300d1340300040c40031619030001050064450745c404400d1008140d4041501402241440000034a80525441482002d0910720803d041034011a01004d001350280000d0300d0202c0008200c1d00704080410000e65603141c40c1c0c189030a14480381c031348e0f40e11070340c40c503981192041d1010081200701e20303420000703d49100d445040d4a070100c01c5018410300d447d4415a4056840c50716260340c0314001100c04656030180040d2240c080c02804000c0021504ad000101176a104131000c1c08450130688500f020721045d10b50501c42030300d5807201044049080e01290180328000c92003035a50031b007198 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 868747535 1250 868746285 868746289
    0x20d0212010c170105240d05070c02030d03050906062b060b09011703120a151701110304110609060f03040c090b27091e0106330e0120010b 61
    0x900043e2000315104041c07001800b0545030310500b440c07401d040707038204454201e60030b00c2c000190182d000c1056030315003402d0030003482d00c0d84041680119842134044400c80403c440f4103400340e58080f41c5a041581c03001e80060210b150000800c5104501c10903c000140003c45030390303040d80e0f0681d10680b0851340300c0094645c00d00346043c00358018a11000e00c420300100c120740d15616481480e021a180d80340c40e80c042004008654048074207184103041d03100015565040c0074014174200c101941a03546000c0c0e81450750a4400d040b240b1071544080d0a5a10310766103010082c2d00e810901c00c80b5041601400342c907a07110803c800450145015907162444035191840c95010f444c400c0400300d000f5200b00e42101000444040e00000d070904022245c490f981c1c4400303050303142c074140400e40120380e4a4290800c0440ca03041d4802d506555160140e140c44042034090710300b030f40e1050709100c004940a060011101c922030450030b02c501c0c9051501540135401d621400926203032030b035950602c42c0d5407160201d41c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 868748785 1250 868747535 868747547
    0x120e0f0901090614100f0309080c0f0d03050a0c0c12020c0a170d0504080c1e0307030f061409101e0501080607080a05070e0411040506040b03010608070507080f07020d0212010c 77
    0x11000480d1031690300c10640c0c5d402003665540840300000d140d1500d00740c804000f07524080d04d0f601100d0900703c69806e028010b061360790f03800e4010542e0109151001281380b040c0d450180c1c0180c1249074440c149080d5266892050140d0841c440070708600800300764540f1669810a85002008200d040b10244811464050b0504254400b22410f0210821080103072000215100c83c0b480c5040b02e019080034107411007205504049503c1c1c03503150103044004000c01c82c090a10700d000f940205002c10100d054410a011f813444207980f8098190320520320700e0b9002503103070003c00441031030040541d07058006020820694100381c2009202d600301400300700b0a554041e00f5140c0c070440303644090055040403280640240100304045008580f80c61007100d81c5084142168010724002c0c1c14181d440d81e54540045030f41e0001c0c002d1000007a00640424203041c03041d0251904640c00c00c101ca031030058001c041074035542c407c02d01281c20000112511000d43c0d00d5090040011002200100b08501070000040803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 868750035 1250 868748785 868748819
    0x30106020c010207181d0d0201020d050a06290d1803020c0307030c15020a0b04060603021c120509030c150d0b0d0c0b1e04080c0a12120e0f09010906 65
    0x115445594100032030810170004c2d44060304024000500c4610840b090000110000d407660300d24031407507091460300c036415401070040b640380308420043e907161070403100700b0354003070b40300c0e1aa80f4a0500808803105495007040d00b0000e803410101894921303140441000c0d10b148000002155640c1d001600a1580500c0911070300c1034110054140f180c29551800b42c0300b8800c0c0140740795409000c100b0000a802007011808003500410001824909454910050301450208a00581c0307044144800e80d01e00140e0114060b5100d01c2d21400c4440110080f14240c00880031240d01d44908140d10880303442e0307038443d41c9960b400c0b299415981c804910003002030300c1d80c0c003038420301460101600d10003040c0412500c805460380010348659030401c3d450100300e411801e5a00c0a40d03030342e0019002442e884000380030342100c402a00c6501d01d469548113a10060710b0481c0026003483c8200803842507071489090790b1041504014003500ca042d80c1000802c0d5441d000b6007102450070340d82e00c0c0a2010b64400d22441c14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 868751285 1250 868750035 868750037
    0x22a0a03031407020d0e01091806090c050f1c0b10120b0a18020d06050603090d0e060a0f0c02191403010608030c150403121b2a0807081e030106020c01 66
    0x10b124244100029540c449600b50f00c1c0400542d540c00e0111a03104480031001800c03541c00082c05003180d0100c2c980103001500c03a10005a1030301d03007000e00b2903014a090321070803c0ba80c0441c904281220b040b40b991552040034040f20551744095900c0160340c0d8446020400005e1740d9141d0301c005c0012901307006c5603800c2800d280b0940b0304910402000004000c0b5a403103c1e200b541c0561138115108003080500440d0304404e40c0510301004001000300d0000e1400801ca0711561410300e541c0c030340c00522545100c1e552291001410400712081103d001d00720302030303240384090026280044801070b0b240c80c42c00b00e500403e40c568141d8003410030504d070902880015042c1140034603d8403800b801101e5440040001450240c01d15400090906010307001d4030010040815042c880c030f04810741c51800108e1145a00400701e50009101c2d140645c60650b41e100c0b804040c0c40b2001003003510348038461507800040d411101c858081111100e005c2c109040c51801d01d200b0301545407a94100600239080c00e00d84941a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 868752535 1250 868751285 868751321
    0xb090601050a030201120209030102071b0b030105010903020405060d1502091e300106090c120e03030118021309051009050f060607030509150306040b090415022a0a0303 74
    0x4801d594424256000300e07a82400d040c00aa141d01c10103030041d014004840d68554800b0568609001082a0042d60401c04403541c41c83d05842c0e4071442000c3c002800744900041c0360343c105100500706580540e80103e0020150a5241013960b114481c4107804043e8085203500451240701c542000640980039400105224016018000100e407294005943d6042c0d82c0745c22204016400584c0009640340314014070081c84540d8441000700c01800305030600da40016410f0352080c0020355244583e03103141c0140f1025529691900c405400b50790b1168418010b11030f405c100048100c40101c0d0100000c00300c00c0401724003490a01c0008990319810342c40720641508101c100040c0c0800d80c6040b90748000200c544940b40c0405d81400c9516004030311070030740c00c02841064003040c681924055446504115014800c41140c1c100f409003450055030010310194421402c06d414000726006000310121080c041101a046843e11740d4007113900d06040d018941051000c0014540c2c14010a0001d281e92160380c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 868753785 1250 868752535 868752539
    0x9030d052104020109080601090c090b03070207090b030312040c05240415110d12050601050f0403020d26040305190f0b1009020c01020c0c01030c0906050d1401120b090601 75
    0xe03110607540c40c007107900d265424074001401c580c01800e24001510994044401c031f982c55680002c010a9054641b001007108100300241c014541b804880c4500141d50241101d1841c1c001c0b070a000e05440321085525000c1882003621102e00000c0c500d101304d005101d5801c1181c903040500203003007039240c1c84071082d10801305e000c9900c40081003120220b80c9807500841611180b4401128207403c04080d541450054038140441c4952002e0890030b401407611080200b138a40740010b40e42c6104103030300d40812810500c81003000d80340141d08004003e004230b0f5040030707400340840816031000d61031a084100c100c0106090060010030042d40b001400c0e00d94006c103051001381c80d1280584a520350040100d100c0100190003e1074010b007150041041400a5485051514405020350040d40c48445036100700c4801407010362283c00307465410103941c0c9072807001358100542100d06600400e4200851038880446c071440d00c038000c3c40d5a000b420140382c41940d40d03009140c0711041200262806110f58854001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 868755035 1250 868753785 868753807
    0x22101080105040f080a0219050109060b0a1203030e010603020a0e1605040e1311090907061205100611120a09061d1003020c1606080610050c0a110d06090809030d05 72
    0x41100c80f540005d00c0b551607035400c0c1c008074507008040038251121910380000504000c01500b100707001921842c03042c440080b400c4107100e001115449816080c4003e01c0d50407012a0103580480c0c00c3c104c50400100748661244c020840c0394585902980705200400d0420524240350941524546034500c0c00514203890040d045040e500040d18100c3c1c42c0c500301320220304201c000d5112450440d006001c000980c98204501901d03068240301d2030021800201e0501c00b000d20b2803080e584111007018201070010700b009030880d01c1010703986696100d0f11549410000e0104031901034291542190340d4103080f10308003032004001f80130701811403000d090581e02001c1c460b915640c0c8802010940d1600603260000c0350040c92600754040011010201490408151300e40c1c0b04954503c101c0c0c094511031b40003444210704850318401c0a482c04159000075a041d000110700c0c00c03480b04c0c04032000303114820203241c40e00d900040b6a510703a0111004480051f51010f541400d0012002c666481e041c100d00f0a80a591 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 868756285 1250 868755035 868755053
    0xa0c05090604090b24031c0c02030316060b0f04020a0c060c03090b04060203071710060c0f2001030b03010c12150b0c0606030c0904230c0402210108010504 68
    0x14062003500320000180154403583c1c030580c0d41030341024a100d094140940c030744103007030302d6510410303c60314050800d6012418005440d900d0450341800c0c40404c3d00310020110b9418425102c1281d050100f0000e0442050010000100b1903000da000090a04910001c2049441208014a018030b0041c040042125000410b0b0080e160b0050000304621b40342c224100c1c010503070b0314402491440044280800c2c000350340d01462040c0c81680300e40c0d034001d00452041c107032550200c6015408201c59903060001620039001601c2162080203041c1c080340360303603803803090702d903d0001075200c081d204131100c082940c0c7c0f41c014411803034006d60080080c261043c01c01002c13502c1c035142401d0f10b2511081900e400c54001d0000e000149041c4c241141c42d40c0e0b500c20b580b915083e01303403a034070b10910404c1a03404040c5840c84449002c0e641c0205403451001100703164040c412003071600a0114000c008081c07a1702e46903400140428507418601d00351280071200481009003042c0c00c62909685407008010000340044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 868757535 1250 868756285 868756289
    0x6270915040807060c121e05010509010f03031103130914060603091203040f080703050406090803090f040e0c0a170f07060509010507052a03150415090203070b0403030503070206090a0c 81
    0x20001185032149401c007030b40c05600911b13803015514588052807503c4040c0c3c42c0810b010010701c220600483e60b0310b508001c01e240c400e0282d10690f1022040130400240521551411464080c0c140ca06000c4030f0000f481c80d040c02981305148803910b80040da0300b102c108900c01548a04102e403841d09608120040540d2000342e170504034401c4400101260a200d0003001a0442981c400b0040c2e0b620242440c000382650442d20514021400718000400c0481000c03007034408000024001142c50a1100c003000050440714a03e6092405444070601d80c0c0e07150440c1042c09800202500010340d000c008a071850b2994109003a01c0c03a4204c410180000c0e90b01c102205c005040034a022501d800c49424441d0420780d03c0d032045204440c030100c444800c0b610340d11107800140b404500b5103012039580c880d200d000f120100c0d002021116415400e40c1140003a50103035440c0e0340003400301c84245844038103020390b0340d2261b0002d40100d00702200300b249840c0e041000c00d5024100c0700c040c1005404030f9481d056001654 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 868758785 1250 868757535 868757543
    0x4080a03090c03020303190801060903110108060d0c0321091406090111062505070c0306050a060b03091b0a030b0f0414030a030e0d020304050a03080306270915040807 73
    0xa5041d0106004641808078080c40e0005e00b44da03580c0001c4281c0010b0f5020155881000c00c00982c0005981d602449408040b01c3d08246000d0400c0032180045611000040c403e690220403000180d0208404001ca00c0196201d815510f82507444030b0550303000040b201106004008a000c418455200c4041c10000c0c0910151012915400520016205000d440582d86107922030b076010082b1031200d4940c51102401819a00010001c814104403518410100c010f0100d040d11a02080080d907a0390005501506411001525603190220115640c4c4151012070003544010101d03001709180070011041e000003103030070440321860b695035903107070600c018040403082c00007600040c1072190200a060100c41f16805403950b5034a5950050010b0001e03084a250500ca100c01124810740000300f11410fa4100806540c83c9907e1943da10321140d000a02280d0454400075002c200403204202640c00008001228400e0386414801c07240740c0008103c040da5000c0c40581444007255904084034817160300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 868760035 1250 868758785 868758791
    0x17180109030e09130c36050105010f030c05091002070b400911090913050105221103010204052101150308090918430509150607240504080a03 62
    0x3584404a1900f106c0d07001031020021116041c580d42982c046030503180d00340c952511050003600c04504444400d02048081365080001c41428a410f2082d140c4502c10391040b45c904030f0300c034006805260845680407031041c902c0185182d1002081c01d0120303040041a0b000201500088200c400c8200b042c0301e0014071a079900164240d40402404440c40b0000c040c03d99009400e02a1070b85501c0b1449000076591946803901040480c1005101c0b60314403e2120446c04803030760146c445409401407030304240d80c50341d401c200010701c03600c810014031211001c070300c504820b0a20010350582512161341c0b004035400c0c290030303082c00000c0082c0103594484070151213540c515a01c214034528000c5d80c0c611a5401d91040d48160458807001080d002c0703481303c041e4180e110301c1d40420b80307468040c000c80c064045030a2401d20103001c541040c5850305c0c4e01c8000039910107a4600d0303100100c1c866502c20740c01510b0520341002003160321580c50360f08a81d4140160790070003151920781c450840c6c40c002c010a1608040c0c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 868761285 1250 868760035 868760069
    0x108071202160b04110f0102070513060807120218040c09091a0c0910170a0e100f0f0e0a03080c090d050f010213060203030717180109030e09130c 64
    0x100e190305892454600e50322426007610542000440500b00b140c044a10204500c8202041e0410700504203000e0b0040c6c005040b80340c00c010800007000400881c2d0800720382c0d01c402c0020916820069100204801203034013038002d529005008181e04241c00e402d54040a00c0180000942c8241a000c00c40b0380c981c00002d0400381d10b2030050070b0886d5120240c2c803510180ca051203424542c1d000180350000c400c036521034805c07130000d2040c1c030b214551614081034000d45000142811905330020011024040c05a4004910120401c0c00300c1d9a880c11074040d242d07842901c980408000d1091002d200e4503c002801d8480c00742d50003c250342c90007003056031850408604d807800354481c265038012140d40101601c10024000b18158000e4000c03800f0580d250804403c0021403d0004c0200c90040b101c0c1d6417404903032134102e0860b141020025010140c1000201ca03400b038034560a03c10001214071030790f40c032450064800e04000000030301911307200300c00385400e00c10300c0000c5d0318010034800c46540d5005050703044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 868762535 1250 868761285 868761317
    0x10b0414090f0d2c031005010501030f0b01051209150403260114040f2d05060a420f11010c0f181e030303060e1306050916080304050a080c010807 64
    0x11081d1340c0540d054800c000380044680683d0b00500d042e500d081e0b0b8100f140341a01c4a4020a681c41110303100d01194080140581441400841c00d50000b041411a01c1d0b01404441c1601c400300e007100e082d0000341c5c0305d104a82d08200241c0b0300c0084035801100724401c0c0e506001d040710042c40302c032144520840d51400060001c142940010143c02c009140900661394002101c03200d070b052200105082c03500d0070000a4691900b08400e030181c0f80340713490112403e0305148441ca20710880070031440b142d92080741c412940c016603120004d1340100665401c98401c4003210081c09036540c4482403480d0703904111a91000a60024502c9070503807161608280740749902c1c0103031404800e1a005400001400c2c0340001850b44584000400ca920030390307040112581e200c3c68004001020f59240341d0081e0001c042d9408034042c4e80140ba0808080e10550b0001403806050060080882d0b00042c401d4102007020896881e1501709440144100e4018001c000d24143c00241007040081c0290184102c43c1c030031007040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 868763785 1250 868762535 868762607
    0x30403020a050f0a110a0806010302060d020405130903020c100f0f030f050a09120c0b04080f0c06151c15020c163506010b030702010b0414090f0d 64
    0x9581c00c0b0041d40c450400507070b2103d403100c500b400292801261a040c1c2070b054100701d51410100d5080030054140c6034215820031501d0b5200e0310128003040d40074040855941ea45070b800318800070b41d001e00020301004074940603042c500034040070792040d00e19282d1340941c55003141f200000c0310b400b480c01c030a00d41d00254007a80202100c41580402e90b10384010050044910741c05184001e005005580c20000000c03022580c0c01c0382c0000081c07500344840003140c001040c000c0907204448218403102d00b4069080107062810f1720444143ca54021b541402c1c442074140351054100d0740106048442c0407a5640c2c44403500c050001307619482e50b541c00594180c0440062045024115041c680c0411550b51500d09224540300a0011341100c2001d101d5006081d9800c4031815030302c0c00da0406800b00703030b103414109400c5800c020209400d5540310034242407130381e80d14480c40d50301101010380003d0505180311454901810790620022540c054130300410040d40040e910609004140789000309401150f52200035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 868765035 1250 868763785 868763803
    0x14100515130308070203010e060106050a03020d060302131515050f030a0b0306040602190c1101030504060f092019090b1507081b010b01090905180a0c09051e0c03040302 74
    0x560280c401d804010090040f00a294060003200240070400315484e500d501c8140a1145002054041140100803406500035140e0707105031960004401c0d03926008901071101484d84039000c150746101c10101c4210851800000c2c2160881440d03010750700c1c00f00a002803003046c040e03113192035011000a261038400d030000d0308007603070240076a41c079410f20780b4000010750011807044520341030040e0007500d014403446030400c800e074014120145c488440c00040d070040101500581c0d00b0b50700c07180c4206800d492406660f000601c200e810140c001c8041d0b4441c1c04100411640d1407054111810500088211300888400d846c2d0403800040d0342808480007880045a216180211640c0811503205100e14000500180542240e03a0085540300c40d0080e800c803100c2c602804d0200c0c20000c3c060008500070750090340d2001c4900744004500d9910015a072800b10b400e101190007080010017803018001ca805102d4001240000b0008010200701e20288044801007032850307402c10200c0054107040c420042511 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 868766285 1250 868765035 868765057
    0x9040204060321080a051012060e07080a0201110102120f0a0b041416020a2001180e060a06080606040603090f02100f0207051503011e0e130614100515 66
    0x403420f60f240c031107038403003000c64595034022903204800a05488418003c080c82070b1040c14861600506101c001c040d400d03484801503a141d965020002c00c40740c0200304540142c02600002d01c12102d0380c1c400141021002010b48500f640144040c07880300a10f03d4141d03400c000d070303048804c0720382d952442400002c016040c0599405818801a0f10622030b0f4410300342d00440e507620341070f112041d402501f83e941d22074000004101401c941103064461602a414015038141454026900039446c1c8802c00b8410a607000511140000414031159140185d040c1004254906007807201d440d2480010705c00303010754070070302c0c052540f681440c1c0d041180003255041440d5009181e000c012001e114010002c8060305111001b5201d080000b092524003080246001410a40c41514581c00e01d2415810f03240d0700040302c079004c0c00c2480007080041b040034002c0c0c89881841c40000c0601c81a05251094405540008a0140070541481102100312014200380c4406076290884528442c42d000c80c18462021101e03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 868767535 1250 868766285 868766303
    0x1a091507170a0e0a08060910021809040b01080f16060c0f02060c010605040b010302340b04210c0201020c0f15040303020708060c0c150a020d0204060509010f031a090402040603 77
    0x29081e40c10541920303010b0015108040700580702c811640d641c06c001e541002040d800392003000031203070180e00100a104444030303800fa8058146004120500d400b078904483c905500300062000c0341d0300708825a030101d2404000e101c5103070b2890150008601d00e000306420066042500303424010750500303030719181e94042e0040f60344890802c0001c1c000d1040d8041d203803080f4101450303e41690710034003d03100b007203007062130310b1203660181d0841a4109030800030800180e0841581070022032031300d01c13086120300e000b554412a1106640e13603444000c030821400c41e00f0320070b0f50302000d800741c4d0380062441c4084000340c0b2103101c0480c90070002011180e515486130417075800010040205513001c1559001c4a015400b222032a458420741c60001d400381801020141c2e0142c001d555800d180b0903c0740f17400516110006180001c84842d5406903031164200b0008a0400200d505142d6071160b0441c148040c0c51404001c0300e000c0c2602400c2000d40c200750301d032140003620007090541d5255884440210341c011001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 868768785 1250 868767535 868767547
    0xf0c0b0304120809160509040c030b0712050c03010f0b0903070314010603020109051c030c11030d03090203160303050a0e130203040f021c0209130303090506010b041a09150717 77
    0x40000321039142c2844000541010205000c3d010004180306032118030442003042da41024103202600340d00030401d40d1780840310748000000c6008981c19502a02190381d60301d40101d104e009510a50303c014180381c80c013034010001000b01843c00c1c1c0d02039096035074490100d0380c0c0c0c201090002e45400c60580004e014401c00d01a204d40003001540540201c910030388400d0707107031680d80d000c201c0100c00940e840d41d00154211050342c0043d118944102131907100310b9900c100b807441ba5000c6403030052940a01030100380d0320740c200c1e41545000c0051168511070901400006421643c0040c828054a000740b01845501c04c4034448070340d5401107050504054603000c40d2289440c0c20103092001900d2010b0b40078400303482e01350001c0400c15150300b80442d00a0303c4107041740c4412404801464000070103901705652603e03650300150081c03203254000d090003400261568140342303945407403108443d40a00190001c10685442d5113401600c0c0120150481c0d1203500c400d028140210811070514051514207400520 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 868770035 1250 868768785 868768793
    0x100b0d23011502101505102303061507051c09050315220506070807050904050708040308090307050604120201020c150103060b0d0503091e032b0207060c0f0c0b0304 72
    0x40c4600398280d801c031130030b00e00d00c1803c540450701d000b515603842d601111424481800d0400351040c510065113040c03400d000b121010b04071410310784807500c02000c0303000041c0001481c0400d203640308103c404048514041856941643d9034030022040e10a08040c00102c0c28414058245080244070107000d4401c91005803c2d00c0c02c1021003100c040903040f8500444412075116581c03030544190348000203001c10f0321030322070948181200500d407104010040110300910346482c004d50f8026041034403a00c01c03d090601e400b070315070f1074000d05402403540f00f440100082440050301c0d603013058010300340204414101070124007903ca0019480c505210b000c002c080d285031030030020703412280610402c210955802c000c01001c1401c0c07900180040d441800032070030a241103c1c80c0e04001035401e20700d0350486c85070800302c0d0500c580071711040d5603200c01e01030b1420707480350f0401e080003415030502c050071a8500702000907000c03080600026200c10710f04200002008a040d8120022b0401e07213090319202c0c0f50510b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 868771285 1250 868770035 868770059
    0x302030108070b0a0804110a12081e030c0d1d070f0314120d02030a091401060306051b0f0d0e0a0c15020706090504020d0f0f05040b100b0d2301 63
    0x20640a40b84100d0b600003030b5092250044c0d601c1c01000d940e54540d2620750303407120211954442c0e0f0843e80840411000514013406900501d03900e48100c54180c1c40307220020101907a856a6004900c1400c02007003000360740040c1904550290740d085c54000342ca884891f40b0001100403000d00d400042c440c00001040200d4407801718170440c0d05c2001e00c1e03850601a040c880383c07268111261144082424030042180c1c20454001e1a0301408041000410600740d8451403452a5204641c6c1c42c5a5940e8500340284820307800340c40d030301c078030729545010507040048030068140c811801c0c0030701802804155943d00c001140c204c10103080c01001140e072001030031305002b0b56800e84c03445075011189070102c190384180c0c008078a4100b200d60a07210748400c1440e040a02020394050710052401680d1048ed0807210b44c010710624079282c00000c800502403a291a00d4200c000024001d062507039040f600412001040500321806681200008110300f2011602e0058004500052400c620310390ba00100d210a5046 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 868772535 1250 868771285 868771289
    0xf0b0a080f0709020f0a1d1504150504030b0a0b19060e1f17060d0c08060a140411010c080c06160206010f030c0b1e0a0306090c0e09060906031c03020301 67
    0xc2550b24090355038050707100324881c806030109510000d220100019015140d0001e078503220340306e40a080c03445200045d1700307903040d080303e6100303604046410702001858080d402044903003401c146290906548910640300b01c020720b461032050f12403008a45546690300710480b08e02c1c0d1a009030140340e40b2110003401c58000d40103294014a400f488590301c04102107508070504900d078603030824809282200300c0e10408002c2c40a0b42046896290380c0000303401012060080809002034035480c00c00707080c2201a00c10681c1c0c2c40d014002140240700c0070904600d40d10b4880740007420804c910603200e00d04801203000764030b40c00e40d80d130150b4400c020140b0400009240c8140c41c83d42960b100d60f0300c805084005040c0b9010107070041010003030500040340c1500080520b01d40b000001140c41d0000c1d072a0380f00707660000401c0800261126002c1050160a018000204203075080820800884201048050400400d03a5204600c0d02c2e01050454505000400000760144040e003c0048441000b5011b94002c2c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 868773785 1250 868772535 868772563
    0x15040b040e0c04050d03080405011506110706050a140c07050d080a080121080702040f090302030a0f020102192303130b0c04080607120b031009150b03100f0b0a08 71
    0x4100001c18510302e1104840540300018059075418042d5102220030600051088800d5980c0c0c8005001b40c1c00c8035400c403c000e00701550740b201d016000241150804c03070315a100805021040c045030000708d820003003080508403540b07895600c0d04210004c9600d00015980010741200041c050141441000d200805094002d40c42c2d00806903640e591a4a1003c40300500940d581c00b800d1400340001d030010b00504015000800106500301046106002c44d0b03090081100568030001e591404a030b003040091070100f0a6000844c2040351210340944c40c1a881041501041042c3c00600c0c08a000c1891941d41881d409510300e4a074174001000401e802d410000585170402c085001505844c0f03060102e4007600d5030003001d042076854020042e00d400070318001d11034010340c0720700c0c0511080d00c0400c104000c0b80b00280c0e000c5190011402c2201e1800c04400220900c5400c10219241c9502e0004031302e201ca510111000941240e5103508000400f0302030b0000794001a1a01e0009020a0001c0c2c524249100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 868775035 1250 868773785 868773809
    0x70f05120f03150a030c090c1707020703031b11100c21020120041403150f04202110020f070303110a170606040909030c050c0d0503071115040b04 64
    0x2c03c0d820000080403600c0000c4c0641e8003014284003400b103a80016050038660b05080003242c665444006040c01d04441120041e0f0100d0340820038580d104040b08219034400003459541c150a445510321030302e100714050b00920723500990354442c0344140340e0b1950707003a005020002160340e606000e0412104449840c4019070034072035034856600c82c0329948480110440300c0c5901e0545841011051180c4010010368140600e5110a442d0020940a0380c41203003010708032800751600380344c0b8003140461110701070040582e601c2c3c0900b85486514480c062004044050307092a4800f0060781d140405504030440c0c800c0c004540055200c2511025000140c444c0e141800606209043e42c4024012044a40300182a50500038054041c05601503003000001e880d0720f2405403118003000555441c0c0300c00700c0000b4015444d0400b4008180007401000340c04650355031036000781c1d845050380d07800754090107004003246414544690703a48042a080403140a461a03440311b5990600064941040c4140c03090214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 868776285 1250 868775035 868775071
    0x90603040b2d0a110403050d0201024902091917010e0d1215180b03030c1e15010f060905040504080d0e011e0b01030b06030c070f05120f03 61
    0x2d5005000c4880081c28000002c15500c1c05000c10107003003109040700c40b1007002c12021021840610040382020f078160009650b440040307241800c0803d140b00d8050020002864107541d189604141c5070055210f08007843c0c0c40852046120000c3c4910400503070b0140710860300003070324128400d916003181e03100e0543c3c2104042c11300d4810b09940c0c04003503079800e5170002c01509400c1d034001c0440d46c8080c0586a00001d03400c85600c408142e60000390401c500003408000c1020401c00a4007524201e0203040d00552304090110414a960ba2414240390715482c404411100e40e48070b0420401e180b01400c00010403827941e50b0465031405054600450307000407a00b20001c6400e04180c0107103401554010320f4039283c400301c001040028101003034169025501c49000d504102c8084400d01003003c400752000a000c1c04000c0090704071580031000d60702400302802048131528051003a9000d054100d00c84140f021010328055051041a90f000380340e400f00461000c415019440c06144280d10304d492031100c00e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 868777535 1250 868776285 868776331
    0x3022413031b1a031008010f0504051e03030c0c030d06030803090d0c0c050d150501170d020a1a0c360102160b0a030204050d08071106030114060906090603040b 70
    0x18806003e0503020401c15401c0c5840400c09000655210b810442260740290301c800015095558510440e4219074a450602c01400414000e008804070380000501002d600032403040d13241e00008101c02d01c640c0000c01c07010f054a406200b16400308614600802c811740e2649404c4080e40c0090b2158550340c4a56035204250f1400340c1d00d04914290400c11203c07a0500d01010003002d40210b0ba0200c690b1070440711030306580a66800358502030000c011004407480d140c00c00107450808820300d55400c6500244060380414010004000c996020083e00c80b91942c51a080d11828030425258211100d4180040d0b1a0080d603106031201c2424001c0d0218014030200004a95030310000000784001103500500300200c8040c14000c0030082c0c1141009400d142d40c1c0d100140d07110401d00c03402e481281d800101c103804c21140700400b0001d078000310b500a0441d4100401c41d500000c2081c101070003242e0004092417240da404041e03546c0d002d0f0081c42c0c01c2d49c1e0310b007a01d08540c00c08420744144c0c1481001c0c0045520350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 868778785 1250 868777535 868777583
    0x60e0304180f0f140123010e061b070308090a0b03011d06011b03050c06132102100e0c03060f1302040b130c02150705040f0302241303 59
    0x100c2030650000c60481e034141c400310041ca842651600030703d580341c5001d002891640a503074841a6403420001c815894802c1040486080d40c01010300c5001100c43c216907680c00101b2058050019144283c5a00e000002c445501d540e10303080c100144035016001082095240c001d040f109020f44800b4650f0782d8a80c00018a80400c2c0201104118907581c996043e9041401c3e40f903101505240006119580324003c0100b0000b00d00305400140c2d001a0041d4060410441c50790440035049510141c180c040d203406641c5071004902c4a0b0100100700055203842c800c00c1070704c0200080540400c4000c192407066075640300041c1c400c81c041c0c0103003000101d070b001c109820244107480d00b90f24250250034690800006101d188411035004010101003481209544581104404650020300306241010000c4000d01401020001049810030080c4903a1410030b03000c81c210b9605454440d0608105007180071004040702031111070000200d10b2a4024940c0c0c00b401d07003224001d40f100c644240c2000c200c1905 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 868780035 1250 868778785 868778789
    0x50c0708061003032613020d08030a020a08090f070501050706060510030c03180c0504150306020d02070201081b071e021002100b0108090a08090d0807030e18091c030b0301090f060e0304 81
    0x1c42010f417001990006032000754601540c03000b018034a04020b02e44d01d051603500180c43c02c183d2151702080c1021a03a40102c4840e420080c110001d2008200e40d1a5081d511007a07401744a0402c0030128201307041188a400120140038020200b010960200700000c004080003803190700000d06041c0c0314000760f11500c4451142d6070300013410f4050307241820240000f078103035440881c3c2a461311207030020100c2da403440a803002448084000da0390700c0c9640001842004043d00361241001074011041103081100200e901c11a4050101c00d460a0154500b0461080701d58000c0d402c01219032400340c05a5020a00303280210303054004205d0340544000448110b40200c60000f0341c0c0c0e00010740000840c1c01c1c82d0203000c1d021001481e206240c00c8682c0d400009030801c00c1c00b20041840c0c03072203850f07042c90029406460440306400c00c8a0b149002003489690b0307269203110424044900350100c0130355200f42c0020980c202d01034002c2c02014094541002d072907110b0348007916070f64a401f010000d01c003030100803142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 868781285 1250 868780035 868780097
    0x40209160e0f03030c03040b07020307170c1e1012060b040501021b060405150d0c030c020309090403180303050c010b0415150315060302030610110d050c070806100303 73
    0x14000d0841c1e0a00c01d640348800c0d52503515110901c084180640100300400261460103051380d1030382d5003407051515109050b0000341d40c8403000107a14903455000600740314001002c640005140514002650a405d41d180078180c2204800c0d00d020071342078101f8000541101074000c00c00000340c1e1003880d07a006014500801c1d006820a1603000c040018418019040300f0004003601d207015580c00000c4c030207028440600d007003d81e0101d07401040103918828480c000d02c480c1030600107942540c0d4020b40380e02c102c05041d44509102c80109003458410702c00c000141202520656200c0d46904000d841600b040d800e00281f50302302110341c44581405c2c080c0b00540b0700140740f5a402c0a0910400d2241080c1c08c485120400d0f0791106944180414000e40c980100119180181c2d06d007009800c1c00b130b02400c1b2092010074004500c083d941480790000c1c030088019850f2070101c0d02c0700512034451381070005a80c02a521031140100740903082c40b1038062403045030b2280d02c510143c4001c004c40429000ca80c090881 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 868782535 1250 868781285 868781297
    0x604050105030406060503031308071a040e070e0306070302040806010b0703080708090120030726180102071208061008070815180a0b0f0307050d082104050604020916 73
    0x49154050806160401c1c070500001c140b054036200842e1440e0001301d040c1d080c0f150442010051004144649800780c480c5002028248104424601182c4194440d03041101030440c00107402c02d02c14042036503119001403d036103032030401541c018083d4015004003c51402544000514030700751108664a1640c5501d50100d5503440490681d04601e0040c0025065502c0e9600801c1807604040199070703010f030003010142c0341d00303100200406040f0580c000d0080c14261003810038140c030485220321341c48201c0b0304552290f90b502c0b0862a01a0060850050040c41c0039084100e220f900000824441c0c87c085e141c41002c0907003501e00b101c460500317450000114030700c070f0003080201952800c5003075010030140170b00c09072030070400800e8440c150031144d1f0203100d41e40c0d00c80d00c1803c3c40e24030610004040c0440c024464503017450000340316580505030003403005c4400100d44c10141c00e1028000c2d510b520b0328603035038880d25003820815211281220201e00c610488030008800420400e007a241225840d580c90f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 868783785 1250 868782535 868782539
    0x19180609050f2107061d010804020d0605060103091b05010e1804063b0705010f2f0d02030702030d1b0201110f0708010906110c0607080a02040f03050105070206010e060604 75
    0x400314441e00314500d07000c0c40350800f18034640028200407640003807610340e0742c00d54800c082030340c100c900045c03ca00950411900c81c1c00d06c00581d0f81e01701e03850511500300c3c00024160b01c42d400180e00418511000500300044c1c1000400f5440030501c02c1d400301c420a80303400f10178400700001c10a441021100c44924018803102060102d80e1603032041c4004103200e2084504040450f02034006d004800648500d1200a0b400701d014003041072100400406080c20650b0044150f014003030125070140302c180d1010740d81d4002106482c0300802080300e8100c0f140b0300307071006440b00c00c200075101d6100c090f0507170091090380a445502e03440b8403c000e0054427883d01001400d00b5a83c01103900c1c45800440703481504c60002414400c0805221450060945600008294440c2d280c034105440c0c0d000401d10040400b4003807007a0020303000c140d29520008500c0d1104032543c60180c1c0e031009004070b812028410149a401204003d0705500c55405005550201c0d466a0b03039074041594240d0b011222160480414082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 868785035 1250 868783785 868783789
    0x7060c03020a140d180f0311030c100b060403080f07030f0e100c03020a052a0a0b091903060c050306130b1c0f14031306050f0306100519180609050f 65
    0xc3c2140401c141004950816170200303e0200c42000c070400c4c2d03003205581030b5000030160011460f00310070520001560511000c03141c4c41e602c806001781c0c00d5001546481481c40705903201022280034551040c0404e840380580ea0404140390041041240410f03440303020100c500f070140c0703d40710b200c1d48002c2480340284603102c0203c1d010281c07268100d007548074488114000031024449141c0b00042c2c50100740402d041c030f40c1030350207850030110740ca030054030104010b00290b4403407002c440c0c1c031440030385100c500c1d20710940444040c50034640c0080c1c00030f0711381500801341a074072800850045001700c9442119051950740743c4210341414480e5a030100801350074144ca44022000070159500404840040004580340e002c1100021910020039801c001001c030350a42003652080090101442d000f03051414401e081032440c4000352000348281b402076034201c1210b20420032070f41c81c0c05a0580400f98416071510151100101070790740011034201040c04035207141b040c506101251401881c0b200d081c403811007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 868786285 1250 868785035 868785037
    0x3060105090307183c0e151906120c0603090f0b010303050306100e030a24110405100807020d0813061505010306050f011d1c030804050709051603110c07080307060c03020a14 76
    0x80c6401c0364081c0c00341c0618125a003d25092141c0f90b048c5d1544004410300f03651004545058000312025003802001c08045948407464400b95902130400003040c040f10b0030300303580034001f41100403c5034400c8c0001200b015032102c083e5028800c150740d8007403131030140e04060724101c07261042a03405900c841c1e1000080b45a9910151101e100c0f207070620000070480c06541d0580b801e1030644034603010f0001c1c0c10096030419070154065441180b410001c181001c8e14020f45651483e0f680c0810015a000411020300300380030440d55060b4001c00411100402142945965845201d110b0210789443c40008840c1803d851a49a84a05035211203008550800c07103000a4400340b10b49820150030803208550b40030748800000d450340030380c0340c440c82460701d85040c40c60000e8641003041000d00b40f80a000c820402c803140c5210805541c00d0200740080045c507041c0350360094041000183c07150003c0051003200100003810700c0741c0601c1c024040c2e01d001100039070036845034070071442c0000c1844a40380d90b100c007050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 868787535 1250 868786285 868786301
    0x6010e0607150e12130f03050607050307030f0c0809070b0c0d05030a0e0a0b0a111c0b0d060c090303080901050903043303060e0f0105030303060105090307183c 70
    0x750005400110003a2140b42c20281680c681280e0b50011700e540100004c0780d40c0000801c0940c800c02e03a19420740d524030b40c1750b180203820134090190101c0400c0c142406a0440040039064460801c410380c09188010485030050b5049401c0d8018500c001c600601044212441d084810307008101c0003003c042d003228664002060881003950b41c600c061312000e814010120001c0c0145400445030408001075011500358241144440008000700c4650030030b042c012080500d01c030b040000e44100100080b41e180014141c0040c80d09190140b8448020b4116540314181d0340281d50f000c0c51030b6240b14503a8221901511040d40c02c0e84117003c2040384400003001031803582080e41901c1412560303003142d00f80c0750480c00542d80100381c50300000c2c007241c41c000f04020340c44842001600e50b15498440465213a101c050103803410448000b4524043c1e8404008440051500c20103e03400c101d050b100b900001d00d0404a03000700000d00351150310202c2c10700510102099103045003100814121040800200580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 868788785 1250 868787535 868787573
    0x105041e08161101081003050606040f0207211b260c03040801051503060610120e030d1a0d03080a09060b03061e01060201090308060603090c1f0806010e0607 69
    0xc202d560111100100d407400c46501c0b400ca20442441d482c80054900c590041840d54000c04508040001c5100010090b8010406039000225064002e441602a109200303015241004180d10301424103220030a002000c8031940c0d0340c1d2001d8402d06041c0035800c420f000050400790b2140d50300c0150707070311079012004207141d141c1c0114a0f000c11000381c00c1c21504035034000e02e2036955076401c00440d0400c0a0701007880140403000790480c0e1400c2000a2042d0340032202075000c01c681821610b40180e100d42c0512421402030017140d407607060f4a4401c8018049101c42d680141c1c01c0c10700030745210b09052820b030091070b91644480002c0c0c0d41e154500c100519a880c019180309494003040d10464405200c42d0307020344120800710400030101d40904114440c10382c00b06045a140c0005000030950040409030042002c4480581caca490303c440b520326060011844d95881014021289001550800948541d101c1ca0316005c859540344001540e8100072000750603001107040001e00005010240020000002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 868790035 1250 868788785 868788787
    0x705060c012909010e0f161103120109060909020108130c210308010609081b12060106080406060b04030b0705070311070b0c01180c06050315060d0903030c020105041e08 74
    0x4074881d001c041e2005140d07202c0b00da000344101c0d10b07402c06904072405004490f060490b00d051502d00700e002814018410480555030f10450304d45d03d445545d00c5410015080c040702d4841c0d202c4c0e10fa040641c0e40a12450702c0f92490107400250032901809502c8003580c050712103260795956001c41031400400302500306d904034400c5030086040c8180380080582c600e00d00164a90340601813402911800041e041078051042e800c10030404450b00003400300041c964a805c039220604103c02041c0d61810001d944000d0740a2000007164803a40030081e00d02c10b6004103424041a0f6480703401c10f50038401c034000503100514040009000a0280d40100703c40c6120b8030300ba0105500114000341010095040ba1605440002c0d103100340e04401d000b543c456120313140c8400d969003216522441c1400305845030005000e0017000041c80b00b208908505011400600741c20b6990789800700701d2000340310400c012130100346011007907034075513105208442c0700320361040b07041c20300000103500c1080b5081c0c40002254a000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 868791285 1250 868790035 868790051
    0xd0e090a0b060f09030c01110c24040b190302091302480601051305071206080d09080604030801051302071e030e01020d0815040605031c08180705060c01 67
    0x82d081d00900110505240c40e030b48491a19041505000c282d0303000034100040984040041c4c9401316075074042030006c680c03000c5402407404c801c481c1c451455007500c2c0a10340c0402d000038030316a18002400c0c80025054040d12594140b80d00b54120301800955a41091030100d05103500c41c0554010002080313131810b00081d400c6007010b640018500f810050a0706a400b0903030100486040d100d03400c008200134050103041d0b041c000030031341c1e645507140314803549611400400d420f58010b100c00814403261140500200780c4503001e0940c2d445010259100140b4140c100045601b0301042080c0115031681d1400e41503445d0000708214001184d01d400c03c090350030004030380000d801e2002141c50f003c6003820903415005c00d007400f80107458685141c0e030543d0040000f6031040e6601c40300c030b5543301840d880340c50003100841003c60000c1161717810098042c415503076503585250b5410020101045542c0ea13549090342c070a408402d1040b000c5008a003264000b60303041c8981d103030110181c81c0c00074440000089c821 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 868792535 1250 868791285 868791289
    0xe06061e13020d0c020c09240d020a030c0602240105060d2424020f15091509030712030c05040501082a04030b0105010305160c0c0504050c0406110d0e090a0b 69
    0x84000c02444c01603804160548454188003070210b601552081381500c0010f00f240c0700d501c090400c904c03a03905c01d140302c8075070004568902c81ca0720701554011040e50f03101520303100d000e580c0701c07024100301042c4032107001c0a40102036503103601410381c2e42c09030105052103100400383c0040c0c8404004c0007407194403180e0344c842560f03040344a0b000070048640c050481510303290400310b0404200c4005400c541000021400a0800141000b800203e42c5541c02c0d29070345114483c2d00b000840c4102540d040c0c40d2005010700d6038400009010000d0042810569a00c5005001d41c100c0b0100b14000c800300703105210400c925801004a903600524540c185449180e0001844d000b041c5d00074001c0d1000ba2002c078050080c02100207034240034140030700381040142400c0c140b8840c0d440303400e40039404000c000a1710808201d07024604000401b40508180014141354600d01c2c402c0d005402144002000c0414901100e10001444081c00006407510440131417560240801800e000341034140e442d85401d004c010315 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 868793785 1250 868792535 868792541
    0xc21020442030606030b0315040b0a0e03030c0c010b040e21090a0603090302060a090b010b0c0f1203011712040b0a26010905010b0c06280603060e06061e13020d 70
    0xc1c0142da0000701c070f600306034001d400c441d4a04440c41c026071040202078000400700b80c1c0d181d0019000300d078407222a42ca40b44040041d25141203031074030b580004410b000e084183c0c0e901510b28068100000d02590300740340140011104541420f58070b0341e21915902a800032034003e0305003d016000703401403400b407819000c2815480c1a500c8040040da45524480605505001041e04a2801e410502c815882d6450b50150181d06000d400c0d24010f0029108400e117000700f203010300141d104802d0356000340c41700078403001c01e0b0400d2003404401c51182d180030301864000b040740c500501f92422220b061608001c855680d0750401c004000521240c40301a1204c403c0e260b81c0741d01c04c11007840c112800c6604180d000e105581d41030b4400e00300482c0030311907000c00503008502c0c0e0b907018415100f0644154681050348121500401c00d24201d02c0c5000004400d00115801588250320307202c084440b240c580c0400e022181c210142128941c1422100d401454900100d0303a040c00710300600050700306281c5110321000c0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 868795035 1250 868793785 868793909
    0x9040501170d050c0a120c0b1503010b12060a05070908100f06051002100f020d240501050f030f040c0302060f0a030b0f03070b0904020403060c210204 66
    0x200c0806040c0702000c500100302c02041c102c118645a424091103130003981d55a038000c440144908881e80305104403601c20051125000c1d0802c403c41c0060030100140d80901c80c100c444d60b4025420000c080030f01c4d0800c880140040864480141801c1d6a600b140d54000c050141c01002004403001c400a404003040046041c18244550009080050001d900e0111905940070900518016020b80d00d81074000c10f036901e0701460f201e008646003000c0c01440000340710f5a90348840542c40c289401182e0031900155140c2c2d14078210703412020750703101e07001502c590141c094504a06c01c400c100050b41c4403401c20310950401e2040c03513401599074582d0b0006444d9000074055035402070000c00d20760b40031949800b4849440c0400c0d04c42c41c180301403c0c004030b80c4400150066074402000000c031044551541d0b412100115008441001318146030722009000b03229002c4c060600da10002c0701c80c80c03501c40b240308031012a06c182c00042075680300781d8031001ca42240701d5020002184482c141c90410042c924070040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 868796285 1250 868795035 868795049
    0x23d020702060c0f100603080702120c032a04090c05100e03150a1b0f030230040209010b0405030c040e0a1a180f0d050304170414090f04032309040501 66
    0x1451402003440c41d000e07044000301c0780c60b41004407c1000c1000942154007290301036a419405140c0e170704101d4904131543c044c141d014401e400b80d00019500801000f0b1840310802010041e225010081200fa40c2075414040c06400e0590003c106610300651020140c040504140e421004054000fa00b40000346000041c0c410030304041005192841c0700e80b00c501e410400415148400700680200540100210481810342c00507501c013454038400300c0e8140d655850900c1c4616030080720f08045a08034207640c102d004111000c00440e80c141150281c3d400e54401500511808400d8808c01000d00b070846032204150041d00c000e240880c40d003068448074601014400e41d15810213100704464003140307601e045100d070030015024004007070104140780035400514100780c40c1d44460a10074103074403021581e0074200e0000a4005140303a481d800b804640003045641d02c0080e91443e89401c030350001200c000f0001480003045020101100c43d01c1941303003141e02c2d401030500512801003002c0303800a8120703907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 868797535 1250 868796285 868796293
    0x30c0c0603021207050c100b03070b0c0a030201270206071104020304050a0b010b0c060f0c0f070c051f080a05070e031009020405060409023d080601023d020702060c 72
    0x40034000f0303910602e800032007900e482e51030824025121901c810170503081c0360b0610384680190301559020850000079207014a00d05544101024025544005c4083e00706e0165003800c4c0092405000c0c2500e031104408a80d4420411056940c01c108542e841000b04540020700820b01c103480b51200d01c003851251748100f004109080307490414a07220101640092692070b01008192007034a800300c0c80641140071101c04e00280d40351040b80010718000e03002c105400100205180c0d00b400704051030074044450941d40003811108140680f244544900c1075000420503210201d28001b4455000d15400501c0f031410601c0080e0100020f801d101c1c91790001840307191920100020762070030b80f040d140c000400729000c0001405a6000c07803020015400d08820402e800288a610319200c140a40690a88500320b01100c4260400181045005886190041c0700310240f40301d0900704214242c03200084020182c1410014207500f16240c1340790100142c1e129001e0000c58016150100900103071400f040140c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 868798785 1250 868797535 868797547
    0x31218060c060b04050601120b060708030702030a0f1815090512011a09091c0c050a061a09010f12060f0c090303261501020f15100603020310050d030c0c060302 70
    0x2d003041c1c90a50b0380c0b0b035102c1c1d0f00e4403051103c1603070000d08890b50607000c17903000300b020030450001540500a220300603018510001c100b154095010005058400986c0c54540340c05269140c00c4540080115800c0c441e0042c3d40703c2031154041c0c0444000840020f468120512038403400071a43c070f0300d402d14605440e0380d1940b50040403002408045c0121020584010106282841d48161b54610300c0b01c502c032900141c603025105052050040804043d0841c08440c194801c0f480c02c0c50060000765903d00c2101b022500100291403c8003a9034101d940d21108046500d0400700c0002641d4000001162059036074100c1400d41740c914051103040c2c01071602c0d026441851803e0141c40d40c1440e4410304060b10b505800e0103c0848281c400b00e802c002114007014155803d040182e10f014a065418030030f1b8031604400c0349001c00000030303040c490390000b10f00710100b541d142c00c280c0680c00241c032208101c104010003404941010400000c20314080c0c5072006030103120307482e9564040599045840001e4000843d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 868800035 1250 868798785 868798793
    0x41112100b03060603070e0c0d290418060510030507030b0604150b07030302090628021902010c0b092a2d120304080106090207050c09060604031218060c 67
    0x402404a000368041d1500d8500000040d0b00c46e0203601466524021201c003203040000c1c51015240700e03082d0707840e007000417405082c1c0d505003088101602c1001c0c05480c0034030f2007890903d0701850032591101e00300c400f81c21201e82c0e036171805441d0052161100450160000001c0b5070300b00181c00c021350081e903034040c241c14198284415201503419802c82c400c0c01410030001e60090004a03040306805280c0140c0f542c07100c80c00100d0318850f90040b14180300001d500c3d03480c40042110f2001005ca013030340843d00c00840086d01c0000c81d441c080030281c0802d503802e20313010200d8068030000340d10850380300984912080f112a103c01c41082031040002000d00d0034100166814001d0190300300003136480c10055030050040400ca2045000700d005405402c000b9101c030310011301001a54060318000c4003e015040e11085507030025000300031306860b0362240218510342410540f0310517000316409480c2501d03150460311046010b050688a4500f0040c00c07070300c0211140800c10ba5600078183c1a52030341d070115540d0034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 868801285 1250 868800035 868800041
    0x330506190302060301171f2f0a08190518061311061602030304231f1b201e0108060d0203011407031b0f0c0201050304111210 55
    0x10500500c4214020074030160b0746003030690f030450700340c04100ca45032844890802d08000041580200f0315903481e85440d0260169000207940c00c1d20307403550100e400244809001401c8003c2c580a20000041251482c0c151050302c1e496800003421601a0411800507920000c80c1c00c02c9178005a51b13a000c00c02100f901c031090000f2a04020301c940306140b9091280c4914100488a07281c50703100310b60018002c2134403241c2d684510341303c035001420307282c64076501d00c40c003080c0c403503841003407650b0130b017100c410700e0346440c110130649441140011184e0741821880c100340c03000e517001c4004039958000089103100240a0062041c580784084a034401d01e14081c00902504220264000400e64840303044801e050f6808003400390b002404850140c1c21341128000b10b80102048000700b851300e8051010004126090b030403032110014290729655100031125412101e544a682c42d9100242d003841640c8055846400603640241c015084068030000c10800605c5107080030f9145510790300010005150900385d0303c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 868802535 1250 868801285 868801309
    0x15090e0d0215060d150906020327030301090b282105060f100803120912070c1202130906151d2e1202090105010f0507330506 55
    0x800105450b40020302c8070948a60002c108501610071000d900d4140003031203513518451100341c00200310100c040d0402c500030f988103e41d004699102c244030480209c8000d40390144964681001e1400d42c1d0a02d02584c0c0680201c4802c90f40c007100403c80e0031114412130302c41d010b08000688422000901e01003403000701510590401c1003540d100c000b8000400c001103851540111115030280b41e582d5142d050f00100c4900b5001220288000b00300b07180041058440280074030504422501d00c0241e101d42d40045110309540181040d030640020082103038040b40f9148030505c001c10740041021107000900c110780c030450382585c4864a880528581080c0a080c0201a105040480300b001120607808203d8071000b5207800e094880640703d4102603048600260001c1203040c0300380c0d84050b41d45040c541c98801c22001a84202c0003100001150b600940110081c0c8506841e8141428010740b500351003034844501c201c00d2040501325440400c11200419294904d0711b03080050241820303070074400c0b08103540d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 868803785 1250 868802535 868802537
    0x6080a05011202060702040921080117030421080f121e0112150603020d05030c010c1e1d1005041802090114030901090c170105090106030201091815090e0d 68
    0x810010b01688410080b2081540c040e85c0c007050441440ca0500004142c0000f02c401c044040c1070318000d015804413060381200c0f2250040d600402e000c0181c16147e104500c01e100224080d80d0044101a95188100401d6402004010308154096001da130050303001c3c034540e0144c1490307441040340041701d00d205412605950b6040118543c101040030001c6a21103001030b0604446285070b0321070110f141c202201541d030290500b071500465282842e525007015261103119400c0116115401d880b0b031495a5011040d4070036103400140340c003020740300010440d10110720598840042c070902d45034504414041000e9541d400d50311032500030b980b0501c111810a0194036401040101030b181c0c0d0249401d40d80c80c94440301c03541e60361200e550140c01000200801800300c071071030704000b0309480d211a5542208044400903c41ca940d003000c40340c01ca07a168007009012031982c1200b480030f2154484625114540000009459001d070441d084151201d980314254054440d0400210903d061040101100803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 868805035 1250 868803785 868803809
    0x5010305070f141608120106080916060c03030f05010810180c05040b060c0609100e0604021f030e060406091202070609120f022119020604171606080a0501 68
    0x261a001050705507070528258503400045013100414211540d810700941c4d0142c0f4a5a603003040303008020b041002449154045412040002c0c400b220100301c0494825101d00c08095185c00e01d60107603502c541e020400c0e0205035844060004025903803080c240a001c0307000c0206180b41042c0d4600c8217031500c808500e48020b030041c400c1000100200c1028064800c1100d011880c00780c41c08c04a0380078001d11140c40340520a038000c1c0201070201042140c03842441c500709204145200300002c0d66414140c8000750003514107038003010390000203001d000401100340350105540607407080403031600e0f1096605941c40c640e900394203402c11001280019800040d400980310389441c26501804c41151441140c0b03c0d042401301e80810446094004d10105034014802d400c2d54150326003003000301c02c2ca880e125000c5c1c460380164043c8058605c080100040d030046c882c07841d26040080054003040c41c1c0c4910b441502c1202540c4416055030b402040c0078110541c2d40c1c0d1403520340f04e22240242c40c01a800224101070b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 868806285 1250 868805035 868805057
    0x12151009080c040506010201142404110304110a1203051c060e130804050604030b0f0135070302032a010903021e0d0b0a0c030617060711190c0501030507 67
    0x60104000904107001c840c00107a0ba5038080040c1c2c003400540301246c9e42444850108586141d211008015004402c80d201e80000c544c44103210807540180c0f1007407202582440010005008020310601c6160068440d08a2035a20010b1104843d800c40046000c290045101e20300c0000c410b242d060b4003001d000050040c2031030040c13290200b18019120441c4050b4003c00d40e81070001c2441154000c0901a2119640355036070b042c910704001c015110b40d402c1c0b00720b907030002840d000b601040210107581850b03454005058001403140d20102d0509200070750140c0f04000001d07a038240401c038007400d060302070014050f4080c15403000841810780f0300c5050200851080c409070b03e40003c40c0c02c2c50102c50b600c03010600368210006002d440c2c2d03403034020064100b120410110107540e4002c0c2001c401241c406002040d102c0d0202c2c101030144400400c2a0b5001a0008039124400e0f02d40c20503400140040c1d03005107840702c0344200c00002c450f606507226480790400308603a580c14414250300070514545082510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 868807535 1250 868806285 868806299
    0x4050901090b16090b040605031807150e1c050c0102060f130b04060f1d191502090d06141e070909020c0f150901140907061412151009 59
    0x40b201508148030b82e9100c0031040410750240d05800003130304445034100c1c3c40301d640c3c540041c0036500c03c4030f100008e1940d0510810300355800148900035a00c3d8034028144480141c041140c099010900385d5601c0390350360861101440c01090305060041c0940041e010482071440064908140a40b01d824070701078960030003410507602c601989855500c0f41000c107864586081071000b42c150101c13200116890720710045060078500200402c203000d50019240340018500d81c40c03202c6e00090b40c01038040000c1c425140c0c4034854550003000c0b903020041101e801042680c0360901142e00058401c404401032006000c503d00104060700c0d44651461a51911880e00b0300c0001c0c224100340c450801403580104141740c00000600c401113042c0f5200c02110f0b24a4015959551101070980701e40080d546040a2000310507003118049101c3c03084d00b802009000d00c0c0200488070820b210840c000d2070f000610201d500b400c00d2010a9011300c5103070814251000c2d210080007050f0410b02011003d100350040104401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 868808785 1250 868807535 868807553
    0x306180c050913051914010b010e15070510021201090b100309141005040c0503060c0414040209130207020307080c0a260106150e19090504030309050d020c0405090109 73
    0x1d00c0068520701810340b0f0b0b44800700041c03a40020018064001c010585801c00c00c0100c1100b0820700880c030050b01c01c40b030001c80034200c64915020301d00048050100c0403450134120f20b070100c00c2d044510b000e4034050294444a00304805c0b8a04841c005800060340e102a20184105602508060104004000503600002c1260040e0344010007072589074003000c070030310a00b102650b5084c8205410350b078511040f495020003c0408a40070bc0e4503c41e9200d01144a060008544e8030603000c0d481946d25040c109280c10544905e1074003801e600a030200500c4106171641e500480c1030140300c00700540c03540303d103104141c24010250030204541d404407101c8051a90385107a108211025000d0000d070001c81d00700f80107130405520b000396000350b09203c000541140340c0011071401c1091a40d0b01e0006408510401401c18001402d031503068000a005100c04a401d60246400c0b520904001a195280390703117590905245c3c0710b121000d60404c0d40800e180d401e05000305648040020f0003002410699a070b94101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 868810035 1250 868808785 868808789
    0xf0d170705030f060301090c080a150b010e060d020418020a110c010e10030209030105040803010509010f08060a1a03010603051f0908040620030403050a0c05040e10020a05040b03090303010306180c 86
    0xd148183c401084c8561000e50145614982007011400c060392920b030880c2d60391000711011544002c00d000300e4070022039544112500303010142d490b03070304544406041001c1500039983c4074003081d40c20000015018125055483c442840410240e107410340410003031310344080c00074130302d4075608040e51840590780d10014401014404403108140c0710720b090002c5009000301243d903900340d840c0005000a1051490180d412a00d0494400c582681c0b942003a10244c0001c0c42200301039070105001c21040f5a0540084030f1450861110603445001c62002a09403411544184e8003a0025003074403142c075592180c6400b00ca44100420b2000b1402540e40d500e241c89288030f4401001440c41f00d514010b01c00342103415003000c2d20001c4035161516801c0c55070700c3c0d10401c03c049900003001400054242402d0090320300440040000d1300212112171484400ba40c00071005804010003000081000d50644010f18007480400c0001c640b00d44c1140341c500e04450a564207110100c440b084200c000410324601541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 868811285 1250 868810035 868810051
    0x6090501170601020a08220f030b0108030c150a24080c151c020906070b09010b0f010c0f1704030b10050f150d0603080a0c15060609260f0d17070503 65
    0x5603501c01c2c282c810000140388070f40c7c4140c104e10110002041c00b01d0300e840c001a240a0030120450303984c0c0ea21051380e240f141000700f4a0607000611403000a948ca800c500c0e134030190b200c0c40420468814400a2a250080035106a041464200510420508010110464806a400b40f002005444088a450144190200000314903141481001070140c041da0080c01010f40220345030406890462402202121990915881c2040b158401c1c1b8210229030441d81068481e00c1c42c04036a6282c901c588419140c0079504165000071090001700854014002980142100d081c2410078040b89a0342000c1e131340c0002d110300034150301001c80d95280c15280950142000c4d400d65a40000e55422001d81810340c8060880c003c042424291103400035450164a41300d10515604802e859940784115002400342000041000a0920041d00d55000b03ea0000880b400740c0c81b022440e164265141c5482814905400d401421f41c00310001d801c05020811074a590915003400e2400f02d400070854080248000c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 868812535 1250 868811285 868811287
    0xd0f0510050f1314130611030c0904021305060a02070f080d02031c11072a031e030e0901080717070605031b07020d060b011202071e02031606090501170601020a08 71
    0x19503c52150703131041c89a9441505076840301e01d454071403e103070f43c842d0400036100107007880c9507a042100498220303031044840701842c90408104109000081d000854010304100c100100429541e445c80094070313445449034001d00511b0b007490721000300785845d0b42c07102c10554004441e4002580d0080b0540e6180d200b01c1080c00b204041c4002128017405010a42a04141e4001502d0051011151011659043d002138595120b414152901c14001d140c5c4000b810000660f103035040c04001c80300030300003894001d05d090b40c031005840001038113414082c1e00c59100d6900810040107400070045001220010b004042c0440d2480c20802030a180b100500da0f10440e0403046002c2c40060250b41620f207250307000f422180e11218140b40000c014650f080c441070115a441d189401200b0542c02180c4440380d000c0c401c419aa8410104c840d0319129040c0c0c120f9260007035a003044002c017045072840c0000c0010b95100d0101c1d51500300003500c4098403142002104117007004114072a43c0005584500c40d501210503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 868813785 1250 868812535 868812559
    0x3040b16020715050d0e0607020c0402030606041a030105030706021c0f200d08060a1a0714060c0319024602010b1801060801030b090a080d0f0510050f 66
    0x890400c110354002c425a240340405407a041031380440909208080d10b1020031039145180d43c03041d592101103070941c0050340f106800025504198001d10342150002c1e1503241003644400c64403c02e030140c0030f9110b928030b102000411a5103000c1204d40000c1c041400076011006030034100701c00c4000c640c40040140000001540c0003948503102d480502d20700c95400008140c04030011584030102c1301100710001340c14501041c024031386140c00c50b0440e140700c144441007901120400c0c450b9001364605507446c40c071070321000292100500c0054450120284c243d90b41e40b512091040001c0102e414141c21148144918010000f200b0700402d16a1b0292003203080d1040c2180080d0000000c200700121001c824000001081d501500004c0260340c00312044480e00d503101e4030508406800340b03d0b90b000607003454010004602c40c01000e030b4001c0603c000303031241e903000c0742c03281c4603d94401d4401e207051941c1d6141000303c0c43d10f64403038140c20104900c44d4503002450034001a403604c00960100b407051555883c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 868815035 1250 868813785 868813787
    0x41a070206190c050607210e0109020a06080f15060301050103090f05100617061005010807021203040f2a06211109150301051f0c1703150603040b16 65
    0x541d00a4a001c03815a90b52041480008000d55032110f001c88041c4280008030b11034074018503070783d051100c04503104621003540f1852040078000d044d030f0580c00c1e550780d594403c0150b160b4401c0302001d8082da07198903409007441d18040c12000c1004100d95401070024a420506540780c008490441d0300c00d10700030030000283d040c243d95504007064024180d2240401070742020748943c101d94121a0803e103501c204030b06c005060f5840b8041211204180c0280107020302070340d0302030460641c00c848a032040700d503d04103218524007581d00c207607001d8a040031400301c0c15040117410f4103590900404e00c111803003100d4462039402080b141070b00940c800d001b0503c6400d80c03c400340c98610008408007003003c3c0480280c100300c21419074032034070b212802070f44107503246071325100c0500440341200d40140590080207040c610904007800010300700000c0004181c440310104138025900f40160b4554801c6550380c0c2080c4021068500070f0f05038050040c40f040c401c01c0041802400d00301d03482044000e02030032080040030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 868816285 1250 868815035 868815037
    0x1050a12180b07020d0201090206030f0c04030606030303021c150513150f0905070c030e09040303090818040c11061b070b0f040b06040e030901030f02040902071a0705041a070206 78
    0x49800d480c05401e030708405120b07039806164041d402603029900c190014002c12400e1711059075000e90480d404101050300c0c00320b284e44080d032003425004024141a00c0f5030300c45040c0c60f10307035006400180d001b0a01400c5602034010304580c00c5d8801008000d40d2101610040329130b003c511030b0f40d00c9070480c1c40300070b120440e00b078120b1036140300300581c0d51004540700c1c6404840c0c00042c1c001c0c03194003480c04d00007070341d000e000e5405189202d40544640502040000800c001c0440c0203104904142d103c26900d0002002c4070b0240c0b4600c0c02501e1501c1c2c080700203c0074403089405088079401000106656030f103524001003001908841040341c06c4500a600d20034880c124803880da4018031400d030380c0040125191400d2001130240340b04400c032070074548801c030400c0159205502d0484454204000100e201e6000750300107000c5800d410005130515503510441000c90700510800d607219100054a6017900c28103a1550f42c2c86034050408508107410b01203242071101051061710182100020f042080d562004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 868817535 1250 868816285 868816301
    0x60f0e01180b0c0d031401231806190b0f090418080325090612090c2606070203041e0f0f0e1501080a090204090f061508030901050a12 59
    0x107080656552a01048880da000d141c242015000728107102da031061080c0580366040e02c00c0c2a9072401642400d00031210210000c400c010843d5030100801d000e42c0b6000c0d80ca01c070f006e1280081c800d80349040010301090742004042c2c544541c07142c442c00c0c0002d400d00300c05d40b51542801100641c0f2041031034041401841e01000e43c8500d50450100407040001240042d403280c000405100303000104014079201c0408051410008101c0d07140043c803041c2c0c4603948006c44d80e85040e00c041007814a42e00c42104101090300021844520242c130b20b0b0301003503072240928115150030001d02d00c1d80360520b0029107138000c9001d0a0420041d40340d607489030783c002c80322201c05031022914026031030b913884400d009600c10703600c11400007100d004005814800110402c50020406845d5520f055444048003002403141680403a0f002c1c1c0e40d01c3d442000b040004a4032500c0c03901c6040b0004251030004030704002c0b261140c4c0035500942c0208000c00569a0200c2500e1b5000403900f0080e07400343e0f030111040080d110076 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 868818785 1250 868817535 868817567
    0x60a0902032505090f06030f0f0303040312020d15080c300a05060a150b03060a0b0c0a080d0b01021e0a03120f020310030210020a0308040206030403031d030d15060f0e01 74
    0x80041c440c011020040c011b00844080b4202d52081c901c0803000354585541240803140c0307070000e10000d40440d019102c4140d0502c2030704001442d001800d40c2c44000c441428040500c0b4510031141407001800c200180d20005400320b40120018407040e420001c041d01c41c51002894403a0f8202e200c8801c0010809410f0b0264002d0075107106182c8443c04030001c0c41055140206d003031645000250081c2c0c0c3d40104d80c002c2c135029043d01c3d0607a04220820b0f4096001031040f92091040e5610b480201e030b01d0310003901d01c80d4070424021803000c213150002460062080340d551302c40c2d030004400b6902e28030009080000650f060915041c100c40050040d00200482011416818000000c11440360950212038060300d1003111400c404d1070b0070f4902265200c1c1d0403640100400c07039440c0401c000d0b16103c40a1580035100c0d140c0031540c60998030f000c0030904071a01c04019a0703803000c2014104200706003d000e00c0c030806900c51161551074258005c2100700c3c0d03100600140b10040003100c2c01c9074440d081500500d0303d0307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 868820035 1250 868818785 868818799
    0x120a0b0103051c090b0a0804051227040c050412060212090a0c080304050a18090834031d01020a0c1d0a060825090f020408060a0902032505 61
    0x96810883d4039154001c0b01d011a00a900f052151458043c41d10743c820390b8407041e480c908240d5002010b89401e90040d10558640c8103c847c4200c404060034018000134440341c10802c220070700c1078514612406088015485141004002c07407126502c030081e10304681d00f24500c14203691090078000024826002c001e234000510f1401c01014020010708414818420031006000903030714480300da26030150f40541a0b100c010203600f00031084800f03940c000f07020303005000000c80802d02c1c2d0b96501d103036000a602c0c200301104190302080040b50380e40005482d00106c2c410702e030f1500003a03500924040c08004181705102002c030303184040380d200b0000081c03211b902040700300c4078944500c2101000030380c00d100c0c00c401c09180b0001414010306405072204030350780c0300020300c0b644d10400d00c0d004680c1141072800c0c07901e88c1d40c8840011044a00e0203071100d94544050016600da0404890504194000b0003822007542080e42000058500040c5a6001c0b0f00c0d0b000048200104031200700356000b00c2d54821940844 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 868821285 1250 868820035 868820039
    0x503280506010f051804020f220e07080d030510030b0c090306070e03160b120c120a1b020313090209062107020705010906141b0109051f090809120a0b01 67
    0x141c140400140e503421540c000340d080b085e032560034158034100c4009400501020800f1010b0900044191605084400501e89585148180c2040303420030850441749500801c801c2000700b1092006561101a40c901408070345014405942552014440109000d091000142d6402c171a44150303080e0040c01410303a010750400a20040821508800c0c183c801d00400300032000d2408370315a04811110884185414030300ca2945e695000c0c00014408040100c0030401d181394417180070206882090114400210b28100e0595580b14140340741c02c06c0c043d035000b00311102d184044000c0c0c036022606404409a92115201c01080311401020f46c402186000c1ca014403d80c0c10450301d41d903208403126402c031001640d90b0300046410405038458003000c64000212248645a00002080001c0300303841310058001d80981d103c1e0850b000e100007994035030030060f41e034030044c028a00821400001e1003400c0c8001c605035200c00600e8031032080c07014822214a0b07000801000d060190407201364010000940039a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 868822535 1250 868821285 868821299
    0x25060207060e010e090907140a050319050f0f03070c1a03060f1c150507030b011d0118080f010617070905040c0b070c06030c0f12090302100203010f0f0b04050328050601 74
    0x1100303602400411720123074604804e5078141040f0300002c5030001402410041d140790600b8200300e149060035038180c0241d0201300d00d0a8070400101148920709002140c2c0d8602d2030a169841d000b080d04409204c030320101400c1c001c450414241d94210800702c0d031041d80c00310003000056418504003c0c54445285400d9844103218a07610007101010701040248070f40e0f611004100c0488034202a0180800d03e2503504070301c00801c8180410b280441814500c216a0794540954001e51365640002131641c0140c40f04401c1210a010328801800c05c2c650800c1034403042d40403103484003003030300901c9003441d40c410025044c0034950510030001c0c6182d08542ea510745042c02e005110345030300e01a400100342802205c101d02441031000c0180c0e40013941c1d448001003101020b00c405804007140940451140300100070141a01e44000c2d4001c01d0240e0320101c21900d0404d14010308a980d0b445500c03a01c0c404d100422040c0c801041a030907112045c0041c102070b2100401741800c4020030500a001403146000100c0d141c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 868823785 1250 868822535 868822543
    0x8070f111513020a0506160312150e06120c030d0f0e15070507060219060902061207030b01030e03121f030c0806150d0210080c1b25060207060e010e0909 67
    0x842e000303681079000c1300c0e2200701b80708403446010314400641e81c800030580007080c440c404221400040000200b0350085d0f501142d195540702c0c3d040040080b03168000e03c125407a0a0159031a892400300141ca0407140140000f81c44000c0340c581401884218501d403802244580003044140c400280303a201c161103070302075064040d00b040008503030510912070003294840c000516012040104400c041a00740d0396500d2502030510001c0481c2c1012080c040d1480c0900301d20621842040603650005040c25030200040c1640e003000701c81c007080d4004004c4102d1007040352090550001400002150944121088094001c0644d0018240604000021503880f801051160180034403c2c480c0c0e202e850fa0008121180402d840025401110020030b41e10250080c0c101c0d65101007103041d91820002c0c2c4000041490b100450000c84a812407040c44000c20503280300d11201022030104c1d80007540c18900c0c042c0d80c454081c00340b00180652080c42070240c1e0311920001740c8064000d0720820080c01d01020150340c17 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 868825035 1250 868823785 868823821
    0x21204050606012703030c0609050604060e19200a05060d020a120e34090506151624090b09100b03030a1808190b060108070f1115 57
    0x5007001340303200010100360503502d11403071100c04400e060340c2c0b942e40c0944082a41610490b00181c41d480c800010940911095200364091203010810700704110440b410078030311044581c0c0c1c0c092560254400326002d0090703c22903100c0403260741005100c410010310654080d50000758401c01c0081c42044107100c640190909414a88448c0000080b10140400b9510f109081604560128403d40b148064815060802e1a5400c82804e40c4210300819a44181d5841c3c00405185803660f0900109081c0f96009582d13400b00808550b040c50036180d2802020b2551480140c51661400302049031a1655100700d281c8211841d020031801000d4504918094001c80d0b00d640135000780001d9940c108080e0269040031400203014500e058a141400d0791603015040e003c5d4050710350154013040700a404c200001700e04c0c0c42100340194a42851801090410004004904020a82003030003202508100c070001992503e0a05050440e05680c1c043d240c2150f811860310003401a40511041d0800305c40c0001e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 868826285 1250 868825035 868825037
    0x803070807110306070503070309060605041803090509070905090a0612031d09010b0d020a020a060e030415030b03120f0c0a0c051201091a101a03060406090e100f02120405060601 78
    0x102c0a00c20040640f0b5500446000002c01c80801c0000c0e071715403080e4043d0a0035445080c0005040c1c0e02e600c04035007200c2854220011440820307542d6401c2c0760304101c0640081c801107c14140c03500e000200105440020b2103014024041c40e00031492040e09030b00240040c0c0f80c800c0402904500b81e084c020904061248490525510100561240c1c04c10001d1581a40c1800b1040e601d840410404e0710001c0d0300c08070700b0604602030310051b04005001405001a56102c0c0f41c011911039080c282071046c6800c050240b00145440c1100910981d00c0c00709103081c1214241c050540c80f01c002d000e500c0c0382803050082d003918074020032160038200419081e0704019608281d07a0011941a1501d00e54201c1700300410185c800c0c289000c00401c05001402030707030751050031400d0924069595824942c0030a040803040d0107a0030020040100070f050a01c9600700500602c0300510410440c007050f5901c900c48000b0300d50320b840c6c0f01c1502d90045144c5404988411981c1c01d07410301e0900c0d181c18410340342d000c141d030070034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 868827535 1250 868826285 868826303
    0xe0a050d0c0c06080411010f03150b0c150702120f0702040f0c02061b12090f30040b0d0506010509060409060513051e07020106090e1b030d0f0c0c0803070807 69
    0x8141e99126242130340c452944021110a004025001541d80000780c0b030100040544501561b03102d50b00c0318032454014a12091295100c2007820760b100c0c04d00c00b062040076802d25101e0b0030842016800a0701318000804045010b0740c40301c803016540e2651243c050f0194000d401d1100545000d006640180b8000d40903a003513403031035201c04820000c49490280580d901c21800e00520080400107200c117600018828100c0c1c1210752120452030608140101ca0780d00041c0103c1c2000d4030101c0311018104041c05a5165441c150a0800008140c0035021005440300e5a0780300103107007a4066802c03508504002080e141d200e90f59202c03d5000360000e07000341401031013002c0001c0d200f0480c9006242c0102d9134480c82107201c04070fa03550f80c29846002054030003199201c050000746154541300da84507030071200029203d0003031804206080620545d403458026440104080a039540c003490803074102c1554640000c042443d0708081002c03074001d401450b15800b0005600007084060301c003c2070100c0c0715172100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 868828785 1250 868827535 868827539
    0x807030f030506010509130212040c090c09060f0806030f011a0102010b1516060f1a01110616030b0a08191a010807030624030804050a0b04050a03060e0a050d0c0c 71
    0x1c4040e90003e8030440d004c90028405610a441c0c40d80c52009206071001006040140c0131200030843c0b501502d003a038405c0300c041ca0030300c0b60b014540105a904035035800c0a00680e854801f00504206500748400d0811901602141207a5001c0c000d2000e00b11021000380b10300110b0749000c223000e0480e03032140c0e400340d8a000003142072420311040d0402440140d000003800c00c05000c48c00301aa5000c0c220499886030f492054180800141c441c03a248001d50f44400705100340050000340c80340c8001802030f945544004200b0501880800881d410140301d86004541d40385c4603000f003891484550401c01490240720301400fa040600d40400200c607000310b86004845004000d9009140c1003030040b0314580d040141c050000c646d040e0442e841000080312240f90038a0321100340e5807600d1a41e0401c0b00c0540000408100341d19200c8107000c003514a0840040c0707460b107408000303011228517120023040c842d218492076050407400d0090402c402d40000035200c581c070074544024003e101224080365403440c07541c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 868830035 1250 868828785 868828787
    0x9090a1202030c330c04030f08090406140a0302120c03100c031d060609060a030204020d060e0709081c02120d061e260708030403110405090a020d030503041505040807030f 75
    0x3204104416941a5100c55241c64203d09074800008058905c0c18204210000025078071045019405000310500c64841c00c40034100004d40f01103038402c04900c0c02c03035040d035006c40d510769250400f00ca5040700c0c800301207004001001e060042289104e0360501071400b492041e00c01541110f81d8800c500d5030300b00907148ad0140802500b808a8143e0f405a40c08a4001007260070b01ea800560800001041481620b40e41ea0000f4181c0c1e1042e4451820f2945800081103907118166901e41c02c10001d02748003060704e05088401d551032010b411052010303c032010103504414004c0c040d8070700d11001c0850b0b031a139500c088003e82e00a000c4500c540b00c1d82c81381002c00041c681030103400c0501940c00c100c4540300c1c0c051010a1109000395250320b0180c1c40c0c001d4540c005403200040005000842c403901a42e100031201e8000c07c002c0340c1c40100301c0421908035840f8100107a881074440c0708040e625040040d00c2e40c8860030000100256044042e88241c0703000c050005114800001d410308138840c1d500e58080c1d01c1c5c0d21030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 868831285 1250 868830035 868830073
    0x10602071203030c051b0318040e031c02090301020c16060c030905060c0106090f0b041824090609140f0f03041a070605010e0613060b0909090a1202030c 67
    0xca2511154070084000000910075006000320001600c1c02500704561031a2044005002024560440d400044c4c0c6c840e1003a090004d1020f1601e08940800c101903a00c82d03059168880d031815842210a480145d04442400703506840036048090001c644a00c5000c3c001ca94442c0c40705443c0501c180c00c86030004445124110798290103500d9034800f00054034081c24806290803000810b691075403a00004220941c1ca4401c080d200308411902140c0c071011402130104956420101c2640b021140a0078408281c0710601e0108440920080003070305140f5038040c2e00102820840181140c0c1004070f04420b009000030010510b0030080c09860080480c3c44080e03a07520b801c8a00c003421900244420060380d142034012003040180e40184520301072440d40c402d021180260044500e840d044024801c1a040c00c4400e800c3d072182b4050704100c142d0600d9410142406081c003c248600d2034000020b80c0303560240022813600da444124440000d88401001c2c1d200c0c0c206c0801c440c41840344078002d6421142c080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 868832535 1250 868831285 868831289
    0x130312020601080d1e0219030e01140f0405060a090b030103030e09090c010c11040e03030a020d0605060301061b02040209060a08150a12080f120106030902030d05040b090904020406170604020901060207 88
    0x511343d6040e07007080450170f40540000d11221415030082e4942011502654841d5500f164481d58602041000001c00507000c94035803820151141c00500550300b000231000210340640c3c1c0708688070b40d1581e007100000ca94902658201e040342c280040000800c060f00409544418001103d0b21040d954074252a1941d512900e40780b2400903000701920b40101d40120803100d02400054804150b1b6114290401d155600a03148100800d070b0000c0c45144100480c45444040c010440703100d465035160910080c0500901440032800c000003442c04001c560710365040f50003842c0c02814094a4400c1503401918480c401c8a0790803034044010350a200e1807414544440556041070226901c1c5078940c0c03901c0840e41c000700d4000071a2641000b00d0000074010641c0e05000345403c0c0c0d000720b00e1581c5403040c903040503254074146041c4001072105114000d039510585c4d0285c1c0050f80e1100217a6290300016001e092580d201c16059580e00445c0000c451001ca0080c4c4201e009441d09078859994a0040b60350740124 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 868833785 1250 868832535 868832537
    0x6280906030b0913050c03010c080912270307030209010b0304020112050601050a0323010803210105010804020f01144b070303090b16020607030b03030d11130312020601080d 76
    0x1e80f00181c1d2030302c40440403081c0ba0307000307a003120003c20640b00072a00311608000e4190105560004000000c4002c201425548241100c40c90412101810080782000000d400f1403012881018940c1291801c0000b4001103400412103040395940704441c034101d5106a03410390001d01a110f000800303844030b000702070256806035281803030a209c9240840080070306c401d000c0c8821314600c40c2980065000305032a400703071080101450785c1c0d0b4800b581140c0240c0c01c5042d02c4e800c00814400400141c1c6c2c000588561051301601c2e540010308411004079101042c04070483c18540d000b00340e0107501d4000310700c00d80c04c0544100c0700c00b2001c00d04070308101c044944501400301c8094202c091034082005007001d002030510900380400e924803a80c0c0d41c0c0d403503004111000103c00b602c1d00202d1102e183d0400826820900c14101000070402101c0032036280d2244c0d040c08828661a80040c1400c6112001140c0302150741209030711020740c6034071b03000488019801d0001c00500c244000421000b0010428250341569 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 868835035 1250 868833785 868833799
    0x30a0302071e350109030e01050903011407031a0102010e1e21030f070809060a020c030d0204090c110303070e0f0a1508041b030302060c030606280906030b 68
    0x600b4401c2e600051005448001c880785588000482c002d107003c4210700d005000802e250b4452440062110700c1d0607401c1d030000c0582c181740d07003c03001c0b90300315407a0011a5020f103000c6a907046d04c0c401103409400110391001c100d8003c8420401c881d83e00d540032243c0c2e8011180426441c080d2400128203071030101c01c6c080c0f11508100210104100c01c0e0502d1908000008161000d040023214100c080340c00320684001346120000800c6401c84108202c1d5501c0102400c140c0e00504100540581c0c40000504890a2950000350305140520030415a01805260340096584039180c40740c100140c10340c0748403000440c503943c200c1c888608010050328461140c1e584c1c1d94000c00e501d9001c014000c882e15100030f4000c11040800300d80d003840103003284155100b548038541503041502d045002e070007001e0310703500c0041400c060510001e40d000c41c810340c20000141c070704c40d100c0d1075020004030303948074482189102005508644145241c09200700400421980300d4070384032642d65805070181c8007820502948440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 868836285 1250 868835035 868835039
    0x301150e0904061b03060f0b1b0d0201050103020906041a01390c08010b10121506032306010e28031a0a0204050a030609060f0f0b030616020303040f0812010b03010e06030a030207 78
    0x342382010348080d68004404070701c06610310844a0400c07051003d1180141d44500050042d420003042c040e412640a55040012542c1040003211a004100002d0f040002d030030101c203030701c0808030315544490750201008000310030030f104021078130070003004121542001300a00040c2d2920600c2420b80c0c00b000030f020041e110b84041d074200e8003e00c103022580e02c900e41e82c0c2a04140a0002115000030b002182c800182c101040c05010380c02c184503588040b00025010304110b80707a60f11003d80410302e00f0644180c2482c640c44401843c0303400202038000002c0380d06002c0002480441d10910320302501155120310340e5101c074121b8000764030850160075003181440c1c104200086e0070354840006e40380514000207500150600d1101a20072050050746c64603201d21140b01d061400740301d40d40d0000d03205241c003d1080401c00740691640030003030010f031032401100ea005080c00b17908411107650480d6450050740070f684072907048149404c2809645d482070720b040001041e60600041541803560546c000b00b012078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 868837535 1250 868836285 868836299
    0x30209040305070b011814012904030602030c22030b04080a1b201e041d10050714090a031101050d090f06200301150e0904061b03060f 59
    0x840060320803070402508100603004116509000741c0680528141201614910038000c42a51000208200100c0c591801040000c0042071001803605428100d084845440b880c242030900a662024240d98000800c02039001801e00007445c006202c2807000e4040070603001100c00014003400010181d400005c0810046402100640038180c40c61800b0300003a89224080c40c4c1c808100c4c1000c84004058899903541d00d50480300c00103005a06903039405074002c024442442004500c6800c90083c1d6441e8682d00303891500c00104640760030f08000700c1d14400b08a000e1900101800c851010000d444402c180c4403250500080359022040101b440080311305644070510038640c05880541800420800c4114042c44c90060380c10349406145807a00032245d034201078040d502d407014040320710903140c4912610001c60005803130554004172007464118580c000141c6031178072000c1c5c20340d5012071141c2c104820404107800242d14000c01d1180c450142d5021281a000c0c1d0700580070340d04046283c024140502c2d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 868838785 1250 868837535 868837549
    0x203040515070c120f02220911090703110d020d0209150301140a05010509120f07060206100f06142b020c0c12070e091c0203040e0c070b0411010c02040c051209060702070302 76
    0x3014141f0810302d902021005103012100402400c540c24045080c012000d40f420340442503100d640d90030305000700c1d4540307600000e8500c210f100c550381c51030340800c9624100c50680e05a83c51400c002e01743d00040c0000102d0808243c03c24030030980644403034008944281000e4001d90304442c0181c50303603803e04950b00f08100c0c00c2c019120040800f40b0a101803245462010043c100c01858a030300640814105112500342c0080d05400c10b00c5009004142080041d80c4959640c00c820107843d581502e4200e481000042c0c4102100c40700101400f210321546114150743c01004501940c004460242c00341c2c0091000e522140c907403415082d0030003001007207106c5011801d40e44c801c0c0c14100b80c445914043c811800b440850031401d030016403010800f4092101c0e072850f42d03600f11504001c100d080c034038650307140c40c0b03003001c01032006021000401400d2083d90040d2088052250700801c2800107201c0e203080140950001c00407203001d07100e143c010079588030011070000e0040849502030101c0358115024000c2d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 868840035 1250 868838785 868838809
    0x604030c060c170414090109050c0301030f0809031f0f090c0b0d14040f050f060105060a030c020102130b0306032e0b010203190804112e0203040515070c120f02 70
    0x2e1110390110210610640710000c101501c4132080d40085200045c0038000500030580040440070320b05000e010013645034209072811250701c89842481160b440c5445101801481105500b600c41d84c2c0070001408030062082e01c0c00e2200d46400c05c20280d403132804105031810703031802070310784043d045007400b80420040023018130030f00c040301c0403403d0703451214070940301c1e80100e40a80703205085005030003c0141c2403000c0014580000300500e603550600002a410b8810000d0f07060504d940d5041c0b5040309030007901540c4825200c00424608296502c1034807102c0d500c1100c07513901c40d00940c0082901c401094061714401400c040008400f0001c48501c003004004820307002c0d040d03200900031010740807014001c00402c03c0040e500d22901c1d00b414505000d60700a00013042c0d101d40c24001c5c2c0c40040342c088011107580007034a8080c20755141d1aa840590441c419600407540010703140c2490f480743d080c14002001e10038800c0d4180e48403e03a0341c94020300c7c0c000b00301e14000e004040303484946025103090015200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 868841285 1250 868840035 868840043
    0x10633090b090a1805181f0b120d120612080d02070305090901030f02011b030e0405040c050a03050601050a06030204080d05180a0e0a0e191403040b0f03090c0604030c060c 75
    0x35415844458a0700c01043c28103403006855217400410003000000000301e400040a4001018075030b07485907481c4008841200502141641d500c030001c00341d515611b40400e0040b004051f122401d01d487d000610200081a03541034240c1082030010301040c01c1c0c120b400c103540d0499410383c1010b21512452010f50f00a082c1a001c01000f8030610a0598078007074420700840c451050262101e2640c07001614215070100a16009102c42078081d01103078005070800da0104040350001a640d41e14030301018900c0c0a0b40141c0c4d0050031008001c01000700004a10b810b0360822217981004554070310044003a071245d0702408005812441c10214414050005440b61001c01100f1a03050810341000c2012004aa031040c1640c0e00701401344448002248070340380007407100c10b01800d601030211105905448198200820260024001502c40c0d074051054401800c40c04240c50703914401c141204a00c0d800a64007070009020360221680245401400c8804884d8000c964002c01850310105880307065422800703036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 868842535 1250 868841285 868841299
    0xc0105040e150a06020706082a07050f010c02010603050c401e05060109030c050114072102060f070e0d030e0a090510050402040e0621010633090b09 65
    0x22402e40d442003883d03405020341d035000344121403410a004001d25009441c211444030740380700040800107000050007d005e00f84140603a03415561400602e8450f00c03007074058281d40703000e0440300f03440d6041d004041181c0c080c4044440d80104c220410102c01d111481d03207802c803070641c4d1040c0650f0714140c0c0b01e1402404440100b02070303508010060070035144140842580300000d1100316601059601c281070300840c080c13800304009811076484003658104d6006450600000d403031050b02503140c2008469845034003018148103c0f15076021105441000f502c21800f5014800000d9980c10030540094480c0100f6500c101c2500811000e0040591b000c5c6400d60800c808006010010f80b9110700b440000d1051500000340f0703140041044404100680119104070b00411040104081c402d40b0b158201030300711615400d84012480609064815240c3c600155081600001d403403003294040b00110351081004000303042004030383c45250305881d0305160103d1002e12041c40140da0800c06000f0098001d0003403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 868843785 1250 868842535 868842571
    0x902030f150315070216061b0213020405150a020d170a090201051b060f15030a0803060d0209040c0501020d0504062003210a0e030307200c09070c02040e0c0105040e 72
    0x40180f080c1110385a0150b0701038240070142c01521100c07000140302d81d00c0d0080b01d91000c13a08580c216002d0060183c425024000443c5100c4800d904507801007a000700355141c4a200b014440f11030341c20110f000304c0903020720900318000c20300075040240d4440a42880c4549651141c82d03007801441203150a80c1045000c0c44000d442000e14800a05200064801070a0501c0d000b0b1005d06020001001c0400c8403081e41c81c4070107035490000e010700000345c0c4103c1c2c1540341d40d500004100740e5860000040d40c030021140902052062128504081d50020b0b1f080c0c4040001800082e10b11740309901c074150009100d1580c80c01010002600a0f00c0c074030782d400559180c41e5142c10200c0400d000400c08004815805060281240540c4660f0600101d841c0186003145003900d005072203000c8100700d5000501001c441d510510006000036080c4400081881c00f040c142818001c044180c0303910101d00552404405c1010150006001280c2140580d5a40d00d05403d20580320000f00010b40030300003601d001941 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 868845035 1250 868843785 868843813
    0x160201180b16050f072004020703080a11040e0a0515130b0102160303020316030306050a031118160509010909180b011d06010309051501060908070902030f1503 70
    0x414010602862240d141c80c1042d111000c105000c0c03500c50402d000080007003800182860013990406904040030000703039240b01000c1136a2041038404603038001d200003000c204054200921501580015008204d5021a00442c0c0100d205902440c44a20900310000303801410581009a12680d00c0c241c20584910a80c003048100010041c98050349890711070307090081d40d040100452100c0643c0360803488918545020b512071080d00c840880c000d90b84035482c4240360003500070000503e0082d00c0d4084041d544d007420a50340c0380c5801141d11540d0038400c0750700040c0d14500c049000350282030420740c05244c2820b080c0c0b9940d0044610505002c9034000c00105c81d41d580c814002c514080300f08052041e0f0140c68002c00b403000580022880c51201c120030560791510401c41644074a0a00b40011030846a091180c50010800041024990200d00105030f03184d02041ca0022030700200c0c1107400c0075445521000036400122040750b0114240f00020b8034001c02600e2180e400c1d9405000d403424205540d81c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 868846285 1250 868845035 868845071
    0xc09010c02121905010605181510020f0d0f03062405031906030f120f0e090a061e09060f03020312030a1506050304051b131e180b010914160201 63
    0x82e01c15940d1004104058105903266010403a00f407003003235919140c8100d54030810000c034490140551402aa8883c4440c000c100d0b044d80760700e00b0011a0a5902c0551303008180289070441c040009050680000d0b0103c04040f0344c01989007880d03034000350074100f00b6040b18942c00042c400180d0780d10408045200c0032052240e10083e500401c40039008409a08200000c00c407010749810403c0710103031982d460b541e8400d41000090204a07041c40040d00c0382c6c100900034041c0c3d900104050b481400c034200c55a421540c01e1400c80d00d441030309002480e40d542c0031a1600545101c040e416400c004042401101d40e800159485028040700140ea03201c07a0040320341c48d8645030000c03000301d030001060005002d0100540c80202c42e01e0300d5003660581c050380104442001c60300d1401039003030b11403225203650310000181a0194060740b00401040002581940c1409011f10068508088500000c11100340da0700a00e00d412140340c0b0351003000d86950389050300b48210524140d00b15580d90354544031b40310b4058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 868847535 1250 868846285 868846333
    0x4060305100611030d0b040f0c0309021809031b031315120510140f102019140f01050f010509060d120e0121020c060c09010c0212 57
    0x59000659803500044908040489801040c2841100034242d1120762002003181c442e0001d600003c41c55030a610041009001b124504298940c201040505a1070313040c0d108030304440c001c580c01100000a4032400801c0791003500e1040b00da400070804c0702c81e13404800215000c50304000f8103e074541520781d203404c41144d120f81c10120701061950601c048050703011244480c41035000108000038104000140e200000e036104100151070446070781c0405030784a031582c0704155406041a250110501401803c18081a40481038448003001118511400055080c40003054060050101c2659120046044403003045000c0c584034000710104002804c1c00740c2c034010b540c050b11041c100d5051404002020a00804081c06041400c1101d008905100c24880c5000b0680c10030b5601c0942c0000121510b85518400074a0f4030315001106030200134507030041a01d11302c550242c5209031948400c46105101d201340050000300d80c0b0f0a50805464060980f0701d0034002d82c401caa070300c079000d40b1b04c901c4034100c1c030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 868848785 1250 868847535 868847537
    0xc0c0b0c010501260a02010806010c0c03081b01090c0506070c0801060e1602010203060a05060d020f03040506071116051e19050a120206120403111002130f0302330406 73
    0x20300010030408280ea0310001207034521003c4d40100c19000c002c5035607220fa0495000e03042008500c00f07c0c038940d00401d50101203d800440340032000d80c84c2c1c10f0866140d0310044242c084003004103000646c03a041172203020081a40203090142d09842c0c0070410245410034401510b801c0d22242000403a040c0900c1103400400c48100421380302d14008600c40c4030005503110a00669004004018541e40d8a000a50a482003110459200c00310549800700900952260007121140042131100740680024107034803c001c0f995808a1082c14600d501c3e44441c000980e042c0360388508401407090740b906114000e1124174503034014030a24404c0f0b0000d014404440c1158190140038581881141801c6c1c24000c094980d03030508132441101c65012454a20500035130610560b060303008070301003501c50f6206250b00034600d811038120440142c00c8400a40c0f0042c4c1404484101d1600041ca5456070108c0c9011aa0000c154103004108852494502841d0180d80f9160070244021400751407844d4014001911003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 868850035 1250 868848785 868848791
    0x80316210e0f010f0e040c1407030c150902010518040207020d033b150403020301060303080f130209150d080c01060e09010e0715091d06032104060c0c0b0c01 69
    0x12072030520070030415115515040180b400040200c0d039400140165400c032040d01e00195540040f801103862111084c0d4246401c00c000955005056100080450380b0f402407086030381d1004011000403c44a00a0000740410303010301c5195800130710400040c2e00b601c40030340301529000841e4000307021168003500440c0442e0300f0580d21460000051092520704200d40342d0190054034404d01881c8510842410901c641c015081c2404000340c10002d903402964040c0090054680384d00e000303410300384101c40070303500754032054009842e684504400b480c9158000c2c048007080d4580100c013069124003001c0d03480c2c000d400080c103100003628000041650b1010f070030001400a0400c004c1103420000030301108601c0c0c1c1440700d510402000411860210b03410b40d00c88210a1a0f00c010a0381c3c044c0d5180d002c00d03c141c00d9031141c003040b104c48064551103142d08406031101903000c4400c40c8003104074180c110520b40800c0c081840f0300c0e0300400380342d02c18600a10394003108a40c0e80d541d4914a91100c0840c45050751 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 868851285 1250 868850035 868850057
    0xe0402070f020d0837030501140d0615080a1e0b0402120c03060403050c2a10020f070311010809010c1e020a020d0c08120f0307030b120307060501080d03020408031621 73
    0x200175008180e105418641405a54900007042c2408149030500b903100e40e4000082d8000c10200341d00841c2143d13801c60003c1d29240e038403010140c03121010482500d4609a82c21303800801c40c404082070080c81e90084002c00b15485980034481000404894824a80302e2052910255034040001c1131050303200c0d0342c41564a1030035034031b2181003021911080709248a6450341004410681039104541101640c0901d424022054228500f0707090407001d08503800340c40b502105100c2c5202103030070400820b07282c410380c513265000f40038200d0b44000b5000c000500303080c02419400039441111440d100703161044480e02c40361274001806112100c8821540045540783c1008616018410000000c1344003400301d040821241e03988807580310060040c0704160383c64180314010350300c482120690020703410440362122440e150030002084203000d002580c1c81200e08001c86103210307000312001e85502c10043c40c103001e2400540d20060850000440d1100746041e986040944e100c50482d041907015510030754002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 868852535 1250 868851285 868851367
    0x170f01030c09140a0c0302040e01080313060801121515060504082107110411041d06041a1e090408030711031810140a09060e0402070f020d08 62
    0x420360b070b07010021480c18880704124060110703040302d0340003410440115880c148013800b280240b189030415499591650008035000c04008090700b041d0668500d0b07810300648500b82036500b500309100381807500c55442e5407400085c02500241c484c400718840c001c640050100700c2e90f8110300e29500503400003100441c08214454003085042014001103841c0c040c0c0344201d0903007690510980f0400780000004c0b0450b5610303901d4680c020040594809203e035296a25040c48500b03244c04107022400242150021031900d10b007d11600328408412405c8202c103903120414442140c0140241c41c0305401207003040030082e100c00d00c0c100c0c4a0f610501c000c564034907110702c1c050443d0007070318440c3c0065031042c0032900081e41403450740d00100204445621120040c03940485800503118a49051058080344907516150001660001c5e60441e0b1540716041c2c01060600049005d00c0c0806810780500b1001d40f4094103000c040c5d05040d501a000991500c01821000110203118499100c120312005003031204071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 868853785 1250 868852535 868852553
    0x7030605151906231303120806010807020d0f02010e0303130212071d1302210c0319082505030d0f090c05090c1b010606080108070e0a020901170f0103 66
    0x75110010550b240c2d00e0401c0002414140300c403001902c0c80c02081d200500080108083d1000001a103a1201609849142449204018400d60004101c00c0303404620998001c500991089020b58010b003215045504100c9605405500c81d0040d55038a000a40141105100951144460800c000c00c4602148144000d001e910001e0320b140b03411808081c00006a17071381d2000d90354280c200c20203020b5280d1044060010000c100d00940c015013408a91440304800c1d41d0113110385881c41c041d03c241402c940309041c0c44a2040010002600402417003200291011000e06031058040007002840e41c07810303d00c2281c0b0088900190707515800420701c02824003042c000c242558459407002c3c010b249156a074a2640105070042078450351030710000844407504031007500c0d0880040303401700c401d0b840d01d080320034000c041d14007908002900c2180040f42d10100060814103d4442e1f02c6403c1c855a12078500c42c00035085071044904108440c503d480c103000e9020801c90003400424400481545989801c2103a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 868855035 1250 868853785 868853809
    0x110c010e10094202060403050d0b03011505040b0d350a1715030a0303090302010b0411180607053403060c1d06040b03061503040b0405010c03021215030703060515 71
    0x3d40024601d1441d865002c11215082a0706040c071a480341d0354104190041e0180d040c1140c0c1641c40d0007070700c4086046010111003110b6041c0c0782042a21041401e2004041c5a40f0380503098180084002d0310108003203800c410161054008000c15481c50401c10256070311130040030000030080c00c2104091110b00c3e000a0300561440c03400b800c3e52000707030f000ca030301c40c0701506019003415940c020200a140c006c1d080a4500440144108511703403080030800450341051102c13210740d2080c0300640b11241014011038100d5504078005001050025001468400c000d11759250201030030790621420080d20700b404806944904030101d003011086000408000005143c20390340c491058808141c0e803070b04021241966480c04100ea565034855010940781001c0301103a00451100108110a1240142500c4d0296100301c0082c0020101400300b14242e01895101d5405601c07040c000c01c03110040c0e00c06454500c40c4c05420754054964a46a0204903a41200c49004080c09400d516600d40b07070070707185440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 868856285 1250 868855035 868855139
    0x90a2a2702030711030301080d170f0414030706020d020705010c0c0201080a0b03190b1b04030203030307270603230f130f050304080706110c010e1009 66
    0x18901809880e200400085480246806070300101280a1600c42e54011201c3ca071070100b00c03507a80d6952581c03181d039100a44824800075401c003c0e154522560034000e079004180011030111030f6225502d0f084044a040c90b80d00455110070090f0800060040c005403c1ca065141001070312003249007030107800d40380303401d85c000100700c03000074103100533a001403001d074000380614000a011607441d0f01013450283c003518400c40d14401c5101081c10007401d025a10f10881c65044040c440942c0507444c010107001d5800003c2d4560403d10000d0340042c0310301440c111f1030020078807000c03082109507509030711401d964201c1400a521400c40b02444c104e440a078005940c43c200c0c10300b9007450255861000e40c1e001900c118920395032180320005221a100d040454141c0140075281e407550380703030a9555905128451071001c140402070404508002003104040584103849034012440180204903210120040d5001403002075980031807490000040c02080d100300c1c1100342c418000c400394406907441c020f40b20039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 868857535 1250 868856285 868856309
    0x19180f03030b09130f030f0c021801030c0b07080414011413030302011109030615010e090106020106050a0504020a080703110c03120915040309140109170303060f030f0c09090a2a 78
    0x50001c0c0480c2c5d44e20381600e8040c03038440074070042e007007044580f508080c001070b41c08409004840030003503510b600039048030701c140040104e49595042c41070340c0f1b00074017001400078201072004008940b090004c03242240414501494001c1c40c0581076011038021050f030441d00b014007941401010b0f024441c0d21800140e14400904200b554000682d031110f000b800040c00340c1040000342d1030b0380d025102e0302c1100c40004060b40f800d980c507130200034028205445100c0c81801c001c030000800381064400c032180102c080e950781c0d81555890105802505240e014011407100802104501d800d0610107801d100c0c0585403542c6c014240300d9101450056903003c229030740b00c0c0d46014000003980045818044031105032607200051a0200140e07018000d40d071003014143c4402c0c212542d40034020000f10700c41c1000316201190401c0b11814035a960090002c40843c96004070910324161903d8524070b079002454804035100000960b440d0300b1004284015414440041e09403440340c11100000e48014040a0000e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 868858785 1250 868857535 868857571
    0x10f0605061b070503030a08090c060a120c0207030213060e060f03060103020d030c0203011805150f1302040b03010e1614090601050d020d050c1b030319180f03030b09 73
    0x1c240d03224203200721007a110000850341800d02c042c0a01d200500b401000e40e522100340001c00790800c14205d905081c10f000b612418035540c6402c43c20369100b0181c6548030922402d22208020040070906403600030361103010303030020061b69040a42440640701500c085180b524107030300e80e9900e82000d0000780c8121590700d612103450b140011308504403a0104c800e050301420038141903503904030b07241001c4e416508013207180d640c3c58100141d6041307075886902290041e0b40b01900000300c45d24180c40c45e0407040d11110100e01603030396070b0100190307490000b0700c001740c0b450060780000c1c01c5606013181c1601941080079100e404060301904000102000f40558404081d428005640c10300028074860602c000459001070b103a801d981915507100359a00104030354100807690340c0f0345802078400c03c1064451061200d11021020054074080d91142c00018892803407a0101d1000d4030781034042c54221944880c505c00816000800099202d002e80c800050280c4001b05100e4040381c028080006400040c840c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 868860035 1250 868858785 868858789
    0x103021507080f040b070b010902090102100b0316080105010f0617190905030a030506040f091a04080f04240306141311070809101103121018020c010f0605 68
    0x94030041410341000c10364680c0c10b4900100e00d40242203000308010300c042070104e894601e0300001c040250054141c56000d07aa1021824244d10032000c54070300581064120030a003603d16001448910401400d9a00640032205090b0304600c203580480940c0c0c0d140c100401200c0500100103000d0400c51522019500c0040d800c2080440041d1034114102e01603403041c81481341a901c00410241c4c090103481e40d5804142004029003410369001e403140b46841182540303403485214956080d6404a00e000c000d40f04034020070002180148150b40c5440304100c3c050b40f1944032801031000c1e110b54800b8140c05031001c416440c01039400b205d61410f040c5452414000720030114880400c040c8101c4146100f000c1d00b2500b40090b0892481075086510301040761f1040060301c00280210540560701070034400c1b400002113034a40400381c44184590030401442241e0040d000c15182e20110380075200703d00c16914041090411002d101941100e54085441d084250080c05000034010010005018060600700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 868861285 1250 868860035 868860049
    0xd0e070608241c03140c0d050c030d0615020c0105070819031103010807091104051f030b0a0b0301030b15060d020c0a06060303030b0306070f0509091302120f0d020105010302 76
    0x101601c0c2c1c903124105805a403042000328000040600800303041c0000c0101ca402d0060302d12030480100d80f40102c03c800c228104030584026610310301c010045080e0680302a1000c0d8400007960741d40c2d010402c00404400c04c14000c82004018846002e080f14680510082c1002040d41c82581041410000040071403441c000703641c0001010700c4001c00b40754541d841a00280400c1944914555007c800040e0859012649000310350703a0060502503659020410074a83c4514020954400498826100305003c1c40c241140380078820300b000204034001c01c0c0000d403000d80c240c2c41100c40282c008018030410500c2d1740390300e0b004643e04125202203007d02c80068254019814030000640d40401c040084400402001c0c41c0319401c02c0e0204101d944a00b8005c003d030480c41e110a00a10030140820455840340001009032040c17580c406041c00448810001440f50282c4141d905804000c054030250f03035448401700f104c000200007002964201000c441c00c000f0041e8600041da4904401040540c595070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 868862535 1250 868861285 868861291
    0xf050f071e05010f0e0d020304182f0424080c0a0309140d0e010504030302100f020c19050c040b09040b070504150201410721020d0e070608 61
    0xa0580d0420a924050200740030300c202002e0010340c00c1c80c1807200e0b1080c403540000750101a500642d08250a5418117030303501d1041c1e21906881d90300c0e940d40010a11380641c480340c80300c0c00701d00c3d034070110361000d00c01e070381903c921020040b40040c000641041086c0441404a1040c4c0d01010990700314018400040c003d4100100842220440000d56401c0303103109501c80c5100e5a4408040344041ca8035a00c0c0c0344e41c50070340f2007145010800842190b9840d40c041c1084c1d400b01ea501d98020300d4030654403502c0c100a81000d100e62000a902072003001c0d01c10700103200f000341c5848070300081044280e040c05d0851a01c0410001240554901810a04903072103d100c2541c0c001d80000489090341c40f01da00c12102da110340d600071103400c2295072404072881c1d8107400084141c104c4010341c106040c50801c1841c0003400001412004d810707804044a00d80940c500d6881d44244641420108000c540841c041d581103000c1007108072941c00a42024156182d2140c1e0701008008801040340500300300b8064142907000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 868863785 1250 868862535 868862543
    0x13110702040c2001060e090a0c06110a0212010903091e0303050f040801060e10080106180c140f071b06052a07030c17013804050f070f050f07 62
    0x21459580ba031402600f05082200c2c1048080d0383c1000045085402480c00340a5080b8181441e0301280214100003480070b8905d4100c41c0240302c042c5845400d5a4203000c1c1d00060226005034015180540c4d14a00c018880110541c00440d180c1c03440d2900500c60a82500302485140c175000c15800c62425400e1044240c1c0e0b40750800503039441504030000024011a40300100c207609050300480c0c6102c04c0c40320107020f4002ca0030506e0700c1d0380d200e00c2c15909a5540b0300402118040c20b0030380307841e001c01035000035130228200d0400c000300d4140240340081660003c00c050a43c894001000301c10445950000d1005800040d1058011800c00900a1030b91248000c42004102c4c0340702e010700d0011031401c0d400b0f088502c3d0b004550800c0d940c4d160118041320315218200d100918222411507035841801180c0e25100e01c1c40144100441b45a2808201d124100c003110544940f803801c000682c942c1d07c2a00e005a010320454900703440c100708010004400c0b08203800030000c040c0501400c1c9001c46094810050340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 868865035 1250 868863785 868863791
    0x703080f0909060301200f1c0b01021506012115140102070614040504020702060f1c06080a0c05120102160f0209100317090d02040c0801032114090d080a0302091311070204 75
    0x844a41f0998010307805c0c0210b04d84191001381140c6041544126041c800a80a441c0300c0d0446034040d0300e214508403080d6002c205002504038a40031881d801c003003d0760743c0c80400079424070080d05480680f0050f8121484804075080e5003095980c0400007000100114500128105400b5480c107000c1d018500c1000d01440d0086040e904540d1150b050740d50360750b0605000c0b501e90701c015141002c2284000c213800704003440c04001044007240887c401341c0d0340780c000191040e0b0b107250009000c0600c1807d414580300d550300f030001004d1400e403403000f4000e060040f07541d00168042401003007007010002e05000c001c1124540300308000744c001803800c058003a041d400241c07284500c101007503081010500080d40181303009030701c032003207a0495440c5050b03a0040b0031442485140b04400c03440c4050800c0408040f0300060030702c2d8040030341503005220a000141458400c01140c0d40d5095454000500c90b0b80429000b01e140d960382d0508500b180402c003c600014811007000900007400d03441031020190040b52 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 868866285 1250 868865035 868865047
    0x5060709081b3606040b0621040c050d111314010b28110705150708090f0d0524070c03030b03120d020d1b090e07020703080f090906030120 61
    0x2002d0f007411a050100c03212694054658070455000b504032020b5228525104a011107414030409407080885454a0401c4400e01c0315a0301c1d0b07016000601c200c4131841c41441c0407a0390340750600f40c034000602c11780c035480301d19060b00c04002d6140c1c0c81000c101c410510344a8000c85450b547c45400f030440702c01c54106a80d414003942c00c40e028452028a070f00041025041c151041c0c0c1e0310007036020742801d10105454680d038a40c0c04001da0120030241009046500340610030200b00100f0081c0740c020401051a5090032a0350f0218035451a42003054500781c02c040c206411008800d882c120010500071004512441d00007405080140d4544000c1c003050b41d94141d00210b6101080140c0c1050789800d43c1c1c82d15000700c0414000a5031202c8588134005007000000c0c175440c00034420815460016480d02c28000d420104512455500100010114820030700e0000100381418001c24202090706450f0b9500c190141c1803140140d0040c140900036031600c03141e001d021003030a9004042107807441c1407654840d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 868867535 1250 868866285 868866319
    0x11090d140a12050306120f0c04020906090405070201020306011b0b0c03041b0906090b01090e041101140d02030f061c0b0702010e100911091501030209011202030405060709081b 77
    0x2800003000201032605540b1455022600300c8080c41c41010201e810308030604801d0200c1c0d80790078803030414045580c0315010030402443e203a0090203256501521581c1480907900c001070503078001740c1e01c080242c0d500000b845050359108980c031b00040b078207a40b4401d00c0300441d40d03407035844039004114164250000c1b010508010456080b00b0004061030014191030f600d40600c00c00410151094282c417900e4402d000364194020041c0d0003c4031203094440800340e56580f144041c00c0141400780d81085032007a810929400341c1d001600b001c2c182044016101d1400400a120300c20000d03102501c201024038401002d421314451004c5440d501c1240b807115501c0d040d0040c0e000d408105d02c007120350301910030805084822a405100102e01444070404c0010615060240380c5209a402c1b8141ca40320b801d080610f94003a40003824010018500a000b1480200c00401241c2098908540c59045841806455580001078101521015000e031100856404621120403d40301c0840c1c016288203260342421 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 868868785 1250 868867535 868867543
    0xb01030605040911010f32071b050a060504081c090f0e09010c1803080a1404140306060603070e0111100509070618050d020108270c0411090d14 63
    0x10a03001d881401048044d04e0314026081d0390b452400d001409601200304104d10800d00584658100c4400362221010b5501504043c48600c50040080c03000304800c0001503440b11080402100f0341c01995885800c2c2070404c214500c4a500107020090148001d07c021400890110603916405114420f2010041c0041d44c181c89543c0c80754014a580d02e0002450041e8400410f00c940c7c0364070003c000c140c2c40c80d0782c25101c1414169180e00d110a43c1c2005000107008540142423080b91424018032060740341e003031a9a41d50241c1c21100c0c000081d8844001c050a08000858101800b00c0310b940c1985460700d4010182001900824104245a451400702d101c003401413120520801c01c00b400182750220000d940c881c00382c443c4000040c007081429840850140c41201503d00080c9039414400c426001110300ea18050000c02c9a0b5887c01c09640b401304417010130480102190000c1c1040484950400c003c985a03111050900b0340200070744410b940e00c0c1e03844e2000596002c18000752014440b08032500d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 868870035 1250 868868785 868868789
    0x20306030a0b19060f06270909140607090b1804020f07110a0b07030909050c160c21050d08281a100f0e01020c0a090c03180b0a0b010306 60
    0x8550504140610f00440c000650980d1010f031a080c404583d83e038449400c00c1015104000c00940c0706251b0049124960080700251140554110011502d400002c0201c0303400c0b0710200e407406215614609050811300040d540807842e8240814110710302005099103100f04080081c1419a16510030391694881e410f80704d60090071130485031100c14601d0080310a0300006113a034810710706104000740212002d0f0450350165410740e20880e40c01d180210100c040e0202070421010200c2c284000c00c41800112070010b1094012003103840c03c1c87c500f266590350b00e480440b03400d0251032031191000c082140000c8004001e607061a10502139540d414580b078204003400355190100c0341e0346142e041110000e8000c0d840900b06c0508a42088814604102c9039502c00041000031400c9400c52010300c1e801080c101c01c45c0003040c01601c45443e01200002c103050100e4100e0703a03115a6800b10321580c16032505c5904e542c0115401c8003109209251640b80101900421101000ba16961000d5207a4460341000b40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 868871285 1250 868870035 868870043
    0xf0403120e070f03061503030e190b0d0c030f0c0e060702010e0a080102090907211e020a080919030815010c060504052407170c0403350306010e04020306030a 69
    0xb00340c2d2500001e01480c440c9201c1550300b81d003801d66280e10f0140c3c42d02d440b81103907455143c82600410003004d001c0c424041c89418080782e92500700014000c0b20a10080100c0b0028042c0040c03403034400e603000340480d140041e000c0101441e003a0102c0340709410825028030410102c0711140c4030b000901c0125604545260301d260002c1c9980c6002a072404150040c04a00d0400c84103001c4c00d988464080707509100e81c080c8450007007620700d01324940483d10fa005840d030a00d16031408021821560003030040c2ea014581e00710000700c400041181001041c00400c683c0710a600c0703001c4003d00325407001030001c10050958013100344100307558801c07a030040301c103607038450b0f4000828019494103040c80364540008241e074074200c842c1c0203459100800300b0003010348550380580786d070200701004202d5840c00320001401c00866800802010010503004404500b03a080b5070300124501454a1003002184015100c04d100c9443c414004d100090780c00400740c1400034020f55005890b5a54040000d05e080c81420010b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 868872535 1250 868871285 868871293
    0x18101e051c0e0f0d0302090105040905071e020a05150606030103080a12060303030209180c0d2004080d021002031e07020307020a030c1e030804030f0305040e1509010602060f0403120e 80
    0x307450b05402042000d0f502d5254000d590115504400035400ea00c6000c005a00064003044203000c1400703980c0c00135400c20050b01d01840b038a500c207203440107483d00b180d0a9102580c400703503102003000410083d208030030b6204c0c442410b46003045004524903020600005040780c0002c903842d503200f0710465039034800c40c0c03241c5418490250341e803e000d0001d5100050950094080d012209848200704800b20b000d01402c2040c03a15100d081820381e401070092401803c0035035413005c1003041078800072000c0c001900510000e88550451090003030725044440145254482c014001c101c0c1500c00c40e510700503840d0040d6500c020740d0b41d03009412410b52041610003507202030a44000310500410040c40816502a8181100008100c1600e403119850911000f822100c0070030050002800b20155415114801c0c140742d400c050301c594003584070100407514604081c0b80c030400710f803a03450680401401000c690024014500b0401224a00a00001c202806000c010306880c0802100c0358002000104000155 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 868873785 1250 868872535 868872551
    0xe030a0224030103080d06090504150e12070b010608010e04050705010c0201090e16020706020f0a06020f04030b010311010e0d1e08041d061e03030d05040f0818101e051c 74
    0x10050640008060548491500e2008908c205440c82268056508406089000040c840d035000140901001c504141d0003526402070400c00d4500c0640140b5100fa85a40780c039604112004101280c140c1c00803030702404180500c03010031400315003003054400a00e024036014440b4001a10020516441480b882e06001c040151081e41c909001501012550a9511051380d07200200c1c0e44078140c040e4030701e0f16045550103400180103a03005040c00c120082c10141041d649458003400a00241e0059442d0006014103400540c0c1c420860140c2c0c4204035044613540b0036135268201c034a20403148180f82ca2015640b48418001e4000946009000c14400030720354203164002e8114819094030b1880c02022601c2c0e2540100a000b142d010f01103401030025410041c041c0111806400090415140700164001003004500040001c040c0003100300c010030a003207204000d105103002d00303003840420080c070034644044c1c603105641c9000740c500042c82c009864240411050400b04065682511f4140c0707020b0003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 868875035 1250 868873785 868873793
    0x8041205060610110d050c011b02070801050c16062004080106080c0603011a03040c030b010909110901030201020304170114090706110c010c1518060204050f010e030a0224030103 78
    0x1caa1003680c1c181c0e403071240301e480e00e90140d03405650749060072140c1d005132204141462251000c0c0c090b40d41d25000106803002c0401440ca01c0c14014044200143c00150b010701c0921003d008050304502002c030790070f142042c49800403d950182c00401040384d500d4826030070340100c4044a16114800d140e019607595039544140600800b010f108000450064035000403c0740b524205070781c125070380407115420681c0e484d41100700e107034401002211002e010382400300c045004000c40c036002e40040040082e1890507820000d0140c02e44043c0944a01004801400183da011060750100c03419039548200207100a05000d0250107404034003540080e0042c00c00a2503000040c008040710300c00d48600313201b41000001e01d034544000d001c00030b01044e00c10141e500021559554900c07400d2183c0c400191052918100480803918580b0070380d4400c0e0042000d011078a405480034241090909092503004070b40e00100380c840309888000fa20903150b1442e0806104003115590210020a000c40c0f40c0e00d603101d00e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 868876285 1250 868875035 868875043
    0x160509010c03180b130602031303110a0806010e0f06040c0c230a051c051306080601110d031a0a05090408160f060903020613020d12030204180207150b180408041205 72
    0x103025045000441c00240d071b85e00100440c0c00d181c0111040741c0001c0d066444032500340703402d00c0640b5000002000300140341402840602d0103003241d807110079460300307240d05800d040380343c0604514401ca00e05417070f200e034994110108482c555484000380c031403201c1e0020216000d200440c5000710034002d00710060100080895800010040d9403503030a840c903000303402160075001d1800200c00c0b01003000d0b01407041d00d014495440c2c0c4040145014030101078900000c500b04028810301c6400301c0e03100e000d0740443e90303164141a1000842603030410005890600054518000600094841503000610100c500c902249929003140c10140340415a090b61070110018641c129050b001070145070007286824005401e2a0f80e015002000c503160070415440380c0c0410405440803205040d03007008001420741500205040302500c00718016143d1035076040c002041421151403040d5585040c0111030ba03540d81c0070082c007440c1c03c05a10001a903507a840c2c2814103101c0d0b80c0028680c0f4503030000700e03410003100003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 868877535 1250 868876285 868876297
    0xe011406090a05010e0c09190e040b010915060c0c08030a05120a06030305041403011506020c03060a0c0212070309090213050418030f03020c150c070506160509010c03180b 75
    0x1650100c0c481d62244081001c8403c00e0150440b41d03000c00700072803003845000026040001c4024008507000c401441d8490000c0025809202d803100c01c5001c000a103d500c1c2901c0340103001e00c5409200071088070b8098250400107000d02c005001c192a2601c007401100071103c40506410011242d03203006044008e0401c0e00032519400c0100148000507521083c24055031040740d515490b15070900b41403400c107048600c42040e00c950559620038950032003160151b00d5000401954014180410f0200140b43c14400020890441e403070502540c215520b5000484403150302020713890b00d8480550b46422030302030005030710800e0310360b002045807228079003500000e00c2100c070102e40401030013814844800c1680c00054004d8045110034003001040e5000e5001420304089100550b9184101e14000040445059880c0f180780040420500c0401004109107500b00c040c200c0e505240500d003080040440c03055041050401294103140010107000d2401105555070241803001da441d101c102844103034020f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 868878785 1250 868877535 868877539
    0x30c0902030919030504090c0302090a14010e010c11010e1f02030301091a0d03030203060a08010612020301241e180903020c0103020906030612070b07140616210e011406 74
    0x1d5103c004200ca00310001c80300c8a0344c5612800d040130300d048000c400404e296000841032503000c11440c822070741c85104040c06800310203414000302e480103000400e00e00c401486d00781840300948003c80410124078030622111003d2911002c001100c0b4081a00e001e1108011070038002c024a90701a210380200c055410f8554a035001c000400c59191fa04ca11907070342c115159040045001c4c5080800e00c6500150343c4908058034401c003242d03030340511608545181c1c3c001c0e200050814503140440c41c00380500103030b006140320301c040681c1d940408042c065803940700d0b420780050400c007106014840350741c07000003c014200d24500da001d2106100b0016181d500d1080307005000d006203041e9550300910035104841005040341781584d44e4902440003a04d48441210018404d40d8000206042413100810b03109109070300d030701000e403111840c1519240d0041c150610014100500d000d0349039000e4401c44c06a201c01c83c0c10568840600d1550000381000d20f41030750b0a509040f05490034092503003416002e0901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 868880035 1250 868878785 868878793
    0xc051315080a05040b07120b0319020a0b09010f0c03020a0c080d14030709181404140f01050610030b0a03080c01060e090c180c250308092d07030c09020309 68
    0x1a11110342c2c00c0b1101110000c20040c0440c0110b500b0f1803189941e180f4100718000000391100c442c4002901d0304280c040307844403500c0a00005401c500300740e41141d00802c5030000050600851a001a01d21207200b9908001c1000f0501b01130300b0706100704070070005544c100c0d0110721050b495844064642281c11044e40114035110348503000b100c85402120f00c42d80460340c801550500b494900c3c3c00001c01203522142c3e0329110805c07080928000d0402c68000c078420f441400042c80e0384280c003401c1058107084200164540000c11006841c4d0188a0748040c001c1d140000703404030b40200044801c04660405001b459005c58100c40c00d100540c4041705955a401104040b540e03220002d030384c0c91240751030302c907000074002a46044111502c1d5807a500101807014190401c54081c070000c0031040c406080074600c0d2020440c110904ad040812a6002488000605075100180181401d0000008807411060b803080403582d1400c01c05110f414007940d0310802c00000e00703a840300c9003000b940080e81c0c079540d80c3c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 868881285 1250 868880035 868880041
    0x1060f1e05030c011d0a030804050306070f0801060f050d06060807020f070501020d050c1006031514060d0f030908030a032031051e09090f120906070221012d0c05131508 74
    0x30040e100c8543c0c41100341d0753f20034903a09081040b20350132080c46104051000500c868000c03d1840d000d440040e041d01d68a02159241001c0c00910b490030300081c448980e00000e8092002e40d034081030100c8040c906007012a51071704105030462078000d050200d11501c0d881d240001c810010310158250a2415621040c031600c0500d982400840340281d6078580d026503516405000031301140c0c9141c02060190603e00041941e032200907055038800516840007903a215034441e580d101c44c614447c1d01c91902205a82400b8134442160f9031452201050103a00c1d103850714444246080700010005440d001d01046200c80e6035500b150154955404200e200d121a14002101c20b44002148004200200000c11124010b4050005281e22860f00ca9811a408000078805078035100301e640503440d56000300d030a11050014045085403d0381c06c00116007905525000112074110841c5a403500f0348030000a0340740010282582d051040d020036102c4801106000512608180807140c881c0c032032516031505030340d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 868882535 1250 868881285 868881287
    0x6040b040b09010e0717040804060f050a0203072303070308040c140904060b1f0c051b0607060b030118081201060f0504210501060f1e05030c011d0a03080405030607 72
    0x2941c07207001076400140c110010855248010105a0042802d0910100740d01002c005102081c03800c840640c0c811400207000c00c90281e004145007403186680c6451410507112500007500ca200e9181d018101400002c10035086c80884c1c48400421544902101c1c1d07507101600d406411035004480c262049850180d00091820444040c00f4680d000108000030703941d510b50705d400086c081150000e40015a00d07600300d2051416a0b00000191034584480520b81502d1410501c3c00c1c400c200000e03003658003108500c60646520082d0340001d0f5101501080f4000440f002c2401019140c43d0803541540c00100c1d4000e10407400c00412486040500503041681c0303412096405000d01050300f40001d0040201304045554400c0601c509507140c802148070f041140c81c0c05080d0341c03003a000001000c0c060314041003428044012407280f103850020702c407030107840c00f00060340b00c0c0780001115050101c0103090703803420524491f4100022038000c0c240b154250326414100d1607a002400f40b240644035240200b1325117 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 868883785 1250 868882535 868882541
    0xe01270606230d0c080a0b240f12040c05130510210501110c010605150a08190213050108010506070c03020f03010908071a0115021011040b03090606040b04 68
    0x1858454a40400340d440b01c008600350040c009101901c009018807079005140082e02800e80d0000485c0d543e080d050610740e0100e422a0040c2405910404090304080355108404c4903030000d01c0365460406844003041c217410398030361207880180698400490104810803015004c81003d8070805c0d52448054040c1003040e000b214411b0714201072140d0a1002003025903900c2099414044c0f41c1d442003496024180c0e078041c00d66a8881e1f000e081e558020440d180c00400c24440c3c180204802ca84c10298001860b680401c103208810301003007001000c0c4009001741c4011075480314481c031044011507440c140c00110595002c9503006550000307650300c00015161808800751180503070440500c0d904a890f41e0b082290701c8050381d284bc0d400d9503d58180f0400700344070a005c2c2c80389602408a034079607030310018240350001d00140c21454401429440c050051071307001030300441182e43c0c043c00241c00b030802c0000800f280070b56070000241c024000204a2061070204401740071f07d5040c0c03010310420300190100015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 868884892 1107 868883785 868883789
    0x70b010806060f010c0803060a0e0a09230c12070f08070f15050301120f0204050103030314010602010b1c060e03071a1f0302090a060e012706 62
    0xc0a01400203903440081115030051880440c0300280172807540040c0507140c024084002103207905c45840030b0024103194005c0300070910b0301d86810320103001d0400c01102c1c2c1d90000740b08103905050512015200c1306550000d04a0040483c041c44450040d4280c18036246c8100c1c0301c0024000050907884010b07226003005022141d05000d01d121140d03845901078005000145c500c0c1640383c0d4000c090ba4107503000d60140f144880c1e00e0b0b0030400c94134014500c0c041c0d4414503040c0000205501544018a5004103098108542e0b80c2c512041c2e00700c6074281a03907500101160204540c04511a42c5541c0d024803d4034001410242c0903440c42c80c54100d404100d81000342d400410303141007400441e503a07102c070110a03103040041d40618038142400329403000a000b000c0030340101d8401c0072203030055805420340d02c1840c1e50560792030a42c061413032000c1c0c1e00004d40c0c1004250030440200e280c020031007 = true := by decide +kernel

theorem cover : BRFrame.Cov 868705035 868884892 := by
  have h0 := BRFrame.cov_init 868705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 868705035 ≤ n) (h2 : n < 868884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
