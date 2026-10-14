-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1377
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:39:52.379946+00:00
-- url     : https://prove2.me/submissions/d37043a8-d73c-49e0-be7a-6a57b9b9d41b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 247482014 ≤ n < 247661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 247483264 1250 247482014 247482023
    0x1f02070602071703040902030a02130f0f06030506060d0507020c120c030f0102040303020613020d150c14030624070209100303110c061603020106081b030f010b011b170706021c09 78
    0x3c005c01d00480502e5406140c000043c08401414800040488001c4280b550040c8009030302841f003c100e02800300240101504041c40e0038086420312402043c55405620082040035841d8000120820300c20040000360602c010702c0812501d6006040c0d1741c40350b0004000740c2c0240507070410045050b80500071501101e51540c020507160381c405a0414105800e103034200d91003028507442e0008554500602010124403020000d0a0400640064031602c0f00202c0d40000c03c0c3e060007008043d40e100c4c22900320000480e180000c000900d5524107401307100b0f2140003584420400280044881074041c4402500d12035225200d161240c518100d0313a5010001e036066000b2810040110300360440c00c01d10300101c0c82400040b0f2000d440e11f1100e0f04014422000240c20411305440743d5243c64108084030382104100001c00041c042d0100003402503850a040c017100403442810b4400b000005000d031801b0760030719260f03141c440c00d00303141030700c060360189040080c1c10703014541820407080030344030300c60009902 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 247484514 1250 247483264 247483267
    0x1e0a09030c0210050f0d0209190e1303110a03050912011506110109050f0c040f050c0f09030712150c0f020601090f0b04050c0910090f05040b1f02070602071703 70
    0x903402c0000000e0800f1085040040a000300040c0b6074645001c1c00780b0440c0380d003001da15a410407085c00a111030f1054090b020703801c002010080340020284040d085003c44904131030b11140390034140c07030705000034100701c213944a210089814558800050607484c1c03030480302585421020001e4600f079070210f184044218000c000c041082e01d00408a606020061030000b250b8409182c07542c2e0704121440392800081e800c02d148888003460036116018030101030b118108010b0078000e4151816010f502600803100b400040c045000e40d50030448000103000401c441039108900c0c1c0307842420f032400a54035252071401d00784035a040501540403090610500d03401040b240e031a000070140500114580e996141d82c4d110314600c0103454038003483c0d20881481045c6540c035910102806041c801640050080240245081c005007041e141c01030120b903000c0300c01081500d00700300002d85400000800d41c0c61104164440c0700001d4010400404581c03840e0241d45101d0398030b607031001e04d6103c00c0701c207006580c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 247485764 1250 247484514 247484537
    0xc080706300504030e04140709090204060e0d06021e0a080109020702091f210b010b03090d1103090d0f140f10020717030708040b0105010513030b060f06031e0a0903 72
    0x40d6036102c242e11902901d0003544000d0b00c1404241280ca0721801e0a52000c80e407020060100c0e0022030100040103818421413425160140c014800aa8500d401e8030512280300803070709001d42c50f015581052241d0f11101d03071030001c034400c11103d40d0004003c10042080300c400000c43d08058801e9a030000d401410b1424155285c1040303101c021200700e4103007104a00b060000c42c411046142001d8200350100380b90109802508085d50800d00590040000c11020410848103441c0402e00240c902c840b42401c040da402015003490560150760045504a0a550444014494031001030109507004003603c40e140081210b9454903400703140e85000c1e85a0041002c0c0c40054483d50003003d505000d454502c07210003c6c0030206800303900648000300000c0070710b400e0005100782c1c104170303d0052400742401858080c81700d0010000300d00c54070015180559410000c0c3c1c071a00c494a507900d42d01c00003072096540f0f03e0400003003941c640e5000d642442050701c140c00107150840911620030102d4060700e0b0a0045d1a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 247487014 1250 247485764 247485857
    0x12020f0c030d05042d06030c080a0b0a0b0d09061503060b0f030d0e0607120512010f06080c0c0c0d12020c01020111070204020f16050a201810030c080706 67
    0x100c0914080e5000110001a45c44d92101e55181c08090301c2c90742c0e004070703007010388280040020b500038001c80102450601e003142246d1382c07142110304036000a08015203c4403404803a00003000000e00c007401817400c1042c5d45e040130002c1d14010307058038071480c5c0401510400005002d01001c409001541640c0450b41448480b4040e00192004140080c48a8681441ea65501001040021044000c94000300c2c4481d504138800310200c1c0500742007080e40800601c0c0040040c0a020080c111416142001a0300d1074000f200b4054202c41010140c080322015860385000507455002c2c0603040014012604407071003d62060052810003081b200e40355007003000e20340030403009501030384410450349030401600c20540610701b14001b999008401401d003018041c100b00541e070300b129400680305d4020404094031686e0308031000d81041764000b8461030035a150340141141c120650130140402e0248100080c0d0304100284203400e58074165102e000584804507580c090310001c40480e2400702084100b10300c0b10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 247488264 1250 247487014 247487039
    0x303070e01110708070306020306150705100519090f0b100e240907031406090f0a0f06050a0b040f0902130902160b19050c030c040302010e030a12020f0c030d0504 71
    0x40010250f800081c0c3d6420141c4c0352607a02da00c201ca0082e0080100300c0c0f2460400102500c0d1256030001c98540f008a5136440d48030481c0d0140201c04a9803a408215001511001441c6004070308008000d280d800341841d650404920070101c424800740070003d02c18903d07140d00c0900f140d440c581031714840e0f114000c000c4006014503140007080c10031384044401075503400e001036014012985000440c800303100000e6000b8000103184600481e190000d00030000c00c04101141d004034072290000d00250303410140400340c100c0703501035580022007001c08950030078550f008104407103003100003000860f40c60b10a08103074003e0200644c419030380c8040030401c102d41a001020b0180c2d40b21070341010810030b0740e01c5107010340042c1c2e2910400710804034014180700071440b60a4001d4001610f883c2107181401815280d8032850100030704100b041441003480b07440070040f0403103183e4000c0204101012401000b540c03444010541002d522072940c180041c0d040200c3d4141001d41c595642e14070305400c02044201c40b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 247489514 1250 247488264 247488287
    0x1109150c030f03100807091802090402030c04060b0a030e0a0b0720010216030e030606130f1b0503061005040302030a0b060303090a06030b181909170d0902120303070e01 74
    0x40740000c110014030751072250000e62044507590001c030780084c18000c80350314002442e00641400e0f031400b642d4401c5402e6107201480c2499044a10680ca0f6517648046030929012820040c3c106040031004264545c120000d00514002a502008000141d095040c0c0d61080000080d001841d1034000c103071200d1042c1c855406c90350150b0054200712824005880c00ca910403403214032213265615500003010b0340006914282c0304118020b0905003010300000d841c0310042441129807aa54516150900b031140e0480e5020500c000281802540e510301e0241459004640580c40b4281080d54403043c2c0c4c0c0a1f0040e03078245d9401400402c006401d5aa400b80d240c0c0f0081c010b694544001c0c0100c920755624144042c1c0502101d540206131841201d00340100c0d5860b211080c00721040c074400308502111092000800d46039131071030109907908a4100300d14401c11403c0e00d0f075101c080008a94110f541b298010540d40351096421603620401d0202c0b240d16400f094412030b0010b00030610110456200c1c0703617090304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 247490764 1250 247489514 247489537
    0x50108061c03050405040e0c030d0e010c17070b06090705030604200d060906051e0f040b0a0314060a0203061804140f0f0c030d12020a0c0f050102030406110915 70
    0x741140480d101030307000d03203a40c40c0840001c0d400140611180c2454040c203140841c03420014014282e02000017034440662031101c2c400c0010102031750401c1d038402d004d40c50565400400035101c0c102c3c2504100b4855000850950301c141410b00030032a00e044c1124002d2050038942c2d035550654944204020103850140308129200d0f80d46010107802c0d00b41c40d00106013040d4a01c00c00501d45141100c0780c01520038660111b40300301003c100f510030000042d08030b50319030013007207170715200196411001400408030705100a800004044002c810005c4040758074810160880c102c40d02580e8138103160086c0e100440345a6007000e01842c481c082d030300b0010300c030740e03081407007000c04084441c4540d11551031701d020052082c0e519030000342903040040d0144518800c91009401800d96450040c4002c2c0c802100d1001840a41e81d0001d0300a80e040e00c500045034031140c0c0040003c5803000981006130107908183c07010b0742c090f490882c08000d01c040c2e8100f11104480d024021500790302c2103102c40082c50300002681e66 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 247492014 1250 247490764 247490779
    0x30608010e0606011403060a051c0b090c0609010c140d051206060403030c02130b04111806041212020c030a0303090501051311011b050d0908070e040512070201180803040614031005010806 82
    0x40d19070740700100303c41480c00c50404012b081c42c050500d80402000501343c401e05800441c080bc90b03540b9a2000c407002e03a842802d200041ea100f80c600f50116076101c2510608034003c0d5100d0f4100b0b29030113001007800050078405400b4503100e000410490b4851403000501040000608030010b040007503240f114200820320001d400c410140c04103003982c01d41641c002c41382c100083d03603810060445503104c0298809407030700c078241800c0141d000e11080d9407010207040217200d22070100c4d076280300300200e01c2c040f24060241c1d02d00521618021b005410043d508403a00e508004c00160382091600c0100c1003180c114050320039040b00780780159030400080c026800c0307056030100d089010a0041240d2031101c012a56202245481d04030f03903034103244d0550400c00312207440d442800041503000414460368800a5207903a0f6a50452005880b40c0b0b51042024401194400c0c2c002000301c00440908100d0b01241c0312141c0f03850542d103800c00e0521040fa10780c500104040d005000d294850b00c525607003e913000c3d180f030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 247493264 1250 247492014 247492019
    0x1021605092e06030605040e010501081513050d0807030c0804030e061e0c0a2a091109041b0906030e060a0f180c0302030c010302030f04170415030608010e0606011403060a 75
    0x10149151075070403c1001c40e848007410401801c1078400c50700380d5000c1134020030035541030040c000e455144e0760b00f40b4580e000400c00420061240c40100e0142164840112207200280300c20107004100f0031601c080c01b1901e018400204140541d44070341c400c95055480b68082c42c000d90412841d40c01110004500400c0c07002d2500022112000502e4200584002841030302d04500c0e207400c182003041060440e007448041001248140070105000b56401c002000c240c0c41d0841200424034025142c4c42035105040c4515a80f00745401c41e00210100115902e40c5030503a00c0d01420780941d030006110718490750001c40000e001500550020203a441c0581c000f04444604164400100182103410b0300c4004010004100314602000840030541d4203082c19801c44c5811505005503200051000d03103440b40b80d45844880c115180c0c121005483e05c0e200c00400d000034407600030010655402600155840c040000141c008005040d6110304c0050391208648115010070001c20b8101400a940101060002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 247494514 1250 247493264 247493341
    0x90c08120904050a14010306020c1002070311010b030f07091116030503010f090b0a180b030106090b0a0b0c0601060c06090215030f0f0403050306060c0a0501060e060102160509 77
    0x3010341628004440035211024401080b0464401909a00c2081d241c4099580d024907001d8406045a402c6240140c56603802088a4142000307003080510151000840c0000c040d04982085002040701c0d008205010120061540d20040c4404200d6a503004d00400c02c0284100d0300311400400480c250282030030a81c0000140f54501c6410441c0842c0c800700042c400da1a004202400408600d0401c0c400d051441c804204a42803e00803416180040d4105400d09a040e4006200003200035000304101c9030740b20445802440b005140b50710a43c032041c3c0000d03074502a807041d01e00b818100c0010300b09507403030400d0944200b80f4415003122915110940040540d40f00501480311203002020240d507490b100c465081020320080a8519a035142e01c24800402c3e8003c09480c2d000006403083c981e10846541c4581c94120710b19001000e035801c14501280000c00044500e018401c2030302283c1148140e0801421f0700905800307a607802210050005901c0b11000c80e0b0807900c403800b041c0098018084112 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 247495764 1250 247494514 247494523
    0x319021903051207090f0e0411120c030106091a010e4c0c06020d0e010501080c0f010c03020a0209070507081b1204031a040204021306080708010509040f06090c08 71
    0x101507002c40d101040740009243d9044100340d0241c0945405061142011941c0c0c060540c81d002d0110012400000a410400d1250400d10b1009005001d1345854a8800403d943c07210044040b50083d4284580021441494000c1c81490340a06201300c0d0401899401100e080c95002e4400c0e6014154618a90320700411750000002c02c25646a1001c940250403130103e22040c224400140c210000700003032180507403140310b080030f180d4454005652202c0c944c8000014003094240300301154a0117000041420700060007903000c1c03c1c2614120a001600401580e125501402c040e016030071405c0204018074201d070f2880e40c84811400c1042c10000103885800c416003081d03100e43c0d625507160504214600b0200840710459000d1415a46002d0039030340c8108800148901220b1540000700c041400c654664054841c1d030505e00341c1e040b00b1141d9624000f0180441907038510045207a001c000702c0d030743c02c1000b029881540c00c50110400d8480982c1c550009140f1071313909441c02070700e160380459110030030310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 247497014 1250 247495764 247495813
    0x809090703111603030606080601020a06150803040f05040b15190c0b131103060903120603150f07120603030e01050904150f080f01020a0915020111030f0405010507020f031902 77
    0x3d80d0403181201c0d52502a04403500c070b40199041c0139500042101e0b5a84c0060b0310a138003541300c10b0208400702071030070900d110b1401c1d03007000f0703440d00001c0b4020944402007070b0031030111f4100f1034041c00f071203a01400388600040c1c001101541c2140410240508241e6945110390f05103091410103000500380e04c07215a480c0e4191a104c0000c4030b41000c01e0107000c0041102c4144440842c00380401e4200b51502e15541d01c20b00c0010142003100b03600180580e0760a01241030030f40800c21980301b00d468a40072062407030b40102c0c0e0700e80106405000071000c20000e481200c080c0c0343e16840e00860b048142c8010346aa410014105510684442014407451130440c5c04c280105016244810118100b81200d8144000038a108a140c3e00c14403441910303503030108889086644219035100c07044070744a0201d000d883c0d242031b420400900001031240c0c100c00c1080d41d034403d9000d4802040184c8480e00c0403a103c00c081c000d94507507988184a04001c0301e442180d0419014564011101c0440d18100812034245101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 247498264 1250 247497014 247497037
    0xb1306030b030d0e010e0105120a020408060a0905060a1a0406090b120f0c010e030a05070806060f01030b0a03020906040608120316090308070611040506180307090207080909070311 79
    0x4102008499054001c201107204200c010f80b0308401c0c1e0b150020b100642401c1d10604005070000c641c4003a0f4010030455030304412079900d8008914204845c2c1d40654400e03c6940c9492103954002244e045452241508540d03110000c1e00c03040c0c680004101c06407154179225544202c11070904d00d943c1e40c59100f054000c040154000c40e0707030780ca4030041020012491a604100c2d4021034400344801b107000c103841c84d100ca424201200400811000300c1c0c60030840c01401819403003080710120303c11030006542403198104a07082d00d04100628011415680081800c98124030302e00d03014030041c0780c5050020350155020f0000141075580c1d420141c9000c061a80c00030a01a000041c01642c1c0c04c0c1402c41c1c0307140141e504041d509503265654140062081d6100034092a42d5a0030700c40300c04403103100703d1740102002045c441d20f0313600c8204009420002c0c2d8030114441d1040010016182e8854000e0760079035608078040b01d0411a03a40180000344400800010405540f00010544620034102801c5030886a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 247499514 1250 247498264 247498297
    0x60c0d030e01060b040b07140c090405070807091b0809010213030b0a061505030c07020a1214070e10030f020301060902040303090e09061605070f021201090314090f190b 74
    0x41101e0942140d10a400650005004002c2481000400300845058030ba12002103819001041a070341e08144181c1c0c0c0081c2d220745441c0c144030a011000424005940c4400151203950b80e81c0c40f0f0180c102d4456859a200420b0039240c1c92018034005c50b826036009002000240c58449002c150014409054000f211541d070f1110902a2000c05440345c040500310301503102c148103d00c19005051408000c094428107000001d4080c01c6445003204040181032400240c00751112500d0301400207160340c0c00f0303403d1030320911000140000f01484801d0140301101d0810319200d0446d15000880c21007241c041c1d81541d02c542000031400881d10081c002103010790380b168a51820148261440d0002034001e074501e61000080c044460621051202e99414504010b40e4030407052400200c198107540c4080e42c007492810340c14813003002c19001490068400c0d9505015020642c60303080541c001d203800c00b40c01a0b6800700c02d190300e007001407d08032015184408240d0207583d500e0404040c0e4013a05c000c0c069800e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 247500764 1250 247499514 247499531
    0x240907020a050d0f0810050612041b09020a1b022206150c020118030c050636030c1e04050709120609060507051804020a030e1608190c030b06060c0d03 66
    0x34404804d540100035126030221b41813078800041c10501414000c226048102070100e803c001c0c1d95103189110341002ca210400c0d1a41e076800100c02504011100c0300401d141c2c404d00310840c4100020104840e50041070881580076044150049040240b50503121030394495012603a0108240c0002c01d100c81c582d9001544045d81c4001071170401083c501008800c000e48003400015859603290b01514415039a294aa014000c0c8051007440d0803490380044003803400c03080b8600210b0072903007540d00304181e003296800f0761b07900c041c8445004201c5100440d080108414a550302d407036000244c2020391881d05441c0503850382c0490351182801c00301151001d503581c3c10324040041c50701a4640c0300c6001e0034018100343c0101e400742c1c01c480100050a220720750009405200c07034001c4c0d02c0251103403800000c0311111191801144e0383c0c0a42801842c41510541104074512070161851041e82c46c1d102c82a5480b0038559a2031940212015210561141081c488058010403c21900120700c915580124072060b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 247502014 1250 247500764 247500767
    0x180f0601030c0e07080c0f04050616031e0e060306010215010b0a08100e0703110d02070b040b0c070302033901090309050301051608040501020904020301120b240907020a050d0f 77
    0x1d49950215031000f8208040262164001c2600c2d80c0c000f500340f06c0140d4a40041d41c0090a600c52500196841a030204401201942c12a50014440d00c6511600d1200034910880d02455020380c1003480041c215051040d89030812402642c0c2043e41030044800203501641c8442299000742c200c0901d020000c9040114180c0c0055003641000c0c0c641e444180c103078109030b030703100020f003006207840103054640c0080c888014008007118114043c5c1941151254080d02d00034120200503901a202e11102c43c0c0410404590f040c100e442d425410340040d8a8109065940c0580d00b400d8413901c0d0455080300340308145100c220719295120b9a001c030000031000b2845c540602079810315007000d40603a01d00701c00c01c0001c40c1800c44116410025052000c0607070348920701280039100b6a01c0c1c0e40c4e003050010000142d03c406c90b8800030800ea00c9080b0f00301060b5591a040c01c00c4034010780d035484042c8a8050000e07404c1c100001e0158211840d8415038218200c0368450500e04103460b02c040c1d0020700350004000500737 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 247503264 1250 247502014 247502033
    0x30a11060718030209040309080d020f0c0a0f050d0c15050c010c0305221424011e38041a0306060409020f04080a050a020a1d010e180f060103 62
    0x2160510071045642a1110300c2c2c00201800b00900555001d800326041c540158254002002c4150480340511038040009440e41035034408060184501c0410034180d11b4091104400d484080001d030404c186040c08200c20813400000680c2c0421401c800840c00e52304019200f2001c591680740c03030b07544120b0140502e0840307507482c0d401d034201450310091059101c510303c548116601d030301404403500d0b4a98104800e90a4041040491510a4410140a1070200f84043c141049003030a0800d1903070342d6451142030295410000d0060515008060240108482d6040340204180001048455000080084009aa14180191200100d41008451719032501125140b404440660442c181800461418012805503070115600411a600401505410740d00200700100842d5890b10441c10301e01d850303144441c01a402101905008103249100c410030460300c501084628620341e20300310308103048000140004d51094200c0b00444014001001070f03c1050b1044070180c80e0a5156181c1400130 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 247504514 1250 247503264 247503271
    0x619170721030c060c0e0a140307060504080607210f050906010f0506091c02061204061103010b0a0f030b1512062d03031b0309010e0a051c0212030a1106 67
    0x81c000419948002030380c07101418008651060000c9010502c05c802580c80d036101c1c10106810083c06000003500721450011038258001c06c1e01034030340b0310380c0783c002c126500d114600800b20540e00010118208522a0005002607207890a100340e055504004ae4000c0c0c46111f00709003901a11101401038418040c4050fa00426485d10715000284c603250108156014001c0c40702d106011a030030b00408004130440b81d03105a076008040e6980c40d400100c2c4001da009007035800b6204940f400c00e00c80d000d84510012281a140c0302d03000307a800d1a4800500710ba0042c0000046410140c5a08040c0c80c5915101404a04065030503c203540359940d49080075401400180703168841c00e17100312981400b000701001d0000203241c2c4a0007000001c001e00100e8035510554584c018030b0b480c2c0700d800e106240004005400600d500760395440808250104010f0070002600620354003100b149a02c88081c4058104188101e2020b840260304031f0301e04900b64196000005070710003241c5c01903440c15402d90180401a403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 247505764 1250 247504514 247504559
    0x1201080309030c0a15030f14010e1503150610030e0d05120603070e0112050309090c0904140106210b040c020a1707050304090f150602070f080604080306191707 70
    0xe80d145085005e0107000280c101501c145644c0392040000e080454001d440c4002c24982000c00c296075906150305400b104495032400e20f004082c0c0d621007817a0100728612040380c82103c04856031100d03004c010303404c10121120414142c0d01d41d11044480002e001d0440540c0e1a83c4601b40c03200600400790701c8102c00100720502c070b90880513060100b074550001c0107042d01d000003004e9003c84030616215155218101142d40c0c040c0c18035081054041e10f1400030181c1c5201a20217018000070390b25240c01c01303442170003000c4c00310320900c031503010b9050052a66041e40318600808074400041c180460100c4c0d2071043d50030016004214204280425410350380c0700c0b2500c400c000c03880e003041da03264940c49006074091100301d1034813000e1981948100340c000c032141140d00c1020741c09140e591500690745141c0c900c1944084001e0f004005100c0e44082482c0b4425504a0865403666a92504010603e0641c144541407a040c1c5080420a0039501010387c501c0e009900040c403140e401d16003000c6444180074120381c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 247507014 1250 247505764 247505779
    0x80601080303042a0f150503070c120c240608060903070305070845060415021f0b040506060f0a12110f0d0e0d0c030e01051201080309030c 61
    0x42940000411650b00076049504c0e440d42c081079440369201e190040255111008401d90041246004c0c12450811240a9015810180303400d4605171401d010460b08078000c80c07855100040419425407014032400381a2400300c184242c0b82e9221074000349494408a03003080300c0d07030408060103a24030604c00541b2510008009070303d0510340031556482402c04c0242040404a000001c00610006540c10104040c01d4101d40f0031065171101c19074081442e81e6541d9600c020311400d6542084810714019000c094a00c9241508296800c1c000c0c8110a242408500c6581309041c45203005801125001c0034941c000704041850108000c01d4a50262a140c414101001b45144446108044070404215400c100f0311200c81480c030745000b0891071203450400400020340151882e0544001d101e18843c5010400c0043d2000403038a83e120b030183c002001040e804050382002c240903450603409190305252047c0361204148003048807200070313400504103070f0000c100c1c00840c0c42e007401040f403913110591f42072 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 247508264 1250 247507014 247507019
    0x3040b0703090804060c170c030c0c09070e060c0a0b040b011e1d060f03070617010b0315060d2c0d020f0d110109120f080f0402030c040f021303120306080601 69
    0xf600724801c1c0c1c81024240701107001d040040002080380f800000c0c038000c4a1036150440d02101c40d45907400b140746483e59002e42e03180d082d140d1904c0001d90303024000542e14100b0901120041c00220341c494002c180d5584a011030170340015a050b034005101d10f00c02c4480706000c1d4900100352402c00b24440d980c224000e0b60110500481c2500e40400070000c1c841c07103011b00039032202c10205814686a02c1240d40500400201044070b5812a140260086440304140d805a0340c3d840703407141e80d0000703441c000d01c0450818038222507490044050300c804120024006888000038003000603801161441c60405e01e0100c107030303402d01d0b4420320420064800781e001800701ca11030407040d9500ca01d818400c00d02444a01381180c1b0100c0f40075802100d00590100303800030386042c0100080d250b894040b03d16000241c1040005a4501c50880d0160280758064020003900c42c014007004007600d4903d0743c02c2d135650340c00d110103c1a0a003002c9a00011030144c9502041d000604000034241c40d61904818055030019004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 247509514 1250 247508264 247508273
    0x30d0c05100209010c02042a110c1903020402311d060108060907020a0510050f07051309020711031b0f0406080703080c070f08010b0415030b060f031f0203040b070309 73
    0x311101c5c00e034126000580b40814203400f0312042e801d985030300444c1103403517144004039801c4250f000c0c00240040855480024550801c007081c0390303507001100400310320314003000142400d4019000b14072000000c1751521440b85040c0d0003003c0c403c8280d21041c00a00c2d800c1002581c00348100d03800503d201641c4200e458400000307804080c028221343d02400c54540040e4005200307006040409600034281c585901e00d1900d01009081d05456240024207402c0205509501600440d404641a0000392001034a8001004007d4124131016602c03400c000b40305040f41e503403d00c01e1081d00420000c01c60400c81200c3c080c8003004100002c1036001e01d142040c1403001540000780717201103e5109908a0395240c43d540650b0a0842d40c0c1c1c4000d41c242c2400c080071031049410341000801c41c40940e002c00c0109888214680e914865101c064a50b10108022034401c1c201000e00c0c0d0b08050002c1c0443e003201d5404048001000c0d1107294445440380d000c4107100400c81c9054076281c00c148145418096690300340c45 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 247510764 1250 247509514 247509527
    0x30c0c021e03031c0605090f070e0d240f0608031813020c070602060708041707030e0a08030703110606061c060f0e0405011b02030915040302030d0c0510020901 70
    0x101900c1a000c07500318000300d41c08a100082207100c05403c0e81e4882c0c21080811003c2e030040300440ca0110b003000c1011072181009004030703101d2204180e00301359640700c8020544c1c1044002c1e440d55006a8a22055008500b4101ea01c002c0c2400d90600398003100d210244a000311000b031080d00d102242480c1e802c1110100000660f031040c044802008040791711800040c0c0c505900181545041d400810b840340120400715100c0b08842c5160266101c07175a510504994540040303500401d6030f1018944205501c8600019002d214440d05160060b08443c0000031a150102d1340100040c0d0300015039502010362043e80e658845410b800240658104480003c035a0f001c2c005100d6506459031010314144245500444003e1400d2901c500c0c007242c1314004508003810458058031903608240c042c4c110106c0c0309410000701c100c01e90146041c03540f001c04000340605401003107081e005080c0400702c00350b0790610091207009656100d03d4565441450f2040c02c01d43c02c02c809032032203481404110b4041e6040791 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 247512014 1250 247510764 247510787
    0x150d0c240f05090a120606051201141308120c0315060415030c0c0c151e09030b060a170105100b0703020c221a01121e0e0c1f0e01030c 59
    0x400e0b079100c22a2070041055054180d00040103021941c50510900c10640e00080581d50240d42e0460000020b5003041d081e280c244040b1080b62104100003040c0e004109000d001c07a9200308122494034103808a0100010010386030f0340e515100000501405500c0704081c2c090340f0a003640d182d41070604e0003003040d110054110301e00701072540710710408507900e01c20013011486c2988001040c0c10b02d80c40340c0a00d000d04407411600b9000c41c0c07140c214030b03100203c02c102203105607001e0b40d1103070101e034190768407060550009800c0c03640141444a000c105030141c8690f501803035041500000e014500a5441d002100c01903004503d040300400a40002c242d0110f90088405419500404480b208542ea1022101454400c0245620703043c44411401c44525189411907002d030398928564944440c1682100c14880b1540482d1070305c00f03202081501260071402d91311b58007009491a01d00040b002c5418070a000010391449407142000f103c2042d00300155841d4800c082c80c0070841e03c40c03c86409842800740d136 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 247513264 1250 247512014 247512017
    0x604081b120d08150f0d0602090102060f0114040b01050d09030206040b0c03012615010b030601180b07060506060c010e0307030201061a07020402090a05040c03020c06060d080f03150d0c240f 83
    0x3861413125281e026a1543d07442006d85000344000184c00e1500c02508280542c0b0300500400001c20440700c0f10200a034117071090100d14034031445d450360420009100400381c0030f060040c01d0000c690050180d108004105d4001d8020f8002c0c0d20b801d241c00c1007814001490741803008001e00040c000074080b603200940300e0180310403082c4d5810352900d0701858800407c1150605110b0f03c000400e00041110141d8011802a00c1c0e581c02049030061030407a140c101d004030b070f031618014070038a8042803c68100340d400c0000500b00310b180c030501c0040607007900c0c155480c1d0300c1d00ba4070001d001130805509110305c60090414074203942c9550080501c1c04218800d580000c0c1c4a141c0104412241c0d50300c24441000918004204000f403820440001c4d0107034008a00b04003c0d40600c0700001c0b910304080da00b207440c0540c4111494900b0901120122603500090605042444010b00149603901c0e00c00d00e00e64500e0050080404051500341c21610001c81320365000d0014800940742c1c0c942c20780100c010225401c10303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 247514514 1250 247513264 247513291
    0xf030a0804050f0303190b120c0609041805010207230d0c081c0e0d03090c03170708070503070c0518010e07021006090e01050108031201030b060604081b120d08 70
    0x264281240b903c5401401071485010001c03e10208074a120101420000c000b402840502000d100b002080c000072036240c1025081520027541600d0803100415a40500610028071124801418800004505001c5605039400030f40c4034240013a0b04051040514400038407100f00f42840325080c0c40b410300c004820f081c4408129032004024000c000d4800c6600c00c0200921035480c106a01e8001e41000c41100780107006180168061a12a00841351541d41009400000a01d1903807041c811501607400c0c29500da1007440f440000503c00c000414101d8000c1c1c00654913804a4100711009a10b80d80c000340c07095220116a24008200090680c11550003103180c003025501e10f5401e078249201d6010310984140f9040c03002c1a40741241d445444003541c410001c00803682c88031440c540d00d00c51400034940460f60440100006810140360551056020b0045420b2030303910090146400c221035820642818030f8070350301059040081d08124004010b00050180455462000c1d0a0403009459000d07000706 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 247515764 1250 247514514 247514521
    0x1b08092205070201050417040608010b0a021216150501051305101508010e0a05090703080d020d050429070516170c03180d021c0606180f0b030f030a08 66
    0x32032029240141840302409107180451000b07000300340850741140c0703004551b035101d04008207000656068035003a0301c031401c03640d007840c4040301c0c142c0080038501e00314401d014104800c0400c0e1001303050f40c1e04a41c0780180007040c2600d480f540030441010824141880c0900412007941d40074010101524840710002d5180c0704c7c59100520207081d0382210981c0c404c0c0113035080c929980300c1c3e162812180782100003c2c160715416880b0781501c105440110441e8001d0740d00b40040744511004101800004000503d458130f00315111055030740446056851320b15149602d0f03200029248c0941c00c00c04c0f8904103110389e280000001d4180c2c0038543c00a82c44942c246280ba00f00b020620750000266204120541c0300c20401c68031640e2030703106160552103031500000c03004041c2000d4901e0143e0030350084c0b42c1950600d001c03200000440760400305a403499180d00300041c01c5041900d11041d030301041500412443c030751008150540d0104508076029a00030101d01c441d4800c080140c48003d000313031030644160380b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 247517014 1250 247515764 247515799
    0xc1212010612090c0f14062b021c02180904050d050c100203091e0d14071e1520030c070f1407030605012103200a05010c1b0809 56
    0xb40102d0000c0400740407080114402041c14404e4045074004845468541d800809004141c002c8004940028540c0c40c043c3e0f20448c002d050b030581202c80400c0060030f048850562850300c00048039448040303035000611503e1559103910300030102206550711841c0c7e08050f42d40c650b48499140c1c421040010100348070043c0e040034011510802c80d80f0314259241d041010310252500031030401501110a59040000554404034203c445010b00783c41e01a144840e4071035034516548024001ca403c00d060500742600b402130384411910280c01036203074084055100d031101d07040700c844e44442c150701c1c00350391500030305564a102240c0e40101d41c0050107031518a2440c01e07500f60340b8982c00040c500c425041d0b108012041c009442c0007124001c0070203203c80c0e680d4401d55120b401410100c2d4160340341000044000c00c0c05500c0e0416008626074000c40000e0450b521117040241500c1e0031125a51070f030310901915035100c0450009920060b01c0c03103640b403010b40c5e1110240d220b840351050040000301a05040752 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 247518264 1250 247517014 247517021
    0x609010e060403060218100203040e0c1207020604050d050c03030c0a02150c13090204030b16020c0310020d050f1608340f0206100311060408070305030c1212010612 72
    0x10399001d0314040e100d03903c0b450036001940040c0402c03141e0b003102010450701403400c01000000d4900d030fa0003441c0303041c0c1030170620843c019001b842003117852000c10500490300c0025000c5441100395901501207420280f501c203080401800c0b502c020000144003112000c0008411250001c3c8001522561809501001c1e42820740355106a0480078694007003104061100004264074a040089041e4041c0c503491500c080740182e020150019009a00040d8080f101466080c10643e00d401215145c80c807640001c2e10344416202d00303004442d000305100344e00d06680c2c0a031a80000b80b80030002a1403078840501c504107a070701c412000800204d10080b0f00e1181c403400c002080e0310f14040482d002c0001010f0359010201c4a030990000050702c5411000d003840c808942c079406001045c012494652464030b4051160700c811070740342c2e41b2210410000401e203904101c402300551091020b56110350711592418101900c0008108410301c0400102c10a1000d101c00241076071220300b0007a11440d151189403004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 247519514 1250 247518264 247518287
    0x60f080c03150f0d05070e070e01050301060e01030b030703170705010612080304170c0601060c020306090d080a0b0f180f070c0b04061a0301060b030a11070503160f060c03090201080f07080105060901 87
    0x54010341381b0200d070180310b00442c5403044110351100a07032541440f004440d188002d01c40e941c002882c1b4003400706203600c29088400d8200005085600e5207481e91a032110300f405444200d030800000091900400400f0300543c8001c10010f0a0030a504004d40c03181142484010700c01040c201075048a880310008940548030300304d500e002150141c0da1110b1001c2e0882e4800d40b0164400e00c981c03000103420441c0050001101c003482ea03122002c607221090341c00041e1184814585d40613003808886610b5498440c410515070100b040c100d1800d040003940104000405004e0004206820220b10041002c44111a8020368031203400100000980e15220440380d44070901036141d42000d400181008009000c1d6000f1511407030100700844030b40400140600c03881030000c00b50b800911a280c1c0600703c041c2c10003041405210005c034058005d41d1114210f891081d80c0314007107641d40340e10005559202040982c080b0b101c04100d11142421240130300044c105201c2c0074803c0800103540141a4070584c1da040c1d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 247520764 1250 247519514 247519523
    0x270111151f0e07020703030306091806020c010b0303030f01090e0d0509060304020409230106060c17070206040b0c060103200f0f030309180108190201090b0919060f080c03150f0d 78
    0x10f400d00000094840181d0320094000a06180f00850204240c2c031800d8510001d03444891120700c0140d64500294100040940d8155640c402c03945032600c09100070f612030200000208110b60400c1841011602401580c800640c840da03202c5a0480d0000122610003104646454503561280b00280141c00c4211004041803075894030750040207241c540e01c0307078080d002000038040d07161503d408680640b03440d0b07809004640c100c0b0100b07880c44510f5005100141c00940494a0729464100361040c2e0351244500b2070203540001d0040050250820001010940408040400480c083c000808209514101501c54412800052034a543c10030454480b08005881010700380320710001c071441c56100344141c0c4002e001d0381c04034500c01c00710310f2140615a9030503110710a42d02d00304540200143c0120030340d0350f0400101b031504110850400410001030180b80d681c503150117294503004003030f0340001d840f020f2844e406000b4050400085800c00c5d104002c03d491650070014803000040c0407084c003001c00341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 247522014 1250 247520764 247520789
    0x818060d09030f0f02030f03040c091e0e0d1413080d0c0b0105030d0c120c0501021201260303010b09060d0203010611060c0309100e03270111151f 64
    0x2000c010458200c80c10050198960301c200d404002801e454210b410641000141c000300710580b250819000610742060140260610607a1522050011120141c6410403914518918507080eaa21805180c4c164580100a400c0b10716041401402040b40034500301c541e100041a800c600150030b554040c01000204103ca032032861054014040407000c04099589546d8140081142d00b80094030f402812800e566003440c0e00d5080c1c076600c074010b182c00420001c11404070214030204400f40040e02480201701c110f544103500d0003806519113000809504c0c52414520f4011070220008825a41184e8600098650340c80c41880022140d10a82480070b000a00c0400040b80850b03120070780d2006440400122407250f1920040241c56010850302d90240e54043c804141100348190011780380152001d08580c103000f030003a065440404101c6111030309120a10b03e0400640e44000308032440b84810b0040d02550080c40c90079104080018105d45803c1200214004141501103007000103042e0361900d20f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 247523264 1250 247522014 247522027
    0x110d0306080c041122080a030203041d07020705060d0906140105030705010507051c1205040b15040c05031b2203150209030c0d150c0e040c020606030703081806 70
    0x140003480240901251841125034064060405115080301400d040d64214180300050034500c5218a4400401e142d480705801c00240d548010005062458401c6e0061a10396041c605842c030003090712071940b581d018800c028080040d0300800d103031069807825515503076140b0700156000d01800704254000d100d64038029088402000c14420281600c00440c00d40750190390322001140e041c080c007800506240c100000540006035020341011003a503a5090400d43c4420320007c00e800c4400c00c0f90150b60481c05c0d64104090861105e20101903602d0495080000701c0c07015200034200e000c001c00090110240d034004e03440b0102d100d8143c03170f64181180c0da42611501004415905c01074140f00866001c410140940d84a8529000b0340c0c401400280042900480602c100261a0602c1740141e54140314581c880365071554a002c0c81c46c1460058a5041d441c2c0290010700044401d2603130040c04640266080c00460359000c103002007201d801018083e191040c1a013190548e007900300c2c07090361209001481e03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 247524514 1250 247523264 247523267
    0x3020f0a020f0f060606121911090f031204031704120c15140703050306150a0e0f0a06020d050f090d030323073005010303090f1e05010c03110d 63
    0x41040704102201558000c0a01070842d80c0d131140159011030303000c4420300c604104011035442156000da08003200c0c074000f1040120107406c440b9000c075115200f940000d140491030178014a8002c4d110410b400511140c110204021014000c0f400004c026240e4203001c6403401c510700003502e02901c503009040d5222842850076040b82d048a10038100524102998105801d004007516558a4070b0041694a40861540c040310b0355880200740660280c0307060105204000c4407409070541c034000b6240e80c0c3e0445110702c2003001a4030300442080c41000b40717440600244e68007156424410141d807c00c6909d0b101e0b1240000030078002c403114142c001c00340310b03000750501d649600100d856a15003007000c24400c03092a10303002e2848003107030384c000445c0100080140026084c010722009940c40c1a6501c040c045c0d40d0740c66026130300c00307030310903400a500c1c0340d414401c0b0f4103019415070081c003403141541c0b04070301070440d207000301c041d284142c03810300c82501c01c1c980a250040b128904910310301d006548030749010880 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 247525764 1250 247524514 247524523
    0xc0609030114010803031b07170901020a0c17010f090f0f020111030d0501060905030f0706081003080f0c0f0a030807140d020309010f110f04050d050c2106060d2103020f0a02 76
    0x5287c3c0c005034048001c1001440c41c0000c440080e5001007a4203141101c0008415441d800600d1490451140d84900800714030f1801d070030005004a00c681a0000c01e041416a0954140d014100c007082e1600c0c0c884800641c8a4030850461944400c945040c0c1e0506c1c00180c07101e84140d19071850a0000192030481c000c034a0b80824180d0301240c886c000d542da210418155500460b8010380d04a1384070b03081c28020301d405120b03515440303040500e00c40f200e151a075840d0712a6802200c010301c18424040341000c0710031414031003070a150408000074400007240380c0380101051809000e10082c422030010704011111644205c0d4181c4d84403d105650300d0515100280c002c007282e1200b07526451918040315035201c1044100c5807603000c22452a420541080c0402c14400c0320341000f21160b02c29040511a070383c540140c03030f5492640407075000c1c241d6010465602d044c90320051403103121382901c0c5c001c8000511004e000009807218284001e00e850b00b231840c00e60080c4a110b00791100c00307030049044544981d0000c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 247527014 1250 247525764 247525771
    0x411190203042c1b040506040e06150310140607060c0815030102040b12060604090915050610080a0b1815031b2214070507060c0f020c060903011401080303 68
    0x1200b02400300340d58102d5102c4064105440d00700342100d4808602d6200d54446144400e04c10034a40c40c1c40c01e0740c3d0310b00203a800e510582c0526100c00c070920400a4515008081124034208000c0c03007841e5260040030b4050103c0719004900081d002d51205203600c0d01c5081c10307034800c958030802c1001100c08410001e04822000c5030501d00d000e2881500d2072080c101802640d040340d1840e82602d003002412107030b0f1450064010410f6410010512000071801e0090261400c054000e818000481e000565080e0581e20300400d114000d085152a050b1002d900035a4540d2018170800005000011200017136001d848130100078884442c3d10003132044403101d43c000700c0d45a81084007180c0e2030b001040d64000804c400403004542c81995404404420f8500090744410b00c843d001c4000340c103051401d54505c000e02c041d20b00e03900081c40410010300b00300152103007440c54070a030f08000305480c540304030007981c1c0c1314400c50550040901007104610b03901c00f501f00f103030b07034103040d5801403000e43e101e00205d40d81e5003085 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 247528264 1250 247527014 247527029
    0xf0b04032a12020303070609140f0a020609040525020c01030c0806031209030304030c06080a0612050606040e070801090809040b010906050405042307110606010f0905041119020304 79
    0x1a40e640c4100d003404264001c81d551030000c40c0c00801e14180c41510075030903410099806000803c40280002d205102e1002c040380f1803003000080061030b090440c81e00e000c0540d10200e56004407004409660380e5425189015021100451559221240208010303001c00b04400008019420901415008100702c920f402080c0d83c10401c1044401d0210b501400c155511505a08155a030501f140d030400005e290703000740907007203902d41a5241c2d80c8440107401035102e84001345102003801201c9100c0e000305001032000300142e42601d480c54840c1c64841c1c04c080c205074801c3d5a690800040240700780014401001920006c100d03c5119062859103580070b5604188194606440a0860f6004203a904169400b50b941e980c00c2c10700301018000140300010059002000200606030f00da26074404080c0305d034120b9500c0c19040c09021002a240460182a10f0305000d8904040c800003a1300840c1303002111000c80380400d181c1c05880387c1d803000d481a458410820811a20100c0c5425000002401100c110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 247529514 1250 247528264 247528283
    0x9030e0f010c0b0a02091504030c0f0f030803150a0803271207120f1e02010f0503150103020706110714060a020702061206040b06041806080604110d05070f0b0403 71
    0x5000458940c2e4000e50700034143d400c2207001c130f400c0300da0f540e01070000c480d03000d09842e18040340039a001d941034000e6070080718183c030320742021311002c010b641c5290f005068101c42c2184103030447d500c0c1d032103038000180034145440e00c080c0d02510603990003000800400e08102034941e02e51640200c00d881140b200018a040046074545001d0340c1407144035030a100500c2c4014100107418003200748070450b00f1640943d13502001204800104002c0f490320502070300c020340c85a608210300d2002405280b01c444409090210038820850300360740e12095031080000904c3c0069441c142c42c5451300082000e0501d8000c00200816564104400c5480e043e10303145194044415640d42c0100003000d91141c40b90094010b081400746610300d02c29044020b4010200900100d900311403039002c540b583d0031070b078000302c4130300204545c2d0006800940b0901c0094a40030000c3c185d540707420b4950500c610000c00c0103a021303000500c40755042c04810f100900c06011a210b461815030b9507000404401d40040c002581d0340001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 247530764 1250 247529514 247529539
    0x8010e01050c040e0105010f03020c1504061404171b01110304020a170a02012a06051e0c03010b1c050108070f0b07170a0c050609010c0207270f020d09030e 68
    0x882e00705840445182207042e4809030b081c03100440d5a803801f10302c26800e0603003c4c001100d01c400140000142401498583ca09600c0c05050400542d449003a416450800120520010034450806014005003ca0200348e4944840d06038440c1148403505410b4a54030b4910a28010000840258003c40c002c1b21030101e83c949074008050013010041d202c1d00d140e400a521180154019002c0c1d500d1003d0040100d60a03030300030300412801185400c41100e01d60740e20020043c0698100030301c440c0005041070340101524000b41413500b01c1c401070180010141c0003060541407242c0810004208504d007541c24001543c2d12012540c0d00d01c0503026848800c81c40440101d0510900c1007134548040c0c02058410311020710140b000784d158030141805082116421840300450420071610740070701d03808000011107a044000c0207041c521703903402110380c84048c0c07040541e420181034a08110040c0007800012040d80069114000303208811075103140340c1c20501000141500b0400c00d4204140a4911044504c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 247532014 1250 247530764 247530781
    0x6120b01051519090803030a050703180308010e06041805060108070b09030c01030b03070b0f0409110c100f0b1c050715270e0c03090d03020702010c0f03021608010e0105 74
    0x70700c100c044080400060064008440c0f05002620203407449050101401c0e407194241402c40e0320848162003c50345520612501c03da2501c903000c80314850080e842068000765400070441103041c410804030601d15000b044565481d40e020070300d402141c00d224012014945045921002e007445000780340e008030030340052039200300d03000c0f01c6504600a010700103010300d800041d0010140080d4843e05481440004210241c00c07a0040c150210a40e56241c2c4031352400030003600382c502102105400030000c0c0100c007a01e8000280518688040d0b40b8042038040900b41143c00a280400301e140e44005420800c40204050244c0c40c54254056011b403410552104144114001c160f04000b002400d004000400741514a100f101c1e0704250408910308107681d50950340a02c101941c0a985904000084c0580350100b0048850001d203a42015418400540c0001c0e04100034444040c1c4001b00b076401039820584207009600718424007400c0b0110b0f03a0707203510750701c1e000701110107113216907600e42404580d038071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 247533264 1250 247532014 247532029
    0x606040b010e0d060e030c030c01060512030405090a0207050703081209060f010612140a0e1b0906041805010c1115160f050403120807080a020c060c0a02030d06120b0105 74
    0x150182c40e024500000c640030300400b0110403a080d120680d460a5201100d88180010400800085c005640b41c20110f2240750031104240c1c4018813a01500480345207595022050310112601101e5040c20340d0f440c0703006100a4403949500a00c107008000001c002c004001d40608901d03681ca07c8007000f1a900c00c5985aa41c400a981074881107036550300410209118101c200c0000005000100701110b802050905550094400100d03454036025401e1101e0003c0001c000e5484400303554811010488010900c010409040c460045484d46544400708040c0441140710643c803400130083c00811f040c00410240d041c06001d55240122181020b08480d0344168a00900e0744031811020701c0f5040340d090ba425020004880e0a010701440b0000201d10203820140d4a0503054450f03480b43d01e05030000810454009001e04030003441801a005540000280303160b200d800b2541e1140e44006981085c2d01d140616407040d40000d00b001d001045204943c0080c200c031600c10600c0c0d02c103598951b000c10a21 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 247534514 1250 247533264 247533281
    0x109141503101a03010e03070204150e04030309020f09190605030a0209130c0803040e04030215090a030c020109050a031a070e0102210415020c0a080c061806040909030809060604 78
    0x1070748011000c8100858036844140003503c0c098050b0004004940800d0960b02c6980c84c00311980c00210f030308001e500301802542c0c0420340408543d000c0c1c50030b01890140760b650281029041580c1c030340c0c0400031074031403201c01850a130b002402800c540c40c00034005c502d1400031034a4140040c0c240f050010366810001089000700b81c1c000c01b541203998442200503e0420b0000f4140c980200d000c0d800200d80e182400107201400418030110094a480c1c00e000c5c2c40c015003220300039481c07002c0740b04000c0c806101050302a0a20303410701d80b0311b1002d03000e400100c540802c50342001d035002d8000b031800020001f87da10702c00300700503003024940d038103a4130100182ca4500f401500c2c1405a0481203070720301800c3e11210340701c14a210540006042503160180c40800c01244d400d2180503074002005260316241060001c4020074405006181c03904c1110301048280c02001c00007140d40b048200c414266a83c1e48068030090444d542003013160465034140104010425100303c0345601520f070101d1403d044c06e0080280c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 247535764 1250 247534514 247534519
    0x1060f183902011803080c120f0412020c010c0210030b0a121506051c0f050604080306180c0a1b050a030c03200312040302011b02070f0605030417030c0706020301091415 74
    0x5444c1555101911407a03130042c181e900b90113080002448080e09914460f01070b2400fa0003070b40d074071f1400340340c000102e50f20311181c0000d541c4451211120340e1f83c000c80c004e01165055400340580284c1e0f94068020340380c180c00c0a90304c07040504000c03d656440200200c22140507200442070040e0380d1000c0780032100580501600190380b902098200401c500098002511035410925000d02c2c175165241808030503a000c84e81c8080000c140f00c1d02c1c4c038203082d61664204161154207050b013010030800e01c9500c511942034040c0100401c1d01a0b05220200000c0c450fa500901502c084446a25006201c6602aa0220046902c1158120a070075050052001804081d00110710700010554040b00345040208103c04541d224403441590034805503414040c585d940c2c000384041414000074503041c60f0940c01c280b04101050007000702052400b810490003090800c40c1c140c0d0307903c07014000c000c0c61141e810081c1103d40000300006840b5038aa000d0998034010140d17080c01501e407030340c01c100c11984448101d0f6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 247537014 1250 247535764 247535801
    0x14070b120411031207060203190e0c041a06072108160e04060302060d0b1c0807110f06030403020c0916050316120c030506040b0301060f18390201 64
    0x20300040300400c0b00c211090703004041310003503c182c01003260f1036408400102c0746d458010083c8403c00c100b0807c480a40580107000b80a00c10f14000c86550307075881e41c42601c0c462174589503002e012501c1102805034070400585242d5942070182040f4225824418007202403461924150400d1841114007034011200700081d151401c2243c40308840341c0b0301242041d5841545d0321800070059449800038038000b0b02e04080424500041410440c1014041b94120400003904176503100080303c0c50700321610f895108192052410303078440803e0350808030352007036034015400000303000506400190301680350301c1c121020003450781c0b40b601d499940f064084444010550610100f900700c9029122007040c00a01e240c00703000e5241a080000071348a280340b0310804243e0702d509010040c2804e00400e512070006400a00c01c07e8a0052941f0f0101c0d003c2c481c41000011222101507410401d800c100c0020f45044002107000c4502103c0c050880c019072409400010b8403041da0110714018000d180c540c600645210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 247538264 1250 247537014 247537021
    0x1050403021e010f1b0f050a0c02150d0213080708031c0b0d0501021809063115060e100212090f010c0f2405010e0a0e010f0914070b12 59
    0x1c202c66201200c0b46201d9500c031101c094040307403d849100c2c0d2901500b003d00000d100041006031070f130360b080780d2088100001001480d1590303411121007403085905440c49988001e01d600c0340d031600e00507030380344003402400026061054500500000143ca81500076255440d940d414029a41c0c41a0016900301e00540c20040203159066032104191000c06080125507107a2507880710b00f280d00008100d1200d0404401407401c80c2080c8241e107601030b8041e201486200640003e515000c00da6028039030f040c02c018010000031401c1908480b00001c5080400c4101c2601e46102a1200144038907140c090306a20095620b42031002540c94000c5140401c16450040603406002a84507202000c506100b120300402d000620703901d442588090041c800f0805202c060650156280c00c004280e0240f90306040051200c10710000031250003641a04000400c26024452103015154001c29900380500d407910550900c50404440c030041002c00c070640d00c046441c1d0044e4040c501661800e1a00d0083c01c1002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 247539514 1250 247538264 247538293
    0x5070b03151003140403200304120803041a0411010e0108100303030b0613150e0607030905091b1207020606010207080613030512070914040209060a0e06090d060b030601080105040302 80
    0x8a2144052441c02040d03881c06400400c0c901c03071041e5811800600c6509140c3d40311841c9001c3e400e007c902c1c4a01551900f8642170340d620041044120250140a0000c04a070801660708107207203d00d00001418052880c05040c1000c0300359801c40301901192182c00b000e1040e600c16480355110381c03803c024802049045460880062007900906600204204000c455a14018001800408070aa001c288440c43c0c84001069480c0c0c181c07004c0d01900c01803101e800000d070031020701c0056501c01d680303085240c0e403044603031807054130142000a418030000611040f94941c1408440c03241c41550211a142c0d1a030710012079841029100301c11650b0882804503594034482e010150005010b0720700107041094000b28a03031250003d035079603c04104100410022044030280c6030740d070750b80c04440840c1801c0800303020540768032890340c101c01080882c041014850380c03907400350341181c50b010b03000c0d40809040e480c00d00e00400901f41d03032601c04e00c42c0d0317800010000703814014640700c0d507415809803000c903850f00c0c0c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 247540764 1250 247539514 247539529
    0x200703051209010209130f11090d080c0307080c03070302160b0d02090d020901122a050607030c05010c05130f0501050f0307020c09070818070f05060703050409060e0405070b0315 78
    0xba5150954007000b101241d6030f00d10748a5101c0d048200400510395118249180855401c1d0200ea00c0c031407000d01000740941d80c5c108000c0000c0340c000302301e540d40300d07144d01c8114114480c40c000209001004500280012000000b4002007403098084607920342500c00c14440d090303820b00c24007001042c10403404040ca00160064440300c00064600040040946d0006d4a9070320241c00c00814466000d5041d4107119002c0910040207200c044102e0040c00011070041141d00c3c00e0042c51302404000642104161142a9034004250040700820440c80b2a000061840d0b0200140110344600e520300031903540c240054003c200d038416115203182c41000701d031161507904010003800942c00360f035113400303015151036440c54460710260350784c01d4603803501900103100d00392040f0191089503c55a0180851444130f4144416160100d45082d2505100e2030111868851900074078189428031600042003000721007c980918070034800d54840c0c07a124904401039000494110340d4640c010f840b48001c5003803490 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 247542014 1250 247540764 247540771
    0x10b0a12030509060c1606030e07060305150d06020306011409060a200a0302010b09161403060621010f05030303040305040302040f06090e0c03100e071a0c0703062007030512 76
    0x34a0b5042c0042c81000400d41e80041a05200d2504a42d00c080483c0007900344c948013424803820100100d08590741c0450b03880e071142c0289401d05640d00701141100401210801c85c01900030414651010b4920f403141c01f03900141e404034081001912000c0400015100782e03040f609028101da03080c000c0300241226480c2c4003901c08022404848072543c00c6032000d1002f94195402600040352045108013800703280300000b008420030080c10804070302e18560000c61805c407080300c90b01560b100e0710344e43c00003001d522419001800f5000c24224580004440c000790358101c03812640c0041d0403a81d24400d142e181d1100b03c50040003d58100b01c24801403070300d0703406080551501c1500003201901c401210085900e902003a20442c0e1043c071408200f13260070820b15008200202d000d00c0b1945548210540d0b0306118018030900250710180044850340c0d0106890504080c0d00c102c910003aa2070600000400c070014500c80100c6100c3c400c15450040001142e04444c0c0c507540d80c62410031a1440c0c00000034016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 247543264 1250 247542014 247542017
    0x90b18040608030d0c140301080c240a0e0306090a03080c0a030f0905010f2702042415030e070e04110a080102220f031e030e0a150305060102010b0a1203 67
    0x10400800e075103000300081d00c0303111500000040c440c04120005010b9517450003901c4c56181b0704100510252601013403100c001401510001300300240a42c8119019420419625410700c000c00c00418140d4080103000c4105000c0d415110180c46400c0413a454081091010300403404040101d0b0828a4420051814210b24900004c14109c0442d046003559000141131360240c4d182e044c80040f0b55440e00c124012180c1411004032041600d5103c04804088410041d104503a40d0312030b400f8402043d100608179100c1406007020090f243c100214000828284540c0042d01e0f000d640d00b4064030004008056820b4030540304c08036036455441e807150701d204504454220201000010300c0d04000d00190942c00618a034450300c3d0750f025094400751080e558081c3c13000c403580c510b00708040b8400b070540d243ca80c00011000c0a8044031414141c918140b03d1601d940c001100c04800070300f100c01d134409608800d06982d130510a60322404012800d0b00d003502041d65101080c0b000130440c050115030710b000305612a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 247544514 1250 247543264 247543271
    0x170102032e051f021605031f2007031e021b040f0c021c02070b0906090a18092f10020709090507060305010803070c1418130201020706090b1804 63
    0x32680400c200d554103243c0038000d298400d4145940703a40502c07401c14040312000c1d08002c1c040c0f500c00020799500d200c595601c0000c4400600b03a403000c042c2c1e0000d1402c0000c03402900344001400d8100c182c40e52200c0c4e010341c00a00c21072181400c4441c800c000d0315042d00258010910140958120941e103111501400da00c80d5031240d48076110310300c0380035155180c0203d80240c00d003c4010300030010010b000c0e049035421500703da8001c0c4000f9240000b41c600c1d03e102501c440d92189190008558514002c0c0c00c000310342181c00c40042c2c143d03641504070520f994860043c000592410b40303040c2c0140001603985440100c1190600038290415004804030a803440c4115507003550faa0f2200000c4401c10071043d201c0e07070001101400f5a54250143c40d00602c8a43c0003103181000a8864500005e01400341c0c2c406003448204464003a030b142400003200168050380c841c40d90808a03c0300a0700100e5038000ca0250041c040c00268242c060030f940c03022614081280d0b4a004c4c103800c3c0721801c0c03038214581c441d4440e0f035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 247545764 1250 247544514 247544519
    0x62101121502030c070b04061a040e120306031509010b13050402100804020f100c050d020610090b0a23150301060c060902150a05130f0506090d0525170102032e 70
    0x30103940031f070084c1e000c0c240005e600f5240190003141540c0490300680100c0c1032501c210903083c4001529644013083c05105c0c0d0b166251311001074140042c0e401c0c02c0d184207003c0390500c06140010b60180d04401e004480c840d032580d00350050301055800c100c80c040c1d07021000222407038040d80100d1205501920007083c1c3c00d511140440003803001007040d144400052249104c0c181002410809030070f41803928002086075280c440c1d4803143c4103545006403111980c031002c0d40034840d11906102005003044003013650307070403a05840f840607540c02109007912401c0c80d440013401030283c0004590503148180d0314920a1022910b80401070603944400b00e030400040c20700072060304001742c064411200650742d100d5568590204070b855038107043c2c200540c001c0741d4040402250761403c0440c0c032840015541142822440c0c10074234200920300d003401801d03c2c0c03c6500443c000600e40d142e0380984190341c0446401070111004d01d4204c2c002155580196030058240120341380f0b800305400713001314810069889094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 247547014 1250 247545764 247545773
    0xc03160c02151303050304120203060a0905061b0712030b21060109110f030408070201090801060608040f0305120405010b15040b0313052e06050105280e062101121502030c07 76
    0x2801f40d409154201e0941e00e001003185824070090f904070304074000c20300c600d0388246c0341c80780c580c41e01800034450b14000e003000401021140742a6028035403c07401d1204004045600039000e0079042040034484c04880b00c182c07964080d603c4d01004006511801080680c1c00c020800004001c10390102000c00000c1c00031511500340100294821441011603a03100c02261001410340c0d041e541058080d030741456030501c0321039402500300c1c0d0312641028401342c1c06007441c1425251449103681131aaa00c010904110501c5015048065178990030748403140140300d00c1e500c603140c6002e54001c0e82040d450400205020210400100c01110b00803000e95400502d582803000c010386220505080c80c0030100314995a07143c40c0d1041e50002c000c2800c08510301030f91142d0b0080c864140b400500a11040740c0009207246d445603100c03421a540207022142c0c2c0f00d00204180c00d0a100c02000c08044810140000c5080078980311003c884961211824020030b03185d0304484040c0d0002429107011302c00c280320040125 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 247548264 1250 247547014 247547017
    0x30513020a080a03090e0103050309011d03161502010608100209061215040b01030606020309012a060e060907080d050304030216090e10050c04060305100305060c03160c021513030503 80
    0xb040c1030001004400414a000b911905d0301ea440940d510002c000100080382c00841224051002403800340740c0841d001d1030101d2010600240ca030f4142c851210b060016042d4a414030341a540c8900703491560300315400089090300c1645c061310840750025071203900c44c11400e802400342080c00500301c234140700801c07024a401003011102c102c04102248412686400c09110703070307000c1402c02c1c170f0144581400c040020b9600e208610416040012a1501404100d55600d6003640307100310324070a065240311424402e002e0204244081460f01442002c998031010010346681191142c10281074403404c441c82c103503410703000100150194005d0440d0201c2c88410300c200040604038912000500807018443d551400a590b240000f000c0d1a01050240181800e8151403c40d819031401058564800680c4007159085900081c1103105180900c4169002c4801651181040002d01e9140c180c01d804103d07405c0000840207500a01040100680d00c03400e00002d0410000380450081815503d40d10903286 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247549514 1250 247548264 247548269
    0xa060c06090b0c03070e01050f0714010f050109140f0708010303200303011d060f01091a071502041703090a0308030a1503080301050102070b0403120804050a0606140f04091101030513020a 82
    0x5524000040029403078010044070246c400030f00e080d604144807a94070800e0780c483d42c0805000d5800c028025001007000b50040403060310b10071003c2c0041d507555607522018152440c0010b111141100014080c08090b03500e8500ca11129603911086074038503107040c0e07000206160348000b005c1d10035042080017842000114000c01c1c91031840c801108050140b4016000c000e081c00303114100762032b6003c44580c0c5c88000d150586201c440c02c01b0a041c0c0c840d06401c0d241c411201e00802c04600419490500d500700d502510440d03031502142110400100a203540300d225001205612921040341031010450800c0a180d002505080026201c10310b540c03201c1522490354000c5442140010050007107503410b0081d40d00070103500301060308050565407003220f418821280039040207a072400050034004200f01c05401c0c01e401150410080d9200d840d103d040f00c1d1903213140b60096581c455244130030708080c0701d10881039800940050050b14264011405440003801002004019400036800f42e900d10b40c10000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 247550764 1250 247549514 247549531
    0x504080d0203120a050f012c13021206071407020a0302120708010605060a051b010b0603040503041409071d1215010911040803070f0804091103040b060a050a060c06090b 74
    0x1118940b1038296003c030100241101d009509100c01e0050f00b030114405641910326032074031228011010f08040300350254011440b454115540107011101c0d440d600d1111426009071081099210710340203043d5030702c1c01a6000400078500c1e00c03203400300c0e1003501d01803c4407a10045c4419040c0f0b07504d80005844550040f106441d54009013010420108248502c000410040e1103c42c180a4040e1029195001c1c0c4403d02c0001c80e9441d002100e521fa00f940070f1b0681c14001414144c43c1e0a05081140c1e680d0494007400001da0000d925059482c5031454020780300c0c59140d0348620407416400043c82400a16180440d0860b01c2d44498015600051244070000040c11807000400d6240c044507400b51180b20210421205003003200340f0410750301100301c0320f400e50480180001101c507850981d400703208540c4000ca030701d8038010001c0d21032052070000314005c6020701c12500306a201c04081080c21809803003110342c0610341510030800d140c09100b00362240d5000e80d2000882c050582c45402c90301d04110350101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 247552014 1250 247550764 247550767
    0x1506030308090610060e0603191b0806010201021204080703020c150705011a0105040314030403020d0b010303030f060b0912010e0f071d040308191506020303100e090705040209010504080d0203 84
    0x1000c2c0d4803c01440342c1c07014012a820b442203103050b402030001340000e4400341c00f412000000600c0c3c90401a04440d081d11501000c0014190296082044030030581c464400036201e0800b14200f98414001d03580d141180414050041c0c41d165202c11243c0d100000c02c605502030503100703400a6aa002c14096401c6501241030f40e00c00c02d40c039015013150049030303103143d0b0307030b0300c404105a42c50b680701080e5001d03294840d10400c0320420000c0ca2a01c0d60107140e00c0254032003040c8400008010170070074020f040302e00c05d40f401d00032004010450300603660385000d4070014260501c01d1240b1840c055415410182c940000014003020310344149040c04208a0303e500c0740d5103d02400c100c558000c206c100f10143c00c120259009044c10b641c024444070002c1e181c020000c0c40c001d41d1041c0320b1541e0b44a010503812151807450507540d02c28000c0c0d2a0b81003103451056001003020000784000602e46a80e00c0741c00408040c003683e07420074080100075088005401d042280a100101e2100c05c108824003011000e6001903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 247553264 1250 247552014 247552021
    0x5090d021003020c07050409150b03070806070314070c052a0a150807020f0304090c110f010507080a0e0a06050a06050310050a18110f0102340618030305071506030308 73
    0x515000c0691b00c0342d80550f2411035400041105e501c00442190014507000c0f550f40c3c00a40000e1501469400200440c05200203001070190135030300c1017600c80c4401c0c20010003903030744120545081052223405002c50b04402c00c00c05900d4202c0041c01090440b5852681107024014045074400380640c0000c045801c40b00203001c110754202c400158005540d20086c9441060b1a107680d481e0301642c03252080e50340e11521010000c600035210704802d01400d030100c9a01751301c9040350f24080d200c20345010000c92000c40100f410940c2c036002e0318041c034140c04020b041c044036580c0d444000b400b000b0400381c400c03940e074807000c16150303400d100c801c40303059004c0e5000c182420201070f079504035004074107031000c04444400b43e1000180d0300d0b440e00400e00000c03a003030020043c0300001070342011902101803003030404e00142110020802c481420b00d800960340201ca1680d1201c0c0262526100c01d60300c042c02c8072510f0300c1040000e00c0b8000500c804c82c482c0702011400300b0055917080c00d0f80c01c2500218045400507041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 247554514 1250 247553264 247553287
    0x305040504060902160605091f0507090e1003030e0301110a120501061706090403120c090314070303050301260304150315030210050c010e061f060e0a050105090d02100302 75
    0x10b420140c4003210085150030b000d62956100c10020782e00c0140451f4030b0b40001034440c88103100107400081002120707500e0000700120b0900910080345c0d01008946520408078840000c40d00c4a80300e4086411808850ba04549050b513134000c6040705540e1541d00c40300d1022209922070090400080c140c0c403094030a9001840c0102682e5050304884108200c4580b1400014031152503250004400d03116480c2c1170300c0d282401c03503204128484038100c00341444d546006d840c0c2e100d504401103034025440820070a07004d040007916143c4500c00500007600900050024400d4043c011506c0a96105181e030000c0007006440d0035604241c0c0420090b0600442d00303443c054150192402a0000e2003100b0320242c1164000341003d111014003508104010078000e1402109500483c42e0351100400c0f9260f520700b10406809444078018443c6042c07009100004556002d075030410032050b4002c00309200c0c182082c3c01160300f5044141c0e441d900c256440e020f8009605e800c4002040381d50990340c00740e40d0701d04c130952 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 247555764 1250 247554514 247554521
    0x411040909050d08040201091406120103080a02190b06150c070f090e0f1510080105181c0c02221d07060c170c0f0714031603030807030e0111070305040504 68
    0x140d00910007800704005c01030707a100704090180c404026900130203c1e5004086190381c010103684400d003ca000b000801446500406006403100702d034215503080d269541c1c0984041007008000306800f61100102d056490003d02d8a2012400002080e0400d5021100355150044e981e00040b1045105e10060007040a00d00401d04000c001c940288000c8a00c8482c240e560981820082c011007100e40119070340000101d650401400c5200092045082c032049280030300d803101462111910540218510340510708031025140009070300c40d08030036481ca8082c081c10010340e07001000c404403103061030903d1541500c1110211405410302c80b410f2083d030101baa1501c00d40750000f409100580080380d00080d0400442001c0b42d00c4071300c1c0b01b51208030800c40d4528040f46c490940801c0d0080503000b0480b07512404040c201c407541101290b00004000c0b000d03540060090201030700140c00b07200010245030090300701405401d006000020b1119040420000e250003402044000600005041041c0e203800d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 247557014 1250 247555764 247555783
    0x70b0a090b0708061f02011b02060a0f090f060c0329011709250906060c0c1a03070315030b0115031409072c04081213051b041104090905 60
    0x80c81d103c82e08180d000510700c00f00d103a06019038240f041d030020f00d20340e04c00e402000181210384003d0707007060212034001e501e81c5402c4070000c00d10b40c501141181800030034002d0300909074100541550620040d05c07000050321900300108145502c403150b90407200c1c02040d21400c1028181808501010307000001448228210006000741c038081d0203110003400003140e4028044800700030300c60100d0007200100744050030303a07012030103130b524042c40080e400b504583d40030319036842809c40558858076604d83c0300d003c030524a100c0800401c1440015102c500070780c00411101c01c0f02c400d40e15000d90381d40c0c8642d030710442600800550780300c0c2e040c07404106405004c3c80c1001102d00c1c0c003440e00c0b8075008150954452551060b8411f039070080b001d00f880c011417824001030440d440000950030b442c0c41d0610b104154004010f48540100280c000313100f2a01c1100c041c440e45500c84064202207000b4920003500d40700c80c000039030b4441d0b500da12419440c41a41c00034001018501d90100d80b10302c060400794240701c03161 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 247558264 1250 247557014 247557017
    0x7030f050a020322061d1f09080105010902042c0c090619030204091a030a020f12060a0506130b031506060408010501140f19050402071a130b01051503040206030c070b0a090b07 77
    0x4c0008103d1f80e58400d98000e42d15003282003160704201c0003403c40e454042580410074652903c5d001103040302c80b1760003e00a40b0004203211400074501c809000f60685180030301640b00c1d00007800300703800c450326100608500400518080c1480389500c0c0c1c040141c000d142030000429800a003c00203209680240f80812154401d69120090541c01281e1224500b02d4028440d5848419094955030343c41c2001c060051790b60121102840c00c200e850005100a60b040c0b4821009110030314444901070140404007203004d0064070b01130000301000e44140c0347c0030b8075107640240140004100c640e800d10915000b00407141c00404c3c21840310040c090000d010380002c0c1d0245941c81035503031020041500f6482210001c0d00c1c0180d0385c995070f0401c5005800595005016501204240820819021a02101a4000d4400c0744140c0d0b6203402304407003003040003220507041d1000d1001030058030300b41000c0e660206130124250324005055a0300c16400f04e0403900413690581e18090081805005074040d94000707100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 247559514 1250 247558264 247558307
    0x30203011b09050a080c060307021504060506010e0a14040506030c06070302101406060a0e06041a09010206071803081c1401080609060609040209060f0a12140307030f050a02032206 79
    0x618000c0d07900d400c4086c1d41c041c0640320000c0410008c43c4200200310380d00000822175140d034101494140b000e4101038a02500264145d403080b4402d1030a00300080031100081027280707240b074501082c4409080001c22685c0d141c02004003107081c0351104002403403a54445d41c06020080f41c0341500004440c2c07090070880c4a03c4e1f000c001c1100035105d0074111504400581013400d40c040c0c1c200d000071410322842c0c01284181504100c028004031844001d03000141e401d07020782d82150f90b90201124003981110041c0d01e80d410584042001c50111002004609442d804002d1049549100402030743c0130302603440d600c1d00d444070042003010070500440360001c000c0c0001c0c0a0030300301080043c40841010304042e10542c00c41d004510241c1d144141da107103040002d0b02d80246c0e1550344d00d0240705411201e500351070f042040380c02c1040a1030041700f26011113506072614501e0841c0c508085600741c210030f01220035440100309140300160345503041030100054154100000c1d04004e002010300d01ca801100000141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 247560764 1250 247559514 247559519
    0x6150e1305030a1b0804031104050a050405061504020d0608030a111903030f1d0d230703050703051605010f141e060406030b04050f0105090303100b0a0504030203011b09050a 76
    0x120440e59202c55134680380c81c85010305014408405107400008000e0300340090000100074601e0101d000f0504102d40c00c01031071390742d200700ca0103503682110000c00d940c002c0400210300071860020a240188040d000508110340c0030104c508803a050f810050301c03540041840001d0903800810302031048410006080d07102d40410a108401c80f0540004003810744403da880c0a002d0140d1119045002c3c902c0707c1c2c025a1422014030340c071000b0008a840000b50340400c00c01d88950921040c075684401c406900380350813800d44080741c003500003010031020003000300091510000c409031219425030085000140d80f6142070718181c100e540d1952100c884600072400c10804d003401040c43c00c6c80d041c0d40b207000e20203070352000c0000d0000d102d107420081c02c0c2d1074040140424032000003040d0030079510000080241d912881003040d40c9000031110002d80d42500300e020302403000400d0251100301e0040c00c185017090344a42c0040d00b0b540402c60380d101501d042c02030180e2a584d00a40000c02010300baa0324004d02030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 247562014 1250 247560764 247560773
    0x70302270a2f030a180b131515140109080a08030f1005090604090804050a1409010e06060a0c03021203010e0f010b04060210020322080a121a09070c06150e13 69
    0x70007014102c18950b200e0082c281141111411945d066103c0d030300b081545490340c12015040c06450041c0d40460502034614861006840b0b0700140042c06401940c10f58075202e03d4011001c0700300c1c000d60400c44404000070b4000307000c01c0881d20f03040c41811035946034030741569002d41c0c1c0d0100825640701e01c030b041d980c01c00c183d0b1174090960360407000030342c0c02140c0b6440d5800c168405204a0380304a800030b0620000003618481031720881d1110340100c84a1400743d98901e0100480d4000703840071030703110b20200110040d260240342407050325031285c01a1b0b54015a006100007094000f41d2210700500204410031265545400f41c8a0251160204640c2440d0500070000e544000c2d00c03142181850340080404d0b111054400d008070f17014803410301c41622030800d20300403240f50050b802040c0440d804035420400456103000e601000c011a0300030002140905080003a030a101920000078402c100c10500c001c18010700403103942030041ea1801c801645801ca2803518504000c6c2161541d2004410010028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 247563264 1250 247562014 247562017
    0x206071205101e030b070c0c0b09010f051b0109030f0f0809060109090512040602010b130b01080c0702040f090c1e0803030103061d010c0f0e12070302270a2f 69
    0xc0e56000f036a4101099100c0f88422051500c0c1c10180207144501c08220450354020303195002c2e24400c102e59000f0030b54540801e480ca002d00c01034203003c03d882c000c0802081d40b00c1d401a0004008296403459981d00d520075141c00c40d4007a48003500010308c030660000f012500140050101100d501e0080c000780303000c2083c96154036040c0615080141c549418000780b10007000381d01e0700117220703141c119902c42d903c41000e402403407080c803002e0050b06103075401204005148a44000c110301a1a400703101da40d03141e0740106544c400c0f40c0485c3e1050ba6414100e050b02d24501c10100c541d445181c9000c081c07414050100000480c0c81c2d030203041880c1d81d82c0144402e00d4040140c5e41100d60050300860051043d440c584412480111046003079842c00f50460400f5601c148a10304600d05601c0b00c2e0b0f5095042e0041c0000784241d954000d81592220808000509084074a036071819840317540e01c002603210042000030030000390342500b111500e682116800100f010201c0410340c041c041c44180440b0b09030301c81e00b120b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 247564514 1250 247563264 247563269
    0x803091302030c040806090601030210020d020307020607020109030f0c051507050c10020a05100204090b101706060405060d1a0904020d06050c0f031806010609081f09080307020607120510 82
    0xc107900800450800c41c607201c00c0e100644081c1c410794105150400441ea5581800d101c241c1c8a40c4030040e03000400d60020910340b441b0440d903405585007100396002d0000d01d5000c03043c100e04000076054000049841d8001075510075200da6100c410300c034940810000c04110014140305590743c108000d0300020b60000c0e0142d00d070311080d990744480441c0340708141c2c14180c031420041c2c55400340301454041111964020010744000d10410001c2400100a00c40d0a402d050010404038a0b02c02100b404100e1864115030312940c0148007629250b01e40c00031441c180c0100c1020200c01e521100301c801e44880111800c54080b0300be442c10a407916060700012000e034089034014140c141d075040851801c5e0092801c44030340740d00008010380c0c2da003032014444c000c4083c4101c208a40c1c2c0a282d00110725184590501c104a44520004100044461050127043d8181c06d07282c020700f55443c900707800010410740281d4030444054014005900e050000505450aa01c1c040303103425140104000c948014240c00806 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 247565764 1250 247564514 247564549
    0x50c0f070b12090106050909060702010609060b030f0a0f110a09120f020607060902090f0f06010c0305450a06050c0303130f02030105090c0f0108092104170a020109080309 75
    0x25143d04032568010507a41d0000d0360826100800c01100c14030006106000f400300b0b43c003c00000381e42c2e2080800f1a45039014918001c03108201040c56801010291500300700095800500300b030a85d031001c0c04591001007030303030480d01001c1400a40031380c0180c0310700c0040034111000c003c116816071700d110f02e00d801040d0081c807561020541c0010b2000702c0c1c1c0011440c039130103403030700c40300f1708054665807510102100c4152481507a000000c03000d502c80d001c03040199501da02c8071400e100010048002e5403440e900744444210031003005990041d042c0c0b8100c00c0100b20300b051134016000d40014004200e5144d04400103122040180c0b400c2e86c0000400c8960080c1d00e038051421486d180d19044446080d92880130303601d58280410b0116138400400c0c4840110821180c50340182627100041d075084004554000050300103400418042e0220241e44507601c0342c80010a140c5a01c940c81840c40013030341010989964880181c440441d600001040054611b001c011030030084c2901c001000d00540f51007450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 247567014 1250 247565764 247565797
    0x8060109020a110304060905120c0f04020d180803090705010801180218131401060e1c170a090f050a05100309140703030c02040c0f0c12090312050c0f070b 68
    0x445521641c0030560b10f00781e05082d00d940c0c1c1e60b100310043c403150050180781e2052000c200c0c15404103034006242c0081a4014040b4100f42451008202c0250050b0403201e07040340c2c0b03030008a40f0100220016122003481119040d8032410a5100c1601d0170249412a5040c80341c0000184848400042015035103500e070407015945640301290750307408008025a0b117411141c0c02c00000401c3d8a103801c03005003485c204030080e95681e0390329012260081e45c0743c691904100703800ca12014441e02041c000c0e10782c40c001d5540d90000d0f242d103c404070141c0e00030315032080058910403061000c2c01030b0000440003030500b2039451622605010000e00072000d113440c20814140d440c1c1e03440c020003a507140481441110702d81542c0d1010780c0ca09001c1d1080c01c80001c01c82c49a03180c4108010325501510903600340b03140e039558800c401555940d44010f030400700c4818405005200c1c00000001c0d02c8030400084442055540b103441c0e09014a280780b410249000c010342603009650148142d00c206010340e10300b0301e20802440e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 247568264 1250 247567014 247567027
    0x60b120604080f0f0c0f150c160501020702030609030409110304030f030b0f04181104050112140c1906020607020703051b0402040b0307210b060702060705100e0708070b040806010902 80
    0x3c85100b048000c80010401041421485e107021075014050306010040d40d070a0f60280c00980d12070b80c0111044555980240010341e13009821042179000d4510640c00103290180315000203103003001c21038041219500c002010300802c409030180713040801690034800e0031814280c0e8058400c20b40c2803411010036558001c40c0416566030400508101009030040260000800f070f20341a40720848015658814107440315160b034180ba100e910304070780c090030582c40c40005640c1c604c54401c0c050300d80c204c040d100d0441090310035541c01110344262021000d901c100d0f00c0c6888006803d2480080100b01990403140b02000071070808201034400004034000c28840d0710380e91001400030300031504001c81c1c4120110401290503008489003000e000b841d1103030690007482c1803881e4142c40d40141e046400004c180700010050620f240036016040c0705005982e191511902400100c0d0b0745068203640030340c0120401c00c01c521092040e48c000e802c60154051502d420543c4895452170103100e02c00381c0681c002030070b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 247569514 1250 247568264 247568287
    0x806040b03150403050a0e0607080f0702190b0306090106030b0f09100b0f3103060b040905010507021f0905060115030905070b0301150504080a020d23030304060b12060408 75
    0x3484109000150200381d1803e150400030a5500140c1e1280b010410b03401000e0303002d00e032610603141c01c0d039449a919440e0440054028080e9040b02208030707002102c414aa140c40982606048007400e14806119100d141450401c6005030041c0e2008080c10315280b402a216100c01041800380b14064039644455211802d03004115940c0c0c1d40010131180d40403903030720500d04512000308058428201c2c25101c3c50711640710b14080a240c001403400448028208000040345900060034203030000304000360a03c00ca803501400d54008995441c01600031100300c0343ea82c0803044e11940c400607401001c01c00105255500359a80c1010700408138213100e0b400000311860300c1ba8100e000001e034090140c1701a259030f0326159203943c20a000e201c21103401c80040c00d120b541304400b61001c68a00340e00420103000701ea0280a0010911481030314a984d0414004050802c81d9034881d80001300800103560301d140a0805004980d000000c142c8101c111106200c26a54002204c64006401008403647e03250500c0c134 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 247570764 1250 247569514 247569523
    0x3090206092b03020c03160e040303050705070c06030e071406041a091906120207030912033b1008010501050307030b04140108150712090201021f0b030d020a030806040b03 75
    0x90381250310030503402c2080540c041610154003800382c04564000c190042c14400b4142d182c001d6225803080b0000140200c1d1080d00403a0304880e00781080d40c5080b00e0394940340c007800344503040300012039201c85142c5440c5504000c00e000625000000e0926540c1180010344244540d100e00880c20b84250107041044016204030790382804000c203c80c0d400700014098641e559070500c103c0000ca0585081d6420180c2c00d4002c49054507031603a58801310300d00f44820070748400860031040e42000394080340032891640901c034070030941c20f0301e0011074205000340b10f0712080d145030303988414001c454044904c86d00c0c581040e0f1007810345401b401c040b82c407541c65000c110010a2000c1c00c01d60300a0405207040442208500c1e403505840e8060140d90710171030048941380c1d05002c26604070000072020120b01c0544025980424845032051040d150030f4120b99100c10b0018041c0140204141e0ba0743c01403204601c0c08009920f1160b15500103883c450900c1c0e20054a001001840c0c5800f031510b030a481d4010b59402d11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 247572014 1250 247570764 247570819
    0x9050402120405070b03090a121101060303030501080c03010207081e070b0c180f030c060307020a14010c093204060302100f030c14041e0e091501060309020609 70
    0x20421074640203280d0400401010594054446009450002c00c000248604507440b41c00d82e603004120f080b405540d400711542004040c0c1d000c014900202000840007801000003c0d07000341d401141e2541000c0c540c6051281800e012440781c0e104000c80707800228102d055074060030361b20803405040c0c04020141080b61081800080c00801e2500400c1031808040c4083c05c54400542c580307420100018081c0201010841c0d20700d0360640c0801400700d071354a808002160300c240140b06032100e01ca0107540f81d0f001c0085080340810710b40d46412031102c103180d2044240c0005d103420f040100507040040d0323448000c014004001000048000c1c2d10110b01d8030f0b0358010400031030b03001c0d0184801122180004203810314031002000000d050211200d1414811a942c2e01b01c0301281103441c0c41d15250400c030001c088100c0f034414242c0d00910b130000814941c01a62136200e0b0180c24080d09800c803907281031344600507058000e2424503103403280f03040141c2c81c0c0318241c501c00030f4142d50510001c00a50b0340b0741002c00545 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 247573264 1250 247572014 247572019
    0xa0b03012a020c0603040f06091401090f02150f040e040204020f07051b0a061416050d090f060914012001110705100509060c03040c050904030915020105090304150905 73
    0x949989074000c0d0410716640e6040701d903402c2d1035039881c0b90b0040000903c416100508904820003002000c550a940140040303481000b40042e0940540401400c0d26168001920325040405010080d0308003000184440c41900c45400c4c9802d050b8034081400f805603014000c41d605140b40050110340390f550480303c1d0040700306034098a4050501d4517645c0c0f4a5107650303510084030b581e9011407560409049880035100c00f9102d6142c40d016500e82446a50070404844804101d420348000202d402805403a40115182d0f40d801042420003025504008040c2d202c6010003607218000c200300d481c4055803901c178020902e0300c0c1c0c4034511003050b505008025160001599413030720400b41c2048100c5802000c0151082c429100034a010050000480f01c04840802d9a07400410005074145088002075a200d0700c00c0611082e40b94544011403d0a84111022004912080c0061101d0f25080007010201c2c2000c0c8000e00c000d140c050110360722406180728000305801c41222000c180c90040e0b400c103002c1c1001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 247574514 1250 247573264 247573301
    0xa091e080f19020c2e050d0c020d1706030634090f080109081617040e0f010e04021809010209030313050103060815010e0705160f0302010b060901080a0b0301 69
    0x1d91020b002c041e0040c004600548241806414503042910300c112103468100c00803014452600030465014180c00c030b050041100c00c0145c901c4180282c0706d00c8600520380e60043c9504900307410003414920200c20030310280c00da414200b10003550005040399115996484003103145aa0400a030480500c2558080d0781503100d104501031175900c99680070860704032140d4001855030b10344a0382c0c200d407c00040a0300801080001d00068001c2c03190900701a44030320121003080000e0700c041d104a070010307001890074058003000c0c002441c40015600303014120100c0e4079425030a2960000300100810b0704461801c111150008190140a6042c2c8420f41c00c00782c1680d40e20f080f86001064124014041c45001c24501a008a101c40c0d001400c80201458455020300707503400c1160111200d50000c00c0c510800c0410014200c010b81c92800140d8118824013584103092801c2c42c0103405d56882080403409910184285c44580c1e9000c0d40f8250054401e00d40020111420000b04e8058a108003041110091 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 247575764 1250 247574514 247574527
    0x403030e21010c0f0908071509080604030309060506090105030a02090a02040504060b0702040f0209030d1209021c02040614030d03022d0304060c020a02010e1903061509050a091e080f 80
    0x101908801c200e1640c40e0f03244c0b101888450000d41da000c00f10b00880700240e10109042c003494010010b0a20100782d14140485020303039460322a813a1a00071101100029200c5990504104050080503000030f8100c0b048000c941c1010b022940e0b0b10b110780400b03071090310103101040c0c100c916981140c4c0940805402441855110011701c50315074800701089026030310f84008601400c9061090798400c42000340036003501d140070f080442310482078202412400c0e6035082594016543d074048440001c050440646401081e80108003c4519075401010b41000c40c0c24030820590300030448a5030020182001a120102c000701d07017560341406800a02d50340c410b01c0400c3c1d1400300803009107100764031409046c0030b0701d441c842049072960320b000e100078003280115944254904d0906810000b40201c50903c40030350750f03030382c0b104001e440202c20301d0509031b243e40d08280301c9441e0500a00707900c0203a10390107005004c25070703940050310248080c2550301c1c0c80c482d104900c20401460308958008180d0180f1588402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 247577014 1250 247575764 247575829
    0x9061d07030308090106060e28060804020f0414060111161d07020708060c03280c0906090b030a02090303160501020a08060306100b0d0605040609090501150b0403030e 73
    0x1014082074003c0751000c40091140740d014050391041c1e50040d0788002c078450810060000055031003013800300755407c8400f0100c2c100c440c090300d10010169540c1e06901401c003801031050b015413002c5424011800c00d61064089060900d4180c1c02023820301e803841301c0407a401701090525000204c10720070072200341c0d00000c0e5001544a460710201883e107150314143c55208007683d0380d0480d031007440344036006903000038101e001000146600455103e000c0c0e01c16280484100324002c0800d1824140c40c0d6110706100034140d0240b891800b5103801d0409400041c00e05850b4180be00004004a004039000a01c00e10740e510b00340191402c03071061200070703042ca000515105003c2e40081a1003030000c0d540000040f207601d0300213003143c05204984030001140d41001390f060150b0380400d000050042d01c464000810351244d100b50802807030584000904048989001802d40d20413051440c0e0402001c203060140a4040e01114201c170f60505210458034050320105500840d00c2c0013100c1811a0b4040c0c04d076605 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 247578264 1250 247577014 247577023
    0x70f09170a05070e07180608040609140609340308070309030206281715030f030c060a0b030109020114030402010e0d0b0405060f101418090d021b1309061d 68
    0x74101511004030108408542c0c4144040c0387c890343c000115840041000702d04154856030200d0300031000703072074500d40e0718040910b02482601c2c0800254018a01da41c01c41c00031100c0131032500044d5510060030700c405007000548802d140000341c82600000760794010580a29a050020f540c003410081c0c80300311003e0640c4000b080e5100000c0c0c0c6140c41520141c85074426050f9012120320a00d41d0103154544240303202e13940c815004586d806200d0b00541106014040001d096001c50a40c003d040c40e1030610040400d9448400b009402607042001d1500148c0c0c2140040c404204040543e81d02e07562a80012505440d490040641048501c0d4040040c00815504948214082c800321809511500000200c262044030030030003041c440700e0188030b18551a42504056080100046000303081501140c0c64008180e0716000c1e168403081c0c0b42008190144441605601480c042141c0140c2c6040802c0021444280011040307554100e110700f08003142c0e00c400680c0319103d0030207840d5042d842699944 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 247579514 1250 247578264 247578271
    0x211103010306110304080d050405070512030a110c09040305070303200d0c0e0105090d0606090e0606031603031e021c11010f05090c010e0d050102160b070f09170a05070e 74
    0x30b050420055000e00450b100849001d954844419460800782c0d6486500800300030300122818003800f003001480341c1d05c2c007015800854110024503660143d414014203008281d502072071003900300d5440e1440681ea17403030002d507000d601410aa17580e50105d107811001046050200c010b101440002d14007121030b41ca01900750007080020410070302074001000d5440401000629000480811040a45080461203903211070b100780d9010030b030360307450740700d41d0003610018075800c0d800340d00003810016513103410850000c0e445540c031000d4000b10f0550300c0c000c0406440340b0200c210743e02c084240111091003006040e4999488035000000d03060340c2c40e00200341c02c09641484036590b0910202030010880f5101e40d60142854000420380192403d00545481c0660b5104c983c0c000d0000035400c0100c0c0003800201040f48035000c00e5128115117240c1510000e0b40500070000b085607241840060070341221103c2c09840e000d945881c2c0802544052a2516090107001403c034020854005680b4104a9030a0701 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 247580764 1250 247579514 247579523
    0x7051b03090103061d060112022a060f040b220203030c010504060b0406060519051c091a0708040201210e15090102130902030604182307050a0302012111030103 70
    0x1100740d66651141703904c00d206004070105203030040469150740c0076052101030002e030940702505003186003240d18403002001c425880b5041000d6041c0425840511a03117034001005e0461425a06203a290a00311800081001c40b80400515410071141c4150b8090f141c45a8000c003200d955442c0c0f8074503107000e4007068030115600c074104000b10300c031481d00307000d4101604d03984e80c0c2e051b0600c0d115402d040c14204043c0140b000b40641040f140003c8008800e458014004e0340102103038081c02d5181451025042e000105d144008200c144038000798080000c4d9040703502480e01c00502d5074050303401d440c42c007520045403003038034a0105513800c410004903030901c8403108030102d691255030b5403509500783e2007000c048515026420405011114865014580250b80070304002000e001008400d11002d071645000c2c1c1b00c061070340e5000c1900c0c0800c2000c69241d56504d0000d03004032840d00000c00d0592005001c005d05100455155204e02c012483c0c08040f040c0a0300420f0120811246015000398005c4c0030a95 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 247582014 1250 247580764 247580771
    0xa03050a0317090307170909011e0e0709090c17090a060605030304080d120608010903050c1618110c060103030809120a0e01200115050a08061003030807051b03090103 73
    0x22400e111002071403040c190840610314140880e41c0d83c4080c3c06c2c0b4208910410700007440000d540f070321540032071400381040f00b06107404580aa18680703c61240c50748001d18a4103807101300614142d20481d44001c8540e2104c0103d540b0134006070607100f134500791401c0407140c0e2522081241600c400500c3d60748041c00341b8000c02180d81c888040c15224880e50140800c03950141400380c0c00719120310042c144803503c22400058058403440640c2c2510104541500050f001181b050300e42101403040c4051210240f202185240c609540350510150b0a0320701d8141c2c50b0f80d01c80b01c1d0705480111044900b042c0103001525655031312460003510010080e150304d030b071920034005940b00840c68070040312480301042d01d40f14a6021203800444080c040480131180c0c442c00f000d228042600709020b40c06000745441e1804001350b040c4420b105520b101a401105580c0c032107014031a458023031500740d0050f00c1e050318041310036a40703a06042d215842020a4204441500c201e40f0507102004030141c8117442d426078090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 247583264 1250 247582014 247582037
    0x10090321051b070507030b040615050f0a05060a021e100e0a11190b18121603060510080601141306030506180f03040f08010f060e040318050a03050a03 66
    0x8001c844084641050030700d44211a100007112031000341401038032500450b00b800f620307030742d070403a5140c404d440441d40551a14403640390059461410b45c00340c1001d964034050240319000246103101980300d00c900030140050741c41025407003400f00441e4250fa0b00d101194080c600408150384031607082d21004231516101c00c6d500c2540c000310300c04941e1604001b000386651034960802500d400d8a4200c0a4011030160300010407150b00009016500c4814442e1402c802500b07051110416205501e041980c00010350b00d10070240318005407007034a8100758001202d0340c818080c050701d00c045800c0380109100d040c000164000780303d0103819640a00b910b001c0c884900c0204110291003003800010401d4104200060743d001d0985a0780c05c170380c9041c108407810040d180295600759407081c0c106240c0a9203000b0240030100090295120301c40641c10100705003446c1c41212101010f014100808004c500b1b880c038600c42a0410b1400c01506006106c4900ea5580b8a00650b4642c1030120440c00b01d01c080000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 247584514 1250 247583264 247583327
    0xb0904050604110409051005040c02010e0601051c0303021e040312120221060d02130b030c030a080a08130203151f080606130906060e0103050616050403030e0102100903 74
    0x14180343c1c03100c10600a0900d4142405403000c1c0c00b0082c030000c00c039040500c00054640d640d000780050050380707400028088028510752402c1c01d005030851800341c0b010700b14118580000c50550102260076290058645034031000404803900000b5501100c81004100402130000c0102085400c1480c1e40380c801107003501889030016401901c119100d8043c3c0d1030070074020340c80c0650413507a1044d0014820041e5050b103a0002d05039900108001d1a015541c0b4440ca01c2e0381020403040e00c1d030400850013400746541d10f1b03a0b180e819209080d00317041001030b21804101c0c880e055500701c0094aa008041e200c19082c100d020100740c420480c1c0d503403403419001c03e004440e901d42e5012041a5281440600846c0c2e0356202444880f00640f02d44091481c1d5450064011510a12070500501251050100207504d1400c03c5c0c0d140c42009007150314612490959480095042022035003140d5140c10202114544000141d04100000c1d480790041410600500200340c2c2c041503d1900b0380701c044a502c0503074554000f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 247585764 1250 247584514 247584521
    0x12030a091703040b09100615030509030d0e070609060201090b070f020f0f010f05010914060915030a05071508090601120609080d0b10090b180409050f0c090a0504050c0904031103040b0904050604 85
    0x7440a086523802e001d6040c24469004241d10040c032408803403030a52001c11030411622218007084540c4c0001c4028006d05038042812001030402d48000d001c241c8098881c212100e10140c40139007030000164142880364000c0c003890889520030000da038410004a002c240c040c0444600300b2140302d01e010b00109103203699101d0381c61282e01120400015035980003c2c03145a00001d00451820902031898800d180d4040000c51103041c4100d0140c171485140c000301090722042028000b0901c40903100b00b000b01440012502e0444025484100b031035041c0d4285440100910100600181400940088100455080300c580c6c0d1105686591200f03440010440700003a81340510a82e00c0c07000c005070002e903200c03509007134050706d0b0040c0006924403c99440030f20b40706e070f506900c1c0d80c3d9400c80b01d40807030545098040964060b4840001303016034a85036607016190120035040d01c2c41407100c0004181403511484c00d81c40040c0c3d55500703c9544640768582c600ea560010640c03903104078105400644142090f00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 247587014 1250 247585764 247585769
    0x30203130b0408100e030d020a05040f050103050402030a1106090a030b15090115050d1b2106060503040f0507050301050c12012115020906131712030a091703040b091006 74
    0x2c0584407180c01c0c440454040d24001c18078490324403081c0719000758507d007440203110440c0d840d1100d40d49d80b4a402d0000051507465884541414503003030400c0050703100403d450310b10300e80c00001c01c035401604d940000c059008412410380c00030108000842005180c0150710301440404590740500f6801d6010001560000d010b603112408401c01500310641c003c0b000391408000b01c44021400391810703000b44044c04c06d000c100d0b00028402070a541c50340404080c0e41e52106441d101d0600c0078a0401c0c20141c018440907000a01c0d442002c40780105000040c0312071130280500400134495820000700c01586500440ca20f058110301c1800001a6480d0342c0c0042c0c81004015400d0200c0c0c640292540311941040038001c0700046e070200040e40450303607003000501d048140041014155401c01440183c00b0454500c240c100e41e00030070240c4251030030700d002d495103c07800340c4001c95551114a01011103044820030812000404030501040182c09082a0700c101040c00031140f42c0a540100c1805a4200e80b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 247588264 1250 247587014 247587029
    0x30309180a3b010e0d1112070c0e070c211106041103011d0a0209061f0207061101020702010e09100306110d2d330302041a0f240304030203130b04 64
    0x18240c0d141814010603468007034014150540d010946040001f0100e51f00c0800100c03100281004240182c641d8590101d4000c003d91800d88520b0b00d480c0d950135011201c1000450905000301211007034684100095a17140407004d00b82c40e0031f403c0c1803074000e0356400c40070b00d03240c441e500300b22040002e042d003105e0042c5191141402060011001c2d02408000d40f005800710f6004070014203414914201b03800c512003506040d40c002c203461440d140004045034041c04110391141d004020a50150f80d01094a101d01e8000319288260b03500c8201101c1d1087c10320b80e000801007810295501c1c00c03d407045c805040c194550103824008044151005991a0204400c0904a156a000c50034208080e5801405d0980e900c00b140001100320300c0803080f407400c0808090600a20b190018411405c00303001d640c4040e0305441c80100b28030082e4001506802d5080f031860b010380d0000c001340081c203500d9a1125005200d01c200700b50340c4e0819040094032a4091fa46502c0700c0029142c00041d0038444608a41c110780d1607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 247589514 1250 247588264 247588273
    0xc0d0809060c0c1e03060105150d0c05250c150807120204091107060c14090d020411130f12170a0c02060a050a020c030309180a3b010e 59
    0x2000100040c0781c201c0d0303518009a1240240c5003096840d810400e06040c002c05136480c131219403040c101803034550140c204c1b90103040c800141c0b0030884c0110080e0340c1030301003546c004128071554400444450003081c60300030003800380941102955455140504000303004040603080300340c45d62126242400e00450013000280b01c040040d10240c1f00305580b2a422110b07280140c0303030035039601111041e42c030b0111100401c0d400010705941000981c0c071a0f94894001410300c0404ae041c03090040c9801c2c00b400e4a8070740a910035039100c4085554540c81042d50004050f14180c4601c030b201810105006180520380e10040c40c11008120500d464a03140c44042d8800540c40c8505524008602e5a4000d42140001d110000e12841d00580d5050007a00264007030307a4800d0b40b181c40451009103440000c02006000390010040c044007520b075280503020407002e11002d0403003600c0d9004038800514444d400c2d0100e141241000d500c02c2000b184e8101c5550380300d01c54041051000c52040350890301ea001006115520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 247590764 1250 247589514 247589527
    0x303030103150902130b040b0d200a08070902250b0c07080c0604141605030316030909020a1206080c09041203061a03040203010e03041a030c0412050109050c0d08 71
    0x8103848001e4102c0000c0c4000700e4049540da0110b2144002060b034078207602e0711011108031b182024801d010f610a000c40b294a403201080e25200c445c818041c0f40141040080101c1c080b4a40750038100500908101003101d21103030751200d00500035008444843c20384280000c81700c40300306c0c42c0d0001e500c0180d0482a0007496440e01841060b407988003a0342112120700600c00d09000b201e050060620490040030491001e100b0300c10824141004407c4d14803600350300a1080c015600d000094603500022050780b940b140056050655030503007141e004910b084d00000e40205400d030701c0b10203001d600c514584184802c1d40c4800b0130341e844900080c0303c00d4210002d000001c020a47d50088441100301c03e04000803801d1300c4102c8240100c1800a580011075000420f200c00c500707091048000703004010014500b000e00740906600c01c010411359020036000040045902c0c0c4486c482160003e00e110440116003600610741107020300a05681681c40d4007694514068600b407100c00a0b4016510006d00d914020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 247592014 1250 247590764 247590773
    0x607090b0a08070c0b0a05010302130c020c090a06260d0e0d060903030608030a0302070506060a0810050601170106020a17030601050706020d09240605150301030f1a01151209020303030103 82
    0x40006001e50700304490f820742c4401017002c8212007405808248070205266042d0b005100b403205121209484980c03a010042c04450750206aa0b80c00440480d003a12a5407220708403140a01055000103070f400d92100361202c0f12103103001d8007580c108c8040c41620300c08041440b0a070390010b151420035820900900107030001400341c0c0e000e80310303030f61180c200010580d8540340600c2c5580c100d00003020100c0d900050740c0b03090050130001d1590012088415051a5061031040c60301c920301800086401030300d4038081021a8003031800010f03a0103428100000075a52980700070b5a03041070460903188261802040c0300394901c071b681240c2c854001130b1070f21f9140c12070a50380d12009600201440c600c0d01d9451180074009041001c82982c01c0f041200d101071607038103003641b43d4115001c03175000c503121b000e130030380c1e00080c412110007035070b0449400c400610040d41032400c0580d16031038008080484036004000204254001c400007126445031592100c4518880b0b6141c1001c0760700c0310201a6040d03209100400019 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 247593264 1250 247592014 247592027
    0x190506100c02061c020301140307050402130501080912070f020103050a0902060a0c0311030c01140c03010302010921240b030a0209181c020303010306051e0412032c0607090b0a 77
    0x411010b00d0303c0c1c1413203c08800002c1241c10a800c503102c070303030480c0c0c00c0c0074054a81040845d014040440e0114681400c080c41020300308150300c6054103100c1080300242c3c243c502407020400c1d617003142c0d80c0710303584e0600b6141030840101098022808280b0341800709107540380340d04c100d486455002e0045031420040417029160341500d40f60482c04c00c804481d521603c140b09101610380c220100c0004900c481c451282c3d4144600006c040040341c500c103200400150380c1c03280081c0c0444103540410a07200050b01a84c1c4d50904a41d00044c09503400c031403065028540c0e03504880401d80b282802000b00402c21010141c0701c503241c01c3d0196002da01040400c1018001031040b88078890104220350001c80e480704200e40f104100300040d005a000800100103101c003500031203610890484038459400150110450000b5020348050321420801441901c4240681c2c001042c030301d43c101003002c094042c002080d26330035208004095500490021442090041e0904c1059880a000035420f15042ca40100e0b4076 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 247594514 1250 247593264 247593277
    0x608060702100e07031e050f060c04093b0c060406051b1606080403020601060e01020a0f1b03050601030c170303040b10050d0b0907060908030f0306120105190506100c0206 75
    0x64004d40500000040643d40ca00071030020780d9804400c4220070741002410301e80c0001c00d0940700d401c001c0400c65150081c50489003910b414040006800e4000a64061455440d0300101001c0e81280b6030105182c24044080c5d000f8000d000c219042c0485076001c0c02440c0c0114843e00300425014400f269442d090903041d0410612840115100d5400e90854003011150a07030015011403104824001031560600041c1e02504403424143c0c402140000004d542d600b800e5405031000e4040c02010040009402e1003c007843e4841c00e030b55407541e4803800c0c60354072400b0a01c011501040c103404001620b00c440c424942603800034001441c01c2da51030b51100e00707440d2002001c05000310ba468202059a5444c4d49a111841d4000d035080044c0e4034126041c5864403550303412840500446000c10005050b0000c00c03036502d080b1441200780c803600c8600104446903c450b4064055500704810040407480365140c0040c24100ca00040c0311b103031500000c0c4540b8002c501d80c0703040010f42020100c0094100321000307240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 247595764 1250 247594514 247594541
    0x3010216081c02031311010201060e0103080a1809150e040804030f14010c030203041a0105060406050a09151701060c12030e150403020c0a091a0f0a090207030302030109060806070210 80
    0x50b81c40007410142203034030440c2c00480d50041c0d400301300280301b01460380b0340d07184170700380000c10100e4208110044c1c41841440700812a490019540840501c076007400c08098203001301800d0b8440d1a038407007002800b10095841a1007429650000d402d00700d1a100c01e000d180c21000c0d151503d82552508000074580354400e407004512285950300c60b910911400424001700d540050b2641803074505903c0003425282c000c3d020000d0500140625500e120841e803c45001e8186550784402d41942622400c172660310600d010400c9148520301c01d500503001c44080207082c05036017107903a291982960038211003007015140703201090a103e442402940700c2d070036500085e01201d0702002503403080651550125011001604983c40f4400103041c180031000c080d1150348800d1100d00b8416500400c3d035644001d0003840b07901f03000c10000698458000400c060326160a082d03660790a2424041d020307510a00c04c00c1000f61500c2c0d00000d0107003005c541c8034040c1c8482d07400303022022680e454200150003064501c1c078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 247597014 1250 247595764 247595797
    0xa0c05070f060c0b06030d0815040905070b0415050415030507050405190501021b03100b012c01090f0303230d0606170c070c060804030c140303040c050301021608 71
    0x28810300c405480300010480b55035000c0d005862032400c11191070003d00346034003903440f290140d00740d29041841d4591003940155101e0340350003407600042c00740c11034610244c250300540030042a401c0c041c800070300c192001c3d0318034078072020400a8212094031a40c4074940714914030740c2e00040c04030b2083d0815500b0060741c0c6001810980c4481c0058080803940455840c20001c2400800441d41c0501c0860f20400250410400c4000c150300440c0d285c01d80c60340d1051256542c2c5001031f060381c4c01100d20401901d08003c00039507041c0001c1c0710131440084c1c1500203000c20120500010180125545201626070581c1d41030403254600e1b5080318040100280d0003100e40d028001b100d10700102c0d10500006000c00c4c0c2d101c1c0c1d00d0380c1c851140e20328502c0000c6c0c4002d044100c100006404941c28030b40c5001110030b42c2c54406035135601d41c01c04680120030800000c0400b400c103801c0c1c61905100201541c00741c0d0040400c1c40346141c4c0c0f041050708078400c1d803003419852074401c0f513041c003c0794041003e41001d40003c5d180301e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 247598264 1250 247597014 247597019
    0x1050a0f0e100201150f120f08040812070302060f0402130506210703020a1703070201050307020307060f0902120a0519150608160b0901200c04050c030610050f0a0c0507 74
    0x19003200c074401074600141e5491885030076a03a90412170780e0060042d00810300030141002c041280c41c1680d400040c06650301039102c8820002400f040700c00401d00041503600401c1c0c507140061a5510445d03084e0014814003000c02d00301090030203114040d80d801030110b800780540450701000391a00030005507001c458014030041a400c0d41c04007204c2c078050f5270b010b4140182107204010400501e9005500d4180300110407099400001040710810b6409081a43d00c84e0b03100380b0100d155200d8840010304407410100c4007207440c1c841d604600d205503c00c5412220b480460407815558441d034072000340c12941720280e075000302d06c02c1581c80d680070750003030b9444176190101c418034405440059120032519403111186245811003800e1320400b405c01180101c1c90914090002444c03040d01009060703140f881d641240290582c100108045010f000d0014050341c40c01864241050f001101c01031b004a00540a508206100e8801c4403141c0b030007198118140380124408075068a48030b00304441510900c8000b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 247599514 1250 247598264 247598269
    0xf0705030f06033a020f1b0a120606050a1e031e02091501140f030c0d02071a01080c0f0d0b1b0d02030109060b041401030b0609041103040209130201050a0f0e 69
    0x784c00514104050b0040e450030482103181080c0881110000f15001a80440c95070000890240c000b4180320b42c803e10072602e5440050001002d6074800d91401102152a204210b20f60300070404880041b103405182c5c640d6404051482d41c90700350040d01004540c003040c00050940c500103004034441c0d2400014505050380800d820300360944d0f28071440d0409000c1c800d20342d03900446e00008100c0c0c80d20818200351907854180c240703000c081d00c4002038110210300c3d4450a078244d0306481880360861528512162158440310b10914280107040e8203018082e4038002c1400d0201a0400c410300c080d2545103a00000c0e1508415500050203d0007003060031038a0440000541c805042c1410080100590b254036120520045603596031281da04000240801c000c005481c10030345600d003400b030a01003002400360002075418421110f2a5a2051401d41e240c51801490800313188074510942d0004255150001e01c80c01002c04500001d00203101049001103443c810240c0016000d003074100f00b0721034400d4400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 247600764 1250 247599514 247599553
    0x3040b0403050c031804110403030504150c0f0b0402030c0a05060904020d020c060928112e0504050a09090803061306030c03110405070e01020304170705040f140f0705030f0603 77
    0x3002c28005c08203841a000d10300c4d051084116160300c0341a02d9180a1455402901900861040b20450311408440c880711038056810000942d41c014001c20921006c0d15282d10160829542a8001e10502c481c00c40181080b06100b400c0e5400100a203041400020401020394414070003841a43e400307100c000d507000700c2027083e0b60141a2041c0603100340243c1d1040203010100c44800407103a10380311000c1901282e060300d0900c0e540082070b034221144144030407681c081c1c00762408140ba800c0d048034240c81c1c0c01c55809405003042c0d441c2100d46815090361414180c064850300000906012400c001189481c60071003500c0c288103802120104105540c1d44544281b201280d00c2561000390001c2400c0141c42d16114080d442501c03414082c402020000c0000c1d0740340580d00800354110620009846008410030450004000c0100309001002a00640401520812195075400841500491441031014588a100d400a59500303819a81e030807041a03014800907000a4060158103401640f0901c4c410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 247602014 1250 247600764 247600777
    0xc030708100902030118050d020f190f210305070201060b041a0307090306060e0601080c1801080907031403070c080d05030402091819020a050a0e040b1b030a09150902010503040b0403050c03 83
    0x1f00500703a214800903000e814640fa086a101d482c0d0000c80e181100083c40d049024201c5402c1080c03902200424900710301116507150022218101600664500e5540b41d04000d2058102c3e44c02848810354500042c48940900e01808080a00c001002c400729102100516400402d900c0e0181c2900d0341e07a04da240856090360030911041c0040400c104140d40c1140040d5001001d41001074075001458501842e04807062550504000c020700200d40744981c200402e5000e5030700b001e40c015282d280c850141c6d030390354424030f4200d80750010140300086058001c136618039900c40d40e803542403843d62982d08000d1081030050a4a40b5800d190b0001c15081c030f001c02451b40f40d11414003000f00c0e00420f40c010000040c03429400280700e40714100e821302110710401d607295003240d40a544a00b07281c071000500c4600c44c802d201d10020769940070081107e584d10640106468a0103084d242c41104e06051600301a5002180064085401000401c000500039640c1d180e1180c02407408500b01801c443d01d081c15607000c0d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 247603264 1250 247602014 247602023
    0x5040312030504060605060f03071d03010c090305070e10060503070c080304030509120105061507023f0c150a0903020603070306030b10151d060307050c0c030708100902030118 77
    0x3281040100003003481805d001d80001c42d182404c0480e00f0303071100c000c1e1000422003001c110500c0007202a40400100600c21040010001e04c000b29a20f80d004000c01c08502c81075809100c5c0c85000180880b50755030a40c0110903448505440d00d040900580305584007402403003c00918160401c04100c0b444c01031401a842581c42e181d90b595031601308110a003c102c0e101510741d24000038403600307a560b400344001c501c124202c5103803035081a0000a14005100400b00c4048000009960220036800d068500041466800d045283e2103213007610341d00c0007481003041e004840042201485440800035002d2003020b4580303440b0440d1640c0c04207080350000e50300391002c40d032104018000c00c0100c1c42641d50200071030b91009445458a403111641101c0d80a61720b041c030042e00c40306010606100400d00003420003604003666824841740080141d80861100c0140340205555040346140104030300e0111000c140042aa4a11080c00a1300030010f03460100d81c159a80c12a81060300128941c80d20b819006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 247604514 1250 247603264 247603271
    0x6040b04050307080406030e010b1e01030f060801110301170615280821070f0807150c0804060e0d0f050d020c0703110f060708160201170a2403051b010504031203 71
    0x10420301509459024060301c0c0f1941001c2100803441d032b0bc00711301d040710800c00d10740400d89401d08401d1000420700d41d08408a15400d0070b5240c1171411a20b40114100c1e0b002201000c0108654031110b612600c094900320703180042d1102c801424a028441c600800b41d0121959220203454840038a0110701c0713901400d0745400c15100942004810441d10107055a208403592070815141e440c01e68510103180c0090800402096040034800c0082d4000403c1700000002c2002e4419190050614401190110b62a0b810050b0b801c000003004500350f851840b40e81c41c1c00c038010584400c140c44c1500500002200d0550038442540c199004010880055006001c0d4502c44842c1906010b000281404c4480c0951000c011501c0018040d07011036043e600f000780310350258500c61004031407a0480d2041000b201c00c0c410301303000d54103109501c80c00381d92101c00c00b0840d1441c003840e0000c00c0b010103440041c090382c01c0255000c1d2500751501c90b20151542c145081454142c9070756a00b030001410043e890000307a034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 247605764 1250 247604514 247604531
    0x2c06070206010f08060117030f0705031305040b010f14091005090301050f13030525031707030b06090d110d08040f061e0f0c080c1b0904020306040b0405030708040603 73
    0x4050101c80d0161480c1d0404180b11414820581ea03a04010f00c81d0301703250303220034054030140b41091041d101d40c030b52007144040c0d440107541030940d40c9400c050303170310120041c80c44000243c41c9058401e0303e200c914103841e00f00d6509158501a600c0c40740c5101c51107041d200420803c0f540d03030703106441c1c0f6500c5106601d0700303a15008540285421900024030800d1020291028009900100d1090300d00c10b60b81417800a40d150150803061618050000c4d10b65400c080101c03103030b0100340d08440e602c00c4131440d88070340e01903664031040201c00f030360010000190400d5040201a100c0d040034400c2d0035200e0f010b2107c04581800040224070140c40f208001e461904001c03c06120000090004034014240c5250101c00b5032518045030307404c0c0e440032540d101404001c440e50700c05540a0b44d40c160441d9082441e0945035603050380060340b00c00e80381d12000f0103c4602c10444040d4500810ba290003107802400604603a42da07076640401c81100070f4410380c3c03248000c2c800c880c00580054010801b0740919074001c604d950707 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 247607014 1250 247605764 247605767
    0x405180a200a0e060306030c060c031920010c21020c1e071d010e040317160f020303011a07080c0303090a110d030210020d060b04090c2309042c0607 65
    0xf409052068032030711003003091150a03540000d031082c240c1c80c2290926a44e00710a0030715440c6124400040641b0385403c00145101030300032950b15461404044c4800105c603030540e08a00b00c0e51a024064041130141c2e00c032030b1150940a080d00d0075442c00c030400600c1d03c0c64038440c03d071402580b0000400150f54503c08a00100c80078031001000f13010b5501e8820310382202001062000005024a4034542c11840c0014141481040c0715015448030910781c013a070b41007040c400d9410071807030206480444d210620f5042450f01c000100c074120b60100b91910010020204008142c0c1e00046054a580e01c0c03c0c400c07808680814801580901d0128000b0003c0c5041780c45d00e0580c950100251038031a0780c0c08810300c1c001c43d8000c514451080d028040060351040c203001044001c08040c0c00512040d000410080340a004680c01140400d0302900d0315403034188800181802840c101d0700150345540240050324040c20560881d40210608959980e5030700c0d046006800001072003403071201d0580c0000140704989 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 247608264 1250 247607014 247607027
    0x612020409051f1521020d05040f06060b0406020a02060a0212210a0506181b0a0305150303090303041e092a0203090303091c0b07120e030405180a200a 66
    0x41010002c0008807000d40f4001406418076170141e80004240290704111080c00f0398101c800d2021895000c100034181820001c1d400c10070410b044614504d0201301050100d14074056800712042e542c003d048110443c2d00340a2181c0010712540c0652203411000444c403120791014005061a000f048000c1e24000054080b5010001d0725460599280005200d51601c0d10700e42200048551001d01c0680c0d1100300701810060783c01401411101c0000c10b00140231645504036a02500b0300070711007500c6e058403c04146e140e10030880510340c540e10802041007160002034215007821014040008296540c2c603034031041c2c8010510b4888a01031501210400403580342c0f840040e203400e031004508140500b4046580e9101c3c22061900c11040114a02e139004002100510010361010500b0f4090401c071034050107001e001c0e0351206581c2e08203e01c12907410000400c0e502150b00040100141c90003181d0402084803026014501d030b55102c100007043c00c0d4003030100c1072401060b1001c159441140c2d00008106 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 247609514 1250 247608264 247608269
    0x20316090605041404050402030c04050901090228060804050c090a062d09020d0f02070f03020f06040c0303140c011b1b0803010b2203050105101e0612020409051f 71
    0x248103043c0010300481c200580d008a0003031040c0d40025158440d400064a400d507050794041d48130341494200600301070190001c6500300e1090740c0c8404e2040907102d00c40314000ca8082003546020f20070004002040c4600c00b0b80b508640500c003980d00079040c0078041040d26204070303101040280c0b100c0301040302d01b4030062a00c8008200254292175290004010341c40d00550303201d940003903034000c0b03880787c00c040d141e51000c001005d07400801c650300e40c0c80340b820a031240310269046d0b000d40104403190920f000b01141c0e0b0340c03056610a030b840c2e66440c2166019a81d460088081c200d000c041400403290204007449405e01e8910068200070071464001d034014407001402012010101c00c001400c0e00284c1c6060942e815902100425521840202c4007038200b201d12605001007441c80203400414001d06511280c001d02440b00f10090407611481d91441d103a2605a00d8000d140a1150402085118810304a900c6080b8800980f03441e58408148060310000c0d101444040040d40f030b06e2002412131045c2000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 247610764 1250 247609514 247609517
    0x60903050a091403120a0e030a0605060916020a0f03030b030303280204030f0b04030203120406050103050709050c0d110d060303020304231c0201030605060a0c050d020102032403100203160906 84
    0xf070f620540000c0703500ca858107a8001d0260714007140c40030b034150284a03084825100038080f87c200088506080001c1c0500352159400790702010b002c42c200b450140381170447c01645400034500b184540d5580010251646010f4003050342c0d130791000600f59003c0c80114043d504070800c681c0d19024400500d07041003402003a90181c10320400080001030307003c411010f4a43e411511b80b191503601e90405905622400c180c1c01076185c400e5040008004095010700d050f6405401200c00c200c0d141d08026044500036214016140d03010303c01400c00095035000050000150340620342402c1d80d0000311010307280c41c0e0708200c3c0540c0012605000c0c003401c00b09094200440911540061a0350760701055405811075400d400c5c9032a04504502964060f8000c40c00500003d0f2150f5650000480d009084003c8034004555034081c030a4202c400303e20500907039006207100da20f05103440c40505110400402100d40442c1c00d4002c903a03401e1070040c49840030314071800c0f04169840640c441084010581c0e08243c10250 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 247612014 1250 247610764 247610789
    0xb0c0f0c010c0806030d0c0201110114040f050c030601050a05060a0e060a0309060b0d0f1b1a0c0d08060906010c0510060303020a0302102304031b061a06040510050f07060903050a09 79
    0x2010316034400c00d107c1d24550282000d0300300282205049001d0001e0801c100c0c40c11402c0000e000410141c1070050000901540aa824000c7d0803420176449000c28440c50741c1c043c0030000c092001c1e142c0a001880440d0007800c040c100070740103201107030150f00501c3d2030781d010aa84130004d03000c0c0301c01801040503101040316100000c24881c0c0e01d024110300b40c1070010345180312072400710340b18000d0030a00c0d1000c0c1850070360051984020500401c43d40c0d02001400c0841d0041001d40740c51341d0f0150010f24004d6000410520a0340c4e10003004403414002e8100070b8074140b140b864403015002d861710a0b603000c0c60107a40076041e0550181400b034a0b00e000362000010300c519180c1038107808404802682c1580340d40c86004002c0c0e40b00d43c07c0403113180c00d6000c10810155000d6003001c041100319404041603a11444030800a911400104842d41c05140316064112003c2094190032900c1400101a002c911100b281d04000b40fa40f0381200301d440741c00c0202e01184002500c0030101d81c22042001c0200100110310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 247613264 1250 247612014 247612033
    0x305090f011407270e010314010209031e15010f06090506070c0e07050c01020a0909050c18100903050312010810051e180f0106090c030605010203070b0c0f0c010c080603 74
    0x7194801e0020f20003c100680000b403961340060b1040300d030340e05030601c80c034410300c060301e90001c502080e01c203200446030303854501c400c80540d002c18025508003180c000c0280c0118840c440c0501030304801d20400e0043e038007030f01e0551001a10714802c4ca0f40a05655001c0b500708604003540500402c4158100500c10750084c0301e003200164000d19102d01355200084101d000e034407058820b03191030043c0e011032540c650011801d0640c2c00d6225000900715034a1501c02d01c40340d00e804550041c0380c8150403040d481a0103001810402e41001c1c0c0501d86003e11501d054040d860303a9031161401c1d500101a0006041100c2e401001110303810001c4500c860b40b41e00d030410003420102e17a40d4003009602c82c16181e09060590000349000e280f2200000d00061007016641154006d2440500811107402240007642c81c040108012034480d101d414203854040e00110301d856800e4684000464000b05540d401d10020004541c05204400103004103842d0750002140c520318410700608603080051003107009600c2600c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 247614514 1250 247613264 247613291
    0x3060608010e0619271b06081e0c1e03042d020f040e101e0903020606091005060a050a031d07050d060605120a03020d020706050415170103030305090f01 67
    0x319082c034402c121300055074a1408070100c82c0c4111040304108402682e001000a00900144090b51000d01c40b00a462690303d60030b0a440b8110107403204105206100081003040e001c03031000c1c0b5000070b14840f1107400c180002c01d02d840c5044602e0b40c000c40309000072081c04104110802e00d800801100f441c0ca98945040e820f400f50840c140c0040607202d9500494800e4090304d580e44a0a074144510080c1c1d12000c4040785150003034001c00d207204110803000e520b040203520040c8104245036034154064000c5484100c00c0044500300906403a4540c0c40000c40080c80390f403450010216041c0640702c0035101c0d000010003400b100d4074140411180300d03c4000004000c0c10100d54007066580885075402e2800740d500380880103003181d820403a002007200c0c40c0d21a034400d00180d01a03900b40b03e50700320703850301d2b82041d4100d8480246100b0180414000e01c07091000700450501040e0600b613a00d400c071031031520409915070a02080c1c0c8207a0100c0e9a60741842a03503a010f0005880781d48207800284240203c4821 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 247615764 1250 247614514 247614541
    0xc010e0f1908190f0303272003030f0415020f07080715020a0506010b0f09090901020301081c0c080a120c0906030c0306080703020d0609050a03020f010f09050c090c09040603060608010e06 82
    0x80040c00c25903102a40c444501e87d080c03060003400310a8404591650361898480042c24000051780420020418410914680041100c03802201c02081d0750401e89002e0300100710013a4403468800f58010800ca6540c682000c0040c00020243e4600030a145454175010701200c10002000b50219003040c07829a010840c000b40c881c1c1160071600042d41c0e1444d901d100c5000900468211561026080c014807010703110540181d4160b03078162060f28010b801c080090328400900310044008200e28041da08080340c140b2020b004220440d00b0a04008403402d0304a03411201c0307000700800403d80000d0240b100a0303141c4651251081142000c00c0760b20705004980355218924840244180050300703d40c810000e0903008480082d51040c00c4550075011840c001e511158a44200710ad50340c42d004d40c54403003031024000c0001441c0c1003c050514103404500380210300d03a0080c14210002c00070085100a5100c51041800441c0503120011707400782400041800d407a4000b1000480d030780603906101212000750b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 247617014 1250 247615764 247615793
    0x50c0607080a0204051c020a09090f060e0c0424050603070909050c0f031e060f0907030902030c0901121a1b0c0c060703030f05070f020c010e0f190819 66
    0xc0c550303041c0e501c2c1c02099000c1d1080350000f0303400a1001d0015000020908260841e2603c00c403411000303152a042080300b107030f036490000b600ca9000304904001042407948a41c0c1c1408041c8182c500410104021400396284481c8880704051180907a00590880d10031ba00050f00f0300f11921851400c2141b0020b0400c032060013a8201d10b56240c01050b01c4507501412116002c3da04044c4903160303e23018107810016200e2007144604001c0641c0022868039102c4201443e03448010940380041d110280c0c11401005140c07412a01441020706035041503840000003030007401c244c0b603544036407100c3e454080450f0500091000708001800c041c0122000420084089190211a15911440f100e00f01d41c0c81e211400c0d02c12600140005000010b00d58150408840d041c09203a0902030383d140d1140c101d80c90700510f00e601c00103800290b88858258402c803003202d5040002058554540c0000000400c02d201818060f28043d01000c070400420405008008070310612003842240d440d041d031503026003d103498 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 247618264 1250 247617014 247617017
    0xa0e0601150e03060408040609140604091d0609070603110c19021302030c031602150705130b031f170601050108070302042301080109060b0906070c03082206050c0607 73
    0x4681e8480d850348100c000342844100281150803c0c2064140307030a455100d809103000094010741c001c80d50341d504500d00c000c081005800310b03103001d15005040c00205001c0c6030101d4034119403000d2141c1c0d0b001c00c2003154040c40c0941c014040041c03401a010f0116400310310344406504052020300c0d0056000b1500511300d080c003c601d884420352030310000d1741d08a4130102c03901c1841d1001c0244007005001c4009507105107410300e180704100e500764009a0307407002c4102c4468150030400e030000708007a118401500664181680f07240c400c039190b143c901c129800481d02410004030700b5480031031007c0c60110b45070041801c07103404009940c0031206c4503255501400741905224800001c294002e2003541281d00500c1d001c401400c202003000e00c80c054800a010900e400070b440c01c80040303038455030351080030100c3e0100c942c440d240c07210060070311030785800c2030000356200c1e040300b800000403800101c0104082840002c600d000408110051000707150641c002c1c108200060007441011140007480e0354106815 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 247619514 1250 247618264 247618289
    0x70c18090c0e1302030d1d1806042004061d100c06180609030c20061b011b0918020301060503060402030907030507091d0307020a0605030405010b0d15050a0e0601 71
    0x4803c820714014009840094141c4100d1307554514860340054441049031a901d0b403250310181203000c1000440804a054408a4225000c105945060341c4001c07000e144406005010a4503100f11181d960800d40c005000f2034000c6c074030f456241b152aa00035004100469a01c0d1018404000042c4001491031008040b03669030041e91004110b504d0000c4401c6511100901070b240ca18a070040600440d2401108d12035412120001c1240020850420011014041506001c0b000251900484410026481c40e541e902c004d008140e50070001810400001d0b118213025503e020f0313a01103040c1c0341e00c0b041107000340f041c030040c800711394401c00700c03034003c2011500940c07070f0307100da64013117060800f0f603030000b01148615030000941e5402500440012a1400103103c0d03080300c40051541c891251080017988403180301024040540100017650308103000b03100015104480b1408074844070b200c03a1059038644e4600304c200f011465140141c1d5031001580c1024440762944000056a07010103000d4818800c58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 247620764 1250 247619514 247619521
    0xb0a2102150702030604060207060e0c100c0602130806060a0816090f0209030d11010f0605030a14071503060905340c08030c09040605030303100e070309020402070c18090c0e 76
    0x40740c1c8299005140c0040a4950b6400c05103000300080d07102d80030031035070a0304102101e1500c14000c158000800c10203421003420031840300007100d02c038007204411903c0c03036030074000840280300407070b45d5201a004060007086603080420410100c0411a4446903060340080782d01d080c001d8a2510701001c543d54000041081c130480103000c0040c2c0121310a044e094071562030741013002680107030901074404100c00204145003440224800751b40590044a41642c8510f0f200800228650040c2c0682c070050340c192002c154075459920070400c3d403002c5100c00240c0742d6200f400240480c0c45556000921800c1c10500080070700e20440e030081e45c1841c0c0b0140700d5002060b0656413070080002214003680310003001d50b24a0030350b0840c001508109540c9015910b841c00c0841e041c01c00204990107119810704e15099145012112092140014003001c00c15403a1401e440060700e9900140550a01ca8960641414207101d001100340c1e04411103826064105061500464160300d050020390b44845446081542c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 247622014 1250 247620764 247620799
    0x100501090806240103110d0f05061903020d030306080d05030403031a010e1002070f0308030411010906080c0c0c090124030612031d1f020c011404090513060e010b0a2102 74
    0x1640182040e080b5800007403d480000c1c1661100b214923040142c20000c44e1100c4003400010501441ca0344c022030070503032003400980307418040c10b0507891092801144a5031581005400c202c01804407001140000c0141b004054060052108400222030030410844030000000d28001c0e03c0601540210301c10040094031520a10540d00600303c07964808950541c1ca162429895204a80540d000400d40b07241d992558400c803440401c507900c0769107204040c0c44030030310341d96158803403600e2601e18071400d8a03100003078071940c2905000307201e000d008000045d4524408803d0700055039101081502c1c103041030121070b8428141a508542502e840c0074650390b403028071402c40300390380300f032a500036803010b02c866058102c1708101218001ca41d00b56403503030141c1c1005644021012a0844031041d090005000e0900c0c2d0741d01c9582c0c03140344404a2240c070502030f280d50046603140e01c00c0a403565110344001c0a41d0405a070500010310060848031003142070b00c80c458150704031510000744108450846046080c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 247623264 1250 247622014 247622021
    0x30c02040906021c0b03120307051b010f05070206060d02010807030e16030f050d0e06090913061401080f0610060f23120c032517100501090806240103 66
    0x1079844201155a1034454004613002c480c2003422000780c90400301904010300340070840700c80481c0001811400c40d02d03054408e58142c1c01000746112238480a0b0000d01d40440240621004011000381c00103180c02d1040c0001d04264004014600810410280d000140d038010445a4005030500c4c00080b940d46500c01c090820310031111100103580c1c400804424001d86011002034140b0605c1184c54454a02c08140d0300325441000040e803202060000804500702a54040c1d0f11180329846042c1c507094990750304044524080d010078140c00e11b00014403109a0803c51060001c0302c140081c042c82c40c10407447c56104200d0b00844003000200b42d484a4050b004640305a502c80e0907051341c0ca900c01c485080308007950801f40c0a00c1481920001043c01082020112402150781c0001584149003181c2d00107680303210003d0050400400d1140792104410191001d07009441d11460756400c11b192100040040ca426040821681c00c444240a0221800715401a10702c03c1003004c1c0200688400040c0c005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 247624514 1250 247623264 247623281
    0x160504052212031508100b0105090306070c061d030f0c0c130e0c0105030403020d0c030509040f06081506030304090b0102070f080d020d050a0c0b04111503071d010903030c0204 77
    0x80034454a1004000b08000c1d01400000d459604101d921480e116901d04000540b00c0d440780c5030084403000400b174080390800c005080042c100545450324000c0400d1030100d040b5400320001c1c010794802000c0003498000c507040f0f00201030005110340140204981c5920622a102c04010b400113003801075180140510369803650003c0a100c0d01074049403a81c00a4200303005412118010100100c07041d41c01181601d00407074055004040f80804050251910320042800ba810302405000d035000d00d0f680c40c050200054652680880c60b1840e012490340b80140500c0d10081c015038403000c22545450010950301155400440442d1348801d0200513030030305489402103060204040008100d00c0c500041c03418541415a003100d18040d007101080b201401444c01e4040020301c1d040000000c12455951940c000e03001d2034000c0490038a140000c1c0c01c0020a28048418840200c1080b01c2039411a180da12682030002180300d41c0015000001c1880070039000c010144a450501d43c0d0954803190700c00f404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 247625764 1250 247624514 247624561
    0x50a060e0106080a0507031b08071206090c020c030309090f0403210b01021501060f110f07030b1e060303030c070501090c03050705120f10090f050106090c080916050405 74
    0x1031a5844080080003094215490001181002e02040240d8800c3c4980348011441c134120305110341030010111036580018040d030f000c1001c3d40000340c10348510b42c81540c0003010150310010305941144401707418030728080100c620070b070014042c900b941d442e5041125880107100500155540c2c1d1880d042d01c0b14114603952030b104c001c2c0c410200f4080c4129500c8104984800d80031a10115180d80001500b00b409015a9001481031004140920301580f40908201c02a4040d147c6580b070280b5030600d401b04591058800e08040000e20403519052220701e0180c1004111603a2589491404240d40307110103801c012621320005210800d2220a5104505640c7d111214112460340c074140665180c0c05401514410101c0061441540e440000c2c5240c0c1c03000406d0103805092501084c040040841745d105036240d109a58100f0f00140c0284201d001900c3d0800b000114101d200300020b00c42200200075404551100e84204c19030440c654a0030100e403011240403c85a0303a2000c541070f020458004101d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 247627014 1250 247625764 247625789
    0x21b01050708040c210201030b12030705030301090b0306090304150c02120105151002100908162604050d1713060905030f0c01270b0d02090f0f0f0103050a06 69
    0x501c1c503440392505000f6405084080039040e203440d4082000c0d54180445031144000c0e190282c010b5010760030400c80d0290007450b604140003640c1640f0308561060f0000c4505400010042c88840403500c24480001e10640041146203800181e451b6648514020b155030315070080c032208160751045200e22601d5038043d140300c08004110021f0f50282c102580c0080c0402c441ca01390715050b042000025020034a139030b000b40200c2c2d01602c100d030020130110109541c041c5040003050074804d1064480e0003e0f92080c041c548110070200c0700781510f055038a820002400c400c0200b044182e803036030132241020340c101c0030610f69120040880f944e140b24a103002c0c01c440c6070707002d80011044d40100c20141150b1040d003d80c1d084c0d455862006131215240b0301c040f808100750307a0100c806403012449086001207001010070300d80b078072042d80d480c240d040510340c4503545800085420040c209640b40c1d0b03402c0382051341c00846400e190000030302070752804e091013410140d4500c0060300030140c50300642e0052401c0d07008003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 247628264 1250 247627014 247627021
    0x20c10020d1b030b0d02090a0b100906020601050a0e04140705030d090806011e0303110a05031b0f01050f130503071205120c0304030509041e05010b0a0f05120a021b0105 74
    0x501c050a2401d055028280310602e0100110380a4010300c5501c800040c10780703051401c0d40e400c01a0b00c40f405004070740c1c46030ba51518181d9649030b00c00b807099449607503140c43c82660710704400207141100580045003d466440000c00070383c2c2807800c1c0540c0295100c902103e95441c2c3d840110f107840080d0b03001c590700d032083d42e007030801403600f00b00324100f03585a0720b0a44045a0721090729800081c441c0982d071034034102494081011a1044012481206001068800c1b40c01552a40c0e855a04039003465460724401061200800301d00b00240000600340f980244010300c0d146042d0080001c000b04001c810240010125040220920031a0207560740180703a10180422414024507030340104220000134410700000c43c0043c072180054920890345a80c0c0c0618120029090002400e0762104c101c0746a018034003a489209558018036018110612506458440e50a0001c01210002c0c0e24401070110030080c0c16209580c6042440d80b016440038050380c2c9440c981c200600d070354984000d081e000d500c0c04050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 247629514 1250 247628264 247628287
    0x9060105030637090e030d020304080d060905071205040308040b0711060c19090806060415180b01030f091a07021606020a120306050d0b040c0506120f07090e0406020c1002 75
    0x3e2400340c0314070110f0f094980d0b45034600241210040015030616900070700c81c4140001e502e03002190300501c605075090500301820386a005075046504011101c5072207400304003605600002c66400b80c21002c80501240c105a100a020000e010308040c001d00c001c4000518000c1c02604001f42900c042400c4036810301c2d00d0742801c002238014030129a210070a044004200d1340c42002074000342c0301414003601c0c054841e00100402407450000c8081c012805a4002400341001414644129030703100c00440c46401c40d00c00141100c0d900c0e1240e5061901e800c02c0100030440e804181803c0340302d0021080c2282c0c9070190164a0080f001d0015954090508008a401c660206d4050380e03045c482c0035000c0442c0040382054045e20503500a598000c6c88019812011912215146802600500c42403410301d07210008208103501000019041c83e00c03040031720003000c0c2c11b40c40e150b60000715882c1c070869040c1800100520f0010240014101540200c1e21080a82e4240072100c88041c40110071566100c0c401c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 247630764 1250 247629514 247629589
    0x7030b0f0916020114162c120717031b0604170a0e0a06050306040b300a02030d09033302090d0203010c02030711030606032505040518011a0901060336050f0a02090601050306 76
    0x3612410840ccc4405555007031400044c8460049a0246101081010040c00d00590f5000481000100940302c002e00c0d10070348450540320098002ea07a02c240c0d0364030f40f079020b000580720000c0301c00340200280d4010f00404070030340788002c04e4a5403503904542c880440e01c003421301e0085180c0010b9403501401c0d00c01a411a0840d03100c0040301d10400001e1918060060312070b004268180b1104001d0f84955800590b04106600400030100010440580e0740c2031500483d0849988003207860169200080c40410b0200b00c54000028941c110002c3c210361900c840800c0d1110007401c0e0580c9141200f10b6032044409401c82014081d250142041003945407240c0381c825810180300d801d181075440d01c004101500361f11020000710200240501d00306034071b46842200106410041302400e00250202d11a8000900c00c0d04011860a8140380b541d1044e00d0030811b06100b90145c2d1011517500400720003006845420034551f0100c02402c4c6103480790398150100f00244089603040c4100b40303c0f0f10112901181024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 247632014 1250 247630764 247630777
    0x7080c010c03032004052404060f021606050d1a060a1b060504050105040b070203070b01060e04060f090f060503030406080408070f0206070b07030b0f0916020114162c12071703 77
    0x80c4c1042d0f00300c4034442c58901c10310a000104058847c10007041c0b1103d8041c241146030700c003c500c12150001110401c0a1001c5140c0e00420006003000541402c2c0c2442c074000d45000782d01c62501c480c0d030307100d42c0302c0090145d210b4800e90310180000303141030200f48003c000305040d00540241c0f062080b4501460814000d040442c3d044503040c11041c085124148000300380c0f0707165540070301c0d91341c600e034201f0006866203208145503d51017901c80601140c01c090074080803000709485800441e881806480103400e84456070011406988140002c01060ba4080d00083c1c001e40c0103180f8950f00da105007815020748801100107904400300103000810443c640661500c1900319550801c03101c4230a8040060030301a03001010381c07040c0744002160801422004a5040c42c0c594000000c040c2102c0c220030112650841d0350514510400f07a107640c41c180c1106201403440d003884046080f00141c440088107154800380c1c56400394001d001c1100d10b00004008207406414403484c56245a881c0c040c0030b560f00e6200a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 247633264 1250 247632014 247632019
    0x370303050a0f08010e19020c0a0302010b0306010501050309150408070c1401080f10031e0605040503131a070602070f05060a020418020430081303050105070207080c010c0303200405 79
    0x80b910351007291150300707114180c80c20301c1e4400030303240c8500000034910041c40d403c194409508104c0e07035191520801292400c2c2d8880d80020801280d142e0800d82400c0059000340d041c00002c100300300600d40046080842d101c0c1000b0507000c0e0b078989041505c0e00d0701030110020254040c0c40404500100105141078060000f40d030390181c1c5580e1b8881a0700040c0054550343c9050300c18420510025030350f03400346010382300302c0c50040441d0003403a103030102035071740035642550280c00c00105590341c0000405d44201031302455101c0078406d02186601c0f8035a00c91040007400040d030104840040207000801403201503008001c17030703105052039440000250301c140309206161101d0000410402c4444c02038408460031005071441c03610418203000d10141c0e42550141c681d081c190350580008111034090260f03a03d1441030b19017040d066281040c2118005041366003903500c509810481a54001034000740b00100786413030720780949146001d030040d00c14172100f69000c45524844980d18034070b01001e402140d404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 247634514 1250 247633264 247633277
    0x9130c360b03011d1207020f0a060c0b0c0412080c0a0501060e011d040803060103021309020a0f09061b0201031505030111070605071403041b0b0c07030b07020c370303050a 75
    0x201a20101d42802c4d0031003600054110704090748050354500003802002d40050700a1581e02042d800241c83c90b07100f60040004500705480b503100f80b01c980841c055118940140d254501820001024074005005400615001001a8280f200c0c031040c08124035159102000b4800240c9030b541c81c2103144424000c10703280200c0b07031600c3d01c9014001c03502c440c001d582100205203191a0a001103000c0d42c004504c1551512121400203500300040c4000d10801c1145c0d503410780000ba810358020302d545010741c049020000b1800d811000742c4000d608207070a66034242000110520740521000603030500b0391009130b040d468105040710303602600c40289a05446140100655981d061099803000425801d15040084c24000100015190b100718000c01e080300d003007401025079030070344c2c06e50560162801d9200360b00211410800c00524203c001c0d003015040c009041c0c900d41d0603000c5101a04515040b00300c480f4400d142e411000403c3c4c42c18024901100c2c0c919800c0b079220b08015000740c0c06102c8a1001821 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 247635764 1250 247634514 247634531
    0x70818010204061215081603110619120f0606020709110a020601060e01020109020411190302090f06163005031003060b031e070509130c360b0301 64
    0x10610844064648a80701c8401d100741c025544c1c1d0003000000307403040009070124008200028100240c031011840003040c1d441450541c5081d264070001c001c110317401240d0038800c241d40540800600500f9030740519155010303c1c0012151000b40000400e0710f206285405008203200c0d50105564040d00c4131100c09221940c054100f80c2071724441c01c054840180c00090050040c1403141540c41d603040f0b014400410b40044039000601150014002e010000c14000745402110001c500c1954000301e0a003070450400009501244150680310034441c490040002e8603c002c05100314540e4695402141c0195012030a801505958003062000d00303c172448480c040312060f10881c126441107911011b540d801c2850355072400081c22028600303542c10f009980c6801080400103084545000c94078009080840c504405e110341d50300003030b14000c03040746c45040803804500251003010071144001180402810030810b0941c140c05011104c2d14615a0224401021013044d002079a01020481c020482000f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 247637014 1250 247635764 247635811
    0x2131a090108041401021905040617071209020607060207050a0b010909020619050c060c0405041109180402030f060a0c03050f06130515060c0106142e030e060708 71
    0x60030034540d000580c901c00040010b1540c2c842c1c08200b1014500150801429036400149101c008001000145011500b000019403160640d41c0101d0400c001408505041c88014241500d81160100581d124190f95045407504000c450070207070018821519200207292103925440c0c04107050300c1c01203004001142c12160f600c0754184030342d03008001501d80004403000602c1c245030703880541c1c144641809000007820041c001140b00709401183c1c0d556442c103250800048429649842c0c0e050320003805104900d031a03da9a002c000c080a0b800c0100c41e07a958400a440d08000c60b800070b101f0f00819042c00041c184682152011211949003407249503505450340502180484105500481c1426a14211280e542c4120b40003400b0003180150031038803401054031035000c50440240351f0b540781c0080028440000d28441000d000b218803104c012030030f0340740d0000c05400801c0c2c01024405658403410403401780c4d1081d0035441c52171041c0c6480b8640000c015007484012542c1c4200700321013003000c00382d41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 247638264 1250 247637014 247637017
    0x1020c0a030641040309051c02030709020c070302060c030405030a1407060f020d030c0e060a0c050f010c05071b0504060b090f12071a0d14071b08030606031902131a 72
    0x1400104100070f05500204026907049502034000c1d014008207050100d41c42d2680301900385c0c203c1c944d140340098039000b072043c145000d07a264045400c040c41844a03404514000c515901240e4044800903103406040c01400d0070b5125543c4500c1c0d00d40b181d1041e070420003040d00c403842da40b400d4a200380d038541551104e05032a810040f40c1c008005030454040d4090090107a44503100e081003030f1600c11299441c6102150071a0b200329150400300e61050079007401c01004115900403100148024002c510801030080c2c000d00cd140c500400c2400d104004125482c0c400081c440107020080c01404015075400084940d9030065401501540301c04031030407100c1c1082800d08100741403690040c03400b0707072901403491000611a210016440b104004000c030510a5000d011152580140a00018245602d002c6d140500d9946280f40b0811070703c0300a00452034078001d6a51007031040c0c4510382c0ea170b03440c0b03104002511004d21040300700740e00c04034150b8000f031614002032007914140c03c980b0040c5000042c0030f070000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 247639514 1250 247638264 247638341
    0x5100504080406081801020c0f07050a0e041203140a0207060f0501060806041d0f0303340e03012405030106120206030105150d021912020c070902030601020c0a0306 72
    0x1c400100000c0001031300c01c08150f130703110003500350802e103040d0004600b84c01e80e4803507118400e040d448440b040d98403001c1444520000c1c041114071425a0f403411401034403480717000708040c00c120515494484032901940080e070414805003c0030210349041d005500c000e401c4480240c0d00340d45001400c0c0c1c4801303141d110340c1c0c2c143c82c034686402203169a070034104000307801043d1166015041903951180510740800002c200301c0c147d40040c40e124904034481c2040b891200d10090350400c246401c3c0110100c4001c0e0310040c0603c20301e840d43c070103124000882c0c007600c602e46040f0301c20040c070300d075021100042c510214142e031400c0300203000c01c039070b01e001307807035040400d400c01940c810000c00041140c2d10304100151004490641c4076400d214025242d00200d82004022401d4505072144130071400703034070420304480aa00d00c5021030910300d08080103035403003d00340214207141d58000b0205d81c660b03000b005081c110090007486100296120718104000d0b200d4550700c0c2c0b06001c0041028009104500c612054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 247640764 1250 247639514 247639523
    0x50d080703021617091915090b030c1b03190e030a110f150c01230f1620010e010608070e070810090501030b04050f0f0a02151209060405100504 63
    0x83c0161180c07071381d00c01a8080d48021104490801640c50b40e80c0302d03850345000d0340c50046003c841403850300011603103504d01040380c00c0400c035101c4018840e900900c01502d8110f880403d07103d40b030b00c50040c1c109000e201d4690004c00c0601c00070032041c05201e0f1003243c1400e1880c040d82c13104518084001072641d103900c03a000041c1005489102d2050505103d1140c2590141c02006040c4210003044218899400310728820706694507400f000000c00d00c4004049404905142130100310f1600322a103003000745003e455a0014800350b603110003070910814035100d450310650030044030240800d00d403600803c031610610105500300200001d05440c0410044210380c00c104541d18a45c2d103000007181d12810042003800c2c045180e00c0c02058110040c0700383c42c043c0d44078181480c6d440c10981040c17490803000b41805015a0312508034149800c00124112500342d40c1a1040103c107814514650364a0180407007200d04500e04a007046044030001400c039010320300903015240f40c2c03c0004042d0050704c5040300c002c1e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 247642014 1250 247640764 247640797
    0x7080609030f130b0c07030618020a030b100b130303090e07050703050307181706060a080706120b040513140a0308060f1306090b120303041e0503040e0103050d08070302 74
    0x8201c6510b14001c00800c9024102d0a01c05901c501801104c0e80140f04586240d82c00007805000704801c5100fa240c00c40c120001a21004c4159400181d21890f170b4040204078040810108d0112181e41149030081d000003103140b41c071541c25880c40318101440c2e00c01030b40041c160940000f00a4200c81d00c07980100386503500d040c0b9008880d2010b50b02680081e201a00308690040102102d8188000c240301a00550030701039a4196603680d0303145040740181c6070a1080c040104201705802c0300141d42e03002c0302d5050410400c1c807000a20700000420f6443c4043e90840c0c2081c013001031006004803502030765481035922a40316141c01d140c5907030340c0c10204002008924070001242c402d01d08001c02808181008015461052484800d10117a030030741e902074805a5154620203100746003c0004106041082c00258103519081e100d1034202601c00c2450a400321210300f4940620400307000711800f401c1c0700307503100215507175904e4000e40d03880100c3d4062000600e000d0105110902c28001ca40c4400202c0090706c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 247643264 1250 247642014 247642027
    0x503030f100803030702060711010b010906030e010605180610050c0a030e2e0f020109080f07020f031f0b010306150e0307080118020f06040b030a0b06120103060c020708060903 77
    0x20381a022015108003981400c1000009042d80100015403140c02aa8041c000c01d05080902400c2a240841a100e0030f90404001e4507443c4d0740710314006c003141c115150200d010300c40c0d00119801410a80c02180d0811001d5100340d42a8a080180030701074501586e10008044140c0011900c601900000344910f401c100200c10119104006640700365a0082012040c4403070318070451004009008101410151800c03041043c42e00704960200303411660000b07001e001d03a6581c5912281c41502103c109540000c9542815900c0c0c19544155500d4080c0c201ca8602d07222654130181d2981d0280010764050400f50300304e41c55482800341c00202e0340c2c2c0710100e0a80480e200026112101003406181d010700c80d81200107014082401810a020109110240414418014807500e001401900d9001c2c4508000410103001003000300ca40c48a180303400050fa91500c3c4000550b03500c130b03511501d26807641707500c0007205001d80c0d07510000d00ea0010342c00700c0382c85590325080316454041c116094400d80c0c1040c80f20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 247644514 1250 247643264 247643281
    0x1d0115061b08030c16390e0c07021005030103050706090e0a020313120905130504030504050904060b040c050d05100b1803070f0303080906100806010b0a020c040603031107060903050303 81
    0x283d9008030201c41c08030b06003240822001c0070b8030907007401500c0c6616020402045000f10444a90100042403040f41101001c00f001c028240320510402d1126100d0b1310004002c900c00c40150754041c0d038001d0101c090581d4040d0010000e420a00054800d030046086c0000c7c20f5024619800c2200d0311409154050390390b12803400001d4100602d000048050b0504060004864004400c84e100d010340340c0203030680c03d04052041103460701e045001002d150909110110f1f4103d402d44003198000c807089080c566980c903160000d00340c00d201c01a001814a041c0243c5a41c10a01820301c6002c481030400241e698000079482c1c85039648144c40e50782001300040c1401e158446020202514003070121841070755540e00d4901c0041c415481980050520380c18011416030034000035400c25140807800303205a0414079042c0e1900010300c2500340301e040c00501c50780080e000340510b03413910400820422055641c0c0c18058000c5c070085404c4220780c042c890010840d103000707040c0c070340950390480011404e59407403000d07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 247645764 1250 247644514 247644517
    0x1020c1b040213080d0909050907030605071107080c040c0e0f0f010302071e02040b1e01050304020a090218191802090d0803040501020c070e0606030f07031d0115061b08 74
    0x3209904250200700000c0b00324442d6603100c00804000e4024a445000d40000410b00a0b4030340010200a04110502c5807044001861000703803901b11b5030004040d20341c071006541140800304521054003c0132000503100401003241c08000806880500411541c0d41c41141d0f1000710300c216039482150b81c02c07404450b040084126040b808107040062420b11240c6842c0d8401d0428594021819002500d090850800c0d0007461154101034a514540c4100c00a00c02d42c0703040d107108814100305012000030151340c0c0e00700910004100780b080455840d040840340804007400b41c40c080b4011502810301ca00114040505201101d110f500301004200103403200d4070180d03000c070700d420b98000050060349000c540340074015402288503100059840c0e08104643d4246003c50303005244085c000410001d664445904076540011000c0d040070036030380c0e071000a50081c00040381110381c08040350201ca20000b01507002046400c010810800c600e50b0f2104100c9182da034801546160405030b03880c01c000540100d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 247647014 1250 247645764 247645813
    0x6021e0a032003070501021905070206070807150204080d1707090e0406060b0f03150a05010e04020a0c1b180506031c0215070302030a0506030c0f010e010e061b0f01020c 74
    0x107041e038010b03401041035443d5820070102030701d843c3d41c00500d120100c0451541e654140a80c0d0800f1810300b442c40d000a140c03030094400c09080b035400010b1a40820968912400c036110700d0380c130115210f03502c03407545c1c555907007150036a41c0100d9110000490100001115188102043da0324003a070207080501c0e0a511050241040718150340300e80001c90034079881005040402c0c20301001f10748a2400851561000e46000c0e00c9500983c01510288200c1c0d80c8181c40d16a561816600035a40e41e5000808507500c081c6010003404004d00a03d82c0c04055030280340c0c5030b00f1940c4849403004680c240d06c00c82c01c115442503d5513503040d80b1103041c0c2000c04822440b51903949500740103070341c034600c0200c8070b8405218007101d400001079070000401002d080d040c4540ca0700150160f00510380e142030344000c80c086100395420b0a040c004038803142c5060ba80714000d500c3d403a00003e0250b40e100c8003280c5002e02c1021180900c03601c41d015810541c4101041407003551455610000100102c0c030000030607414091412 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 247648264 1250 247647014 247647047
    0xc060c020d17250f030e0d02041505010324120f0b0f0402040f0905070302010e03070807030b090c010809060105060f0c0607090e1e15010c050a030201020406021e0a03 73
    0xc03440c21000c07641c2e600032200e29071000981c0e90364800c20880c1c0014502c8000001e20640c2d1102c10808002c1042141c242281c84d5040c1400203240400c0c50001700c110029220007548541031142e2440e0000e0070001a1086031004c0c2c80901c03074803070101000e1400050f00741050a00000b140410490350101c00481e05010780102030152400006803180f4103549030848040c2d0503400c0440c184003c60400d40700d82c421880052404102c02040303940d9071603c03201d49200c064100094940c1490090b501804140d0084c0903800407a01095560719000000c40e40480340b007059801800e140d460954043c1c25028440d8102201401e134580c24031040107502d4000c403a040903070000501c0325001c01a010051940122560340710000c4a51030050383c0c00b00c00900400501c1a0500d8220888418100c410901d81040952141c004003400761801204c4050031820090080e104241282c41410703019802001541c1082e82514030309c416000c0305240100a0026140c110340c05012620086032041000902c9038040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 247649514 1250 247648264 247648279
    0x1209050102160c0b070f0b0c250c0b0f0313060618140c12010303030c0207051008250f1b06021606150510080703150803120f090a0201110c06070605010305060604090c060c02 76
    0x9c1d01244980c2d9200500d41141c40d04602006c2e06120880700c242c001460803100039131500710355180101d01070102074502599124071000c01801c01c001500684060809885201e03440705555141e00c0c01340ca01c0c400c40400450050020038101140c5100312511016807921120259195550442c0200110203a502c00c60040c0707070000c140d617654801e1440030a002660391001c0c85c2000810030001d0000100303200326941e8043c040c503c200707030028241602c0e910642881c2c407040d000c540e82404410040034005088074400100b4085a2078110b54100d40140580c8041100420307481800710242e000e4060240e211030f04400d0b01050a1154100c3c0d6440304062030080b88200c4080131842041580c0e4016a17101d40001c030300c0c0c503101c2d2850403200350b1121041000391500d0a100b00781588820a810000e41084280c42041c5916202040a2146d400c0042c20311969107001d400c5c010002d00080c0400c4605001c0e04001c20f42d94941405440c180d80c5d00509881e01c10380c03030040309641c030240c5c6248c100d810050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 247650764 1250 247649514 247649527
    0x30c0c0109030905010216050a0b07060603080406030c020d05070533190f06050603160908060126061b090f03010e0c0a061e1209050102160c0b070f0b0c 67
    0x9007030291a01c440d1207a1900001039042c50700281c00e11985802007103101020400410140e03071a808000108c40148094540c0c8040e170381014000383c18140c101501150340010001640e90303140d03000342e590700c00740e80c01e4030180d2a6510b400c44103841b403001c02030306a0307200784030751000703950096010409031a1040311a251131846446840441c07800300c40140700840700c080e08100c3d00c0c1060140e201c070f1030000700080058604140c0083c0140c00042c1000c03500e44107103c43c02d00918010f102c01710240060700200e03105c3e03607036580c501400c1c61448002d00070060f1584039404210003000441f280144250140040144a507540d41e0384c0315045034155a520400744048003400e61028407440707c0c1d450b40500648021003946090000410303859000e081042314070540950320b1041c0c6591031055031454a0120601e48110b1500300151100780d20203042540700042c0048115480c08481004501c01d96008405654801e01c04146014a21018003142e0b695502a0000381e41c002126600c003c1101d001401c044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 247652014 1250 247650764 247650787
    0x1030b04050907030b09030403031407030905030708060115030501180b01020c2d030a1a041a07030f0e030f0708130e040506070e030c130c020705130605090a090308010308030c 77
    0x3903050325400b901c0d401ca60414000c0c0034290070501d9001c012080290700c0c01d8650303980205204a411411b0410820203d0188205489108440d0040400038201c3c0c81f01604d03198259100e0031b080c46122480c45c01e40c104506014001e0182c00c2c1202e4424044110000d18044143d0280c19006449030442c007441d00d180360700c1d540702100c03482461110070034811211624040105540071205d54203100c4d0f44948400ca002a0300310341c0c1940c1050050140b40100d44403031518501905090100030941b200303050401889540c150300210a0707440000092113000440c40130300d0707208d10542d18070a01c240f108002c010042862640200300c102d20b1400d000e00741030f64604119107442000e8408507070582040e07090024a95010401c140500400c030068503480603100700141c81c1110b0800710480580e103074041950300900071310041004240191042c1807010300401c40400401d11406218440c0c0306500204907010028894030080503070680790a00740381d095480700710044c1c20040c0b043d00c00c0c8404024005415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 247653264 1250 247652014 247652021
    0x2007030908061807090612020d0606081207020f0409020a050d0c050405010f0501080106020102040e04110f1003050a0c020606060706050c1909030b1f09020c010b06040e040b072c01030b04 82
    0x10104407041003020f40e041d11400f803c0c10031a52007414218100031060120400c11100c2d8074800d075044903a20080f4209103840c40c040c080961001c040b502404182c0000386c02108010b00031030307100302c0d903040ca810b030300c1e100300021101704c500c3c081d4104541142c103101c90304041d0070099450340035031460f1000b103980d81c1c0000c0c2552001d81203410f101da0041810407041d6007060960b0702401081c0000d504042c1440d09581c0d403580000d01c09400c80b4030009203001c481d200c4890003000524040e0948000d20301000001d0080c0c041039034211081864807146440ca00c3c40072030b0050003814000d00080c9070181d40e407501000b03000094440f50f200c2108200c403d11600c0600228125000c560305d956009518605003140c80601c010b0902600c501107c03107030b100b800c03031001e0030741c080d0f4101001c0140c55640f6507024500508864490701d82001001802003100b003000310303d5a220354400c03482d65000780c5d500e400494581400021810071407040341c00c50404802c0d1085031003510841031400103907044d44400002c064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 247654514 1250 247653264 247653271
    0x130204090804320d030905180603060c09012f07030308041e050c0d0c09020c0307120e060313031202040e091006050121020912030a12200703090806 65
    0x16560001400c00c070003c0280d400300c81d51500441d02c100c00c55503e880780c1e144503c0440510340714800c0c46100104160058245c64050071000e0004401100c0c00e8400d079a01d00e5003584c06078401d00c44c0d00001400301d040013049070b00d0044181e641c048008581010450360142c20704150310300b41d600c0703019a1b0040038104500c03002540a65550401810b09080c40180c4941c0c0b645404910a203044102011070303000200301040308802c0c1c442101421071410180300c00349071500190001400000c3c0544040380000140c000e05018014510411941103030568840d004885c801e900040c040c400900344610704144003050718040c1c02e110100c00c1d200001d040403030b40a0f0700301c00200e6101c0828040c3ca100200002c6032246610741007007100500706000600701c90004641400014a81c84034080803480c5a01580c0c588440a0005210b00440c114015241c0d00081c4d100e500140d0340345280c00d10f0071100e004868402924407103140041e41c00c018940805d03888640e0903818400c14420000c0e040d83d08002d440e10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 247655764 1250 247654514 247654523
    0x30203070c05010804030c230304090c030e0105151002071805010801150b0d1a15070510051003060f090f0506100f030b011401091a0a0801080a0c0e13020409 69
    0x356142285010009003800e50000740c100158403003040002a0440b0901c80c000307070071640c0c0100e10b21584581081b90090070300c10654a001c080740006004030150030503d11100948c6090001c1035044020a08841c01291502d0300c5905420b000b041c01c1c00c00e0041c0420b02d007103c1c07040c2ca074403584030414017594401c000030385981566904010083e00c4028030445448003012880244442d2900321034201a004400100c08103e0380d804028104101819010b034060b400a024281520180d201c200300c95001031609840c24022020301080e1078100703108440c402c1071450040301c0c0c69400c40c0c40c0c0302d005000e24520b905a155603101030402246002810f0204948290003c100701c5c40c1802040c00c00d00707110382c818605441c20000a1000401025016044d9010b02401b05003142805004a8001100394840c00c21041544080d520050411008101d2040d8a0312000701c00e90341c5400380e55840b40781c43c001504000903941c2c00e1002e116895182e40d0003c000c0b0a8410140d2490380016086401141045a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 247657014 1250 247655764 247655767
    0x12040b1308031c0e070e0c0403030207080601270b04091209060c1a1f1409071b0308040309170105090d0f02120a02010f02030c0306030f0102130b180409030203 70
    0x3004648100e005601528203003002c1d6041c842c0c0c49464400c40490380440c018040c2c1c03a00156488120100f01c944000c1c01100820303403650a060070080000d034804e001c150018060003101050a0f100024400d049417110300700401200081007540403410f01c1c000c0e10014045d20b80c4451080341e03441c1d000d54203150b8013640c1802070681510001402e1000158040418800b00e003a80c4000708006005030703010107626100c4010355503501e1820000040840819444120035207a0200301c4e80c100f540b000d10036010035594104641c03510b910640e030a8208114218105d50754101c035a0009119030794042d081442810908111520f5852032030306901030070042001a99108208a2503440402c241c140f1410b550803d031031402c003003200c000d443d81600c460311650381c100050600c0340e2a00c06d5021030059401c441d0304549900b0500d0340c08920360310a455291080c4503280305101c040f00d06108407a20940f0342074054405c0d51030800c0d622019082001ca4803c040040300c4161010346641c082c1c0005e0b03078440d5020f036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 247658264 1250 247657014 247657027
    0x50a090906060e0a0f06090306020903070302180108160f15030f0e030a02150f0f040f0606030f1505070824090a0203010618030308010b070f121101111c0e12040b 71
    0x100d21350352580f20115a4180c3caa040000503005031161094940200340035940348100004071b860301c00241c1c0001d40208001c0c00c0c0c07d031001e03004403069050750944d0007540d504552004050362205c2c0c49000b141c103045500c0c04100809240d0f100c540307003840200d0602144103e08489058200c801402d4002c546800004030b0312151981889800c4000c03403c200c0184080c10424005141c603200200303a49050354010f4045400d11a00a48010078941d1094050001c2c1ea2640b8080c0c010f440042d40803510b42c100c00c0d0410720f04240b6409141c0c850b8216555100305580d400d1071041d000b01d031180440415034142c514480f46a02e8944100e4030406107104056a40e52501c40c008122a00d0034180f2206200d48240920019078000c24090468242c1c401960320360f541400d000342c0710f0303109003002406d000b1495641c544e256040a056034080a00e580200b0a101030307440403580503c500320381d000d20548090202d003081072655105421880e203c0040756428030344e60300179805951290300301d00030f80325003c20403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 247659514 1250 247658264 247658269
    0x30e150109061a1806071b0321020a03120b0f040e01020405012709020a0e030f01060303031503054201030611040602030d0e0c060f0909070306060f050a090906060e 72
    0x20202c048403d4245180525071080c00000310382c0400c2081c072a070070019003142032020744c10600242c01049129840303903959034606404017829015441454820039101e1401c1d860000c80c0e005000c6825031035540d44102a12010350040c03440d280c659601c48078509070440345850f14030900b02007011810005035074904040014100e0000001c2181040122441c0c0c0a803800c0304800001c11121408000350702c6020a803c29914a44180311094040c821001c05c003204403015007111080303030301036141008115040400089030303140b1400b0203071180d40071500e001d2000d540c0190642c580c0c03c10501042c0d440c418a0f2412418580c00b01c001150a5109001401070000b1340c82207a40b803803541000180751130b00e030007400ba48034003807010001d01a40c0d40e003072901042041844144c00c4800e0003044556510803042c900c0b2555081003c00500a080c001c1c00294064001c2c1304901c00c0e80c555885504040c480b0203001c455a600c010041010040d42140008500c040d40c0907440c0a04015114100140814010b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 247660764 1250 247659514 247659539
    0x313090605090105010c110301020f070b0604050c2a01020702030330150d030309021903060623060a03020706050103030e10030c05030c09040e030d0501080f0319030e15010906 77
    0x440751040401c000100f04030f80c0c000b007081d00c3e526441034015014818a000103402070103140340b030302c1c0d0366500012030508100c4a080c10600c90501100c04000940300d08003d400b03540a5148100c0195025180d0f20207508550218207910800031000945001c800c0c3c0c3c04a403c6030007a614007445e905010304074964190781e80140d03482c910f40020000400d458803042811a01380d00101880c021810f5242a00a2602c81c1c0c019503401c50700584032840b140358180b28800040c0b060310081c1e03801454203e011540440310020701070303440c07a0070442500030701800d003c00900d0360005903694149079080100700000752542c013800d4002c5000e9110100c102041000740041c2c40c40a00c045400c040c078004040442c0c81c3c028050f41e40000c0798480390703600c074a04840490020008405040c14174070020078500300b604d6103030304014181c07022807050301d17910300302c080e41c00f030381c03402408480002da0f905006140c030054402da10004441c91004e08480c910712841d2100c00c42c031002a005050a00d844150a001c981c00090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 247661870 1106 247660764 247660769
    0x1a04051020030306010f1e03020a09031a0a050a050f0f090a150510080f06060108060f090a05090c0f010e0613081006031101090506032703130906 64
    0x26030741e9680d001111041d000031030344007003500500d01c0b640868040c00d001100348054545000d505074080d400000c0f1040c10008240000804940071114000716002c5804007954603041c00000001503a100500ca6200c80d414001809005440780480c20391044203828510b02e25124034804500b82084070030090a440440003c44114524540c840c07030040c050181e03800519540c40641a88900c0000290401c9030400750000300356501500c081a4000e00003050380000007400300015184e40340503212901980e0b6150b04004000c1e108014200340ca07601202c03002c2a80c0302140000300031090342d032411400341c400070270303004000d43d40d0a1100c00a130400c4000c0e00c1c00c40e000c0c440010010890f51100b542c5190340181400c105500402504041d01d0016050510b15503a40c203541c070118003094803904140f010211140d00c00c0700140050b010745120020b480400904e81602d440030b984a64 = true := by decide +kernel

theorem cover : BRFrame.Cov 247482014 247661870 := by
  have h0 := BRFrame.cov_init 247482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 247482014 ≤ n) (h2 : n < 247661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
