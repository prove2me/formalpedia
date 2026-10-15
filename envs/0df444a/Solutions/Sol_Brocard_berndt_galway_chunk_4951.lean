-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4951
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:15:40.184564+00:00
-- url     : https://prove2.me/submissions/3b3dbbb9-42fd-4393-abaa-cd53b1ea6bdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 890287769 ≤ n < 890467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 890289019 1250 890287769 890287819
    0x406020a1104020f0a0207030b07050304020a06141c05040c0501111b0312040305030403420605031906140708160302070827091506070303060506070b07080114 70
    0x4090001440c104031100249070b10745c010041000035074040319081080203540450581e0100d000c0c581141142043d90000e441900c0d24410001001140c0381c22185070380621044490f80136402c2e450f0b800c0b000000990348050301084402390f4502071035500000b402d500880850140380c0001b80603028021071190306503c41103440000f076425104140d01c41d010480e00e00c00420146010704021a203c616500d40340c09010309112042107404086624401410080c002c8840c0d001c0f8103203410b01c0e0701406100a4030007010715500c8694180314000303903020502802407076a803615016200034446041c28143c0c0201912094a002000403d0750f00000c107459809403080c81525218a80980340c480561103060392034010761901041c2c211070810401a081e41000c070086884001d6a1140c02f918004440c0d2940c2800c50314681d003d41400946402058826400031000c2c000090080381c48401b10308000c4450282114114042804403002091140060544c00f101100003451030300c20030750340c481070f05403000d0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 890290269 1250 890289019 890289053
    0x1e0a1b1a07021f091103010c0201240807060c020409020306010e0720120c1c03020a030b0102010b09040213020405041a030c0d0816150207110f042c0a02120604020a0501050406020a 79
    0x445031202c0038003503902307008481041c0310940c00492070381c0c00c50310740c0016001d22207030340b1512203c12030081017071130400b00c3c141c01101c10901f4800203240c1c3c9800800c01130509140700941c14014030001145160742c50310094014a0180d4545500400d0b07030004a15020205c1d481e58040da100080f0f00c1c00d40040c40004201d29030440054070780c05e030314012500c084202500da20201007a000b15001c2c48403079240c450305e103841200340300034800d96000e40d0114054010160000e801781401200403030400949070120b1700104000741c001c005e0030000360134106140042300c1c5910701c24010b84140744007529021080c903c0f100d40000c6541d24010300c245081841d04001c08040b10040d1030b80360420142070452015091031401464100302d142030000c00c1010070b0ba084944580329038135000980500406d2003595541c4102c0b0b510a10300c82c41c1c01007540610303003041074200035804060084131b010b4258001c200e1500030307442500c001ca03005403180015196801180903240043c0d2002514a020500884074050700217 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 890291519 1250 890290269 890290283
    0x80a1e0905180718030606030b060612130501181b08030a0807031802100809010c022a060403020a0314010b010f080609040c36021e0a1b1a07021f09 65
    0x4403003561030603d80132050b8019034200b03a4992041040c003085104140d03100008456451070060404180c0e1160f0201421500130020095054002c02c8800d500840494219550302c80b002d0b02980380c50300840c0100d80410860180b482e80001e540d0500009440d204012910348090981d0361315011801003910103030b00140007540c0e0082c94096150301204181450444e95008140e107040100c107403c0d50300c1c84246c00708550000011015100c030484e0103800c20350395644c003064844c00c0380000442500603901f01a5005135446400010420400303121440c0060050003400310200c980019540400e2050824021030160030000b4214500510b14aa01612801c0f40030003150b2240e48604e40c6100100c0b528001c1004002d2402c102c91016248004030707030aa103010351520002d421003260309444c3c00c1207040e40c40c20215002e0b000354003410454803106194804012004c1280c00c003642018074814819280c0651013012421042c40031490104070420304080c41c500610900d42c040c01000d08d80345c141d41e15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 890292769 1250 890291519 890291537
    0xe031905071b0b1207020a0215070201050c060108030a0f1e0c060e010f0b0a050a0302030a0f260405010e0402161b1d06040b030d0c110409080a1e09051807 68
    0x3049510700c0b00000b40424074401038aa8010942984120340b001d080542958082c3c0705035401680c4205c0c1c813980c0a054550030a0702c030b210034030041c0c81d0b41c0100d4564082c94000c240c0045a40000003020703040c10308a9941d0848440c0c1a841c040e5508603030700c01071035014a00080040c2601e400b40c55404010391080700000754068a034443c46084881d95403003554032984664004e4520319001c8403071005448201d40c150300351482c40d80000e5840c1d40407480209085040d0307059900340886600c414403180e851310018107040038111004095980140a0140880d040e40c440000b181007a100344d814609e2104219100811151100b280d103072085c61950700721850082d0b0101e50000000f036002c00300f00c00f545080516040481c00c200640d8001d0250a000b6030010300100e4100350f001140c18001e54000282d0b03c0c4217030a41c00850003802d00c07a48098090301e80000da0300301d210380c0b05000113400710305154105200030b0f0203042107902d1411031003403642c040c04040990481d03845250302c03a50042c0c1107081c40110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 890294019 1250 890292769 890292803
    0x15142e080c0f1809090d0c0204050423071505030c0717090310020301260322120821010602070b21040b0a110304080d0c110102031501030e03190507 65
    0x2d03511800181452801051420300c141c1030582840303030803022003409070042891100004124502c80c00000c0e00c9151110301140034000001c4200721000030580300307070010844a01e07465580303131500d104081c0050070700c4142695652190003503901600c00c40007054588045d50f140d0010003040101e04140d4000100605646a03408100c890f1100c00f00202c090303129850822001074080c10414203205120901c0d410600f20007004c411594074494280f1081280c0912880c84040b00f0710903005001009080c86004040c4401d45000e46681440b40001100c80c1400900780d400e02402031203404056070103907000703001000100d400b9024a1600e40401075600e11400604075491005490646042c0f0140c0c05008040300c0c14020302100840d800209440c600303150b5030300500c900c9005040e50203280d0350001c40020600c42e40500c680c0d001008002c1d900c80c24128209204817051250740e0780800e16202200301d00b240044181d40c3ea4400c0c9054100100c1c8a6840c10b44640c1e02c0040c003150980488910004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 890295269 1250 890294019 890294047
    0x90b0c0f19050f0a03020d210603140105100e06060705210403030909020405061b1f02251a06030a061b2703060e0115142e080c 56
    0x30140e5104040300c00d245078a81002c60820400340c80b00b5400c2c2c0c01002ca04000309400044c18070300540c140c1f4200e2030980c403160081c007211888440c201401c0b4140100002840f5140c002845203c00c140c000700031326161460500c450200c1442100b940030480d0000400754500302000c0d00700745024400f80c031a0946292901070340b1900080841c5203030340003c141030040c180c1c01041c0da00904480c060451405007800c0002d00c650042d5200042d4103809404024a03d034000e000314900d0b008503207810a01d070000000102c0103034110500d8042d000c0701031005556038010301801c0d40c10b159081404144850600c0800c91420080208069054459503200c0b200150440c45900e41c0d039420040103000d44076200400074240100a250580c048081e17003440c140c3c600c031175642d04046aa0024000805115402106000d4648950780040441c03080d1030006048180100032a049070707044410a525500703107031461010158907040105000c98103500ca6103030a000341842a084200c039080d0358140400c40017048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 890296519 1250 890295269 890295283
    0x6040c260403021203010e0a18050604060911060f1603020a1403030103060605040501080309040f11070503040e01050402070f0f0f08180916050d1508030310140d03090b0c0f 76
    0x80341818218100000c0c075606020f00352024107005125851549003403642248020041c1038001001e544d014003221603035803c865401c2e00769020040d43c00c90310303081c01c10030001c089200301030f1079244405d6909081860070004075806981e400308000e040c0303074030403042c03181c0c40780252403c4056208100c0ea840c042a00401d503c800141c42000942d600e604500d00001030b52940c0d800700e405076050000500000002206941452105441c00030b421048a51140c3c09883c803a58404204040000c0304010b1101c0032006005552005807002d5559a072002804200d01c9000e0005c0c142d2501510b03094005200d140780540d009010340041403585400b82c840161075401001244111000c160100c0c1142c2841105254409074645a01d0049508004060803a01c115050a4282036550008400d0643c3c100041d101416201c401c494030b030f141521051900c40d4040c004e00c068004030307a10341c6903149031140038552040e038569288105540b400c8812502d60f0010583d86a00d8040c60b8100d1009000801c205 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 890297769 1250 890296519 890296577
    0xd0611040e01030b0a0c090b09060a090e09030406180b09091009050c07060c1814030f030409051012050703030e0409021023030411090403050d09031206080f0606040c 73
    0x1320a2814620b292400b1a5440040b00040c0031522a04020a49a090584002550554178150358543c0742d0702c106c1d0b00c11425000b00090700604001d10405400000140056603440d40340c466080885504400081d05188102d80e561042080210040e09085039078682017540605d00c42100c40e00d8114810940c1c0c4202e540c1c00c6220008a41c000070b200325406114107128060420004108260080304002d0802c0d00881030b031840050318007031803501c04115402c1040c01c41420341c1e49654a4500ba4006007031b00707580340010000d25070404141030100442241403940e000004020700c3e80307959401c1c0d500a09262a0540c460b549140600c0541c40e01717034501c40c881c81a5a902e000c81c95020601040600a200000d00c94002c14420800050030084071480010011581c1c0e00c46513a0701d2500b2035840c17003040552055581030500e98010143c220a541841d417251140601c5a03030344580003250303111aa20210501caa00c4880410001d04140d40035800d40c54072498883c02c284040c05107420301c3d01e014481c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 890299019 1250 890297769 890297783
    0x5030406210b0312031f09090302071e120201030b090f06090106021902040b060906120613020a1b060b031f23150102031e03070f05090d0611040e0103 66
    0x3004a03460344500205440c8100c040742040312104410220350f80f80b0382d480e11104012030000102c0c0c901c0080c907405000c0181503080c083c41241e283c0042401030b00301204114054403603c0000704007003441c844a0244070614030f08c0a2985840e00201d0003042d101c42c0e5041e4181556856035010a48511082d644074840740d204481c2a1700704078043c4084803005900030f408641140403034113503d14122a4082031241c04035808120300c8070b5040010541d2041c41c20990703124200080d6051040181290944201412119581549030316044030060384100380d40300000440015401e03031001c1c01c60240c491900d014600c00140745956001281c0b40150404038000074a80c807041c13180e4008001d000d400c070381c1c1c502180c224040c0300f20410b45180803800030f0b02c00c0b140240c41480044050f4030030015035903950705111045103401a004400c003100e60050302c10100043c80c8452600c62903024a08441003110041e07c07509001c54030b5200c0000030004a210508906020800090031261480c1d495000c1c500540b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 890300269 1250 890299019 890299037
    0xf0b1f0909020703032a14031902070507080f070b0d15080f070509010b0c120d09020a061706120303160c06050a1d061314010e49051605030406 63
    0x3045000c0300345086546420040d0f044c11801b885a07010720000c03400142e61912030303101c3e22036482034904148104c110b008018408a004001d0141c0081d80e041210411411f54031403540440740a6101c8496014442e40c04004001ea0040400c2583c0440c0c001038040344560001a11008051305101c085100c0981c260700004081c40a468403040080c0140a5035a0701131030b2151110319640c8404551203c2210304002055015101206410002e000742d40140035031031007510307582c015001174054000c05121070128800640e043c24008060b80e0200400f40041d4216902c802d546c02103080c2428198040040c8940e040c800507101e4010540034220a150104041d031345c1109444000e0f20429401000d503106c101071105881000b100303040c0440c0c000c0ba130300e00810322141c00c107805444501d910164500c40c00e0400d10b01c0343e003190b20042c0c0c442c007d00301448000004914880c5940480da4140c441c05040c98000c4901c0350150300100741d0050b50484c0f4a15100701c07625041e055402030b44c808008100400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 890301519 1250 890300269 890300291
    0x1b07060203193204030606030501020a090b0a200a140c03191a0a1b1d010e09010b091917150c03060906040f0e0a060f0b1f090902070303 60
    0xc040d501e00c81e2403864030011160701803102c1d110a1401805140300340c040e180f809244456120b04480c080c5800071814070405a170792600c90b000307601c001c06460014043d42404640e440e1004100d035001d40309580c66840303220380c006002c240b0382d400302c0e004141031040c0b0300014001b61003002484001c8402a011344410013403c020f15082c84060800e0340c01c12101208030500144090103401ca030b921585000c882c0684d10102c0310401048421205101e907403000c400700b078007654092503941035503d140985000d04030b911401503401002d114180c0f58801421801400400d03a040003a100c8000c009058520b503c0d50301130b84038242c0185401210803145940c2c451168134008002d260321100d030a00c0b01e40780c5450180c0600c1c04a00025083e036100c2c8000d400800c40e00c0c2c0d036036007001d507006c03585901c04c20001c1c41041d16156940d04107074044414a01380800028030300c1152003040211b190203040030708002d500c510526461141d02c0e410100340254107801040359525071001e003030140e200340c90000d0920562 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 890302769 1250 890301519 890301547
    0x1020c1e03060709050108010b03070302070f0b061503151507060903110c011805010815040606020709061707060c1a04080306090f070f03020c03160c0f060203040b0a051b07060203 79
    0x421220034012810130400069038005035150444c1c1c900314500d512501c4110f001c4010f03216040c00540303ca840801500c050091348445030740101011600c1c14100c0c0b108404c40a040d000c00c84404440300404007086506062200b98441e4164070741c4080340c0b84c4507070340d0b0b40d80040b100f50010a40c00654101c0e051a4031110821040507405000d080160090702aa00303c44010143c82c0255810440a02d020400c4003d11801107980620004c0c0180600790b142d8000030750340d044502c00c09903890708054000401013003800000902c0044403018101c684d00b401015501856812821540e46801405c1d4100d80350b065044103000b18412030041e59641420020001400300140000001c8680c103000e01c0b0398290032890200d00d21f6010b0401684a140010800d400c41c05a5440e00b001a80008070031410806800d5801c0244c51040031890102620782c20102e99a004600804c512660200101c1150500900141c60b0506041382250401c1805030500f608060b210f80c0074401590020074410101455 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 890304019 1250 890302769 890302771
    0x170c01110313050d02060c010c0f0306090b0a0501050a050f03130b0717040b0702030c01140604140f0601030b0a0b0d1401081b04050c0f19020d03060302180601020c1e0306 75
    0x300d000298281840d95000c078154041a12509205482e001c48031800c544507481074402c10b0410500070842c0961514028195071005001000060324040c0301050010541c407440c561001701a00e22100e1a05040040d14207034044421041400b10a01042c0c2c50103549100840c4030300e10502d840444200f06181c2106c040201074003440601c40c2c01346407194074000c0c41e0340c0c0e0b940c020b400030507084054070385c00d1007a410340c811480d0a0b0b01035400c08039045801888242803038020f00f01239404224414690440c0490804141c405100000300c4401007231066100350000614042d0042003140350036034480008245e5884211107840007030b140c2060f60780e04860070303038400d0051086501038000034500340104103100c5601b040c52803003140e45801080300c805410f029a001151004641550340540c61a82000c07613808995110041c40303003d4009148a02c030303001340802c581d07010385248881c144003111070341e0506000709860304601c642e0b408036070690345451102c210702c03e1003a150f0a414014400345820800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 890305269 1250 890304019 890304047
    0x50604050c03130809100905031203041a06150a0f080c0901020307080c0a0b1f0f06080a0b010e030303070309230d0f020c0910060201180305090613170c01 68
    0x100d404100a004120541180c1c0d00030802e08554501140e245081c4103903015003100960410240381504600e150415800c20689a08804a4982610600c0c9524681c0b1080358000c041886200020700b080700f581071012342025000b440345043c5080b0726816403150b0004a08000080c00b101c24103500716800c40b00301d9800a15019410740b4080c0030301d0020b5500e00c19541e00515045000911000c00c00c000d02c00380005caa4400407068607030802230000407500c182481901040405131000185000c80d9190080031940c440c2c6030060141d4076010310f2030040010301080e505021301c3c0101c0c42116582400118030848031034130000b40b41441410580c01c034070306070200801031580340406803024080028101444103d00e2903d03070803581e075003d000c904240540c0c045035000b80d210018081320700071003802c0d00300759000d82e80200301000311903c2c4111500c800c83e4000d03001c203400304458545030400780c00414521080003889a502030b13070780a181040d1150030145580d00e8029503803500c001d6911007000f0071001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 890306519 1250 890305269 890305271
    0x50703020a1d06250c060504031202032d0c060a1512020f21071203030e0c0a0314070b04080d02010b01090f050904060b09070305060a0807030b160e061b01050604 71
    0x70400001c2056807040f41000340341500501c0e0329004014074150790201c6558046000c4918943c2c1c4c546c0a0300d150401d010485132070744d444031560101d40c030000c16120081605038050f610001c032417110100e00301e90f000031350800350000c1040342c640d910200040d902403001b10100046841c0e121032000e200103003c0d04214014500295401d000d40c2d907001c000740d04e100707040383c010501419102c04081c8041c24440203641900409400082c5003031510b002448140c002c2d2002c1c01042c0d00803820a032949054111190f01c001c600b074041c001300d4501c2d070900c841895840704480711682c841d4091003a6030040c0e4080c03c0c081d40f040074080c40d43da80c280103402040c0800e0074004041403c0140d108070542071401050700600101c000102844913542040c4140b40020b04001110300b07080e90002c0150801300c56150041c010405c0010703007185c00051040407030b0703040b400e6a44a901d6080304400c0004034158498200244450003c103d0356840004000c903001c0c8241d04c0349482406003040c0d0958070018405c1d8421 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 890307769 1250 890306519 890306567
    0x80109060608060f030106030c0b09010305011a070f0206090a0e040501140f0a020703031514040c08130305070c1a03041406040c060e13020316030e010e0d08070c020301050703020a 79
    0x79001580c02c1c0d00088100d0303940c845041c00c41d02090041000d5440548641740c40e00001801e0b9510030010144070100ba40e0038802070782caa64881c480140042485843c1c2c0030b0070440680801c120b030312016102840140618900f86c4658005000e440b00c603044141c003240c0c50410302003002400d02c075000c1c0086000540c01854540300e1480001c40d00010596103015400007610760400d4442d5100d8503005200300204080f264940c410b0186446c1c0302e500340d500840c41e0008070000ea501403042544540d803d2078060110a5040d030f800c0760701380c2244d84100d60f00c10300c402d00803034252940b8590250756000d410754981c50745024104850806140c01401d206a003080b0305004c0411b40c000d106400b5903449040c0708001ea4a000b010800b000f0070588100c0d101d92000c000c2c00442006200310700c0390741c0030940e824489501003030380d4a403c03200c4861900001e0341c441140d07074200c0c6d070090f0369003a842840e82c2030912035802248c0100e0b00b5181c3c00c440c04000070743c2c001401a041c9801149414504200800c80959 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 890309019 1250 890307769 890307779
    0x5040515010903080a020a080d091401151e080105090a031e050a030905032a0c01091404051b03070302191e050c0a05030f070b010518040b06040b060a080708010906 72
    0x4884250001504c1510001403920b40c660080240d415a41d505c40c48059881840c602d81c100102618101141e682d10300a9814504110501903048031060303100034101c80c0740c41c082240c0001280b07410320301001c5803c2080021a01780c20312a191040c4070300e801421a41041e480c0080020440f200c5015003840008441442d00d507011003076549803103503420700050402680c01c10358510701901d641034545900d0400d40d050140c803d0400e0200c001241011100f081c00b80c40c0040d81c414440e401201c4030100080c0e40180ea0707140c140c100c03c2d000745204408208000400091144a41c8100c4103035001c281c0000b405c0000300407008940c1603245403880e1604c20404030111200c1c07840c0380c505c0e040b0100314000c142c803c51402c090004640a40e030290440c0d95400810f400c00c030403a0062507003a0341e12002e0b10000281d900340542465a1880511121540743d620380d501c0003820a40545a641c1241ea0340020707401540712003004044a0700b20751501451480c1c8180004c0c4060301c16004440540d0814100700a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 890310269 1250 890309019 890309027
    0xf2312071e171008060709170102092209051006150302040b1902070f0305060103050c120a0807050a060f0b040b2b2909010c0224040f0204050703060504051501 70
    0x91406000e0040092030311015800f07246010300b50003c406a019030700c24402240d0300501d0030021a284260113400b20360305c1d215101d00700d0150980080d0040076908406007845280844000440a000c1740060866a00d8850525002d40030000040c1640da40c0d100380040500d4250f603810001c0b080c0703815450107060070408680c2d40074034000480b04240810300700c03001074000d2050788058540901003400c140d5890034032030f80e0b0783e200384410f543c24000d007150060681171a1500c04900210b40e0b000f0300d800c210300c0e66595541e61041c0340903101401103500410009240d4000d03a01000341d00c01d000300c0c0312100d040401040b55585003d80d4880c41e540e881d000d4003586013041c10b410000981a1800a0b9805810820441c540c0100d88034808040c5029040000d9842440700d405030216000800540c2c4018805076aa114003040810700104070800c0103100a00300340b08240c1c0300784076001c1072400883c180d01150a03240103407030200100b80c03039060510103070500348291903220031011901514411201d001078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 890311519 1250 890310269 890310287
    0x301031109060d060209030a060203090309040e0f030403141513110108060a14300d0203040302130e010e07141905060d091a010909210f2312071e 64
    0x1080e04e40c010900c5815a9403d010345060160448400d556030318200c009983c80ea804115021320451400c54545013130000000c00d00c655000c0c08004601c0c2138119100c00e0602649540001040d1144403440007601c1314641999003d45a190f15a00c803100c084d00d01000d40c02c007032545080c1005518400c020311641e8190161046410808054a020001c000406c42040034468000703115001001c00041313025100b000c000e03503000c03100196030f09000020000c0340c9074481d42c400a580a142902e550806072107541c003813040124040c00004071010700800c000d0414070300742c1c08440a80d14514005c0f88d5402d01e80b40640700e0b030340350741c003294126803c0c48000362250207001c2d0100002c5907142c0c040703420400003403c403881c05903803415111400d69550080700042e280305171040b55111211015542d5108445010103810b21503929072108042820313004842c0221079003c040d12520603080c019250300094001800312040d20079085202e071a00c010f01070040302c0e507204100c83c7c0740c6a03188100012a4020001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 890312769 1250 890311519 890311523
    0x1a03060a02090607020301052e1503150302030a03021f2304020a05130204090c03051e1017030d06050105040b040312090315051509060a03030e150a050301031109060d 73
    0x50b1a02e0604011948a02840b140250907602e0306040c454521000400704131480030800300c40c0f87c0781300c1c0c400d03e020701ca031424442c80001d90300483d8900100d80c0690403482e00030043d05005181d56a59030002071030041c804005402682058408420b144c80c120301c0c03024210001c0000341722170340880c1c440514030204a2003c00c41c820341440803400715a100113209000301002402403208142000440000b54024071580450354a082403407564540603004082c07040740c00a9030280000081410034540580c02003d124418002c0d65001c140300f00b0207074241c402441c1c024025a00c89608010300b204844003500001d050000c00d001c00c000751652141141c003a294050160761050a03110f0080c0d8420320786030002003000c0014640b0214500701644000d00c00d4402d03600401018031400b003402450481591800c0d00003000003000c0c004070380a6444a40e03c908090700d07043d006800304030028007907001f201010b00000c00000040044c444415080160044200c841140301d040c140005041070420301c0d80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 890314019 1250 890312769 890312771
    0x80702031203011d0105100f0309051510090507030504111002010e1b03010501081203010b0f250318230102120a020c130c05180118030804230d080903071203080a1a03060a 75
    0x19100030002c2c1407103214040150f8033309500490800c44081c041881c02e5005c0e41c46c01905d483e0008610900c640a090b00860f0030026580b4443c1580b4180401c03518113152480075592139807001c2014250400280740c08030400300b0785942d080c80309004c00d4250344060340301d4441a4404882d800d282150402280d045561000c1e08a41e102440300144c1460300901601104072050461429942001c000d10301240c6c900c07a9032842c500150380f40c000314881c2640d01a180c3c0c40c2c1140002d10700c840c0c41032005c0180b0140c05004699000c445101d030403026034014980003005801003010b005a9090801800303030103d4404030107110a01504000420314041c100e5041c17508190310110440c0d903401030b166a809040f003104071309591074680c10940307016800ba05c034416115003514054080c600b021000c40c81d05000042400000440c0c58030b501005ea0400f0305141e03032500074400000707440002d0b9007001001c0b03032007511001c06c01d00d0034200f03c104650b10004080c160b00c48044110695030f030b0205909a0000d44504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 890315269 1250 890314019 890314031
    0x10110a0c260706110a02070302010e06120a020a11061e040215030f060a0501090e1b160f03030c0e1c030302040801060f050f0409050a080702031203011d0105100f03 72
    0x800d0a040d0050261980c0004110300d1140310008915000b444001e010320000d00c8408110600f07100d09101e40360034040180c1200100303100544c07003801e10b007070301c0b0600400e11410182c2a14107265070100694070480c8481c1c2c0091042201c940107401c407e04884880301404003440c01c08100c50141002401c1046180407101c0080c1c219a00c2e510810400c1c0a030509850700c0b40382901906003444000d40e42c640c40344009800020310742d8840c41c040c0007620440607429641d40c950705a040c1c400341c4044649040e00205000340c2c03d400d15210310204495010b41e01c074176441000b42c10040c00b04c64405500c50108121a41042c1c03240c0c0726104800740f0341c0c1544840381c44000b40b42c14200c6c028011900004c1d080d50070000d0008101e1420030610040e10400c8440517001001081080100c501070240145641c0102804101081c0480081d00090b03001605807499071070003980c0300d4820342c4240c100102081304c9a0400d01e11441c00e100c481d000d00301c00c0d00c04054000c0c0080000d04010028007000c4201038461b2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 890316519 1250 890315269 890315273
    0x601120209150a02010203061905182e061803020603060108040219120c12170c0307120305010608100825030b07080612121905210910110a0c 62
    0x1030b600000c0ea2440030303601d032101c4403d00024083e52003a1040ea2042c000780e20070050306024514502e0031598010007444602c0008442c0b281c0c0008000d0070300006103506c10894143d03c160303070510701d291116185101d05080c140b84001e0440340100c40d5403803080d003002d1801d00040e00d511003101d802050900f040c0c6d040b55240e100040400c100c1d0310b00514510b00c9044001512100080b02500892080d4051400d0781d448040c9045810001c940242030218103220010000843d100100030566014050b24a0024076445d140071109819104400195031840108412035014142c550030070141034402a28618041210b03a0f59000c1030740741050042964004840c8125400820f001180e00c542d806d0241e20b0404806071852a08840c0075026182007560200d814002040d20501804014034507030602d6044658040655004c08000091000c10807815150b4a400c0e41c1c05c201c4100072384440d074030500e000c010080c1007410000400810a0030300100e04007600c016826240010700d41c0c40c00c00781c1e100480c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 890317769 1250 890316519 890316529
    0xc1503040516091b08090304061b14100501080a050d0311070b0a060e0606040806070e210703050d020111070b0c1603030f1b05070609080d060f1d0601120209 69
    0x20201403619a040c1c0b000069a140300b500804a807551130880f800740000182c1c402d4851100c1201c001c00326800410003441f040703002c0c50b504040c41400350ba40c00c85429007075507810b070180d1603a14140e800d03a0220414100c034400500a00b0301501da814060501c04030156590f560720005c0c4da440d00300f4161554070f1009801a1082603070720103a001040b0110b10b081c114400c0005040350300030045c160f480080003410900f0710000f00d404031071081c2c1c010203840da00c0110441d00c0c010075030b00f4698010020030441c1000c0491818440300d103025013001e011400e1940ca041c500e4480350002c2c1000b50790401c07140a0242d003814042c2c60b0304580022071002e490360f0750b964140301480b42c00785d14600da034005103a0f0f9042c55415803015002c40d1800e182008610f46401d00765031407044020403a4000340b010000c0d00c0000340c181d0030910f0f015201e568a541041c181d00000070907119141c0040000442e10681000701c10f50707100e801c030455502150111007604007140004e192a40304503242e07042c280c000542c200581c8030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 890319019 1250 890317769 890317783
    0x609090415020d090c055503051f0c1b050c091e0c040b040303110c0405150310060e241306090f1b1b020a081e0c15030405 54
    0x41000800204001d031901c40c51040060040c240104050036262551003030000c0c21032500c040700d04000a0341407408400012541410628805801080c008141f03030140c04a200000b45200d840600b00b0b80041004918a0b1010b2204c1401e8003800d106003c8082d54118040c0200f04401c1e0001c404155280c0c01d10903c0d040d1135040641d0019144010403000b01c0c503001d01c150444403418500d10040e107900075100541e00a81c0110521108104010400240139078803c41501b400c8101343c034080c1c01200001070480380c08072556101c611030401d1103015464144034600181d140e423442008142c0c144440c689103102d00034088118580f0003200188e0006480354072240005e4020303c5111400081c20208019012034031031140f416007028080c0f400384402e80201c96103411380d54a501c801d00c18150080321146c1c1145105401c010002150002589403000100d001c1c1003200014814140c100408101c424a500540b000c00e802020320200716030345d2541c044201d100c110b0403d54480e01c032820000c4c10510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 890320269 1250 890319019 890319037
    0x1050d050f0d030b0a12031b1406070f0e0102070305060f04020102030d0f0209120303130204020904020702130902010e03060709090c0e040911011b02241c0501030b06060909041502 79
    0x104412201407415859001144c4110080c1e42c40b0214542d40c1100c01039481a034403000b004180c0004003940020040d104082189024040d0f0000070302810300390034245941900c01000085a41c4c0104100640107401e51381580c400380700030039004d45192070726502c680d80a02448070102c0c070a804101035a10800581c1c0130606511001c006142034801a10001c0d4410b880c0c0350300500400c0b91110a041d00401a00d20030024146038090415042d42000001d500c8006503039070240e828090080581c96100449101c1e00c0811000280c07441d682c0000740c582100d107046c0750b00c030382c2c0168100300c030182c0d21075241000c840400d0070124444d41c2204c0c05136071a142d64840701ea0003038a895000b10a120400440d05034840080c0ca90039014801d40c2000300c0c20b9100020003a410220190080070f040e9040009204481402c4c607070a41415030201d03819120071900300054646d00c1c0c44030010b105020490314191b4020004503009498641118045400d0030740c02800a060758440c244048240440c54044500b00c072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 890321519 1250 890320269 890320273
    0x11070206160302011d0f0d260901180b0f010f0602120708040e0718090614190b0a080a0b0105091c0c03080c011a06031e040f0c0f0302010e100801050d050f 68
    0x143c904401c4964071881000d5640d03031b505c100403c0f91741082c016204002182018010601c854521003007108880402802c3c010a40d90703515002d000100c1440c502510140c4941490051800c1c00052013400e6141a00004c40e15908843d0400185030000303941c4414281c0000c0058640580d41803140c90790103140c0c484034416503800f040003c1c2a522880e240d82181014402a05250f154103c80c001c658081c041c90701d042c005004c00040901d40900c62a003181e82c6c803600340759802e40790301c40b283d2580c009010b01340104910300d01b802901240c901420700f81600c01c1c60181e00b400d8001000400f18820090005a083c010b00003180c1400307008a071403009103412054a55036110210113840c024041c0740e0401a40218501910013a0310708142160700074141c480c484c0c14076001503251180c0d061005003044070b41c0003040c800f0800042c00141050014180303152200b004074a03500016081820559429116092201d491038072640c00c04019810350310b090b581c1144074400c81c40c05a141c010070751740c0800e0354 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 890322769 1250 890321519 890321561
    0xc030810050904080a180302100509060d0c051b0a031209081207021b040b030607080c0d0501151101020702010917120708030402010f0828111c1107020616030201 71
    0x4c802080020848004140d5403403050040f05111150320350392500000b54082c03894220704101038801d501800740c009004001ca0301d4414040080402c07140c80c2030310913000c200e0100b0200c40c90310066a00407400d003034420183c043d891160f50b0003400d06000d02180c0d054280d44490880502a0100680381c078003050140300c8090342041c100280d6a5030748100c0c440c80f02800c1412203040f50425004120034000c0c0078006201c0c0e41c0b1100029118408001c0c0724614100701440b0341040c0c62040c0c081d490003028019090092044a4040140f010021a01d5401d050303004104120043c0d83c000410011960114426442400c40704030f95403c00701c5034000c0010f072907404035889051013211001107008a100b41c8411103440a040e0302030320008021030380c03515005040070328003a8070301c0d80152445540396040b00018000d1105102060650800d00381180103c1c2209100040820a403150303449200c5070384800340c00d10310154001540c610440a41c00724500469881504240c001d4004030f83c103031211440c441d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 890324019 1250 890322769 890322773
    0xe100b0a0c0f050615190e07020c030706050301080d091503090303151d0106020613060b150d020c07051e010e0f04021b190c060f0c050d020d030f0204060c030810050904 74
    0x520701055411000d000182e2035417001e513181001c01d1400c411640f242d0701060f0b038035042c0e0441d40804010711402c290b0150100340c3d107290390f06001c00e50180486403074543c0c0702d50528065901d01410484480140074200405228140014002c1c2c01b1040242c40c006c0b13a00c551510b41100501101d2101d002440000040458400200502104515126184035150baa03aa1034203e1f0b8581e130070b0700c07200940c403122000d01c40442c00b01c0d0040c0c24940009400d40d500708444a50100d599407114010901007603001c121070384414400d000410042c602190796081c001e0010851000039450310380e01c2030501203102080f0200b030316010840074041000810454480d50b410f613460010700c2800d202c0c1485030244450389100002c0d014600c2a0703198000710100d0002d804d0100c103413000341c00501048144058800d0039800207000300040070101b40194081c09211450040240585000042c2e2144050050000340480c40d4044014107107e81c05140541c826107481000c0d04400807540c00c05600700c50790008200c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 890325269 1250 890324019 890324023
    0x51e1b0a0f0e03120f0c0106050306070509040c020c01141312121704150902040e0d05190e090703050c040b0d1547030a150e100b0a0c0f05 61
    0x720890551289102c0038a800c0c201510307081c203151000d00f4040d0600002480d10086000342c60a042d00d0400001c0f80351711040041d1401e81e0031200381c000138a0002c0d80003501d081501401c5040a010f00040c140c840d40788001805e800c400c0218944e1000300072a041c080e0503030034403050380249691521028010150300303003c0740446080c108800440c000c580c0c9442145081c42802d8451604a0205602242c030f420445d00a488a9103007079070322940320010040c03528001d0000e01c05a030110344a440d42c03400c11081d00b0001ea45081848402e01403140403012890700c404c141d50742e00545d9850000307211396955440764401d001d075070862134a9000114140004200719030041403070002400241e2a116510410600c0d00c1d08020011100070201a5407912503602140700f06049100c0405484420310038491084141d4104584201301030b62100d40c1c08600c5280c0c0117410000d41202c1400c000ea0340750858903465224042d1145082c2500001504441d06100d544155038450f403180311481c80e8041030520355 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 890326519 1250 890325269 890325287
    0x30b01080c030f060f060d0206042c0c0705150604090f060c020615010518130e0a0213020a021e0703080309060a060b04081504060b031c12051e1b0a 65
    0x41c028419a540901c84243c0020864440c0900c000a02e01c3c07075a42005000310300c1c4507a80d08980004051002084200d85a0340c2c0007914140601c9091402c3d08000441d12601d0000d03000103006101004090085000800c00c01462154024100300c2610307880041001098030002c05071144040700581c03000c07c52550010041c01c403ca42c2150502d407651034840e031000c00035040301804244200082c621740c0300f00542c1054152001800c403059034224070095400c2e40c3d02040400541c0e0880e5a0090451502021500d4041e10b0100114103010300954082e68440c0f140003001c10107507025130700c140d0301e0000700500c4000e103074080911341c0c070307403e014079101d0340d0340b1040d02e210320306078142134000c100c1030340d088140c43c11140110010b10380100d0199008840310400380c01502d90680314076641c801a1030402500006000130325108a04003d030950080190b0008521451085c0c2004180030189680181440d400740c0c0303111101109888210b020000040390072561001d18102144e0308110a030030503244 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 890327769 1250 890326519 890326543
    0x418020c3a0206010f030609060b06031303140a14070c21030e10021c02100207080c0706050909061c0506010e060112050c030109091410050402040e0a03020c01080709030b0108 77
    0x81d2240c42030460607030311040d003401a0010740f04c80b5241000401c16680004900710f014000001e500204000400e110341d008482c44041c0003411000302c010550b03c842d25940c2d900100d0b004504010231110010b0044840d00305440111001051724404d200e40102c10f50001d00d0760005150a19401c035440034062184040d0940c041750300c000d2940704508260654111460466020b00f0300940081d2104507200441403c2074118850f80e4240c102d100700342d1000740f04603030081136003903140c100b1401118034054440e040302003044410311204000b0780356981d44a8002c8812200d002e8407081c1c01c410390011714440c0001030160703c00d10340001491000036080a00940007039035115603440007244079005480e4107035400711240000b00010410000c55501104500740700c2c0d4050101151100c0b80ca51925507126682c803007965455060104614180c49507828800c804000307461842901e4501948a400110005050184040000f40118882c1ca80400134542c04001c001c01c5584484600d40d03207040c15005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 890329019 1250 890327769 890327863
    0x6080c030402010c0c0e040b04120305060f1c050a0b040533040303020f22080a0201080610051c2a020a022214040b3106090803090c040f020418020c 65
    0x50b800c0ad01d48240a0144604005444800000d0700031044c03110b88a40f441c4240d00805607070b020240011814010700c1d00d0540104059900b505240c10054101500000400c9004400c20940034640020054a43c3d4841c902000b185c0c090707490341001c1e4040e200d01d0b5050186031000044200c22441e1500d07900d40d00c1c148003202c12050a803a03499a95807820802d00180c04520080b0001f04a0710704030408008450852800c20f080900c072400c0c2080c06450032540560980e112202e51803641003032040c01c540403003100b10344c415101016030302941b00c2d012200013900a040304240c840c4440c140c40c203a01c0d10f1900040b81004500300340103d0310300d1f001083d10b0444800c4059804542c003e104191742006410803000800c000d4610540e000e00440800c4004451107900c50004030080760090340030b14420341032000504000600041000102c9241000f21603442d4418001402500e10f030040d025a408682c07800140e07030f40d440c15800e03490580c0c40f40c4c1000070140880900300107040d4543d03808980c0ba5450384 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 890330269 1250 890329019 890329043
    0x2040f0303051206151b07120c08010c020703020a031e0c060302090901050a05061207271d04080301090903020c0406060e0924040c050706090305090a06080c030402010c0c0e040b04 79
    0x100300807240a00320b4640c040e0744c1d0180029082d01681b00c0c802240b64611078112582c140d170761045440c6a0380206420303a100030880d0820401d030f030030a0150020305e189520140c0005411540004c101d903003980005081d0351100f083c000d510309803102d0b641c4412500100703a282001e0b0380300c00c014065849100901c0c0a000407200019141c1880c403849420340700c00800c0c140c1400d201c0c01d844e1024140007440301c0200482c507080c0c45000c950002101700840f08102035014020f003410100c00c184050211303504881001102084081001d0f4420349041d61310061010407025241d08040345010701c001d110a601600c2d0410000720030342c01c0b9071211348649050380d200d40c0a03a00e07400403c0d8103100802200702d10114141680140d032400381c2c03002008042d1824a64208412a03c4040403107001501c200c1c007140300007900252a2901c00b103c0d42c01000c06242064140c5010038140d00d4500010748001c0c1445040c0700f69108001074516000c0c06400400141109403a150810300030307039001031303405458042c1191 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 890331519 1250 890330269 890330281
    0xa0b19020f0406080c040b0d02120105030f0d030c20070501020706020312040f02010909051905131112070e090c010e06090123090d0b0f0f0f0106050d02040f03030512 73
    0x3009407040e07401c1c000c2145080902d000010340b90010010070901004504000200c0e140c21303030401800c0c1141c0140742c01038032015a001d0319514400103030825031096010454080400c080080c900080400d20314000c65114a0b0341380c01d4507103003411194400a0b8007008a0300943c00000030b202011200240e00301d9101e20707078602040e600c9200f0307000240d442c9454a000100424a42c0305e850040a00c1032410126281c2c1d2404003400302c801c00c0d206170418030042850031404144030b025550300201081e03c840038011066440110100e171810000740902d403800e00ca00014002840050300074800d1247e000c0c1c461410b0100262100000c00c41e80740460341812107685542081410b441c003910041e101e2007031082c2c0d000880e0b0050900340c03441c801c1081c81002a1841d540b610516640b0441c0300303121402c084d04003c0004461420300404400d60001e0007410003260130088400c45044402c0ca00303200b6900c0c3d401c0c205d1180603100315007140c070341940741500000426078003000800d10804a0114503003551614 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 890332769 1250 890331519 890331521
    0x9021c0522030e220203041209080a060b0402070b010e01150f14070c05220b0f0622030501150306050f1b1605072c06131d0a0b19 57
    0x14566000310201d0080c100d0000e4040c40801d151150300421441641040e10852050040c800d04003101040c0c01000307110810414452902d1002c2c42414024500350a00d41c20035030320700e000c1c41c018090781d4540004860549441c0d0489040701e0704690126480c0d031311201c5483d0b01140070b01c501d00210030030621020490f4401c048881c00741a2503500c3c003200300704c880c203142c074281c20030907068881d0ba1804400007016510540040e0307a9285030140084a01d0012920f403044441c0d64581d680256040b109040855070341904846600c80d40c0c400504004c1400d190010256200da00010199882c2030034580b080e100c40b40d910004c0f2880746100388442d03964201800d0f04524240c03a6841030707022078a00691010041005042c1c040f100d501034246c2442d4588400e440c01c09990b220007000102d0440c03503c080b00c0c22030200304108240000d50b1040e0304100011501c0390016001e80c0404070390350810105989808040e400c1c04800902c02c403124030140d07040260306064155001400c098555030317000004007903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 890334019 1250 890332769 890332801
    0x150c111c1505040c030b1909121407080708070c030f0f060f020711011202070c090213060f050d0b0d2f180402060a11190b010902030105061b0709021c05 67
    0x101c103a460304c1d140c0c91941e61010842d40074003501030034008070b051070001490a2285a8109001da0316014003c410070074081c1c54045c01d010100c2440c0020842c500204800004441c910b592018140340c1d2180356042400c02c110540c3c200030500d43c1d101c06220240300c40c0380e807880b0015018032000c21900c880c40b1300880c12440303200401418041c90070324a443c1c41d1b014880c2080314000b1100c000d49000780e5a40c0d0890701c1017aa4101d4000e4550200d024400d00d0010380807207000d0041400c1441d550038602d5401340c014059a8800d030001c58076050a414652039180384005400c0e4081e9414402c40140201c0c1881485515a00b07410300e219000b408405241500304103545000400300710820303846a800707100c8507a100144d06414001c81d46a50510740d43c0c00c00c4031003803002d844c409524a00c01c140c5001c039010007041e0f0010900c18010710050100e903507003500301c49060304010319107030001c12960039003420320b9134a611084840c2e1000c80e0105031120741c0ba201c0041800c05a038200042d0b07880d03107507240302041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 890335269 1250 890334019 890334023
    0x60306140a152a03020a140f03120406090f0f020112020301180b1804050f121201050d060605030607031a100509060703090806010f060e0a150c111c150504 68
    0x32001c826000c0240103040183c4004000d2606800b030380c0724003142d00500d0250100403801684000c420505000d100e061004c070300c0e91044007911002c10241060380d500c1c060746052640d4240600c010904000d082d510002809a000c45010702d80d1400b400d0186c0011041401079000c180310041203c002c00d042c0c42160b060345c03c80d500650104150b104644001c1202c0f10005810410b415950140a484460590308c100d200310f0092034511026a10107040038989104000360801c2484030788481006d9802d01030540b0003e0310132080c1084103040210140203580d02c40f980600400c0280480c11764560400b2252031141807900c451701600c10240b105c5440071a04010005805000d0a489490900c0040c04254020301e8581e181a80b5044c8050800c17000380d102040c141c01080b01082444e4100600b44040340c2d0490301841000c0c544016528500c004903001010480c00024503004c1010810740703895a054081e20b81206560b001214005020b48100c0030b075004444061000070002040c01458407480d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 890336519 1250 890335269 890335289
    0x309012a0e0112020309010b01020d02010c020a02060c0a140d031a09010902090a0f12022d090c130b090a05100c151e06030c06020d1e050f04060306140a 67
    0x4144980115500301d81c0d08496410800707481d04228a40c0d4a50000d140182c90f450000120807003a84006803501070004811300569042c149a08000c0f6000300e00e9a4060340c054403030384e5984582840c0c240c180092032400a0421254002c003200020000070001601740c0d842c0c400b00700400d00040c40580080c0c06a8816034096400d030018456010b0580190141d107101610b045485034840f1200b0780941c045800148496070305030214415890041442c2c0614101d220003a00340c030004c800044d0060b01d0304d801d100d00070354000340401d41e2a54a101200c0c8411144890008103688840d0418076544c05190202d10818509101041c1c40c544203000f5124082151948004920582d81741c070684900e00e801d001003107030b03610304003104c070810580307219039012000600007030050851802d40008403554000760219407100403508030550f00040700c0c0c150414a22410b0402d968021400c4035240714280c4058040381d0301040c0014000e03056000f00c02941d5000309041d000050310340a00a01d600c5074071030341d80d0355 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 890337769 1250 890336519 890336591
    0xa050a0305190f050d05091306050d06240b030405161206110403020a0b19110c120a02060714010605010e100809100510140f09010501080c130b030901 66
    0x104102d01850801c240b060129880b0f9451036202e080c00d1904c0c0c1c0c80d00c40013040c40040c41440c1d500c1d1151840d91040d60465080013410704100c00b0454040c1c0a600c0101925594007050174070000c425001d003140400c9040c42840f09480344401001c50b0401e95084850703104007140000300303528141d04c01054a40c41ca940740b100b6003080d12050003038807105109020708901040080f015032221030103c1d0161113a510303840d6803034031b21400d03c1e01c218180c070324904200103020001c3d20305120046416186240304641503401c903400c4100c0281413103040c200096002000041c03001c200603d0711007141011702c0c000000c00205580720019500c040380c261a0550010000603c822801d000300030740368112500104882480150858000480340c1c2560942c0340080c80380310402c4900c18081e0500c620200645120300c0304019000410031001c3c040c01440d050240c06d200040010009400303803000b030344102004e8242590f07107517200c0c141c2d50300c03d68407080030f1b509104a0f14104807250280715507800006100d440c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 890339019 1250 890337769 890337793
    0x1d0d030e1915150f031203050402061c020f030f16140d09140a03121a0d0b041707060b15030405060a0b03030705031305030c0904120323040609020a050a0305 69
    0xb0000380d030503191480e295500c0e08402950710a510000113041400d0b081200c650450500e50f5014860580f58010942008100030050700c9520949107c3c19401d8180c00302e0801c030000420280c0500000c6104280000c01004002c1c0316030b41403103020340d0740c000065505e0b9908020454131800010801e4510080800c1046e0703407419554403c02c4a0340c001c10358560100200c11600d41030402e402c40030307070000740745d5030440d0240360591141100440d12a230740758400c102414003140065050136000341010122900140502440c618004c00030707079460413900e55940e224a0081c5c001c280e40c0e014a805060301c807000641d242c5019041341c0c002e80e008402400203580c0e041c500d0015100300520290507000038444c450000b441000540902c2e860565042c03070145c109000e06207400c0c05141c031240305200c01c000344000324458505038201015645004640c0894101c8180c0c1c0c089045a013045458008900300018450f0341e900c609203051003150316501c000d6030340307040080c10581800040e155400502400e46 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 890340269 1250 890339019 890339033
    0xc060e0601260606060a2a02040f02090901030f1b030b090d0801080a020f0111121c02070f0620030c03060102010c0302132c10060305101410031d0d030e19 68
    0x13084c04a86040d844000b00c140001003074441e010010071011550f010081d04600c3d01d03000301342103419005011410703300e240002452608061101510b00694008c1d040e00b03004203000100302a54882124007601544d80c0b500c0001c40008940c0c4807184e00400c51400301461251104074102c2d24148020000d036806034081203144200440d40700e06220b8102100c0032070380340034050260055541840e0b161201c2c1c8541c1c03c0403e030300c19038010020385d0748100103010006045c0c80400c0e0400e50480000030308540443d48240912403840ad200c50002008010030000ca10008019407040200780d00a102800200b5010f406030301070011007018240e10003206000c1d2600300720800e40b04000c14560408202c003903160380c81c40782d0b00070f6414080005280009109544e058051a41c2102d982008101c1c81403074080b012156008448840788a0a50b042065100074401c2c4c2140c0078825203c0c50000e44010ba41007000d50b41c001c0e28940d440443c1c14400122080e02000c80c00740384004004001e540c0c00b96035995024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 890341519 1250 890340269 890340277
    0xf0f031902031b0c161d090d0f052101091d060c03160c120201060305120a1d030c10030e0d03060803030c03190e061012051209010c060e060126060606 66
    0x10101e05c03880345c62804002e948490070000b401141030750150010034116042d0f5610004020b1000c40d800240011805a4070520003581d5412901d0000d496030040202c8060314400c0c46400c000401103100080b488103070b035071301410005001da420004400d2600070442c0d101c0303c04a590004082c42400090304200080341c00d08a481d009140524240381180e0750302d150714860180202c0140c4d5255000d00400104200c0c80c4403a600415200b801d10030002c4008001188041c181d00710030700c0140304404191000c001d41900c0f2000200b48003a00350010200030002d00010398003481320b00c10008040d880c5406032140758141c03451800550301d59652454895420fa00140c1100120755802400d441001c00324459098241003d00c0604881e05008251182c01041c0d60000c2403602410b80ca0400001d50003d96a03940c400750740f40e0140c5426089005a403110300420001c2e101c1d5085c188694000e101c00b00d41c880c180c550482d010340907400c1650200d5010b00d601c5e403d451540d844040859824603200000d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 890342769 1250 890341519 890341537
    0x15170c0108070f0f1b06050a050a0507050408100c0905120109050105010506070807060e0c06070804060e180f06120a051038041509090b18070314030f0f031902031b 72
    0x1445c00d003503a0320300e01103440803520484801d6480703040c0002c5048600805400c00b51502e0410b003403604161080d5180c4982c45110000d4560b1410b0b481c800d0342c001d9049600a144c01000048a9083c0303024a90280480f03480445095280100200c2d0130710b4640290303000c65800920150405170f441d41c90100038a4000020102403054864898260b41d40341c2c000d010041c4906002604e592a02c2e02c00b0380101130b1648114400c0f4008111140603004034964281d0181d5042030002081e00d5550202e80015404810080a4043c4100b0401807090000341102500d486210401841140f580c1e40643c5d012010340440d696460b15107506c1021034028006049070b40000e01c00034902d4081c0110201181094cc00190721580720541d070f000f0300403040310b080e17840803403150700300f010320444200340c6d4a4507010300005102c00d1410702c5440c40c603141041500d02d003170040302510741e5840703541d0001c40c1c55400031034072182c04200c035600d4a00c5600300350003900c2c0100340d070a490b050703180b00d00351000046400074484 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 890344019 1250 890342769 890342807
    0x30e071707080d0f0906090e040b040f020301150e061f3501090c03110a05211e0c180f040b180117030f0d15170c0108070f0f 55
    0x808207141c0c2d024020043c407440f03241c032181d9094031803440282562005a0101080c000709100800074607508403043c562265100004980e1595946460502c008400710003a401d58a0560070445200c4001041419103450036485c0040303a03190420030150201c0321062021100c0029641102c450107042015072400480900c496004800c103504070402d8030341002d9191520380c08004001c100a0791003800c0182c12203180500401c039042002045600c1442001800c02c000001c08000e600c0d44400606a0b203d034000202e200c41c102078050b126084643c0030004524850030002c01d402c2854201150604d19450010920480e50703d02040b040040d0002c2c80c6820540b686100e90903a52896031202203a480e10f80c04400313550510f078000c00c00b042040d04401c5164800c209031440640c186040e0f6140b501d04980215580104201482d04890305134801440003880c00f48050a414020441100403802079a4103035080d80d80c0d040031141074050781090004103001c3d500c0c2c0000c2a00c0307810303444699404289 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 890345269 1250 890344019 890344033
    0x4020c07150503010303030606020321070e04090c0801050906070c0b060607060903030c230904240308041d01031101140c0f060a0b12060a090c05060705010b10030e0717 74
    0x2400401c08038508203400000d04000018030405030035115400c05024544000c5041c00c0d84c07c0c00c1121605075001c1c0543c074032200ea10000d4040ba00c1030051055010002c2c00911040c02649840d091040e001c1c010301d1119400e007000500703903480c0000c41c54401c0a0710b646d05529204c40307031901141c00c03e01411035600110108001400300d6500d0041040c6203110740d0b0002608451032500400100e40809614a420801039640c01c2041000098500d10342080380c0004200780c00c00843c2e41c3c00c40c4000600040190f42500000a200201d0058005c40d0001482000c0613000c0d4554a0118130090000415820400c508910107510843d1b003031440300d13001c0c040b2524100070f152180d464904282c00d1605194084410405561540e00560350514001c0d1030300d0652402d652012a02c03490300400203035070a580c0b04e10764018400040c035600010714018040c40e60f6a0030700d0078014083d2181005060256041d90300010364584a44180e400a140c01c0000c1d20703160f82040c1d5107945120b40d40500344131030710402c0c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 890346519 1250 890345269 890345279
    0x9021f200a020102071a180303041a040312030209090a090f0519030909050106090e04061b03091b0b09010c030513060c02030609070e0406020c031c0509010e060c070204020c07 77
    0x98410000c00c00500000d041201a51000910b8035810390820000955988005100d00c012001954441008004119420102e000c04a0300e940140c0c0e100d000314040808200c0e0a01040c0c04c01042600c1c0100c2400c4c8640c10440d00a07816440346100d0160006a03c034001601e540469000468451040031080c24014003900c416281181a5894981c10000c0410340d20030160040d480000078207910790709121562412402915108940c89620300b4541c0e160009000c00505511110030554a101081da07203c100e010003c0041c0321906045030300c0552907241c4030440c2000381107041190301a06030103103043c80c0f410044030003c0240c0000c0b003d00100344900400d5102c1e40701850050300d60381d41c492003a440207004251508a0140a828031a04051824420343d004c802003d0f0348180c2002c009a42d030311211145a10b584640c00006021f0040a03125106142c61900a41e004401031002800101e0b8103402c5162111410b45104007824403c109442c0142000c5e000b0b001c4009200c0140c40d1955074403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 890347769 1250 890346519 890346557
    0x804050d1113020306010306060c150e0f010c03060f050409330e010209091608070c080d020c0c0420070f020d0506010b09040609110d0504230f010b01020109021f 71
    0x2030100b040700c0076008420010309590500c10b07003000340303203624003004106000d896000501942c20035250308951521144640058100008440031b10414020820044501c1d0024010285400340810040212070001420324160140840c000e820003607060a101961580b9010018003043d10010908440d40c02c101750841e44c07040e0f8000110100001d80e03a8030b45541001100d0400401c0102d10281c04440700301c10030782c400900c0350b00c91b0701818030650710310b51030600b040390f0b0040424400760a03000140e259130400c4003040070800103405407010310140002e00306d407424134007903e00f100050704400e0000002040842030010b00c01800500b585210600300d80305e042c2004c600741c0060000b0f4000048070b494505203882140014401c01a003046402d110303802a0246109044001c00b65035107035800325080c840c104e04000b004c050035820301181160f401c0034060315583e15112541203540303080029003040d40180150065203a0081c000d500000c2c90001504000d24490002003c10880300301504048101c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 890349019 1250 890347769 890347789
    0xf0105010b2821140606030412051c0513020306070f0e060306060904020301420f2a0606080309100c050f120903190510092105071205070804050d11 65
    0x1060701e0204022074492113900a4010180032075001c0d00080040001051000c034505015902078a000c0e0b5480483e08103030080040b410b0f083c01b041d00e291105100300700782941126903d4910a40a454259462070000e403581c022405072040400c1607250341000c1450084011580804010007840c240407407000481c2c1240c00c2604008010460000385a0f881550700d80001c003c0c20082c2d216400000c542d0241e40b81c882c4044604005204002040e9000c45010b4140410782021a03081c800b071401c0074412030700c8201d190180a0310214a055400305202002000f198903201c0d01500c2c6000d40449094216803c0a1416054980307010705c041c10181c0c500c1c00d204480154900c19440c54644038060304040c141042d902241c1264020800d000c40060b002203280c005248100340000b1791600d07a4288100b20f007601030742c4007100c2c40d086800249540d070010003030814640606030390040c4080d40c841c142c84600c640c1102034404903003070104000c50b103401c0f400000280d10a80e84d0007101800c00d4041042e600c0c3e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 890350269 1250 890349019 890349077
    0x270c0e0405010c02070b0f04121505040503041806240c0b0f070e090403020705041d12030f0108060903040e07090b0c0c0f030120070602040312020f0105010b28 70
    0x51116640340083d541040880060212065968070f05848081c05400f98851031041451101d02e550081c2c00380086071503c951301001c100c200340814505031170010380fa80d20a016100032458015a0090181c141d0300c40e44081e1111b00d2000c000100c3c061443d00c0079003048442c03200811900041e8600054041d03403000d0301071040910503204509140d0400782520700603c0e601c601600c1c00c80100700201e0340c002a610211030050305d0010301c1034400b9600060765a55045612103601c6607030031020b4072854100c01103100710858100041140d89924070541c641100783c880002ca0391041c4004d00c00580a6440a0b8202c25036040489045039507284400150f000742c0610034203504242d40c0841141060303074031400c000800720002c02400302c526078600e83c040030b14949407001d29004a120f03c204441d65049030090758212401c140c480087e56002541c1380ca070300304c803a5000e50074980000341c1d800324001514040c0169820007810305403c0e85500908808101d0034000300504201c1d0511f260760f000132504800302c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 890351519 1250 890350269 890350271
    0x90f030d0c020f10120509120403081e0f070809010302130b030601020f0d02120d0e0105010b0409060e01030312050702210d061e12112d010201270c0e040501 69
    0x101980104a6681083c10b0003600600d185004403e0541d4065040f40d10700c01500000141794030b584500030714110391071111840380ca000090100501c100e40f009021600703440710392102e6484c12240511105d0140c2c290307000a100e000c5c400c0c100090200c1c006007418900c107240050a141810340d1008031802107034050b0b009074100105000040d60b05202d03045e182d07580e00c1c0c010031100e030b040403000b540c64505610401031000c01080c00b082407582600401c8003071020b080280083c3d41c440c1072421843c1c0c444d204050455160110009152440101340c41c120ba8245d04c92043c0074100d804800b000c0c110041c1040c046008400c00120b01e00590a914508011058800742c1c940130010080400c0310015040042000f1031040901c280341c13200c103203550035900c1c1508441640d01841c505881c0d00d0300d0411380c09a000c40820820710740d02409005c010004680d0200c2010403050000c0103a080365071100c04101d10300342c0cbc002d120300420a010000c001880c80740041504556603090b0080c003400060360125440e07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 890352769 1250 890351519 890351537
    0x1505070618050c190b0f0c0f1c0e0307051c0c0e0a0b0306010b0703110f0d0e010f0804030905090c1209030c060903160b0612030705010f050a1808090f030d 68
    0x44102000030003145141a80e510180c135840b5041c400c040c411921800c00740b40c1c03001a5090000141d07105503a041c00510003255445859110711a448101310702c0b0510220540d6442d60904902c580c443c020300711409030181149070b05100900c503d078250591084da00d040d2068459000889031f0200000a02000e5402c804074107103a00040141d41e040900030303200c0c1c0e2040c40148070740c0d288a82140ca00507894200110080040c8a1450800303000c00080f0209005009020413a19007061f1003612501d000d0342d41d440d003003102e40e805650203d0306a4001d400a044c4030b07001c1c816403c014030020707007103803554152030f09080d5140d08560302948112018919a000071810000300a01049499041004d00e0055800e0005110600070440104000036040400820100303070b0316182e1800590741d4a8105043e250b03900d9041c10810f009c0c00c0d541700311135005071412000640355400c038440d04000c0303010742804802c0344056450b948081c0d000a50384039445098403081c1c50440e07a0400041402007200c6d107414041c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 890354019 1250 890352769 890352773
    0x1b0607020c0a050d03021009140d080601090b0c0c2803030903020f0a0b0f03041a090a0b060306010614070809090907091b0f1b020301020f0d06050a0506041505070618 73
    0x71200e20f039101d2401040b8440c3e00d900000d4001c1200d4040b108003250005150410303051507140140060139144490154a01c417844841d404140301780b05d10170a03240d2003025980c40080040f03502c00e11021803c0e0741c200d1520b0020601c0e0070802c2c0b40e80555100d1a42c24142c0b0200a00b12001c40e143d0b00850100d0a003d030104110300381171005041c0d80c0700803109003249925008101d90075219182085840a40000c005030821410300521a11030360060520b80d098039000320180e5592034020700c242e820200d010001003140c500028004c0c10385045540e1708a10210880505845030000941141c0300402803200d405251580404a84111075400041c945245080e03000320440d002800810010340302c0c0c80c002e0703a419800403d50380c0c031100507181151840403440c00b07034400405c0c4140020b50650000800c1010002090080c2c1104c1c96408400c20000b980c4504200f00c0d004240300c5d290300084180300400950300810094084c00d0fa590400394a81000382c1da03210111000e40c1c3c86040309130070303003022941 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 890355269 1250 890354019 890354029
    0x20a0309090c0f110304090f0504020f1f2a06060501080109020a0c110310050a06050120150c190c0c0b092d03010213050909070b030105061b0607020c 66
    0x40180c0032003000b481114450041041080000201c00d0028400d01c210710710000b0000c54004000ea19000c001038175203846070801904054a05034450400a008400607103403000c0c285101001000e082403c00b011901305950700c9181741e04405000340c0208210b00f4006180c03a103100704a224070130025519041030005441c5c1001130700068066481444006400b94000c408401c0e40e80d04940c142001208032030029282c070703150105000340139051006214403030342182c1005081e1b0740300b40c0720048044a41034800c1a48000054407100342d5104034500075400e5060f15846030488040354009140c074000700e20203e6510025a404ae0009110704003032014001c004100202908100e141580f0300040303c1c000450070040f600b11981e820461030140e0420740000b607000f003038442001d0001d54980c0703c8900c3c6401c001c22188551801540c100b0002480b401c00882c0304016114104d04160443c1d0901c4184a0541c01c01c45002005800c0d1102c25030280d08208445440744c00c991740105491481c20080c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 890356519 1250 890355269 890355287
    0x3060507050f03190e1009021e01081807030f030906031404020d02040b0102010216080c0c09040c0e0402010e06040b0a11070f09051504021303050c0d020904141c020a03 74
    0x9401c124082c800020100e4412003120b8100e501000b451005801c2044540024050740301403c46500c6004801d28442400340c1110a00900031191b4000280220807143c508042d00309070180042d0880c00041c038003000040d1030b015001d80c024101e9079119140d50302c5075000800520181d020402820701000119498020686d100c2c2148019101034186580408c0a03040c8450000f4421501e418507400645d03c00d5044d034480d0301c00344030050195a603a0a12948591004003044514095014540303036a0908214803801a41e02811603024a0326100510a1808000e0300c03c0b070402040e500301301d01036030700d001c0944094002100e4896564204a0001d8a41100c0b14064210358208540402c4040c0215010004603403040c0004549544c40141502a186160724029449880420741e0a001c0310040301031030030f4a01c6070040323401550b0704000300903460350344a0000b5446108500080d00041c4e680341103158000c5c00008650403510101c2035040b220380c5404d0315900503803160280406255100100c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 890357769 1250 890356519 890356531
    0x10c051c09020f0904110a09020d0e0c1c0314030c041401090506030a020d02190f021513030e03010f09060519110f0a0908191106120f09010204080610030605 69
    0x1c11009400350b010540c2d403540d0000451195507440000760901501440d00215114000c02d04010301d51101000c00094002c1070002045903e032444045166400284c13411000c0c1009140d50100700c020780c0c80c11601c060441c01103080040b40c450070003c84912601840c09815494034440e155428580b5002c1030115556405040001820080005032a02001c43e03421010b80000581c4e40e15001116402078800c01c101e40c000c50518660300c0100b10350156004032484101d5007500e0b8000d082440100c0921025280d83c050240c0170020500064010364451601e010064000328094038640d10900840e00100016600a5141c0c0100700d0444076241c1071260140320650700704040f130b440c854400e83e103001e0643c07411001c00c8000342c0550b80d01d014111a10042c08507500710b520344a01c44001940c0b4100040044561000c039140401540c60403005891507091304155203540c6070b80303400d000c41101e080500000240d5608020106501c9400e22500d881707500c000540210f018590b161600450714001c0079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 890359019 1250 890357769 890357771
    0x12070b0d05280506040b0612180a0314030601120504060e0d0311031f051002030c060c18090a060902070606140a050307170102042d06050405030c041805010c051c 71
    0x2140e580020003014102c100d501420001403a50302c0d503003c20010b0884c4011540d1289000c11341c0c00c440030302032245603c150441d41200304c1500c818108555110b40c0c0c054002d0210354200f2128a6000c0d03000041c5a01940524128030302e17401c00900c120132a44180c0303043e2205a12038030041d0041c0c404024900e00e803010341c98200841052001000c04c0c82c00085c1102000a02d007040754501e103201c0c13000302c0c0c0c0070709002800414801d00a8202940d65400b1541030101809040d00003029109260705032180078450301406050f69241c10104002200300414912107150340c1c0c2004500116148040d1450a1045000203505414154018980002800c09900c255041d034800d1115171000310b4148119840000c242800003400040c180c064041d9401c910340202015010b4510243c200b5030a0034543e03100d0b40301d40c0710140c480c00202c0d0a403055000c0c00360503138000d000202c201e04255001d00858001002664070a15860341e07050b0070754410042c503070b00045001c1a080c6112500310600da02c032081c0c41d44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 890360269 1250 890359019 890359051
    0x501140106021e160e04111203030f060603040c06050a0306091a04050f1b0703111b0f100f0f09080703030e0a090504020307060302250b0108070b04050d0f0212070b0d05 74
    0x802564092203010b48005d994069022404000c95041240c8444000906500040c900000d88658a8008503840081d044000740071410a080c81c0e000c9901980d0802100300009040900035110380c0d0003040035104056840900160b020403510651070001c1002045031814040d100800040e07603400f0b4100c1d8602200784040c0000b0400003141c58242200400076191200624141641c040441180c0e0520394098038003c580c8a04030b503418100001d900300da03006660a140410700640380107080e1002c01090886200c5c0c5804c60080d80742c039061409030f141c4441101e48035169103041c40c40692003240440c08d1182b49501911309104000090210a0010020703440c10b41c00096031030f42688100414580c1c00a400c2004584280d030001c1840312049164200600512f406600004244100d000600a80002045c9111f9106c212002c5980040003810418000c0c0c851484850701c602089a02c1100c524004200c4036090052900500140744402c1d200c4025840325416258000c00c0c2140c000b00340e071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 890361519 1250 890360269 890360293
    0x1a06040803070308040507030605090c0907020105060144180a20041d070510030b01020c131b0e030c09010303020d030b12032701081603090501140106021e 68
    0x400d40340d0032601480c00500c1c40d180e50501c1410300007c1d0300040d203035900705810003002190005501b41950420707610740340c080d0343d80b1904900702d030b0083d59150300003032025104100035648540c0501080b0715900010034280f004500c0080b940c02c031803841488002e003c03410440c200c07080070502040d160858000d800200d90541d00c1301036001a800d007641d02c941d00c0c41c1e032103806500c80c3c4c0d100c0e2780c500441c0c0c0e030714544040802c4401a52040c02e440707060f12441d0742d20241c45c41140700303006000c1c084206030010003075070408601300451451101208640da0b13075540865000c482004140840d4007400d40c549250010200042c18207002d5202c000d10701030250000100b002981c0020b81c800406440d1400081c4aa04040080c03110503408440251501c00030800300030b00d2844c5040110300b810880758a429502070303880103603030307043d02250071404591800021102c2c9500a811500c061448ac1c000000c0f00d01c01c00000f000d4010007070b00181c006074026103c0c200b01207030001860b00c0c200310700b41c000e0407054891 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 890362769 1250 890361519 890361523
    0x303040c09020c210c0c061306030207111008040b01050907081501021e030a0e040b0109180b101e09051e120601120c210204021803060405011a060408 66
    0x2500c19503451982c001064150640140316a94000c140d12120b104204001c61a403402c0307402c24030b540b107103074042c40d00402514078000c07088540c40340244420101162400c40141c2c0250007403c004d5408508040c0b03841405e55444501007034650071911280040e040c2400e240681c0c00e070503007046000311002401e025690390000c0c005a03100c2407030807642510f5841600100d003040d000680700a61404000030302690030501001802065007240d640389043c9580104000555110041c810b0116400e0722040c411180300c241c0701000c0015081c40819820784242c0854080700354503542000081617aa4855401034550400d4608041030340f030710b01c2c400d9040c05c00198040a544440d100c48100c810000102512202001809808003500703598881da5264203c0c03e20041c0990222401d10060320086030314038074000c80344152005c90300300424035010340d402e0000030360000e0007045050a41c040ca0702001d5a0412005110f41d21803400452030351031100c1d00000503510094203d00c40c500c280710a00071400c2c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 890364019 1250 890362769 890362793
    0x604060e15010b0406110109110f0d12030f0c050309070b1b01060f05010f05040f2102030303071d100e1021020a0e040b06120601050f0706050a0e030304 67
    0x420005861004824161800220040d8500304020110001503c0891407000c0c0040364034a458103400c903c50350600c14201d80350300720300070b1880030641c0d5802011706000c6400310b072034480500000c8951100340c448201d80e61038518044d0019441e503c10748000c042c18000d42900d14581d0a1946c2076081100200d61910564054402804400710b151240c2002c003031550319590010320001c00115413a41c08840520503140a06400329400074080e0488920420490b000c40b11101410440a400e10f0300c00c0e40b1081a1000d480602c61000d203603000560340c00d000031409440ba43d21990000e0307032900d28641c851124000300070f00c01d16060b0b4a80d95019005140140c0100c4125007003194040d00d00d905480c00356010001220240018a0341800c43c0c03141e40c0141400606074880f49401580c0000b0002544c0004000d90b802c040d003840042c030402425002c1e15007281c414101a41071044402101c4520303004084180c0c9d505403124180011904e19101350507032079607901c029602e1031070540c88d01142044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 890365269 1250 890364019 890364023
    0x4060b2103040f052b05160e150603091f1b02011d0304050f0913240e07060903120306030204050a06030c050f030606130b06040f06030b09010602280209090102032203020604 76
    0x45d088202c0081210a004031522004140c1031140e4142e210420b02c402000304031105418a18801d008030b20900d480002d40c5d00c030301c0c4180f00034140b02e58503e01c9000340c441d400500a0000362200750156035050404c0451a040d0410740c00001c5c0c004002044005808100a020407a90001c10049c025900d409444214242056440c0c8100d0348480c1851224045202d0001d4400a0800d020510030b843c0d4a41d88a2075807201c12060202c85008084562600c0f00e91044402048265400300b0000354482c00040c00944203080c000f6040b5500e80204064540403a8070740c80c481e036101001d004120201c4066009071800303489246401c10040c01184d6941009000c40e8031855504034040c410000d160404a00c1501c041c0c43c040d191651080220000355035400748801083c200700c4040801d041001c11203049800c26402810b12030300c4020340190101d2000e040c00826034210340c151000d0786910f0801801103039000001640d038500b01b0f0442103ca00e601104542e00e004882c40c01021981c0010b075242c000e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 890366519 1250 890365269 890365339
    0x2190e0a050109050d02010912050109140c0f150705060702071d130303110c0f031908090706031d01060b07060509070303080406020d020405180906010807080604060b2103040f05 78
    0x17045a000603140415035500c0300c00c000080c0610541084010741014509620905125140950862403e03842e8030001c2c1d41d6075000740a1085034406c1d807500440d8022841410499240762001d2619001c2c24012f042362080007580c41a2002c124030b460040f100d50345c1e100c01280101190502800441250212060280c1050f849070303000e03c203110b5010112200740c00c00c502200c3e1901d0700d84281c66125040720076940e042080032420b2503c1d40c8d01640c2c0c0d1500c1030181d1382c00b4042c51402d0020660040c8441440041003140e9039211b9030002409101e414041c10010041a44030b0f1214500a8142c3e8002000c18072160013011003040041d0b0083c040d070350810351161001d030303c0310615607210009000d154801170703005002c40d0350700c0c41d28100390200b54080d02c2c0703d41c01c0c1c0d41540c1c0c9410700307103582e840c1600c03943d001540060001004036140d03034028000c0c0c0f2401005d56031030560f03541040031246810014a801a01b00003010480745040d03000728001008291050400180305480d0468561070a2620b11145 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 890367769 1250 890366519 890366539
    0x140405060a08070305250e070f02030415050c2103370213360e06040c08100b0d03030f14010f030b0a0e0a03110c0402190e0a05010905 59
    0x50307503840803000140801e80100c904541d621309100b03a4801703070b0034130801940c1d030400100f28a80c61031016400542d0782000d1401451f4035010f000312201840320612004500040c04041154060703003900461818407030707075102e4407200c10440da20708015a2986c046c88440c0f0302034600041c80700b61000e40e40e10141b04400d050025074100c1e4a103082c0340601400f145000380c11246844141440d90142910301e07a08601d500720303192103041c210100400b8210498543e8101000d0300110718500300200711403055090085a505480f803203c40c6400425141102ca001003040700b403243c1c550402c8054041d000f03481041c8010000a400301d100b1040700300000e0109611070b0046a8140996040720900e5924404000b0066035500c54810785103002c3c3c041115800380d01401b1441c041c5541c01041d0703c50704c131040944600003180d90192410b02c0c0903541e0f40340e10300400c1c4140703125649510140060aa0300107550031a00c85289000b40003c0c59031040da4851041c1120131721090b6480b440381415100242d17040c1802c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 890369019 1250 890367769 890367781
    0x3080703090c241103041404150608061309033608010f0c02030708040b0c120a030f0605031911040603210f09030b060405220f0b010807140405 63
    0x90488008082c1981c455054001090b81ca206000c00c59803902200c50905684050300c11548020345040341d00d5154000d00c000c2c000c01003a60664900f8a10060002030707040180c4101a40251156000102083c0342c1010800c1609104100d06d120410b008020005210300c1d5401a0070b541070a000003100030714600181c0c12408541030050302d12a0404880c01101c2da03a80c00107806400d11038142d4901c9030403d200c00184c64000415a00881e07484040d85042c1820820400090b401c90603100f0603d1103155900440b02040200a01d03044031650b602055440d400f0515800380d8000b5403285003e41e01000303c1b14502c0000303410400203e603110858200c1c0000c0c6800080152290360009096200c600500c2d01c900384044500c10300b01c00b4180c0307a1051030344203c0e80a07520340800d448090b00c03400003d40020240d2900d507200c65800b5039480e458030b0303411903940300203c41d8038600c000c00c40d45030081c40c024100b44010701014500400410005160311418079544a000c2101c5819071802180c40e000400e02c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 890370269 1250 890369019 890369021
    0x20304060e1e07060203090a0314030f0a0e03060c040302030a0b0403180b0706050a050c04180617030c070803160b0c070b0705030f070f1710030c0b04031b030b010303080703 76
    0x10041c0400089030400c1d08600020340c140c003600c000364001d0388075140d000110381e40044290b80401030000c00002c4000e1442d00c42803511070a0b8580300034140010485c00d140d4000c1080503007030041560341c64524244a0130140b41c600840581803840d5030300240070410060740c0026945c05101d602c031426041c07684030303441d040d03840c0819900e50300159924800013246c040c0050000e0004240a0102800079444071041c0307000301d880540e0340c460483c1c4100018040d040134a0601c104401e000c40300020300c5580c0e1503080714400390307408100c1003540000a052100201c104105005003410b40c0c00f40d072911100103c11794180040c000b00901154030800041c210384c003004195808250800345000c0240340c12040100168030440300080c40c5400c040226214501c1244490446e1030b40781c541c1c4031103092940e8000c44480c0c00408200c0c0c84080050088001000c480311003000700b001c154580d17201c500f50b01d850742c2080d031340280804081c41200001c00124816190150459805050030030042d01c841001b10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 890371519 1250 890370269 890370281
    0x61b12051305060f0d0f2304050f10020909100e0a0c020106090e0106032001170a1e0c120203090c0105160b01030c06141c020309030c1c09051c0602030406 68
    0x40d900500102d20001c40341e2840005125607004600c003045094142a1514100c47d0024680c0d410b1072a00d0710305200d03004010401e1900a40108101d64001c9010003601389030000c86c02c0c83c0611590041038880d80c504058003500c0d004500003081d0b0404034181000103c01400040808007030075110241305400034000c0d4001809005554014021441c108001c140078103e00d1000b101c0c812412030000c907c005400451000408050b911001341040070b0150603c012405426043d1a0b42d40390612060b109511f204441c00f0340344603201240c0700c092070b440a042c842d180d41500c40400c1c010820824011004516555100d40900340261034030390044001000d03e40900780104184041c2d0004018480200c624404071481da640b220a000b00c403040b840b00a00800140c180c4502c3c0403400a860000150055580b041e01c4000310f90510059281e020f00c0c00c8920456603204071400d228801d14960b0000364480949401e17212002c4d1407140741c685803644c4000c000060242940440401e0810090703811030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 890372769 1250 890371519 890371529
    0x30f1c0507261b0d24050f18060103320103050f0f10110f0706021305060a080403081803210a0c0f2307032c010e0d0f0c060207061b120513 61
    0x8074281c040c0000c41780000f8169000e03217441403280030030001191406401c004060408540901e40a8071120015800340001c528807502c1d803171000e590103034480c0e40d810a0345015242c000c450100ca501d5802d01a040500709801c4500d1030300a81e01c0e0024800000036120300031401034400140049040149a840340544e10030a031035040005040028083e098000d0480d0603102445401490350740d00401102c1d1041d020f210004c00c40540024020a00030080281e2041d24490008416250940e00600f075520000b81d5841880085507100b240000c070020580d400070494608000004120401400d2000b00306d141404011509003120084500c1e9500a982c0e041a2080c83e0380360b15803450060001d048000c44202c071009082c4240e0444600e40000002016060311454078560108052041c0612070300c0302a50b03c00864040780d40014903002001c0014552035004d00502030030000001d005141c454864800c91300d15203c1c10000c254802c40841c03600d01a030401540d554074225002d0900441a880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 890374019 1250 890372769 890372801
    0x509220615060c050d0302070b0114030a020603071206080a05031903020f0d06030618111e030304120209090604170d090f0b0a140405030f1c0507261b0d 67
    0x80061210f80002458804038850800e4410a04100404808902402101030310440508004001d48521711203540d284003005010b88001e030159801050656000740e558000003425a8000140e20300d0750b102d01c402411540c4e01401180d1103680b1116a04d025451603441c51100032812000054000c0c0e04a4411507640d452007920340806544910041c85588000d4178000e081106400503010798100c40e982c06c1d94006100b01c0c8540100c0305010103504110105004480b030750041070203e50b01040940020103091414443d50001881480948030010702800c040d40d0045040c0320006190305911a149490404281e03110855111220040c0c0502c44018240c5c1034144401c00c280041c014506110300400c4000740400e65208280d4040c2c00800c44000d002608280003d1080e0034034080141030300d400002c0c1a51008001c0100c1e80c0443d0360507103524010503054108607a1151803a141d09094a40804095003180b40003404403485100c50001c8214461000480c1d080401c42a40401c6600e064218 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 890375269 1250 890374019 890374061
    0xf0501051315080f031c2a09050a0305060403030c1b030c1112060718030203070506070c180509120a210e010f02030405010608061303080615030403051305092206 71
    0x4000f605c1e603000c089032544810003807180c0e04130001306000d039280568203038104c0301e4260038903136039030400103001e40c24101000001880041c5e195550b0540320055401000641a00d080c186005001c5807508442070007485100ca007111002c044140b03034446081e40500381100000079620348103020b140d00d80720007035100c0c40a03240c07004400c0000a459114095540712180709202c90942c104210030688402581640140801c0c00282809809042c402c1d22078139002c80c40c82e4840e285d11060340540d850150303140d641d41c0204070043c1e02c104000ca0301c4503145c0d41c0300d510306043c401c030040001081c0d000400c006078800700079519103807055124018081400008100d02e590402090010f940251000d0710a0f6080c00c1d004109100082451405401d044804d405440c405940c281c4660b44c00501043d480389a050101c3c800b0f800807002144100c0c0300e0350720341d603803807280e044e00300401320454000301d000d600c00300100700f45904290309003c40391109221100307005034a4a8444041d1000d01440a02c92180e60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 890376519 1250 890375269 890375293
    0x23040f05014406070305090c0303250614040309140a26030a09030302210301060f09030503032d010f090b060d0c02030a02060702010b0a030f050c03070314010f050105131508 76
    0x104400d8082c0006a50a200b29124040d030160386114044001e27600da0030801c04020110010141c84d1248410020b0310301020440f502c528007110054001020340410b0442001b04060f84000540090244106030101c078002c42808075640c0b101c3d81c01880c51180030080d010b54041040c10591800b80301050440795a5481d8041c01410816584011009449580c660404e44440c04460040c42c8500214860541c0c1c6050300407940d00d100300821310180441e0b228040301046040c40151301c1900c403440201d0b040d0180e6520304580c1092401c52456200c1c503c4010b004007490001c186044802b040380c085040460040000c1c3c480c45180444c4078050304c0e00310040c080c9500030025148104498003610600d98907850207900782c6200070400c0c3d5102a0300c003000c0c0000360218080502041c0901c04a03500080c4400c007081c07900b1784642003500e650710003030750024520209004082006030500c0b8240419450107000c200303440085a01281d003941c40344085600003056004810041400c40304941400020b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 890377769 1250 890376519 890376523
    0xe031806120a0b04060806162303070e01091e06080a0605040615021e0c010c08040e0f1005011d0d11030703060b1c0317090723040f050144 61
    0x10300f41c1d281c001c82c10050300196480010528512491200f503c014901c4009030701154402c0720051003503164502500c0d805600170303605015601c03912144d1200a0342d80010380015059040c5030707002e001d00002000e4441c81411402c4044000c64009003401e0700d2a0701d991202d8006001250000c0c0c1c3c205150440014080c14540940b460442041c0c00740e5061f0005608104050320b00ca00d2084410717408203414100d154031a06d07050002e0382c05140f0706420305440f150707048401c0c42c1c26515044240c51b4402400b008144170300001c0024182424607980e6200303010070310120364841e0440e4074464820550301c0c10a00c11607020003034000000400303807894261240380141c01810b50f01c0b40d440c007556141182a8950125580c0628502d4042d00c0313542840d240500b40b041d201100503c581c926000d031103030000342117140c448001f00320b100d070368030711a000301c44403040c841294000d00b0300c00c64040c1002c0c0104008031448602e81d428600703034001404610005d42c00519003001d01040c0715000c0141c19010108a0704c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 890379019 1250 890377769 890377781
    0x1110a03080a061208161b0305060907060801140103021c02070c030c0812030f06120105090307141207030c11060301090207120801030305091c020310020403030906030e031806120a 79
    0x400300d000c02c010380d16004d010654180120009000e420100801d40300300e440400c49525562003000c5000440e18254441200c1d54880e6204940b640e0050b0203000c40d010062000c207014242c946405a13840d0300d4905580c03c000d203420790403030500d9800a0300501c20b00704008a080074504110056507200007070321303164401c18501d20042c2c907144880b90004c0380003500810300e040d1030050301c0e20a07411921881d40d01450281c01a050b01c2e404141c025041c44041001e00400e880344a4500c0655140e0045040c240003c103410b84101c281900103034014100a035418055401d01d07500340c0782000b80d20f500c0349060162141d0303a20340680e101102100000e001d1019800510300c9034070034800390301041290b0405982520b02800020003140080c019a0301605291100c02603d4006c00c40c10503448120b50046424121503280c015481500000e09005042d00b000c0b02c103000304600c2c40d08000810200c10469200e0051020300030b10015030701c440c00c0c0c10b0355401045c7c600d06c809041c408051410000c1054000b048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 890380269 1250 890379019 890379031
    0x10e060105031002041a160b0a1e090203060c1c1a0120120c010603150c0f0c0b04031412150f1507061112160306140102031801110a0308 60
    0x45401d14a0902c0040e40c0252170490b41011400d589040303071081a0380e00c41d000410540458a503a090382c101040b50b080d0058003448074401c0010340e000040d0b07020a944e0380101740604200382800103004c010f80b0001205548250404615500d481441141c0800041c5030302000b05170381d0a016040d40c100c60000c5032000240000d0f200c4010310320540d41c00383c40d10218501c100d0303c4c64000c038400600100204006014000d550000064007680f2076880090081c1442c03d16400141d5504c820315010707070481c06200f10101281490183c40005030303100782c612130b8001c03c002c0070000e0ba41c03c0045a40451810b54043d0020242c04080c20f2420115020001d24094a8207208508500307103c099400e0407003070069010075181d00d4500e0041607455140c0500b400503007901400350204141c00024080a0503d4014088001420040b0010010080540750f83d604030381c0707200c08507200e1608581e80020464030704600304180b080c03002c0038000050b01d101112007603840c014029075514604040c0d1040e1643d20640c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 890381519 1250 890380269 890380273
    0x6040b09101b0309030203131409010509011a0c011401140a06050a020a0305130801020703112122050a0f06020f06070e011101020708040b04080c100f030c0908010e06010503 76
    0x1101840005465428510400390240201c0b410145442034010300c5006000c0d0044074a032000e440d04140b4866050762146020325030422682c055840d1100003240106000c83e22549254103100307080c6050142e09005007030301440018030030310ba200290411020110b403c0c05403821503a580e41030003250303081d204480e131042c000d10b01c01080050044080e03649007072066009200814007030707134103641940c08644a03c0c0c00a01c40240040c4080e0240020180188a560365400b90120b94500616001d1140503540d10a1000c1192070025185c0d102556000c0c18400a501c00b40c0d0103007021310030f207003100d034104c1904641a000e0101780044125224404c507000c0d41c1c00c607000841d41044583d221042583d00303130005250540000050b40c0f00e120094041c40e00c0e040014501030141d92040c449501a0b80842186034020078100249282031000558000741626202d07025010050020420004401203200307159480e00c001380031510811070900500000e84c02001100140084aa0358003002d218082c4a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 890382769 1250 890381519 890381533
    0x305070c1e0c36060b0906030a090c060305061009030b0105010507051c020a1e0f061a0312120c04080714010c2a050a08070e090f06040b09 61
    0x691140340345024054204900c80d110310380c1280080c9044105240941d4204000700012407140c00010000508414086070403084035403548401d48030f080e4421603012498034062040000403501300466010f91001c17030380d50369030ba40d40201e004001d148000000e00a00035003103012a24070b4041c3c3c0010300540b0200d807024894010120211800c51003800001d02044488004010340d5001c1c0020344030142c410750070395100d45d03174078003405141131001c0c0043c20040c2d015900d401c040c4800311400c452400080e4600210303140c619100d00c0f1025040310002040e1580c0c98680c10300040000d035a40c1844540103040e03d00303000c41c904581800343c00182d180d4038444840340119200c40780b11812642113940441c0030b01403c070700d000c80f2034801102c60080c0c58148007251014000141603000703909900c48280c0c0b10100585411030482c5286030b140d401080c02616452810701881d0000035030030044032380a80301d80ea4680c2d1500c100d0f9083c00721001d6450000d100e102d00740010004425001486042d800301250b0700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 890384019 1250 890382769 890382781
    0x3090204061a070b180a0804091b050702102705041104120323040b1803010c050409050c120906010311182d0a0e010501051801060507030e0603070504060305 69
    0x812100d082e80c0316100700c08000d40303c0000d030030000840d40300c0fa00c504103901d400891030f61541803048148080b0b032948000582842403018a11400001e58035040f01c5002e107441d0311201408500c144440644078030078401845120b0352080c4901c003265070800c0c2d03e080c0754a19100d02200301c1e44460103040d08c00c904006441c00d400e80f04005840441e03060410600c40407004e500e00b034a00f108800041c10034050b003070100004102c0b802c030040005103518080342d55540c1d881c1800c00d0f05002c00388a5184a40d051100080b001d547c440203403170648038211000242c985807404130240a02c15000245405203203c010080142c8003c101241264040c200e0b41260040c0e0b03000f0800401003054206140240c080301140110755031948100e044000e104407060091481140415485401c86080d02074545400c558400480b0071b0241030b0040405945920401500344512560b407101400351310f003049008201d580a162288900041d6000007403c40e580d241010640141540d229000d81070210b410b04e404204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 890385269 1250 890384019 890384039
    0x17010e01020417070e0444070b07180614190c0507290c1e1c05190503070207030f0c0e071d1203091e1009060906080a0905010c0309020406 61
    0x1108640c01f0400c0c04d001c0342c90003884100c0c010341c4a0001251040c1c07900a410321071400c0307601c90608405042c459202c1c9041c0c038103020078040c01401c05040024031805600c59400d031034202016105507013031440503200f03501c0c40c1100c0e81c09621035041101c0320740d02001c414650010135490b9414054015684110388445004030b41c101443c1d040820610088580124000350300301400b804008841901d440031070303032009201d401080c880742c0751480d00311203030032010403940b0860740c0ca59902c50f0408904202c01360810038044400414a03406004000000030790b980d109100d12005142c0c0b008800c2501000c074106000c8007910b40c058114515050303800700d1011405544840410706441d60036001741c2d4151014880914840ca44905c40d0380300621400f6451782d41c940b00340d611034008074580d0b4445100b4004004813550034107008000c2c040402424130241d13600c02c01070000d540c0641040400b41d21021408801040b551201408035460f00c2100d100071a0b0503002806014002c1b1400d03c81c0781e0b102d0304410b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 890386519 1250 890385269 890385271
    0x1805070f0f0b0a0e0405070e19211406010603090b0105060301290f1b01061203050a030e0a020402030c0d0506040c1205040609020307080601060f05070c17010e01020417070e 76
    0x290030070075200c81084000d8480b002024035000500c0e0803c02041c8840c0400c050f40d600350356441c00304d9208070404096040c81c0d03002d500c44008907040610040d2504400c42c9540d42d90404149540c0050005002484001108203107100b4150080742d50541c3d40700d0340100108200e0404940e550804c0c800040d80f840d00c0300a40b41030b0f45008200c8003c076a5400c114036140c1c558403c070038446000c01e004c1d00e0748030341006020700080c00003070800c03440740750702502494212a42e81e0480c0c1d100c0301c0880350804c0401e600c0829245200b0080c2400206403c0d03c0035024a086071000b0003d500c1800041003040c1d00310f0501c054022203511000034012502d074a03042209036004a0403c44c0007955010011203041142d8000642180c02840e00007100385803a0046810001c40d03811241c004c0e03110000401c0000d034441d0410503904200d01d04035051010701d039681c401002040c860148510017260f46408100800e41c00280f00d0040300c3c0085640f156a140705010800502c1d0080310386014005000400300d103800340072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 890387769 1250 890386519 890386529
    0xc0408071e060e01090b0d110c0c040e0318060307030902031e0c0306240a051c0201080c031b0d0216030207051201091502031b0301060203040e15030a020f010201020d1805070f 77
    0x54517441d0400c8013000d034076081008107091a0b5100c00030f80021102950081285000000261014260310710600042e6803200b0203a83c3c5541c420025003071001958107450448100841d91135641c0d856844085028081918001e5418024281e1141c080c0040d1047d00000400d404190b90044151004143d19010100c5a5441070f1041d030700700e01c15070f0a02d402511442503000b42418050390f00d0f0300200344280b01c80e5445240b8403280309861010f641e0000c807843c0d84400d03034184c01e61845c038011800b0b89800040b4501551074074004510400300109580540d00c0352030000000d00040162420001c0d921011441028003070031002d050741407070200600070644000e421060b121503801507480d2090080d80024500800c20200d40c80c560f00000c030500045008104950040d61140e0610050b80c48042000e030034144100840d080b488090746001c196640c40c00d40448905483c00c541c000142c0c06441058204074107246000760002c858050302c03410205690098040310b03456901c991000542800f54010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 890389019 1250 890387769 890387777
    0x50a0501090605010c351c050606130302010f031d061b160b070c0804061806090810050403052a1209010207030803100b0a0e04110301060c0b0c0408071e060e01 70
    0xf8106c5013042d82a00c0706a540e81c041c8074034103401c050180340c00d41262406c4a900c941000c4200b6200403030b40201c680108041340c200f89804040407a058070300301240310082c140180391003c0825503000c0e510200000084001d103070018800d80c8011500d0715030483d030007136520282c5000f80581401c810305680d920ba04244502601c200c280c0c5a000348040000c103c4401c00c542c0c205a40009034450b0090300c01007669407581581a46100e0b0820f801074065004502041740c0764908003c0d0a03000912006511900c030b40001e01da441e0b0341000c0f507061149000b8107107440208100929040170724100601c50805031000e94040c030101d01c5541d0142c1c1f091044c601c2c0141e00102050002c9004c850007990001c4110303a8641c100b41c0d6039004400c0f0303074215a801c0300102e0340c0c0740e82d0031405007050f00070000441805800380d0320f5503046c0003000d071080c410080050305041f030010000c0c004640382d41c1181c014103060350450306041d42c0d85800d241c00781d1000c250f0042c048100300001405901814013121000c4050315 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 890390269 1250 890389019 890389043
    0x280e0616090314032a0607051c020313060e03090301050a050411100315090c0e0901030506011a12090303011a090a060f0c0204050f0a0606090e0604021606050a0501090605010c 77
    0x283d20444000d030700c90380009404200b03c0c550440003200070b509011220b0131140c000c0c845e0140042400e10400034a8001480350400075405007100b0302d80340f642c074018000c0005880791540079100b211b4550300d8100901d030500e40040c5207000d24000018003d10300003240244101c0d0783d460340b5142030f91020340c0c00038501000300c040300743d80b071802c00b0040708210701c030b40790004450503100d030b031b282c1251403035800030403403036501e00e080040d490388401c0112040340140ea030710751154510303580c09594500c144901d0ba8000640480729506890308800c64041000040080d019410b00556082d180d92003031164043d00441e1403070240d0040180004d44010900080c40c0000c058030703050307050381d03050b2000c040c0d9000c010140c100400140d98034400c03180a0780d16443c01948900d08604d40104480c1660450810b1012541c410808100214002c6901010568026803180c40c805c0c03005000f4801c4600041803d030038502003150046660703220324100e0300c45080070f02c1010f070380e2001910f02a080c030300c0260088060310 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 890391519 1250 890390269 890390273
    0x9070902180f0612150405010602160603110f030406020c0c1503040201031515020106051c2d0c121209051e0f1305060f0a0617280e06160903 62
    0x1903001002c82c5030107803400e8a0300c40031035851508440100d58a8026201c24003444495007000c0c41810302402d054001803200004400d860f03208030030b051088508042e111101d001122210200f90307081b413149450b903c3d4480c1082d2034880c020b074024100c92005445103850030b882c2ea1034525807801c2c0001c0a400c056203140c032a6001100a401d400944024580c114040041da82074402c850004003030055000003002d1741000e00304079594a41d0b03403d030402c21103000c0300400420852505182e01c11092402d0021034100d4508890703060051000280403d902548000307001c5140078030218200d80b2a103480b540e611a12502561b00b610035008850300b00032149034110214414500c3c407040f941000306041c04c0c038100200002e0035596610b06141110383c0f80da007400143d050075501e21981340c0007151002c00160030203100600304002030144000fa10340c1000403418810f1000c210f1b524241400000c111082045640440a0094907140c0c40180c812180001c00038940302100c01103000c0c0f26031341c10100d64555 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 890392769 1250 890391519 890391529
    0xb0f070e03150f06030a080757050a0605180306010e0f0f010b040e100b190306050303120f22081c0b030303150102330f0c030f2d0907090218 62
    0x4100c03508142c0b066820192740048400d41900c0103a80c0d0000306c101c00f100380e22111260346400c1d40c0300301c2560300309030400d204903920523414900717984480c0390a5031100c0c1d0380340b42280d000b0780c800200c80c4c0500401c8004210110444c0da040c2c45202d5655000c089911030740001c40300031310248034074082c403502400140024100c81074015000481d042415900f00c0d02d40032000301c10b900040303520346903407500030349964410707054000d41e802403600320301460070003050060085007110020401402030000f00c00080020504640d810300420412090750f2070241c0c0b0385000d403000d074042150760703011070b07030090031064903481034012244501d001402840c119260008004004141d03800518150300427501c082e06e2881500011300c04a24041059041880c4000c1110407404009003e0880003914801082103060841d01180d801510004c07802ca42e50f40d8002d091544042281c6007401d10301500312582203042141203400f40240201c0301940e51b0180c0e40c2c9041e81c200c2c46062008103400f0070164000c181c030b14007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 890394019 1250 890392769 890392793
    0x15040f1d04140a05010501080304080c03070e15060d0213031505071403090a140304170a05060c031008031908090f06040213110f0d1104030b0f070e03150f06030a0807 73
    0x41d402c6665421a950700d085c2520403d81003c0c41c1984017040c2003048000802528007074441c2900074041c201c0c2400c800c03071020040146100404299a944480641c542008841500c00316200854880b10100048447c000141c84151440f5400c4101c4200382955480341074054665615185a00d41c030841600c2e1076500010034890060264500650102e03038000f122035803a0040201a607a5603050900301d01c04d104140b2400940d562201d100c00380019400140160840284844940c8039540c0c0c0404120191007500141200c3c0004205803042c44044c40300a00c00000544034281290b480003681079689540692204095101c0c401003405420075000d045031603040001c02094121b00c0c4c800802061703000241c2580d4156000421041041c4148580513820703180552003440c151a5031a143c00c0007001a1036050004103150200d500b00f030003a0502448040054150341c07041855503d503070007203101105d500703220550010003c1e00070704d000300d20086021b500042c1107003000000d442d12006061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 890395269 1250 890394019 890394053
    0x1080705060325051c1d01020705031c0b0d060212151318140706090e0601051b0709110c070b2107020a02031509010b011d040b0f15040f1d04 62
    0xc01c0090030581712010842035101d840d1076002148007030141701c0c0b0807800f4200c0410308480b40d1041c400407002420100c210388580000d403c4001e000c0480b40c0b22440113090340d54046034401c81e000400e004010154028005040d4429004a00e654032002106003d000c20400c1c2d03640101c0c100030f403040c12850342c0c0c0058107c17101220301c80681e9015507116030360610201c0c0900c440da80b00d14001c104007a0302091041c013501044560780454100752002a2060081d50070480218881c2064510f414804000c2c990040c60520410700c503041920342141307459440606801006d004500000c59844000d000300c400d0702c50722042d2400d560306911120b05a59401030701c0d100841c0118550704015a07420046046800024425102c05081000d612805c485080c1a0f6506000003600180050600c0c140d424012920a44e004550032070a2000030310403c0c80185d02e50344c0305014140d42d1480c8900701d4040c0044d9980011100217058a402071001840c8000c0c0c50078400341070700d000180010b4030514504903125 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 890396519 1250 890395269 890395277
    0x30915090303090203030408060115020d0c0f240b0f03010614010e27070e0103091203052e0e0f0c030a11040503010c0201200405031005060f0d060501080705060325 72
    0xa402d584c0000d04640c0540c0c001d0013135030303c40780040c0054040207500501c4024140001d01d1505048d00010384041205a00502581d080c881004288084502884666511102e80c260303141108420403004041d102003c07401200340e518030510307505051003810140e81c080c00c0900344004844004540210114506903000080a85d141a4442080c0e0038451020304071041c0b680a0300c4c2465004140da81100722060405007000412008900d061485c00c10454840c540032555548a21640d1410081960ba506645144c0c411440310020380080d14001ea8618040f0305059840d0558146100042982c0b20030021a040001c43c4030b944242e44801c44491983c0030781410643e5641c0002c1c02c65514603891009170b51103c1c01d0b00128159080140e984a2030381140604090070000826070b40c8030701c034910700316880d42d03400492025030300c1162454100c0c0b0001d00d1000b01c00154076210020700020311514180b4840d4030b41c04605071504d001602d120f50100305600c007a18060707550520020180c0340c4000184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 890397769 1250 890396519 890396531
    0xd0201230a020f0a0c020f060414090c0c1e060a0e190c0506031f060906020307140c10090f15050f16020604080c1f051905090628030915090303 63
    0xca50032001500241300261280c6a1007005401403041c0c02d001110305510071003081200303101c0d00064071800c90009100b03407846a869959482654043d10409814050500c07802c6103007000e1201404541c0311141001c8140c03001c0e03468000c03102c0103a03000403210015035000440351041032410036611030100ea01030041d42c00410390350300c082000d42d4810345030001d04441c03a110b003000d040d21145502c8010850f51a010410350710300384000351603010f48400101265442c41100507401c038100038003880b24100070101d00d10003c9460014110800900c210841542c1d80c2600042481030003483c450807000603180c1d2450906c0c04480030070385600c54030b00843c42c2400c51030a0005038071540c0280014101c50402807070020f1032003041080310500c41030a490700b6035402c1129901298840309580082428101041c0d181c500d0f00400e440ca03020f80d0201c15005640482c13020450304181900c1e882c1003c040c041542100c0da0381108030244c400300c0c40003a10380300800d944070380c204410f6803000301a280645800191 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 890399019 1250 890397769 890397787
    0x4090f02280915120b1002060a02070c0305010507171303200f0105010326040f14030a050604050a06060b130e19090c030b011706130f06090f03020d0201230a02 70
    0x40070390303d1070100000070006041d18410740300e2803003001c20010003120300800c01c1c0340c4100002d68801006001c1000385030007245100401c1003c0600a0265a103c8003c1c40149040c41c8000c04031150354001032070801da580c0200380d0705ea134940011081d05070155a002004200c400b1401c0b0000c1c40c0746100c801900c81c145d42403c6602003881914081c5205071941a504444201c040d031070900c810348103041d40d0004100c200aa030485403076040840c0c0b6103581d0820003003074400c0084d0404080d207602070441c2c0030781000c0108010001c2118181d080c8140e400304003441c0ca5408480c1356018066803000044105081400041c440580a503400b40383c00e0300035200d10781e010701d00c1c0040d1401041c3c2203c0e6161250400d10401088418550160510720610081c0074440c0e0009079650401500303802035155030038060742c14811280801030880e6000300040c03085403414504100c001c080344400741d00501a01e031480e501f0746e1041c040c03481542e1001c0410310418503070442002124030060840c2e1020340d030030004500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 890400269 1250 890399019 890399039
    0x40c03060c080a0f0e07050d03090b0a0801030209070801050d02010e032112091614060d380d0308090c2806021906021804020c0304090f022809 63
    0x79a1555181c451500b0401400c1c03003910004074182500905200480c401607000080880403140c0845900190302451f00b4103903001d4055402c6000c1c420782c0000c040101c16000190503048a1003a41c4c020200e540b0341d401107032074480a01580c0d41c0700c14500140301c059842400c1602d00c503600117050740c9440213641184541107110914148e001c0402180c0c45101c441c5511045030700a4103000a8500c9650080c55203031580e1607805408516072040035062500d40f0742205540e181da000f44000c010859210819101000e9512460500d200301c410b03052500c1803045501e4010b000024102200f190f8940c0c0e4160bc9480004154000b6885903003c581015030b0b50002c64951087c40c501401c003c400300080060500e01071f500b1840942d449000c030084128a44191001e1a5403c00c10068a4041c0c500305045022451900c05038032500200d266004158040020021540c120108201c090810320031001607018054410a0040486d0f6005660711030b07205240f03821044d1880c00b0f4070030300e0301c40074018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 890401519 1250 890400269 890400281
    0x6080a0203041a180c0a03050a02090405070504020a091712190c080313030810030b180f010609060f050a08030706020306060f030906071b121206050904060203040c0b0309030909040c0306 82
    0x70506400602501032111001c1c0543c04002030150b1b210b80e80c2c10705648800e40c0d036050229009005104440008041c00340600c03040004e824010000d650b1a800500010540c5006001e0300c4070544214820203101e2200081d000da1524026880508001400000040300080465070206001115006900103040d490046200e104010108120307045607090040003210003e0a583e28841400024408178000d02505944070400040da0440e0680b507020260401c4050122035440f50309001001c03c0680298018005807a040b500503e0801c0d900e000304480d5180030f02c10103400d90020014000802c4585c0c004540c080701c0509458600b40090001031450f0f4011a541340003034001c0e405010070a503004200d01641544003000c040e0070720668a580c24a140088064414405100ca21507403408142e000a001800024040c5405d841c181c00c0c81d80181d4404c1f642101e08c0b40580802082d0304004c10262030141400030000c604101c40321082c07103c2088042c000359051140d00b1000030004210740911 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 890402769 1250 890401519 890401531
    0x190603050a0f060e0d02120901031d07060e0103021305060d18060c02010501090902060a0c020f0a0e090c0109031a0604111603030e0303060d11060d0c02030307110706080a0203041a 79
    0x42042a504100c03046422510006a060b0400c01701122015800030710951603000d51050280d8440407040160300071708034403906800400184210a0f00d654000c16000112002d503143c5400e94080300c40110100e10690507500004040408280040e052200280000642d068000251000d0748a441602107a03162401c0781d01c50b4903126050b146650a01a907401441c100e5800d00005801da4005441130050729030706010000f208a000043d541d070112512160300001c7c1001c88407032703110384c0c0e08604440100c0d610203443c4203148011140d54401d2001d0412aa00f0685402c00c1c4010340e010381d11800d50180000e82d21603200d840d01d80040680c40b00130f08245084660408690680d0724000c1e00352340c2c1a00c40c20a5940050040007050344445003503c1d2700d10f40c0640d40034030b40741038100090054041c051090046a103000340902220350000b008500400d0070b901c0710102d285c00301e514560780f1001801400006001003010801003909900919041403080100d003050041104800f00745030401c0b90a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 890404019 1250 890402769 890402783
    0x60503030c0f0d0801060804020f131b14070b0f1003020a0f081509060703020f0d02070f1b030c1a0d32090703030f090909050c040509060f190603050a 66
    0x5002120b4001c1205031034049007414007228940c90804060500c081c010400381c0681e840f10001c421075601e03441103003000ca19441003000340040744110354010100d40706032500820701c400c4101080c80004400e0360035241e030107050070000d990303000f206c007018603000703050940159041c41000c0300690341c1d200101c1c054203104584808140c81e22a40300c3c58066441c55002c40c3d04040b07400d20600e000c0c0420f00b90b0b40203005042c0541d4035030005a01807414840c00d00402c4440744003107040e4041005a4480c0c40c40e0300c0c0241c071041c00c40c01685140b603140701c10038031008258900c3c6080400c850591220a10030000340a8000c60606001040600c15141c1204c3d181c0301c00d1190084e01d81d055a0416a040d0755000300101c101c1c040d00d013040206035113052034000541884069444a18914440d52110000d008032035814801064140381590b81c1d0f100140916105070308080010b241c000c40020000e10402c4e090071005507036100c00604040c0542440104158243c0f5083c012002c00c9003000710350015446440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 890405269 1250 890404019 890404033
    0x30e2209060506010305072c0a030609050c100c1704090e100606110a06150815010302010e0d0f121e022505012a06050106030506010315050102030703050d060503030c 73
    0x64480704072480148450705162403c0140100d01c1e500c103901c84000f200c02d4044824811100d01013451211034941c0d10740c1c0c8071610080110400410382c203d5a02244505e040b1100071118030100042c180b040403481d030000d02201c1045000c01c2c0705541ca00e030400716481e142494181c944003003005a40400c1441e00140d03210043c2c0c0f80d01b8040361303c035500003001d8510301101d03e03150106c0c5e403607250003803404054106034617900c5a02481020424100080000c20200c03124040701c11520420035900744000c0c5d010404491103880d1038184113600d841c1042c0d02c091502c0400c2d880303541c1c04400600101e02002048040c0744030400d285550100c1480000a607001000b021440c180b07221070000a45945003555001e5070001c00860b6001880c4564248000c441c0c20307a0030002290000015800c100d026007000d042c100001103858040c5c0c0554060303a000c1c0c0e42401800c400c55a0614104010702c03440340141c0c020041440860312030030250008001005002c2001070f0740e400000d185801002c0700c4100c0b900000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 890406519 1250 890405269 890405273
    0x1804050c2403092b0305010b09090103080d0905030a02010902033c030d050103060f180507051314040305214303061703090d030e2209 59
    0x4582110088200d90540e200c021034110780911600034409500148000301c0841d03102803050241c80d14042d001c0040200100b1410ba00b0004030f40905400c0340400d10344000030407264105011034000101c040d0842ca01640303140e03035601541d8402000300151654900e240f030700082c4180020721242d9120ba00100740341900c0e004250a199a0441011446075101c400441040b0b10341f529210b21421419505181c00300d604000e815803140aa0143c130013460302001004200c8503a0003160614101c400800109020b40200c81040c0c5080d20080c201d40e002490820103841c018014640b000000710307000c600e20041d8140381806200c00d6900310701142c0b000c2070180d207900c3c1120b10746582139070809011003e400c01041100b10006901400075203102039040381220a80c9800c00904523051403018030144000c1d10000800401c1180034500c1000030010110705003540000584204100040c021148801603a40948001240406090304140c080c1003844090070940042801c00507220f40204141d902c40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 890407769 1250 890406519 890406523
    0x51e031308031312050a0b1321030c0e130203061503180d0207031e03170709050a080a0b13060b03060103061a090c030402010c0311010c0201090524190b180405 70
    0x5812134410008900c0d264404140c0c00541d1084864200c841e46507540c803400000780c1550910700c0d003c0d12076046800402501000c0040c0145102c0450b0f600b000517070782200003260035140d46985254440900035096410b60784c0c170f40c015a00001e00030403009000181c003e070010f090f0800c541c500c00c00d81a88002c41300d070003c02d0001740000181c1e440502561420b40d503401100ea880c0600742400501800650020140107001520300c1c01d01c500c2010700240342102c4010440c18243c025540204840080012001c000041000d03500b40d2002e9034903200d944111034505031941080c02074030055196580748032503880a10400b40030714060003000c65003048600d03581984240f08954103006081840421403000740f41015a80c0065091a0440c2280b285003401c41c2d105044000c1800380354a400600c0142c40e80544c0324400e064810410740701104240d0f02d980303c5004044100314214000c0800041c00e10301860840541002e22010015529504102041158000c0c26003014442d1880045c00244502 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 890409019 1250 890407769 890407807
    0x31701080a240e0705030c0604031e020607020409050c030d2f0c181e01050a03062f070302060903120103080d020c011418010b0303090607060b090708100e0103051e03130803 76
    0x1f081d51407900c0d05145a4a610b07800350741d280a244004808428801155607050846a40344d0b0000c009022054140c01c0c41501c074134030181c03014440d00c034240d0442d42c01402400748155015294900c0304150703100d140c8251000603800c000d5601f0340601040c440302c568404045610088083c25000914604015210700c40010303038040c100c070f40113540d004119907610402c500c42078a5001d500403410689240c3d5180300347e81105c8407400a003c440d03040125100c40c1d074001d40b0790207010740e0031907a03251111100180c8030b00c40d0304528441e9400c2c44c0c0050011903850801004200085440185824080d015003401c440c406460b002170400b9000c00e20591200f2801c40580b8102188002c0081100e640d0001b650303403248400d0207005038004600501070207042c0d8002c41d004040988040308034a0225401044d10600300c2d0049030380b811511000c98208010b90703400741030ba070740300000300760300300c8400c507400346422282200707002d144410003040c0602c15400b06443d0017054000300450b19003001c012050041c0d49 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 890410269 1250 890409019 890409043
    0xb010c05070b1314130b0103090501052802040311010c021201060f150206161409060d0b01090611030904020717160b010602031c05062b031701080a240e070503 70
    0x20030113107200c88540e1040005040200305910010b6114030050059025064000c4007400340e529050400c018a480e00702642c0720b11000001c4c03014001800a0030800302c4c011400040c0c080011061200d8565000b0422180c0540c0010246060041066003041c2910605d0f0040e109016008908200303004480800040b0383d2218006001d0138a8000e000041c0304030344600110400c42d820880c00364210203a0300b1605103230000340c12141d0b20002030452002406070240740e140082c15010000031a140b00b030040c90000046c00014625044103602080040e40141c4e4064582092018141003403515480050048030a09410a034000c100d0341040c0c222070f48140c1c00340e070564208203c0840c4021628100006a41489100080030380f0381c0c0c80451540d0007802d2402041e4200726039805070121413600650503180c480c0d940d5001c0365001d600840c401450070700c1182a55801016407500180c0340c0c2e0480d4401c0256501d034890000d20607001030341521030940e43d001140e0095003092006041c148010200c0300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 890411519 1250 890410269 890410289
    0x30912011e0603050c15040f1e1e0605072d0302102711030304060c060c020d120207060902030706051314010203071202030708030f0712090203100b010c05070b13 71
    0x1610b1504e0342503e030460034414074410b20030303070401c1114181c007581540c02a09140482500e0151107007980300003112049035440c2a907165480001d00c0240c000c00e0820f5040c00d0310031144003940b07000d0003034905811500e012106001100c120010315010544d4070407114030308103203501540c189414041d050480f00b6000340c07081410f00c903a01c0d40803091241d10144203c01c1e103a0300000c040580c1458602600040c280c039625003c000f80015100368404500080640642d908100c1c8125148040c0e81d10074011a65401040200d01d4000c0309003040c0c0c2c042c20030070b03014603000700d2101c815500080c180410b542215000c55004600542a45041c40c4410003600c514080000394125a10000c1c2d602d000700034005100c1d10385440c40c050494405d0003552a0300c2e500411103500e0b03043c00c4440c0c03501c903c001c0390100c0000c2c1100d002e4040400746400b40c100c040d50090040e002d00d80d0703070072085009064562915414041000f8200c80003d41c2009507800030304242c1c0c6400e45915040c03410803070340d40c403503401240d240c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 890412769 1250 890411519 890411531
    0x6010207050a0b1605011814010903120207020310110a0201140405060402060c03040e0406020a030b040b090f090c0d0b010501020c0d03050a03020a09081902010e01170105040b03030912011e 83
    0xa4546207108030603aa0a01203c94846518208000c000300c601c200c010400d5081240500c4625484901404082e22603101d031162048004a6142207032145000540002c64040540d446403441e98003d20300280058155114a905d503800a01078032641991310800079000200010700560a02c2901800380704070074110f0b1036061688400d607507954040d0020303200380c500095201c1c41500c100301311001414007034549a00c034a8642402c10080d08101c5104002c42c0c1001070005d060319061003445a6070000401c046c1c8c068907600c400030301e0301c0380003040c1c00041d224004104ea419505c015822a61910a0b43c0100350340d03042100090030329003c0c840707850103243c0ca220b4000020360000c0c15159805010b107001a00e4054070b4804407402080c6502807002c078013481d610b0481d04000e4107074400c80517000382c840100c0c05049600440706850707490b03004c0840c180c0c5075005200b01d1900e9046030f0329042000b800c80e418020402c000440100c8100f00980c1269550320141040c00c50307001403c2003d60785104108a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 890414019 1250 890412769 890412779
    0x903012313030c1103151608070f050a120b03030720030a0b0718051c141c1206270f0b0d060504210e0f030a030c03051803030a03020304020906010207 66
    0xf41c4191208020001101d0070001d400588003040b00d00707011007109500f10b200e418007401c1c440503165146640300028002c8800500f002d0701a0482d1001d0300210381d115860540607a038115914201000164041919a1806076003980c04002420302103008480281001813101814140d85041421850090b0407129207440070540074450103074418040e04015460549a800940021400e41c10142d03000304900da0891b186130048011100042c0306042201089040354001507840c1c02200c02c0002005d901100300403014420083c00346034070a10300340403650a1b1204050303003420302c6050140081c06010302c410240038155001701c02c0c1c40340b51107004002540f084804220302c00344105000e00480d4490740424204045504110180c501c9610030f5062010364031801000a4048240b051103091400399890441c5000f0500f55445a80f58403031214910503940d094840d03400205880d141d035038040080c0c04040d1424001040f615549030b0780141e40b071415204000c811040540203a045500508003448 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 890415269 1250 890414019 890414027
    0x80d03020a111501230d080c011d0c060d0e06010b1e03040b0112020f0301110c070824070c050a080d0f0e0601050618180f060102060705030705030c090301231303 71
    0x41920708410117004c0348078004540b22a0306026900c840c0e00060018845018080c264010348048407082009005118407681d5407030485510754440001170b0030500b81d248032854450028482035a43d00c001051100d44500702c2810f140090344400d80a000000300d0044002c00207075403440480446983d00d0441c1415200c0e04403d80c1d0501984c2403001c1040a141d0955480004040742a40d00a00911484005034540c14a41d0060001c0a005106880001c50032050110304145145c9910803205091110500000d500714006000c900c14460003403011004a40b041c00036040081c007c8140940d41c080c0c0032400d008a440c96110000c00c0f41c0392441c0c07000c94403808130300c243c1182c0c0115103541c1c0700d0440b08404203540d850540744c90b92000c0744e030606004144000905c00d10030703600844040ca0b03a69031007005988802c81103903e180002c0c82000006c0e100c2c1d01403400307150000d00c0034070181d09090f0001d0200f0300715101c00d03010203562840107480c4e0320340752083c8100e0f5900c02d0080d0382c1c11b4610b00d80740d98003034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 890416519 1250 890415269 890415271
    0x10c08070203040501030b01091e03200108060d03111c230a030f060b071103060106050a0f081f1805090d090308030402061303210c03080c090406080d03020a1115 71
    0x113170415496001580a580c0320301103200c0505101c06081c4040500307491030303c01d4440c0d81d01c030890703c01309d4810360360a07040100391513165800d0041e19000b4582d681d02040000f0340740094811014040c030146080c200500c1000085503040720003400001d90000321502a200e9050b41c0b808038182e0030042c1034003044802e10000d0b0fa4201003a030402081c142000c2007024040c00c5540c200c080d03180000301e10a014405508408001240f0540a5800990300d400c0b040b00c0f6442614554408207481e002296a2940b00c0d80b000c95221a10315118007898400550007802c4144035803040c0c0715140c020b10401007002c11481255080b807081c0340140030307001c0542c0c0c0282006c3d48510000d0704884c00840058250340700c01089800e21140c0ba0091540b00b5180e20b0005d100c40044001481c4080c2107805061645000e1200820341e99055214003000303030f4031030328081825800b6042d01a0044d0700d602c80042c0850302000b0701e2091b20800d0310090789178100d90310b00400c00b0482e004030001aa1001c60140c14860300d01500b1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 890417769 1250 890416519 890416529
    0x14070e19050403030e16062726030a17060306041211030d0c0801030302071d1605070210030e10270804030b01060c020a05090601021e0106030605040b010602010c0807020304 76
    0x1181c1e550391410250014500d0f40d03290301c003e0280380c1c4403d000100c510481416a105078481c51001040c004503042006085a4101d0743c40601d603409000400002035a81c611603d042c0e0a0340082d560071004074115044214100003180c01540b828103034008282c2443e80c440410341c0188503074074158548a040358030607080e601c280000c00026500d16807080c011540c1da240c6000b4180070b01580b58000801d040c100344015070050040100100da404440c004a01104032446d5908502c0d8031004c00c002000f62026100d4030a100d4104a140010b0b1120f042211928403191400205003243c0b110382030802204d085080d01d083d00c0d0000300c1c87c904061801102c0001c0b00b1280307000180c01e042c580101c00340b0443d00090300d002c1c40a4000a441540802500140c910a440c00100182e40700180030300ba080549070035000d60404101c1e52021400361800d6003071041100c00100b80300d41e9940b41c030000c0b60026241074070b101c00c10500502105070240100c00c0c48001618081c03840c0e140c0b00000075140d010368011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 890419019 1250 890417769 890417771
    0xa090509010b09010c12031103090d1b030c030e0406030b0405060f0a11040e040f05060a020301050a15022e0c0e09060102060601141e04080d0f0e0f0d050708070314070e19 75
    0x1b001c100134440c2d4800c1c04a12000c05207551760f418039000d0700e80d8032440ca01c20200090400b00f80301c0002c0e840940181d03400ca506403900d4110300c4040e50184c0f000f0500c1c4503400e41160395030f0303000400710f02c4600303065002e00c2c00b03440036013000d0070075651322804488000c3c070f040882030070a1011403007010382104503002c1fa0300085120000d0345892508003065080b840d03001e021031040009000c0c0e00383e07069000f1070403904119581038202d6550030b0404c1d0241004c40d04180940c200010f80d04640c1c89003032410b54074180c41c1e00c03140420324058542408988001480c2c1002a111007903411041c28140c11081d00302109000406007854014002028024004400980301c50049203180e42c40320a0f6500e50351030142030000e40c1c0c5031500c9000c07003651000b504142c4000500c007410320640c003034020385036040701100280c040401d42d043e24051003203ca0310481c04036407910503503000117242901070281d480654828030084401a010458092070722102c0c0c1c01405d0803829000522100e104c160f04003c03124401110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 890420269 1250 890419019 890419043
    0x110d2001021207081312080a023310090e0706080f27121206240f0a0509102007060c0f020d0614061306080604031803080a090509010b09010c 62
    0x204554500907150702c540042404011b40108014841b0050000002254203c80000c841e0580c080429880d0701d052400d480507200d401d1800d40508208a40e0019410a070603250716910803038681200c0200030b4040c05a0401c81041c030a02da402400c9941140588640600301d0404510f400424500303a4840c644030040741002c244030316410b10003461800514004e194807100304c021000c0040200b00c60b1030f40f0905114901b0f8160554041003108000407107090303d4180a02705150900940c03140b051101403013000e00034618180d58511210011030400d50300c86507843c010007448210441e42100d883c07110340060106104140e4462403602403117401071120880300e5600c0c00850001c0741c50300d60240440d0304049060303200c81e03450200309001e04030a40705584016030305103400c400c651581c014032020f41c000782c01040c0403078851900c0950200c012840528ae01d07680f40d9450810f54032004161020a0642c001000386207400c40100f4014052110001e2a0880002c0002d00428401000a0200c89050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 890421519 1250 890420269 890420287
    0x40209060a0f1413030606171b0d0b010f05012a080a03090204050f2203171e0702010b030c0108041a1503101a040c09030609110d200102120708 63
    0x612011290f1a4440d00a952004004c040d0364a9142900056404600b070000c0000c40200040c0e403000c8080d4200c0103800c0c964801001440600081050f0710740c0b01c1c0c036000009000c00c1d400c0528900030100194003094403031403c030000d0042503030440d19202c02100602c0b10580769401c00b4842c008141d210401c19920041c000e015401000d0f070350800394102c1e10b004100316000d06620081c6004000d0804400c003002c0c00030080c0d01d200c4a40d0070f00240080e100c0300d4108600d800607c21190004e02149207440744003d615000c2a00c030100b291107000507074550342401c1c1c031030405215021500000780b812446030300e010345807284d00413035000030201c1d80005100000c0120f44001810144484000c0550300c080301d401070208007920b07107800c03060701855100c1d6a4071000e180920800607601c05a40b41d00714501c0c5542c4030075006000505003907409071020b070021032441d42c1c0c051207011024414a154002050b010322a82007611440c48028190740c80300d000b0301c4100502d0020b4600e00c2d40d114410316915007580c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 890422769 1250 890421519 890421527
    0xf050a05160c06050c0105010b09030703020105030a2a18150e0a030510090611030103030e130b0a030b071d090c0c0708060a0b100302040501080f04062004060e040209060a0f 76
    0x1296002e0449500840c1c0455220b070703c14000c00b2070400f800000d010780d907228202c4441078440c42c080d00c0c0c1d15030302034041040194042d801641d0300501c0c4203000180600c995406140e0385000c0104440301d22030143e440510550417006032004281d1125a10032070701d00341418160a2000c0500d4102031206040050311603175074441164019581c41000d60700c0c01000301240740050070001038101c59890408120104180400090740d04a0341c240c0d98412401c4135150920000066607118682e4440c0c60340c9502c890341d11802500801144500c1280f0710914101c10024404010303403900725050701d070003d44504c80d80c0e64072085680000c0c4100d081a40c0e0400b00209916001d298ae00001140c001c0008111680e0119031115107501c07410703115554807400350502142244a2030044ea80840c46610200701c4000342c40000952092091400045100905a004403014030724620000383c03200000b01804450751000100313107080000c1d00c0c1075080448240c0024900c0c000e200039081001107800d0701c0400c2d1841 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 890424019 1250 890422769 890422807
    0x1a0903181f020601080106061b02010c1e21030b01140306031006080705030f060403080a020d020c030313030912021c030e0d03090302191809032c040506010f050a05 72
    0x214030401c030841c0151a002079142d941c24803510381c10754a809800200e01e800740843c0000f81241d2a5540142c00b2180d0054591400e41c06083c1c400d800480341e1801d040340c04010380c2a0403030240d0aa03010f00b144100546040c0441e0324140c6041604051400045980216503003003003010800300580c40f0350314080802c0c40e100c040300071004e1003804e142c0f001969070300120341c1c0002e65000342c0c16684000d140e02c24441d07580b40181d40050005015074000346140b1032550260000d404080d80151404140449051035a00280da03540003024000e0090000c05402444010050610308501c07100c4800c0f80d00040d0600c0d10015540e8082c0310580d11040800d07100f4400a4100c001c010119040c441650500900740400350100728011a86500e04441030135280e0030380412200410700e908030000411081c00b02400c0c074002c040f8140034502c80c10003014829254a040100b4401000c00c20300340285003040700f520700191910703040c89508101e4200450384402101c1c10b8940c682801a80c030601e1041c1c1c01c213030100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 890425269 1250 890424019 890424049
    0x10203060a05043e040905040213050403080c0c12040e18120909090a020d0c0905151e0a0302040c03141605220b0703050408011505030706031a06040803071a090318 72
    0x480005c1c04150b00a0742c0d0b000a016038003e880c00c0400c000c1c0408100102d40c0d05840190200c1c4040000900c1c0c207d54000070600720b10802d040c0d03400710300d40509a2105401c107402c05d40c03000c403000080084042280c00050140810040100708030715101c4030080261144082c40d90141c0400d6000400c108000c02049005d1503018199000d6181103080c88501c042d900e004101129003810302040000103c410354010141d4001c10003d4170a20121100c2401400030606036042004d014001015a88500c141d000666490301c000c2101c90381c12080a00c504070040c103d28540011b170941e8004c144c4c0c444150b0364000031840c11044041c038032a4042000f82d08030740c040f1840030300001c4c1c1c2104041d4410080d004440c03009001303000201407012a00c0c2c0b681000d00070543c040d4041d0600b081560b100b6000a071aaa0b041c09550420300b8035100840d1885c0d00c030f50001c40b03683d0b1000645000b0400c82c111300c00c03a1007500c41d03018041c41c10082042070b128406d500e000200c100040440002c0e035505c001940400381c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 890426519 1250 890425269 890425391
    0x60e0c160f050f1002040e070c06140702010c0207050402041208091302180f01031a040f0f111e070309090b04021209011407090803040b031b0c010203060a0504 70
    0x505a16009070f035003001c000644a14003d8241200201c561350098400b500c05d40741360304d029580c030107208a440c65241102540c14507103c284001c450310100e59441c2c0120150b6001141c0b201905002030300d8409154402800b85204100403c280151601941181c550108030542e82d14890000906005819111000403a100080c40ca9010591140c802e04260090b640504104034034001542200c07207a802400c081c03000c03010320211030303e020751000c003060404500024220b0503802000703044480c11a01c3d040d070000001419598800d411a01d50418a02602c04500d880400d640040030080c2906c5680c0c0b0107905c0708a08040e5942d5501170384e02c21706260320503088600d840b012031400303458407850b00c0c1c042079940004584600d201d60b082d0002d03200002c00440c80d06107030079003030881d0754401000c07014243c40044642000c005198010129000008005a2682005d000f000303140c002c6e690103648140e00d80041036940d43c1030715030a05176442d1043c00c5608002d0000803101c480645403201d038120030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 890427769 1250 890426519 890426543
    0x904062403060f020a08040b0a0e0a030e13021303110a031709090f271606081f15030902010216090c080a1107260712030f060e0c16 58
    0xc40c4900d4100e20403680944014004100e0002c603480c00ca204060f00c000004e0810301c002000704080115007500a0b075950800141a805c041c0210b003402160b0303204400184440340108424076142103d5011603185100840c07520803512034411030440a407000501c00d1181000f481d1503075850100100003150091010041103042407228159940446503803803284d50381c100811740e41c2e54600c410520039060201091007207060607030355040220440284141c1403240d85850121043c40d400703014001d0900341c803100c100e410815030003117002d002d080b5001c44222003040700b0001d0108030201ca0308000550305000500943d01e000403400c041a82e200d80301001e080910008807440180e220b04000c200d40e81d5842e003503480c6c407500ba506603030f4a454001414036090007110081151001901d098071042c5030907201c40014848002241c1d0003a140665900c502441c21501c1c8503014000c507152400303908820003006041c00d9594141c18070161903183d00750304c00310b100314580340b44804520011703420403030362195 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 890429019 1250 890427769 890427821
    0x705160212460501111216090807051302190503040c081b040221040302070602010c0212070b072007210209374506110d09030f090b09090406 62
    0x1b10400c280d0b280780000c0146c00034079100500ca188110709460f4148040d100c40703880c100800880d6540300e11509020340d17003040f01030b40e055510320042040504546405c0d4803441e0508108000c0d041a80c015000d80d003150355149092400030f0007533000c0b03100840340162140b2100540c441041800d480c14003102401c0b0b4140020f141d00062600c1c201c0d08254003d00128413400022a140c400501c42da0740c07500303400c0c00390070005050045d9440d07002c025441c00d00314501d86214202c50004942c0e002c0d00207500720400511001c001c1d4281d80d005000c1c00141c2a0901c0b20035404500514801807655401088113008405488007807405600b441d0030040404400001400c4500300801650b0000f4013100d181c4090995000d11401c2c04021100c410101034050f4031003c80c5618140c054800106d0703074103940c1c443d01881c400c0304801402848404074000500d201c043d1401038a14003d0304135020a00c440d02034200110000b140c21100c0c140c02c1a52400e04548407032034140c01030022080c0122111700301c4402614 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 890430269 1250 890429019 890429047
    0x902040c110d1b06181a0f0f01060507110411040303120b1210050c21060a090509070501110c0d03051e07020603070516021246050111 59
    0x44001034141c8440054000b400e03103182d00c0c44460b04000d40e07665140700740422010750151880c410340c4807640b241d082c810303545e203052041c980b84508800c480d20307000d0101d108030b1400801d6104003078010444132541461000781590003100c00c0205010000c08841c81035840750742040300c8411400072029255622458050b0002084c00282c60815140c0100b81d012480c10f071186115100204005c0d2019402d2010702601914000348141802d0404005074201d154245981600410160305201c555041070400c0000e1011260f1069100e00d04040500029450104214080303e6090034082070b9141582c8a860034401c0352107185600c500c00700c040c50103141d00300c0d00506c00003029242c1c0c900e07208006e01c0d03405114014000042c1d007146042c400205114000c00040c055104041411111020a0341c000b903100f4034044150340403504440c03a102040c005000d442140d146003c40202185419100c0321a211071040104884c0c0e0582071036400b00303000082d80880f800c6035110000e682e46000c420342d0300f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 890431519 1250 890430269 890430287
    0x904170c1014010509011503060f030309030506060f01080a09170c0a02010924030b01050d0609230613021b0615100512190e01050103060617160603050a0902040c 71
    0x501c038509104810300c0c1e50342500003260603140010490080c990a01d91083c001422150f8010141980d54401080e0b180c40011410300861090303480410060440c5801c608003480904800c0c041c0c034200311000203680c3c004a00341e6014000352000552451182400d50800326000c0030f00658210001e01d89410860118034015428000e0700c0744517003036550340701048038100401003403013038a200c1e603d442c52400e100b5001b211300414140b42543c105825014181e04554a9074003540b816540e8171008410309403c644070610701000e0704000c00c031364a86207000c0344100040321552001d071940095110207000180f2220200c040c907140481d02c092601034040011038840342101c5201e040120541d88045221300c0440307020b0309007601400d6103510f500d041e002442410a800d07014064807070b280c0000c0301100f403150341d0080d8090500828490702d001e0480e0400701e840b0092103125003002ea00d03070b50185090b050ce0003c484071850300140c0c0d40d4071102200000e2155280096010b03043c03040c09601c26521410071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 890432769 1250 890431519 890431543
    0x2d0906040914160c0b060d12020a0b070509031207260403030915020319140711040c0203162414191505130603050d0c050705040501140904170c 63
    0x4007100d031102403418003e8200d480072200043c540615840010300035060f5942c004002038a0220300c03920560700c20440d0620310241100592180c001041403020140c0070342d40140c01400c10790303e0540740d0000301c0c1d120612004400d04a002c009002c404101d03944405420039081a2241801030400c44202e200941c0248803c1e0001524031070041114812044030120022958000790700d00300200c03010401a21105028006014421a905000000d850300500c00c4038450b40e80c01c2d00341200d00d07041100f1500d01c1c1c03c150303086500038008100450b201e840b0801d0304603003100c803910106e001c2782030103090313045030242c240241d50900d4012a100042c0c6003d85000f807115240511000c41d0301a140e0003241c600da031410807103803207240c81085103040000e90980c1da810591404034106440e926203510b443c0500d554000000c261a1482e020305c6024002100500f000300c034103000301d51600a2214041090740c0615100d00700000c00b1804000200510341854200840b06503150450b102221f61625410340f44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 890434019 1250 890432769 890432801
    0x14061e0901060509060d020307080d0f110604030c0335040201030c080c040b0c1516110708070902091f08010f09090f11060d05090a060f022d09060409 66
    0x41820000d060007038030256007003e0035140c100d6664008218010560050a80c0c060048480200d049103050001843c0c601c0240c42d45d01c03040d1600c00005284214090001c50190401818400041e80c04440070400d076030035142c03440c100345c0c0541d00310300d1a80c108030031464005200205140e10101221036148502d0003620204504061800300b55143e100c00c483c41008039804010034410100244060311510445104441c8840c28610419209000c180c0f0082641d0a9058686130003a91040030080c240160101605241d031401d258117950f044280a131003039940e00402c0940c1d042d1030703d02c181c414010703d41d014140406085000038140000c28010410f814501c40340c040341c05480e034010381d0003450340b0960561420146480d0030a1002542caa401d0748010100400d0705484421b001d028081d0a4050280880043d00c1c81d10000310ba45444281000d1801880f0030502d480031281c02c00e10a540d60111101d43c00402551101c0900c01c2841040d88004007040109180764940c0c001f03901c0340d01821b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 890435269 1250 890434019 890434021
    0x150708070f02010c0c03030507053c0c07050f06090d06060911090102030d02030c09060a1214092e1406030106061e0309060609060311030c0a150c14061e 67
    0x124280d8004d120440003066407088000d0009209130f004035413107851850180c0c106950441800c4a0020a03682c9020407510200c140c10440000490740d10701c0a50800414a0654a07090705902c0742c40e42c1c85214825156100084040e072140c20449130407502c000c020390350f900e04500d0040010142405a0051589808084800707800e02400300c50f19584140c00441c117000440074420301039400100010741ca003c00b0b02880348242c40f2007000e4503034111291158241002091007600071140b800300c00c40c001041d59414000b5503480420041d0a03e201c060407009045954a0310304034141d10120464035040c80c10094000c485502d80686014003000c4000b8014a9903485084a000c11040240126810701d402c058481074040d034030005a0724420103000c91442d80c0c4401400c1101c449a205072098952007001403c0784c68140218000f07424119002c003601418800201c488184a06142e002d0050100b004814003101028128020292170100d500615200006110225510707001c02d048010b110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 890436519 1250 890435269 890435297
    0x13020309100c080112140304051017150604030209071107091a090705030f2d06190b03130c03050604081b12030a020a0c170301050f0402070b0406020c15070807 70
    0xda0604860211181c2010911682c03150907a10101886030b45003484200b1000032760751a4685140601c1032242c480c01401200d04040c00c20500d07004082849003180802c0301621503031414191403d8980648108060b5034a1000c15075a5030b4210b800000b65100d09040080c0803045600440042e038081d591502d10101408244a031902c010f07508240840c00034800510300e0031001e01150303808003400000d20402d442d058098000100c00c0b065002d0010840d800b0400541000042c0b041341684101d8207004a5252119800b40ca00010700b095640f0100c241d01c0100f48442004a540590f030000705072401811b042c54a0580e95010440502018442803d4040d0301c80c4c0105264890744a040b225901c3d50f41c0b03020404001b940300c008103409000b001d0840388003188506082e2002107600c221031a40e00d504201c10440f959980411091289004110b0700b40041e1b80c5100c255000741d4014805610340002c0d030405d9081c91441c0410300c098008000401c02c082c1e41c85a145801101c82d0b4642150003d011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 890437769 1250 890436519 890436527
    0xf09040629130e04020d08070506060f0619080a09140604170301030c060503060607051902010e0418020d05010b090705070303180515190606093b0613020309100c 71
    0x440c00302e10510007904410046540034102d8280e01601c000c0141c45038611070b540b103034031035000444241c0e81d03079103c20100012410114568110603108645150414610800c0d00d101c00c04c0030400581003103c1080400e0a1100742e802000c40240e100c070140d0782e4618001180359a40d82c0480341560000d0a90030000040c02442040303d040e81e80001d1008150740c00c104054549a00140c00306820560400402010403810311540900c4071135070001200c08000c40c000100410150340b11144903174648a04006d005040d84c2c51030f003100e82d060300d40003003490442c02c00c2070042611501c49500a078291040204140d0f00400802e1040c0c0f1a441c200015001d0251015020350318420052580d842a60f0714404040040085a40010070100490600004e2101481541c0d5240d02802c086008220240a1584050324501c8051131030524540000c00c1ca512000b0f00c22641260640140c0c42d800204141d0f44494a072140280807401d0299501d040070480c60b543c0f81c40302c454001c040ca20704404003160710300c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 890439019 1250 890437769 890437777
    0x21309060b0703030c14041d0604020a0918020403050a030207030606080601030f0308191e0509030f0f0f07050a20040902012f06100f0611030409020f09040629 70
    0x8050450790400e12255020760040602006403000c0c070030181c4c6982c49044408000340050300c14500c02e51808452080e1400c1090405056544035600600801c4a03180c1e20903110400c0710101c1c1268040451000b054034001d1065400160590141d94880f00506800240030740880e44244000c1104983c1c40b40c850380c681c44280801070060381e8a9220801107031050300d0b02500402c25000c0302860180c40c02891003100d10103025040f00040038400e59500c1c014604c42c580e403100d03c0e040030354030301b00c2d10441000301803242d03445150300e860000c11901d081c5980242a10b450359072040c101c03402d40e009418600b42030900c003102c00da042581125241e4560030580a4015415410b131034410700d55100b84240d03000d09101401d02c28900140000751207200b0b10401146000d81041c00d81c500f00681841ca500e4a110695000541403190360200c91078641c40000803034044400010300140c0b187e009402015a601c140d10f1104da100742844004585c0781132072807281484650640c140741030303820103416100050207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 890440269 1250 890439019 890439029
    0x302130f0b0a0f050c060405010b030d08060d030c150c39150f021204050106050d1509032c10020c0a0b07060b060f0304061401030b07030b0307050a0902130906 70
    0x80601900060500070740a200700300000e13080c01c0d42090014600d06181078011181a22160745480d103105403801d040c401e48040003e94039058095242c004007060241c03805910050400c4201184034092003582c0c031984101680001c82841030303401000e0000c0c41c19080c65003030b10388264008180594603c0403c1e8140e4100a50003e054602441c1e888441212000e0798400d030103943c07034600c1e8421100c030750310003040a0400350f00341c0c054a09040c00c01c00d0840e4415007209000302c076400c0414022540109003540814419000403400000600c0c04462244403050304045c4071402c5054840c00d42100c04100c8000001500e4903005494155022680e5540e0958180d401210340c110074803020261400a10343e55009403404a0344c00c04004c049602c5030310406034050420004020300c002c005881c002c08210040c0840c4a48265046850783c080280000d440038090598503004c0341c01d152402e104201c0144402000e51590954452074a07002e50f000da415410030105603840880e03882003504c90041610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 890441519 1250 890440269 890440289
    0xf03080c072114070308011d042301151203120513030c0816150b460f030501050a050405030f0c07030804120b092a060c06070302130f 59
    0xb1003076902c0b054072160030302d01000c100004001d6200b06504144001d008a51195480001a61400032241e03001072081302e401c1110001d030814440441d400c1204440900d14100c0c0064001c0e4203031541d24018040c86513503504401002c400010600140c404503083d80c1d0194a034604a030b01c50502600440d02d0450713517840c0c2e4901160765240030a02c05c2d0003030064a403140c007016203000072400c0072024920b05a001203803161f42e4112a0003004c280d80c05981403110003130700c1f00d2031080d9507400c0c840c00064000050841940000d0a0348810103880c404400c0003016409101c4216900c2c0c0c60301c51780c440b07140c0c0400d860b84d608000c080380c002822841890301c035036042070256040103c581100380c42c41e804240c90307d11500c03d200000c07010484010040005121441070607211004610700300b0680c460040861000d85c02c408604c0e108950390400014942a00800d10310314024024000f070114003810708920040c0c0f140d101042000c03a0142d000b82100d42c2c010340e581010b2662960280800c814174044c0314110303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 890442769 1250 890441519 890441543
    0x1c11010201050603190602040b040806070f050a02060106050705011d0f0f07030206040504051801050a150e1003060e0a0f050123010b1218030705100f150510030b0603040f03080c07 79
    0x41e41801707040001c194030488000d80b400ea514028016250840d4114006641003241800744480e0003160f0749001803070314104507090102100e006500c600d014820b110910200241d050304002c0c083d4032480550200c103000d080c048044e41c3d400c0d60b46542140d0341d80340d00d2203941c140e19414140060148200e03a4000e0a007841d0a0a010600005d0440640b01e030b2400c101c0e5108056680390280600d07449401d40c40700c002012100f1034610320b0560055406080c05200303580a100c02e42940c0354480d001c2d20307001400803030b032020350713403038403440d06042181c080d04d00c0c0c42501c00f801c00c001c41074000000c99408051440d042c0c041c2440704186045c42840b68070101c101c10001d0340e2455400005207030340000184810074683c80c100d894241903503c9070900b120710b81c01c11024031191300d115214a849207040008200034091040a525504100900402d8441d017907442c81c0d480f0482c866000600010750240c0b4150302c0c1c0c00d140c500b1000d448410030007280800c0300000002d50200c462026100706c03071f402440c4554a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 890444019 1250 890442769 890442793
    0xa080c030705061b1506031605010c020d020a150c1505010503032d0d02030f0a0e0d05030910020417011803080a051504050907090e0304030b1f051c11010201050603 72
    0x18541c00040c00704c011070f10b0b280c502501c0c080240510040911a800da4064502c0c0460405003002803100c2440405512440140711030390344189008246ea40c140d4800218040f213000003480c0410f55400440100e03c0550031580c826032240c2d128121a21464203028001c00360002202511400d000e01c0380c1550044c130400700c51400d90034101d20f0200d03592070380d1800c20341d0300d08010000380d012080f100b41d11074000007031105a07a071000c0d09550180802804001072071280441e15143d03000000700038100040400415002802409200b040d440d044130110350b616a03400a02ca018020210204659403a00070003c03800300061202e42e172025450340d01e8038100e50724020000d00528010340301c80e882d0183c4140c443d4036905c0c3da00c80d4900880c0c0c0c03403000340030452070500017109440300b110340c603180f0b9007060201704002000d0441c010f4000c2001c0c440c0e940407001c403a41103002c0640960001751702103000d40c07010521240b03604c0000c0255010315510514194090300690070b0350019216903030158890703004809 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 890445269 1250 890444019 890444029
    0x90b18060d060608120304110103110a0c17030907080d050406080c03130209040b22020a030b0c070501020a0804031710030b06011b05010e0d230f1b0a020a080c030705 73
    0x184040c441c8000040041d10355095034548012820358899000000061009101c00c44002a650550909e030600120503c02c451820074083c001140381031140a041c2071040203420404ed026504a942c002e03a100c0c40c05218403680c844580c07040300c00e103004100c07441c0c801511580c01c0f5016600c05856440e065107500460050f95400200103485200d42111070310b0069582c00111030199004a10114490030111901b034011844007442141900c4902e0301d100050303e41611b035204403500000b10391035a95400c03c00c0113841c4a400f50040c429440024080f40c1140c210b03a040c0e016038000e50b41c01d1144080c502d04203600d00400c0d2400a00040095000c20001c2c6104076841d41c4640d040c900a641480520b0748902d1600c040075040311503035141c03036102841031820428034405444030700d0240c10b1842c01e9080030071040d00f04810f801c45000001240c0060001290468888a40040c0c10269400c411f43c0b078252036091301c0e1000c901c2001c0c09580040d40080008581c098644010040e180386860641002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 890446519 1250 890445269 890445289
    0xc1b160b0f03133206130b0a0c030603050a050d030c05160f0606180204150e010503040b060a12030e01020705060f0a032307050a0f2609011e06090b1806 67
    0x200c05440303080d60511810b01a0042c00d90345180c1083c541c11041c80031511383c0c101940180a090600c030701d0400000418034440e0595040405200c00040a0450500403005404d094102034042d10a03500031104103c000245514000030f10742d8200b10741c8407003a00881d0b06108550940b030b07242d1717103006596002c00da03403218840c041c520888000071903540d100400c040d8100008400c10714640d0101301040125034a4a01484031411450a00d804901040c0068800d020191010b41444020790002e9056184e20070040080c0194007413a81101c000c928006080e03021100e140c50040c002d1000001c1c1030b0410500340e40c4500007182c1000e0500200790340c22001451044080701c200303d8040040070b64000c0212000740200380b961741c0e290352000811009451008002112420040c0c440422422100c02c000b034185d100200c0c0001da01c950304e84140c03643c050f100804070705541c222404100e0f440b010351540104200d682c44101400103600c19010414850100c40308007586e1800c400c00281a840c002c6086 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 890447769 1250 890446519 890446523
    0xb0409231501081b030a020a03120203040b0f0315010206240402040f030804030c06180306020708190201150b07081b0f060c21060112050c1b160b0f0313 67
    0xd4598161207410055896800c0e40203c58a8001208080d042240b90228030a1103809600502e440c9616502040800c501d500c00a044c1d280400c442c1034000b4424001c030380c014034801603199221851140c040c00350381c0c030503500c20185400040c89006070b0b5001165403841003800b071201500b00031140d1914100c4d8000e00f07440580c4641d0030040410800c010014002c0550b019a0141c0c2e100c03402e6260044940000d904684c003804018a004003160400b80e2080080d00d42c40030b00543c460311070385401071745c5005205104041c02c0402d00719120180c1d055201c3d40000d242c087c042d1803041d6640c0c05c0302c21340f44180d10000c2d2261034100440b07000d0b240601d0f07040c40b8039100807044401107003400403024140041070310380d6488203200050380c1da40b0044c2c05c046102a01d46180700203c81e4201103002a0104500d0b480708250f0079114000541e8800c000c9041e2040008450030b43c408840d92181080d0b12045010500c0c0c000d0400c404010034880c8888041d9080720a20201d0700b40b540e1150400111010740038101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 890449019 1250 890447769 890447773
    0xc12090b13031218031b0306021b011b0507060c02150103061a100e010c0305190302030901050f0f01060e0303070c090504020a051e04020c0c150309010b040923 70
    0x100282038481800249655a00014400740e11801e40ca4800364501100c46018100a504150280c100810b00c05900499030701c00300d000300701c807100102c203010002c041d400a41018800b00e043e180c00702d80b1600c41082402080d00800241e084022030389204004860841c0014205105000005580791f00121500c0c0e2180102c4a1b903120900c408102d40000741c00803500241c840315001d03080103c0c0100c1d160700f20300499414840d1121b50a00800324121280a00c0c1046040c0c050036040c54003403001c507451081c0c110710140d900d1545000c064049c0d030050300d5614007580380000080c06519080c41c1d0724003841640c10034030026443c0c1001155518015075a0641c580020400302d000519003280f080c008207030b400000b14592415004000c0c4102060b072055008054800980111684e1410314500d0000d00f100d006881d20300000c03100740b81400d40c0302c01c29004403110f0035245035940844051446440d000c0005d110420401c3d00b8030013a190800b0000b0041075048003560903107166188501e40f00048201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 890450269 1250 890449019 890449037
    0x3040f050d0f06110d18080d0c11010c0c05100b0f01050f13030606051809060a0e03070c06230901090302100c052d030c0c060703020f06071805030d0c12 67
    0xa6140890310542e40042400b40009031740d180080782802900e005041d40c0841d10112400358403021081e00c20461007003d5203558070f0341030a01e5802505081b8000c0c011800030040740d400c0d00c901601c2000907130002c0c0c8036889140680c03070486d0361130b00a0108079800038080140000150b0f0040d141c64220701d0307405444e801c0a114488038210204102c070001c42c00340201050742454a03041c020344007411003002600550740c01c10403186ca080083e40940144030b00c00002443d1145066460543c01110401801c14154180024010380d0000311620000d40150f140010880a4800f00006200300708001d40424195a8100054500440210078a8141d420051074110300d50791510b0400400110240c5051140000d840ca80600e00c107042c401000024020f51900303500f00d035915a01e20780c0301c80031446480c2c000380d15810180f0910807514011900c108640d07550038240005031401000408000303032211115030000c0c4a00d00051030300700c202c1081d2904426502c454540652604581c09a0350601c20b0b198 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 890451519 1250 890450269 890450273
    0xd030210141806090615180f0105030d0903031e110a0606261f1401061e03090209060108041e081b1c0807120603050f010c0203040f050d0f 61
    0x10007a400c9000d0301240201c02031800051416000c1404120118150301c8481000403143c00002c40b00c3d0440c0c44030b80804600e00118000511922100b8480d01d0f0741008213040c0000102540003080c1a950120290340201031040411102c0d003000b44000350000d03020141d250002003114050240860042c50000a284201c442c018a0324120807421600d055841c001082600c2034100b010f04201092001d40d5015403140c0c41e415995400d20040f5204020340903080700c40a005544181180d808800d20110950f0791142d001d000700d1520325000030000207404014800e0783c4179100707164465500402c84181c9032190b41c011222903200402c1150b0f81d6140407039400c1c1038140310122503801e6120f42c8074180e944039802103203484088910070b2000300d503000340e00c0002003000c000300c002c0300c5003041d140600080d600c2c0c010456903481025030882e541441d20300084244080400c0ca01ca01540c8040240540c5007507017412680c174850b91040e6120700545480c248000d103444082482513a00408070a800d0074526 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 890452769 1250 890451519 890451521
    0xd020f2503020411070c050901051311122701020f0a180801050a020d06080610030305130e0408030403021b0a050609011211120a05010302010c0f0f1406011d1003020d030210 76
    0x6920085401d140114800c02040880000100500001d403a04588c551614011440b00000502c1c4004000c0d110f40070220341e40c0ea10801c0d2090452044101d1081d42440300a070b100441c80ca8000c050144000c0380e86400c0101c0c1402182d100407416200e191409400d80307001c98080c20f820000c00621100103000103843e410900441e80511006500140d4410700c4015180440d500c983c040c0300c142d00502d081000760603000c20104200e0f90103041a59a9442101180b0516519908654405200e000a02c414040b040c400b842c800c51080c1c00322100000c2c0d00e900c07040a601d0100c41140c0c01b07244040305106508018026082c156410704014407000e40402903070080d02d0220460400751240495130200740565071600603040400c99500700210750541d0002032001c000d0481c05812100c10b4103100c8104030030000d0f880000d94110800c081c40d46c0e00b410145442e680c00f071007041140074203072010216207494000d81602450380060782041d03c138075540c20301920080400c0709a0542c098079940c003400f0b0b24a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 890454019 1250 890452769 890452781
    0x702062a010c110f150a020313051b040e01050405071a0f18041103040b0f13020616060b180115020f19031706012316050f0d020f25030204 61
    0x55a01c50a5020031503c900e01e00d055051410f01c3d209510131800e580d070500403801d83c140c001e200000056a030790f40e4040c4901c0c90804804000f4200c3c410f95821940d5115025805480d00004071414024004074110707031800d0b148141c5d006096904003100c200107422000842d50302c41910048181c0c10030380e0001180301c65420641c80c669024505032000e1441d031401c2c1c03003004504c40045040d1403c6045c5501c031907000d407900802e22440700c1480d10100d21b14014103c950003400c5da000f4000d44d5142c8000500b015025040c07401122103a091415405142c43c0031010100c0040c1100c5c500d0601e40e281c00d901c50105500170003210150701030515184110703542030012042486610f45d5174131192001d8a00100926107800316103401c0040c4100b80f0040da030b4050380d045100107001c41600c082c03200d0350407901c07018416038000081c011400103402d003c2040c00304200181130300d0141641e0030314180c1201030fa181c015482070355101d50840c90240d58480510302000c1074008815807003c081c9a203e5000c078088500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 890455269 1250 890454019 890454041
    0xc030e011d06070c0302060705070309050d20040b011d270702060a020a3507030603050613030c020d0309030803040812130201020c010507020103090209040b07080901020702062a01 79
    0x1024800240910401c009542d000b03c0309180132034000c41a92002900c60301d0103000001005800999501414410076411001c5c040051901c99020050700d882c2c0c1040021401c200385d400300028040110749880e119585015038181c4560a50590032035040611000d03080c0c1c2150310281c03200300c0280c140c01100442c20541340b4801c000301541088423001e441c000004040c3c55a0740d004200498115078080d02601c012201c03400300e41c0d14064000780020400c00e142c44a03007012034901007008440d5605030040000ca0340140c05407050754494801c81d602c08003200d0406008180001103035001804e00711426007115019261003010f03d91640c3d01d083c0070b540181c506464894011981801c0b9080113041103411264a2000e00001146540040c0d2145803008000c0c0c10710002040c08001e690081d041082081d60003040d0329003500d414a0700b071030001800c0c0e40c1c4800158071040007440700d4034144210380310240c00500241c10700d440c0c06000082a019112040d40010744d007000311507402400d0041e603120f44e03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 890456519 1250 890455269 890455301
    0x15210207050d121a01110f120d06140d140a0b1302010f02010c140a020c060d020a080105090c040306090614180c0a0522021608180604180c030e01 64
    0x42441040201480406070502d03c0c800c0c03602c2442d042c1d21403244000803040d8400c3c01e00320706d6502c1c0e8405160034641c4000c2d40e1b0311a40181c500d00590199560b00611078052404010002c0301c1d19100d04610359241802e245800c00b607016000c1011584400c043c180c0348011504603a059000d556030100307295030a803088804030420504407030466800154184050f140c0748020090f500440340006e0002045040c490b002c0e40000814042e940d1090052104892018101d2683d806114001900940c018944240007d0201d00013088031f14029160300e015240c0034441c1d40c141404c40c1c80310002041007540481c0c12980d02c80102d003030f401c0707000e041ca44543d040710038564003184150b030024204102130200511840c015030040c041c65440c804800000725141c0004034031000d1f070349c609030003d20540c185600801c45644040c0e00700000c40d030040108442321144031099000340030900809000b24043c00302c10b000c1d440100345d801100381e4481c02c1042440c0c5404100810304101681c2100d401b814207103001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 890457769 1250 890456519 890456533
    0x2503020406030501140306040b0402030f0a0506040605090f030304062f07020f03060c0a08040f0b0c04060e090c09010e0321070c0806150d08040b03180f071521020705 73
    0x42e8052041e6801002c00c014143c1c0d03038820307050000340c440c1c01c001c02c02041e01d104903000c01c0c20364404000140c420849442141c0c40c0806e60b0a140340d90780402c03181120b0715400d000008502140108903198184c02500003582943c42e5a95001c001d0400b100099101034900c03d02e110351450b000c5041401854070341d00c0070755118036900500c0349114442e450b26000c0d9001101740481120b5600441d011502c0b24600000c05459900d48034456a840c1100640400b111405010501d44e242c4020000c40714242c80750f180e452149414022504022280000311000600c1300c0b030181e50041c0000f01c002d900040c162991040c41034106c3d8017074034503d50960f21011004c105c00c4100320300c2850a4003d052103000411051500e004c081110468130b001c898002c49512464504101101041d60007510041801503103918000c01c0a00500c0001d603d420114400c0160360380403400003140d030b030055408a065110410442080a4451400902584e1441d2807003c4030a004210745201401d40244514003034100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890459019 1250 890457769 890457779
    0x140d020f0a11060105010509060c0102040f0806060102060109050903090409030e040c0918090f0204151205030a3015121406060a0e0103060b010e0d03030506092a0325030204 76
    0x1040450002c000c4203030300960040c840c0c0d80c0c0020603140340340030031151950740e0042a078082d40a40100d51042c000318074047c201041d44007002c41d0807442440281c0c00c840c80c0c2d070381c3e0714000c0090392015180038200780c00800101d4441c0c2015000103112034080d00340300086d98041d0000c03804030b038160b03a001000102114018404a4031b8821081c1c0c45049800c014424244030741c0711002c4034903e1b0100203100b10b03590400390803101d900040385c800601001c04da03440c0814207400d191381c5a900c15030b00740f0001060f41c41000000d601e104111a0004010146807180244e80303807040008203607001c158040c405d494040014015201000340a02c2446118009241c0001c01c91451030070201510301d82c0b10780400341c002d010340030350440d1040c1103940203c80860a00c10390380042c0d809000461f0540e800c110550302c0082410341580255024400c25181c020a0307030b0312035000990806c14164001d00b650070052064000280d903401854004902c880490046516101c14003480c080309107004010940201c0c007000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 890460269 1250 890459019 890459027
    0x3030906020304051c020301060302180604200a03090303111c1103220204060e130b070e010909051b040e0f060a0302010e09070e04050a021b07080a03140d020f0a 71
    0x10050000e40001c41c141810440010344c224140d542d000c000308441300e008000e56400350061801190040c0a101154020001383d40c1029800c80d0000e00407400d00b2520116240101e110046560691645504010791003038102c028003011201502010b8450b460355400c400c085001303080c18004100743d1003130300c90303c5c1d528141540c802a0403403111036814003c1024001d02d45c8003010748042000721420104145100040c002c080c1504043c600c01d00030010402083c2d0710404400d00f5074003944405042c0d83d21035600702e4080c690300f40d0380b50018105140410201900d5082250812800d1045114903003d041741c90249421907801040c821a2640610014148201040313401c10010f80700200001e05640010705607181140304540222010350010704580d120703031050107a03964014800c0c0141d0500d2001d00002c0e410248440095051402d4011280c94000503500c0803035003010301405030106180c03400d450040d52155408a4608100250340f10120584000c081ca4420105629250000000001c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 890461519 1250 890460269 890460287
    0x71202040615050f03100f090f1817070c0308120403081803030c0a050d06030303020a0311130b0a0203070615030b07081b030a09051b270105191e0303 66
    0x915040725449114402c0e500100300d445040541080b165244c0310214000080005c0e5405450100690103001c41d6159261300104000b0f19854818420324210704804501c0983c1102e00074040c883ea04005454003403600c1c040c000345401640603200c002d0381d07500d510b14075078813a00c400c882040100c000c001c04c068000804a42010080e8242c040490301b201525a403480f000d442032080c880c2c003150014a25105500311051242d0315001445405e64925015010750001c01c42c140201e4180b0078181c040154220503510469000c000e88000703207150009800103580081000021400100040c1c0d01040e020b000d000d2810400710300c0c24009614504041d065500050180d100700017071f910a1211700202903050701c1c020800c0b503180d42d40d281c1f203134491500103200041005003a40a541d245083e420001029880c1114045d0744c0078124428808081819681d10303100802c4602c102c00040c08141064100040000007070003680001e01d882d905031202011800040702c4480c0c501e440203108050703000d6405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 890462769 1250 890461519 890461529
    0x60f041d0a1b1d0f18030a17090a1703060a0515030402101d010807180311030d020a02010512100302120f0d05040510080a02040e090d0e0108010506030105120c030712020406 76
    0x300f20ba6034403181d03542c1003000d0150401c00c0d403d0380c0c800411a0340120070144060381c00e00c04201c913503480c4407072000380c0003c4413016407184c000c0107240001c040d0200402c14241c0b19500105000030841c00d15491445030b080035001c503400201c182e6002c10141c6031001c8074048800178104080e01d903c0c0920412000e80154040b8030100110355000c0c43e6000c0307100c01d036840c003984e0074200243c280d915560b0440e8400c0c001e44d40c48007280190b6030000300303020075000300c66408030040c0c2c04d54203480416801a0b03a9030400200003800103500308900c104c44141c60080c0740c0c1118050100c4c1d942c25030b90f030300000e000b280d40c51301c1500a60004d5410b03515000d0708000c6040f10401909100d0704003868100003a80c143c0c001031403481440325250000f20400361a13411078001d480d076540c508807070b800d1842c0d80b290342c3c490707201c0540c010a492100c00b0090358000c505c1b55040b204020807245c42c585c2048103004480c403011b881c1088600c07414620610b943c0c0d0078000e0101401d4000400b003034180e010b004110a03103241c0c1d400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 890464019 1250 890462769 890462789
    0x1808010e0a060b060a0507081803060a02040602060c0a0807110a050a080409153501020a02071a270409050a030f090e060307060311070506010f050a0905060f041d0a1b 73
    0x117201d8140d600709043d140c1070b940054520f9110b29070040c00109040e0760a801e181c0c540502403c0082040d03165002e0310a4810560895840b5518522000054803492480c48d0110710700c1c00006d220140b150940105291036801502c1c882035040d550346282905d4040c0444600401050920401109114004401004403008050301c1e140200702c3c2d128000305150304130340108803680c120022600800d480c5401401100031580d5100100f0001d44403811400b0328002500e492151000002212041c0d5101c0440500b045c28034a40701280b4a03254040d005c01b46402c680c5900884001c40c500b07018920b0068041d445070020b40740b8940000b00244401e410690a013034100c0184031064a000074490140c1c2e9817407c0004540c51194001c07001806070b010010f200d80f15130f100104002810000c01001c49a0a0f038022804680f640460010344d40110349103604400c00c01010202407405030041300d1016114840e007016183c401c91030300d0405690540959080030482c10180d503048401032000d00901038814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 890465269 1250 890464019 890464027
    0x504110f0a0501050a05040e010e04020f0904050c0d02180f06090a0e031c0b0d110310060617072a1202030a0210020d02041d040309050a060f1808010e0a060b06 70
    0x218252000d000b45410010f01080c4808264081e80407200649880500c45805603500c0407040e0034181c0440f0101e000710076003d00b0115a090410207075004541c0304020700210150074007401540443c0e2401681d0250350000318014408800380c210b030207807903582031641861410005000c007440c40540300081e024500700c1e0f4407141074030200940e40610004944c21080007010803c81c4050103d03850900e40c08200c00c4680400c005100e840300c04070820076001d640c01840d10029050444101d4842e01011840c507629011046c7d5100c0c1d4a507a202c2c0190400303404031104504100d01c0d4508039204020368034072900229060040e8410f005010a0161008520b4074410402c02074480d01c43c0e0010b54156074020800c1e00200082c2d0f0107407805881c81d04958405011184000060101e041d501a804a00d4054010805061084006098461517141c800c5203143c0d010301244c0710950304500002181180d00d011038002001e02605811070000350003800182c0d000d0800c001101c1800c0d44452080f18100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 890466519 1250 890465269 890465299
    0x30d0801050303040303030e160f0e130b01060e030a200a090c050a05030702031c0221220503160327050108130f1209090c0509060d150f09050411 64
    0x421201940d9052402007000c540100460703190409803002804d0b881c042050108040b002c1035191011101c2f070b8505098680c4490060075202540481c1c090899008000140031880c045ca83e005040c941c090216000c0306200e80307650384240d5001c00100340340401544c448100346001c4505902410500108200040c00081c2c06005807040c1a4401d01f44040400007940c014003c1c4250761508140941591665070000d41000096001310f480707484440a4020481d40e00e030110b000c0350322034081d41f1007800c2c4072402c88000f020307035000481d01214144000c01c004600124140c04229140d4400d4907641c04c400144210b060001890b00c02c114501c21405e68104100da17071060400e43c000c0c4800c40d0302864840300d0309041c0251754580c10040e02009a540c50180442d40c828042001c95081400822540000324403c480130311a00480d030758070800c144a00322424003640d0004104c1d521198200700d040761340d990280010180307035200100c05983c1d03804100500465001e40030618604407829804a2515 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 890467625 1106 890466519 890466523
    0x90c01140721030e0f0a0809060f0d05090105090a120c0201050f130f0512100b0604030510020706140c070f050c03070906080d05030403090b0f0d0903030b030d08010503 74
    0x204840d20440d10002c1145600905c84001400c02e03007142d51100c0100b0b820402089038880ca04001d0880c4a21140d001418641c180d0314010841c0e00d4100080c3c2c6c02c441d001030035007540e900001da40c0030004501030b0151280a12604107030b013680d40c19000403a02c41c000c4085124522354005100b01e04404880354040c1110318446244600c00d840c2d01c1401462441d4a061003000c2d444a178115403070342c000350400303040501c0150600c0e0507e90380b921414030b4a1140240d0700541a40002e4030f1091100a0141c20101e07940f5515114807410708280c5464940b103090000b0b411880c4005020701049800e110f65500301c5001812194159194200d500c0107081c0b07442484501d00c14400c081000c1c5010764156032080350140c07106400240383c0903000070158004002009003080c00c001c3d54551262038490360150340e02a58000450006810030305151004100255003402a0740004205a81d80 = true := by decide +kernel

theorem cover : BRFrame.Cov 890287769 890467625 := by
  have h0 := BRFrame.cov_init 890287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 890287769 ≤ n) (h2 : n < 890467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
