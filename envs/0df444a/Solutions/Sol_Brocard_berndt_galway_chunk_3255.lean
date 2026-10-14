-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3255
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:07:13.812216+00:00
-- url     : https://prove2.me/submissions/ccae2bed-495f-4743-8001-b880f64e5133

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 585251798 ≤ n < 585431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 585253048 1250 585251798 585251803
    0x41a03030403081809010612020a030e030c0a030e0a121205070f030c02180403050f0c0c04020a0809070b120601030914010603061a0d0b0a02131205010c0908010b1f0201020408 77
    0x150700840340300300c00041c620110040500495540c4e0b40444015215502d0084c0c000c003d020140402c04800d6400101c00718081d01940c04410202c1044040e00d4031000a0038586450b084450340641c00f00c0c10b03003070725001c207840c100342448191820a800d1074181031a07900c6218440001c9021798041c00001c01070340d07011542000038901039034820795410140d80c204d4418410a131030542c06c0c401000364028103020021384c0010079a074500102c0c441050f00e40c40a181c0091600900110081e0001d10005120704c0342a800340b175051052510200300c5e61000d6403401013400511420301004a408007030310214055610a07000741d49603a001e85502d5052010142683c0d00712a115402140c036580d689542032a05a5501c040380741c9141d045031001c0e00001185c41e94000b041d00241000200d50f4000340c0c900f100184050380c030000e001d49140780001e440380c81ca000360007840f40900d9400861039089002420080c140180703070110802820b43c0b10110401c03c038440003080398140720300955401f2300022911001c01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 585254298 1250 585253048 585253057
    0x10170a05030301350a060506150f03150d1104020f041d070905030307030207030b04050304170102030a0b04020702100f032405040507050c0a080a020114091c0806010e041a0303 77
    0x318086420b000502c5288481001001c00842800c0900f080b401140440420300760717000ca8110b130f8040380c0c5030340c3c140001d802c064544050f03e02100000c01e100c0c4840c44c05801840c82800d24460700c0b01210403403001c03c1140030440c20001e20b00449803660201d00d06094001c0c2030b0409910148909080e140d202d41c070f030004092074840c4d07020710401003003120b201d80c844c20810090100750043c510780103003502c00039182c1d005400060490110480030404010080045800609078801d0003007480f9441058140031758415909102568205030612005242034421039614503401084c02e813141c50004000e82c0c814422201010a00d0b548114210071750383c595007800048824040b0948400b404e050030002251030150610040050078001007807000030020740700012940009005444207140d410483c0075082e40701c0000030800c156414405080070001c0c1d80d040705240d80114440e40308003c141116001c108031009030010380c03c440c10520500701035106c0589a8100e04000c1c3c0c01c0c0000c100403d240d03a10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 585255548 1250 585254298 585254309
    0x17070c0902030a0e060a11040b0c07032109150504090b0d0c1206180b0601080a020903160e070305041e0f02090c0714030a05071104180c170610170a05030301 69
    0x886400385207005000b40505580615910390800c0f20340c21f403041d003598500072130184900f03009000a202c0030300f20f400c0020380e0040d03a11800170200302c503101c00c3c800b40031120035445e680407945500020462540b00d800180500d0f0305680c0316400e0070714010b907460160a00c10700860704030200340507010101d04448003c8010740f07940c000000101d401407400350115420b0000c0243d1004107501d5407030000e04003480c0150002001d2804071520313100c05492200134070605149030b51601c108044484203e020f90124030407540640c1d0202d01750740e01e040083e004d4440450b07004200409103510403082e40040c20220f00c202c3e00804000080e9501030740032441d3b024085d51100c80e00302012640d10204900d0303101c00025418003c02550910805040c040c00f107004a903c001d0251071950034142c80703a1282d40c40803004202080c41508201e415041c6050703080210300034002c1080d00d288189200f113a00207440341c040e00e095040c4a10580c501000061000806c64201ea007070300a007600c000110750104081c6000c1c28 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 585256798 1250 585255548 585255551
    0x303040f03031b09210c060e28030606080307260408010f0501080c0315011503020c011a030f03042108190909180503030403140405030a03020a02090a0917070c0902030a 74
    0x741407541803546035221110301580b026281791000001500301500030101d89081c28540001d400c40c0001a5009a100b038028010241c24007401c8540c1403c070080e13000300c030300485080140603100d040d01511392141120140101d0220201c20302e1031001d038004140318000d10f1607403d0416498060301420f482444102d4990552254010311200303000b8040723250003074411001410f44101c0111b042c1152641403007074182c0216070300f6855226038004c0e0102d170f013900c201d2002004041d4041030445055001031550324000d00c40ca048505801600104403015903652000059401859401803034030380d541d03201d040300c0052052145040c20109040c039030400a180c0c2c4c6416007a141000721401c200d034a0a40000b070740382188040d0102041c80072048a802c00d42614080000b61032002c0c1044c09889140d011641502c2038010304030505602251b01560944220359000958039204102402d40d40d0700000a40182c0d0600f00c019600c17464100101107062050100d901c0540c3d80782c10b07040403038004541600e4541d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 585258048 1250 585256798 585256817
    0xe011406030d0806011403100b041517130f020f1c0b0601020109030918090b0a090311030c03030f1e04140d091a0a030204030501111b0f0303040f03031b 67
    0x186002d0000c01286a030b43e103408680340c50000f000030996a110740b82c042d01858000081401300941d20f410001400d07009201a559641d10030500504005014200b0001151413100f6940d100550301400d000c0c102c05100300d000c03d0003985402100c0480c80c402280c0c17001c10810001000d440d189500703190180c240784c039800840240d00f041c1480c6540140140e0459241c80c5200c400a60130508440542d02c0984000c1c00820f403e45a44c5c0081204540203410101c06d981004103400440d000300c41c1c55442580c903038100034005400295240100b00300e481399030b001400025042d030000841030380c0c230080d003075029018114010000e508061095800703580102d84800c100d040960300300082c03200503200f07240c940c00c400c0c40c0040e845131003000f0ba0f1f03c4141002c0c00288a00b54540302e034041d034001d542c002d0002c10102e03010b2055061503502650502d19010000c0c1b000c4a210300d004540038484602c5600510b207560b4840e9181c401c04181404120241a80e41410069080113400c808408114070303160030100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 585259298 1250 585258048 585258061
    0xa051b061602032713060b0c01060902040b030c1c0f0221040b0c0d020c060c0702041401140112090b07020c09011401090519050d03020a020a0608011211040e0114 71
    0x3034016501c0e411080d948101301020030920112100702a081c106080300c000c8645a04c00074492070800c4c2210015207040c200d000c541d2034000801071544c005550020010940d592178801c00764059482000e074103510510020340040030403801003450540a000e01010b1500c1c0520b50320886407a1042c210a0301d82c0800c2e2410031010100e4684880403034003030080410700d071a079590860030100400701d544a10022035050581100c54050b10701400c07444003501d50926281417100c0d065080f480c02a84201c0c10070404144581c002e00455050314200201c17035460351040c1d0010f50706088158801003803607640e9006000032845000c00d443c0102c07103030b50180c9014806007003040b55483c0181c000740f002c1504904020f88982e001490002182c005403031440d0301d50003842ca10410b0905541c08140c101d102508044109a808078004040a1007101c064102907106c440031102c1800c24003031100300c00c807100341160200c0d10390b0701c00c0491000010800300381c030342004140c0380c02e5428414210356143d81c0e00050006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 585260548 1250 585259298 585259321
    0x8040509010e13110301020910030b100c0302070b09060d02070b041412070b0405071a03100b03010f030206071b17010e010c0f0804140a030503070305090105070e0103020a051b06 78
    0x1011941886400781c142030b9616000f004030114010080300f10b20001c5101a1020b4040e00c81e803d0000345040541e010440340034024200f04060030384200700b070390280440580150681a042d54069008052150410544043d254000c8100036444181800f484101554074001000600d10032201c48490b07041910300a180b405082d40b042201c0d41180711070030018452841502e442076001500a643d0f5140d6040080c02c1050581112110540c040201501040941c0045000b10004143c0100e0f0308c0d40c44074034101c180030a0141222400c3c80c14000c10152600c0c50160020b1805816521780d501248000c01100303039503030751244a030724003400481d040d00034081c4a9a808090310310001c0c0091110030400800b0310031702310310400074001e291020500340015010550f0f030b0b070015101141c45070396607810043c0c1140c004841c1080064103050004201c000c2c1801180d01030180b5840d1840078400c40d200540c082d42001e00d070300d02000b100340300450b4288410151211a031207004082d03c200e007001e042c0c950 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 585261798 1250 585260548 585260551
    0xb07111f0e010507020703200103020f030405071a1305060d0227030c030105010506030403030908040b340c05060a03140a0c020705030303190b010c0210030c20060a0509030c0a08040509 81
    0x425500201c01c2000400c01056203e48e003c26080c1d00c0080209000c00141d00a020701380490001080c088100010098005680401d68410720400300207203201e140c1d004240d200b0a070181c5520034007801d003044513062880260401300c410860160500b0b821045c1101e0201d4407d0030314500c820115a80100360070140416040746405030001d00c03103076040201203051480080c0008003016a5440180305000c0c2c0d003c01d0b00c000e4192040c50075940d599845409070b822856070b007480c002500e080381400e001d0408001d002c8015a000101e4181c0e54544001c000080d0015003002e0145503c801c2c14501e89080c9207120707441001d40d10f00000c1e6404c00702c50020300c1d00d4000d0b040302d03019500c02c005010603503500618902d8044490440030410300142801201c0902c403942009401c42c000040708044e0f10b030150002c1601cec0b8540c4d92604101c000c803482543c0310600d8560301031141c4e00076401184600a60703810030b644c03200c00501100e00c0c10740380e02011440c1c4018402e054a12150116050041e85401822035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 585263048 1250 585261798 585261811
    0xf0e0109030813210c0b0901020a080a0c08040f060f0e07081608060a0f020d020409090b06100f0c0507030c06021c0309080f0a090b030c250b07111f0e0105 68
    0x42032007070010b0740d420008402a0702444500303d40b00c0300702e03907016101c5d40303001210960101c8440350034200340c901540030303421203043c00300410240400159040020310a02c403c0f5070407030f5103120316030702c4689075031400422802e4162081529047da54004030a180140e290b0314002200805103e0714010500d800c0950051082d442050405410041e041e80025201d030000c2d0384041c00100b98803d8680503000348a214460311040c0d00109001501c1e8900d40d0117a030860b80540b9484045540d407904102c1140d842840e0b8001161a400b81400001d201e880a0031016100b0021685980c0d2280c8421441543c250701500040c1e0080c4120f555000e041256800005620f08083c00b00300c00580d180c5043e0b004441441011751000700e4020201845880113600400c264200c8559a082480c200c407181d9101900302880740320749560f504e40c3c41c408689039840054000d00e4074006c68840a004030780b400d4001407045039a10800c0c02d40080e508241030640d608600b02a0009018001c4106150a50f14004c114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 585264298 1250 585263048 585263071
    0x9020d0b101a0a02190c031b03060f0902130507050a050f0c0304171908090d0602090409060204050f010e060403020405270c09180a110411040305010501080c0a03240f0e01090308 78
    0x105d00000ca04140c0031094030740c0700380100c14240e1001004030801e0310651015152504180140004400076402508500d00036141d44103000d401010b0001500e40940b00301c40001c0c410408400c038144210044d0401d00a4a107515140850b4104c0017895500301ea007200384a41c0386040607488050007084045000c01180709144a024102d44803040c082c0290004e03e400f464228518000f0444640d048540364a4000d004118914050178000001c0d0000e02560340500c0b034412410300c040d0b0090030700da4008000204260300e000c0c2180c0c05d000c0900310140c60707800e07c4a02d010040c0700728040c185e030001243c0403c100070f003503607071443d000c02065002c060403030502a031030b070b05000d2107042c004202c4441c00d94000e00d40781005522003020400504040c3c1e074030508104082404400c0020640109049480000884001da1603082c100710300407141d4480202540f800e000d0800000c014940f19202c0e00854a000284c141c51001461083e104040040300c00c695591aa00c0c042503000045540c010400034070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 585265548 1250 585264298 585264343
    0x40b1012120e010306120b091204050d200603010b07061b0807270303120b0103050108030a180b070b04150c0e041d03130e07020109020d0b101a0a02 65
    0x15250a40c601c0d140146080201150b14010a030340650400301c02084100501c001d03644450600380d1174808241c40314076240c002c0208012001100c0b4041d6819104001c0a00244400f039940b106801000030750f0024528060aa22169542e24940034500030002403440981d25501c0b41382000031143c181d002001244200c070002c5214984c41400b650740001c00303003007200b01074408180000c079000141d1150401c460315002c0200405034011b0790b810b03074020192414405112514015000e0340c42c01d01400c0c1840e03000303020362a48540b2885094003525000b00c07000200070740b2a10170700c00395171010340d06617200030040050000700643c007150f00c240800d40031000c0002c00c1c01c09400516114807010740904c180d40ba0381c482050aa1445400e58886000340100d0356074280f10800c00c00b240f941449039100c8035400034002400a401070190001ca03540c01404190001d90507910150300307900c0680b0318860018042004103411300c000010418520a0300d101d26100c61851800a00e800c1cad1500c0482d003180c1c5031b0107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 585266798 1250 585265548 585265553
    0x1516122d08040206090a0305011b1707170c0d0504060c1101050c0f18060714060117031e0c0f01150f030213020708120703051510020c0105180405040b1012 68
    0x3414141c002c1da0445042c1e696460300c00000d07841402d141c1029180d03500e4803144803c00300680075124610100c030780740c2c40c0100703400076903c0f00c00c03210032940c80011501407441b001c0c0c594503052201c3c1d4808480d01942d8106181540d45038115841100c1c112600390360340c480800013a0b0480d5104404141c500000d010516009000003060b0080c5000701d5418800404d502458007003045044c413405801501c03940d11100c0a0400b4841d031015480052802e0159a001240407414003070000100e110260041d4948940d05003c2070100c104890900301d01842881840c088401c244a82c202026018002142203010055080402d40d469840b024400828400800c0180c46010451940b0140000300503280c18075801c1c180d10611030030701d41e03020700780c41c601c10404800c0d05548114098050f6025140040c1064410b002c051042d4042840160b4020051011103600c141c0c0280004180301c003184001840b0f8030041400e49005803021070300b02e4041c40800000540c0038040500408014100d850f10704201d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 585268048 1250 585266798 585266807
    0x513140c010207140d1a010509061219020a0b0d0606020607020120030411090f01090c0302030f0a0507020c030703210905130903090e0a02180604051516122d 69
    0x80c8220381d402a04c001c00503840395125543c10700b5468029144043d07402c04008180650b100c00d02a562003a240b00d00802d03401d0510b0300506502c545801c1c01042485c05c040030300c3c0300050b405041240c0c0001e40800114110742c880300035185140d00c560020920904010002e41045801003894086a243c00d003100d50302d00e15216802a40c60700030001655a0b280c50424090800140000766001007641701407050103040e4002d16412248646010400301401c840d045080c0d120949444102c00360010101d0317013038029a408141c0126840c0101c0d0820341020340482d013462000ea100355400c10b0008041101e10000150030300d65a4440e20303200b25210308140006030070020b25103116299682c0c40840000301406600300c440605400c15090701e0518110340e204002c0c1d0300a4014052220b0f14200481c89800c1080c05d560591381d0081030500b4903009081c4104643d048080100c01c0d03034480c011280d0105000c0c4503503118003801075950028a0302030500510741240c015110030180740031820442d07034203070b0b01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 585269298 1250 585268048 585268063
    0x10f02070303030e030d02031f0e310203010e2a0604031e3804020f0409030311040323030322060f0e07060e0603130f080403060513140c0102 62
    0x240c240014034401d528a05842c44c00341c04071341c100c210320000c1070003141104d61030586000c1d00c040140c0845d0b03e84505051034070190503900c6450510000d0501c400301d0300d91180080310800bd04040440e00c00070360700001e0a55456401c0e000e41307034001c401c071300e0480820024000c1c014400120340c0051600044007082c111b01c1180700c0603002011103040c009220041a080064040e041100000018540070001000f82d82e41c0103440c49403220322a50440011000200b148219002410001d5410b1840305200190100f03c0781241015640c900c00c413101000314001d48055402580050803810365410346aa101e2a04034281e1040d9100344100110303071041690907800c4c04005060026508400d03e4a031002d0400c0d007501c540c2003410401401209400059803a04544890f070b120400031030544203000c0d8520045e80c4175800d00440f01a0b00c408105501d500751040e034410240c07140383c45e40d00d48441e821079606440c451055048111030400703200c4642ca8108070b15038800c0180c80b40d0301c4001c0003c1d546d03019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 585270548 1250 585269298 585269303
    0xb06090306040303021317190f08121905060d060203090307080f07030306211b08060711010b1c0602070807020a030c140a150f03060f06030501051009050a0b13050d050a0b06010f020703 81
    0x88c02045041002110940c403250340e1009045844039485015152403040803140c1d4140800240303c60101d0200c18060036002d80d0b80504403600700c5c4119103c98020b940f00909a181501c03080003000005101303940186800e02c020001d41c0d0701d4004916004054a0709a4064070080840e03603540007240080d291000c1403140d2085440d880c241001101c101380b1003965000000c1800340d0000c008195030880d1100e41c3c4500400300070000d6aa480c1c04000040e580c21040740940d402c0e000081000030300784d0303006001590041d540c1d04d040188a0f40064030305e1285070000c5a070140208030030045120040c80f14403086904659494840b400d014100c01c0c50030244a00104010001c0b07030501125000741d0007000a41006030a00c440c4e0394654402a0180c5000e100c0c0c41c0c0103000000f03500c180e00d4420714103d000e41d07000610741800301b440c10840e80c00d260485544041c03004d0103100f00007019030b40d509151034a035200e04098801010300d030402c6100320000a003c18180010070f403000385519030200d0b00a0907682d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 585271798 1250 585270548 585270583
    0x32401141e0103060b0316030e060c07060f020c0d050a090605160209060d02120d02073005030c06130317061516020405010b04290901030b06090306040303021317 71
    0x81c1c000049001d48860742c00b404407400b0000600c554540c85030101700d8008219101840744650909501da560740c401c80308003d003454103000032400120a0340213400e00d140001405801c02810313498043c1003130396404034200400c03000107419000f1030304000710400030441803e040703041035a0031016004151508900a02c140955000178419594181307202d2506a0080d005949000b0720300c020f60b641d0f90700303c80401c000d4800c115000440200030380b003803141084101b0581e84003106800b21041070004500040f41c640c00203006039424060108042c520480440036001030505103410060000e150007840c4800c4a22094100041501c920640f000744002d0301880d160758414203400e86100c0c0404540081d030141c00c1c1000001c041424901600607644c0740c0803400283c4c00c9800d10104204070f42c0c50203080c404c805100c9034413590f02a61000c4555030703010380800d142c440c1c40f41c0024241030080320704401096010030301a2008c0039080c0d0340000f603c080400043c4801085003855034034408007680d035401c038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 585273048 1250 585271798 585271849
    0x1208040201170426030105030c0603090a0209090703050102180103060b0901090506090103090c17010b030a050a080d0f0f15060c030207050904050f03030115031526030903240114 78
    0x704011110500311814131030246400018500c0c01ca810398028407400c0d209106611180800b49041401c0f0707405943c030600101280030059083c008c03800e000510246030b0b8000e88070000045102800100402c0d80f510503200c494907081030014003140d845401600344000144201480c6036040544002514812a0103070748824802004074064501850300030030f016a068400240c500d15915260f41c8091408024000c150044c818165605680c0b80d010b4a198011580040403420010080515a02003900480d80f550303240b0340c400544104030303103021043c0e84c3d6100030307280200e6040701c00000d08100c0c0f40c003070200f0384c0c81d0300c0003951103c00d4018184a41a004042410000101b11080c622070980b0196500e940e5540b013180b20110488001401103814400802c1140c00448241016921104100320044500151141762003c240d04035840c070703200030009140d0b10b540c00c111003094a00803c0c0380d110300055808541c2c40b01d15041c0c0c40440030070284119840940e8030000c0032a01c4100c46904031048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 585274298 1250 585273048 585273053
    0xf0601020a170408030c0c03010b010804051506010c0c0e0601020c041b1116080d080901060e0c1b19200a030201140904020715050711031c090c1212080402011704 71
    0x3d2107070b54040324031480002141420040e000c5503401c0d042000310020042521100c0064404810803940206240c0000da600454102045000c0e82c01c00810301d808a507001c074650b541d220403082d5070130402062404100308002e42d80c1c100227003443e04609440c140441c04da801030b00d4260400d143e070518203014440d620368060050070007465a03400c01c1001c02211042c0e42c0c1450700d4a441d141c0341c0c000f00286442c00001d0324840e050041900300c503490058004550f0f501c1000ca50144c01206169180310701d582035400d80a10b00308101c01070781d444a9034180c01c0b404e07a880c290020707140403109003c0d25042021341076030583d510000c15007200e0302070070f201e260710700101c455409a200d070000c92039002d03201056080c244404140c104069090486040240d9210b0070341c1a20a03607042580004a40c2c0b0406c02d44c000d908501480d286900210070020503140d80741c0d550410000e01680060360886003a6851906019041501180000c12410080881e061540000300030500d0010302c10016200c08002c42d04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 585275548 1250 585274298 585274343
    0x1104090206070206030a02090a0906030b041e0203010f0507030e070e0112050312070f09050105070209010504020c1906092102060f0408041502010605030705030c0603160318080d050f0601020a 84
    0x2206035000f01010b17541e00d81054440025004410b00a0150649820100340341c0030510845098076000070512899664a035650600010012141e0707a240c88600010001a102401219802d0f0708182c0c000c512482d2001e001021551803881c0d10040c0e40c010b000411030666030b401041e040d903281401603010035201d0f0400c40e00e94403910301e049240e00380042c104200c83d54050851080e8001d180c2d034115040c1d5403070004440342c0c001c102000e035204e4801c80040005140690042c104d0360555404c2d196075140d100030720090000352600548081c0e0701c44d501002006200240700020115000901b00c804100c014001d513a4400242802401c21282e000315090103180c0e0203550003401303031190088010140c448028003803e91485094040e10802e280403440740390104007146004006403419045940ea4050b81d801801c980f8940002d155560b400c500600802440d070ae86040e0160000302d0b519404551950b0840e040180000401801a0184072242c2c0e40441e9030105550404d49024102c0050861800c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 585276798 1250 585275548 585275557
    0x50a1a0904020f1512070e010f020c010305091002121515120720030a080106050406020c010c110303221d0a09031e020106080c06190f0207050d08030906090a1104090206 74
    0x1134404049902c11141d440c14007501d2007801ca540e030762610840303c9001034510700300c07142601016801c06440071002d940b1a038020350340034041d0f0301101c3c8049607018440d4100e0b84840702082914042808001214001404800c000381c000e0f00c210450030400c1c00060038500403070000034409200107000c02c958a00c02d41903407425440003030b12030440900000203241d580d40300d031010001140c0d8034030001803d14020405e8070115001034014061128a4000444000c03120302c0d402c6984d2007441c070071040c031614100050001812104260004080108522480e4499541c01602c0b4410102960079016503c0c1e003200741c11040a07000805c02400501e01070303409910b40c240210351b001500c1803001400340e05400040441c1c90000c2a10050010002840414803136100600030201d104044140494412031701803a07003400510540d1010f0382c0701e40004001e40002c01e000d0b1503010011003481000c5406100007900105154000d00c080501541c0c2c445200f030340300140a2080b41e4640c9400b065464080444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 585278048 1250 585276798 585276829
    0x4061401060509040c090510260c03090f0a2d02030d0203031801050105100807050d09050705011403040f140a140d081e0109180f0303050a1a0904020f 66
    0x265195a12080000c110350031640d10544a0760a0a90f2002c2e07050041c1081000c0e184060405190f01341030b000196043d01c0c0107107002500c00c2d01500c03101c030140d10f1541040e029102c1040c80c180e80f41080b07040c880c136008520321642e0302c0d9000b0010320710000e040c18091504001000e2004107a803d0b602d10003030254103010300080d4040c05085070084d4480c0d404002113204141c0001e020840000d13031002d0320f080340e20901950ba0040c442aa4041c1c84a01504400354000d10500d0854a4a100001381c9015100b4141d0215001c1c4e100c603100b44030f19178010000d000e214424450003421441c007034690b080d090b044220b025101d4410303010400d100710410301107040d856800098903000d0318207420b003603540c0f0b4002c00305000c001603041d800b09558040300a041d81c2c3d6462076031904112a405c00c031001c40202100c0303405030580d000000000001030640c081d0800903600980300000c651408000b03400c190382400d03e03070b0003042c03c081840c09059507900307010320b42154050702c5200c12001c0090100303000005004d40b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 585279298 1250 585278048 585278081
    0xc090c160b0402040609020a080c090607171207030216110a1d04140309061c1407021b0306010b18040209061c0b191716150318020306010e0406 63
    0x1080107001c0e1040c0041d0242d8800c0d2400c00480d0390ba030100000320b0141040c00c0300080c080c080425810301104c40070b070001d504028200c62601c0d80680d80c00d0a04441262084008540803900715050251402260b80c4801e10b0f040541c5424400101810588085000180155003180380e038041c684030320014071b010b442a400c0014003184900e0440480040403541250394102050810646020120a64001d254054801401c04a1024401148a03052801e0178001d50361000905140001d111009004030926005411882807492210300c0c01c00b41e0609450103a40807000421040e00030400b100e1090304810030071060039010000080103482400704065000c0e20101d001d00c03080390602c18007001540140700820400c0c20440a1190545915900c46819034807421b0800481020b20813888240180100782c8680e03146400b0104c0c0108400c1d0416112290030b4104400380039014443c803481158052441038000846900003a515001400303443d0741c038002940030504109640d04100300c000c441400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 585280548 1250 585279298 585279337
    0x30201140d09081c2009090c0d0c05190c0506240607061b0e0123190e1203040f0b2802030a0e0d0506040206030601111e070602030c0c090c 61
    0x41407aa021000c0710b0104e42c05140c4075455070806404c255120700020a500316500300800c410820513100e078003c200041382c035420032440500c0c0c20144503064203030100c5d88a003030325200100c3c2043c20455a0720700070024410045e907540003051000401e0b961254102d80030100142d03100c0300940550501102d1543c00480200d0328008002107600180a0844003801c51400040000000c55100d012030041901107641c880041c00ca04001031101c10744e20101d054854a0619181ca031a503a468415060800058804110f0002480c00100c51140002c0c031500841c00e06013820410003000e5154894410013000010740801008104014a40c42c24421800c6520744981580e0103510b9600650507400011010b403201e40403841c0481600c440c0c2e40e041002498559156400c0c080303540d1001c0e15079030511030300005a207030480d810031540c24180350541e06031000f03852104503589890341c0c0390440e80542d0003d02400b95000d40000e8000400482110181c10503111020783c1d0765148503500107251030028454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 585281798 1250 585280548 585280567
    0x1701080c030d05030c040b0a0c1e0b070c0314090103141e070801060e1002120706021312030c06090206041203020d0f09060f0e1f27030201140d0908 65
    0x160410a04829410759940300726048040707070180702c1141c42170300c1541c0c02d001c180200181d50001d0203811140381007141c2054511389860101078070101c100054011176440520800c01c0e04495207030080c00f9400e01c101c2021090b9030103002050722007007200703c01c04c0200b0400d00c0d90780300e50016200f00030b21a01541480c18003407420480070045a2840340d10a142001241c0346074810885e0038102c0d46107a41d820242c48101d0100070441000503070800c118450001c5118140d0b1040008110191261100594600340600c9200c940700740c5920501c2862032580b85032000c07076000303607604a8140e0301080024030721440c1e01c002445401207401080b400801100a0000c15030000340d10380b900150b64030f40c1080c12245120444421030240201710010b2480c010a00c0c0140c010458101c103214000e0014810a5105103a0a485a49141c550300000c14100041180040400300540360300c803072800c4040154150303000030304407000040c0300300313070742180003c06015405255004020580d481035905503034a1080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 585283048 1250 585281798 585281803
    0x41403091e0619320a030c030f0c020f0606040c0c140708011505120a080a0f1101020d021309090c1203052206121b0e0a0b0c0703230a12170108 63
    0x1141c0b84e00140c10001340c1810500d0215040103091152944040c9001c28420303044014181d4a02590107254440b4009202c2ca1014000e6050020721036000307140000340814440d203008000341000c1e000c2e034549030303201008682c0204c481b442c868101c10f0b84110004030307070b06003807500250354001d0400e540303408500c0410440408802040324011548031a1001803042c00c03030b4807030724810001400820100f0040b0b1030b050081440c4ca07100310b06c6040c46603a000101d5031050076a8410002900056800034110a2029658088502400c1c50070010170080005030b803003246d0f160035402030540903600b509500c4105807090b401c41d2820390381c0400307602d80b50300e103203a03840c107109600c2c047c0380042074110341102d035441064496010b185810020705401c8a150140a66144014a42240d0000c2e401030010581000d08402400d51440c0e10f4001c2918600d1410045807440007070802240400c0c00c80c0701042c500d1b00020f061440d00c1d4011150000510140c9402d40e0150310990141c0d1104110100000b11104013 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 585284298 1250 585283048 585283067
    0xf03030b150c06070e0a051801080f0708070e0c0409140106120c1d03190b01090c030c12050a0612050f1603120503042306041403091e0619 61
    0x5458424180c00c0000e41d03030016029004140d6071a510000006220512440800300c50920290900e40340070303190070228600c0c4140d2007950550b4200c1c2401004a0b820411030241c0056200028140300c0b820040c100d9141c542074816190b03c0044200482c0d0f18dd014101103070010100408100495108100194100c560921030a000715400382d21114a25540d4061b03c80702e0b140580c1c901a4502c0380410618080902c0c100d900e802d84552640003e0000060007030f0408140580d072041e21961500c015941a40e60550450f0205810004441c072080e42140400405203100305000c1a5541d80640e5440104551351140003c03080347c41c10481486400303d204d90280064900382d41c07000f2085003200c00c200300c1a100041c5070390042c4d44504441c611641c040c1d078100d0b03c81c8082d421601c501c07240c407a46039006908440403a0304640107100402c51040c129602044145000e1403c001103500050f05a40c0502c5c40045030502040ca0078040344e81d050222100d6072400000c4001002d0059001084840b2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 585285548 1250 585284298 585284321
    0x40b220609060b01021603060e0c030303040c0e06010e01090320040f060609141c06020f0d0501080c030f0705010e010c060f06030209130f06090204020705070b0a031d030d020a0c0f0303 81
    0x1d454192111940701080c2d00c0c4151b40f004560182c064955514903000b0304013042e030b15810340140958145180c2c4c0600096008500400d2500d500d070303060021030f60903064080c01144c14812030700a40c4540c0c0e40c0040380f4504807600880c2e031103407844c040102e0700210310740b04020b954814075007040c1c0000120750b40d00500c2594102c0d41ca120003c1c0e01c0c2c020142c000b100103502c265101e05040d260a5000007040c036040c8906106480c0942003840080301c2e056076400540e91403010680310401400786880400440c410385134220300500076001014101c5071900440e002e018100304806132105480d07400b4509440b092030340104208100301f40700c00038500818447c04100e200b203104502260054030307003403030040107550080e130f0b20300a15106681d4040245a41c00040360002e400b80509c10211b641403100200070550180c0113551081030020080440d020744200c0d240c0e643e61340d070a11000103000815640080b126030001a580d664001d01131361a8001c0400080a00c1c1d00401d4400400d581500800c00211 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 585286798 1250 585285548 585285551
    0x101806020f160302240f0f04090f02070b0a11070f0b07090f0608070c0c0816090e010246030e160b0a1805130504020906030a0506040b22060906 63
    0x102900300c0307542c84002d24440070307500459600c203541d502400034502c3c0901400d900710152600e681c401141c240360b0002c002001044501007010800c13000c040c0110703c0c2c88001400218640030715a40c3da020320000c06071840c07a04c15070b2035200c690503031070820490300c00f07907040b80203c12061414076000c0b803c0482100c011002503c0f649001400801410091040c2d4000d600c4d07660040d640c40c1400c40d0f00d003824480555401d5242031002460344800d2008110620510800000c0e560034421b00d4400c1d80c08541203910700782c2c410460070380000b4030038001108941e1003418000380d4150b5400540c0c40c0c0003e80781c207159100f0403804c0c41d001003501030344007480d040401e105031030300702c142d00c800452100210310980c083c442d005c015128120b407041030498000c1c0179100d039450301c494a40c0e011402c1004a403a00f044006d940317034180001e52804001c013a501907000c400800c0307210300694646440e268042d01c0141011014400703d000b500c4425130a8038102c007161080003210782e490030424003038541481c003940c007139 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 585288048 1250 585286798 585286813
    0x3090504111b030c06010b09030a0c0305030702180c0417030d0204080f060c0a17100816030309080c0d030c0305121009150803160302030903150f07050306090402101806020f 76
    0xa40071044d500006000400740015a1034464200c000780d220b11031440c0e050103400d5821000030200400480598007550003143ca402c1c491060203411701c07546880c03490490805040004051429003120305840507900500590340c510311220745140140c00c400501030340003190114121000243d0080c42c0300540c01200c00603201c10300003617130314860740c40c6100005060724015680d400080c3d06254004a0a54030720b82c100741d403003800905040e05004000b0b00450b1500081051545c441c01c0d500c064141c3c10041c108400d6008001521280906c41c02800d006c0d40601076410b05000b8000e9429643d5042c0c1d2160b02072805000049407100f5600a080082e854080c03040c03d83c10340b60312880150f81180c03000f5031402480038001580c08105d10421000c6210800c000c485a440610041614840d140390b0802e0508020741c901c2c1c4012401011401040303410700412000d03070390390082e50b030300680c0540e4600400c0c0711000c1c0031a4103c83c09003c0e07405011080400084481d800101d02d1034516040c1c05464a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 585289298 1250 585288048 585288097
    0xf07060e0d0c1208130501050103080a0908030906071b03080a020105040210020607021b0a09020d0b01020c0603070903060f0e150703061d04140f0a050708010b040618090309050411 79
    0x11542645014107401e101d450a00f84440c001e000503504046020001d44009603960b03281402e4600980003268400030201f12040fa042d0001511000380003188060741c202005540440c003079009810700a030041601891500d50b03c48144600c8019540080328650b82d2212004080d01a041c2500c0403030050885c41c0c068403c283c40400e009010700600d41c080d040003d0811038801800c081c203860558860000c02c40020020307034030b00c020461111710030004940e64107070b203002a0800c0d41c500c0f0313a01e004a1041041005207540140d00c44140c030f0344560000b44000c00c01104200801030040c00030340c00e00c034002844000c2c8119200041c4251040d41d0280301c03031070710b845481c0004206410300c070003011400030104000480000d0005142e2000104441a4403800344160345441c12414050f10190080c070b0040c041480d003801071001ca50b0303040e5400d002d10b602e8048500e03025148185800c20b41503903a0110002c03d80b007802c03080001c00e40203200b40000b5082d6522004542e00c030886040000303000f400002d11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 585290548 1250 585289298 585289307
    0xd0209120f030a1709030a0f02331308031b090607051605040b030726060c0403062f0d06050a0915150c02120c03070605040306050a05090c010f050f07060e0d 69
    0x1044864401031402d194841d6070955031501c2e234902030700650040d6500840e100105001c0ca83d0b807050a4024480c1c44040c0c008583c00100029119241600700c0b42c0e07425000c0b034401700c2200d400c01d50125542d802e46207004680441c83c003801c407540764090000607c0c0c0c4d0500a00080f02c54001e01d1401a4820300e650300d10070402204c84841030711b90141c10122080200c03490101c40f00c8202c00031072000045410400042c0c1d414080100e0b03d81e828440e0124080c01071010b21301c41d80c800f0742107000e03101e03510b5015142c9010542095070113500741d0040018181c003011310031ba000700e001002c002e8500d29a03940c480782044040e15040200242e059000200018100c0c1c1800b102e442c090115140c4910300c103019001e00211114483c4102000d10425895003001d0b20100100d000604255039090744444c150b145c00b40c262000640030308051410710090041c1890041000e4000d41004d003803c03460307103482202c10346032405942d440d426445d60200c0c0d408280302c0207801400583d02e180003902d407000032030700c010384 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 585291798 1250 585290548 585290551
    0x30e030303010e25080c09040605030a03111e070b03130b07110d02071203182c150f1908070b090a0609060504090b0409080c0a020f01050a050d0209120f030a17 70
    0xd0000c1c80d08004290640b0505001f0082d00390050f2001c1809501c900100b4602619a00c046000480c2041203201504050124412100384d07429130f10840b14003c640c03627950704414014a1503000300040800d100e40140c64501a090b075100300090050318000c040030f40401c44413401244140580c0040b52440303403010501e10269802004890142c2c2001d8600700e40d4041e002a0000c0003000c0e9800c040380000c40e001007445030046400054801c810043d403500031110000d4001170300d01e664401c1492035559285a0200f01110580c1d121603000341da4400602c408150342e120704c20303600500d000420240c62a4000742003001054904c0d80c01c2075640c00c0200c1c6c8011081c81060005103007440244840340540e00002140b040081000ca001c500c5034443c0c20305940004420059680b280c240340085051098245034000ca007401c0187c2485102c02010b019441361103030889401e0760000d1119203541e40e50301c0d0321248030b007460200e52410040642c410f65039444030902c1d0010a45d2100e540c100d5081c004100e6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 585293048 1250 585291798 585291871
    0xb04061707090519031502030c0d05060f120c03011104050a06110703121206090b0f0d06061d010f05030a02010e090a061e0914060901030f030e030303010e 68
    0x205031600c0840080851500685800708100a00d42c001685a03a80c42c510007204004c0140d80d070040f40b562400001c5c045401407802959401801002209006541500c0740400c401c2e0001c01c06a03104000603000c81c480001003503010701440c8182c00030350800a80e61041306030540003003080e084842c1e408600c50007a803068560042000700103014452289140d113240c2c40441085920550300c03941d424049002d070294401c001414094081034090080c002e940c000d10188008000441f5080301040041c1082940f1a004500c124006403c000e40c90b801031006008454401c064800d00141b07035070807520f082c8599004003c40c0200410645000305107800010f5058443e10400c01c0020203205441100030303d1115070b56079402001032005002400108908a402403c03e610f604128a0404940409142c541903840c20700420015490f011580d50540c0e40001e1100c11503810740c42d04a0b034646500c403400360180004000000c42000d00800503001d042003061086607401940d001000764240150350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 585294298 1250 585293048 585293057
    0x30702011415032113090203161d011805031c090f06230909010611010f050411121e060612030a020d080606090618090c040807030213140901050403090b0406 69
    0x80e0130b400799003c5a0103158a2505203414148900003c0f41c0c0800d602e907a118086460300001041030080340c01d88107000031001c03410405039088542508420015035008100d060214041046080c12108817644004040c010103c1e2184070400040840301c2ea4038120a50110300030a501040c85402c100444043c1d42d1250381d58101844c1c1042048189440c0400c0740e04000700c01c0000c01d03450744039180b265020b0421601c07900e03903030f00c0c1c604411800c4985032181c00c03110924010511001a00c601c00305429600c04940100b40101d1120015080170b140015041c0e0041910000c8402004003207801ea2166108466040b05503850044a503180d204000d44100140c00030801304c200705010308000c03a04040042d0280b030030900c803100824615440186151700580c6030800310301d142c1c640401a06d038054400401c05080a01c4c00070510780c1c8100901000380316180192552114207001e81c041c030201415480d1140003414848030260007003000395820340c002195004003040d6050900103d908031034240e038a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 585295548 1250 585294298 585294313
    0x40b060a021b04020706140906160903060c18140901240810080d020a0b060f1c0204020904050103061b031a01110f01150e011a160201110303070201141503 68
    0x8141e2540040d42c03030625070107682480300e00041481486052400548149448a90705103015207611300b50300108010019250080b8071100180c1c040c2028048136403144000ca940f502c140c0003a5810300d03024000201c0e4412001c00006d000082d10291405500207607155a0141d0303e4119190201010703032181103c0d000300010b9002501d100d0743d4100c0d40a650310315030046554a544030b11b82001c00000c10040160f002c0e07040d00003030002c4031f840300e60400c0c002c54170031000c030100e503000c604c2c102e030541003010491015889100540d00c460701210700c48503000380708000c0f640c0c48c0c0c80e0040003440030182e405e10000d000913502c090070340a0b1141400d188030004440b00641290801150950b1030341d9130f040c07a113004d07420b00c6844400e000d01404550744040040111a1810141a80b04c440c0d0160302884e0340380c0c102e940d0512005585402c82d82c14200c00c0c1c600b1b104c140c61078001a264500c004444807a07601c000010084080ea0642c80050842008010f903034191320341444900208009031802c0e940341d0407458 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 585296798 1250 585295548 585295573
    0x411030601050d0f0c0b030a150f0302010f110f1207030e010801051c0c09020a170f0105011d01261e04050601090221010608072c01030c0e091005040b060a02 69
    0x7109101d00034450b2401c031103017503204c062030440e0b03810a907540030185450308061600f4400b0150a40301803d642011f11180a1458000030820690303c50501c0510000d004001e14040c010b009454009603283c04039000758214942455060348880b00c20740005244146400c942d41c440c03c00c9071f041300c50080c40c50a034003140c03042c2c40845083c5118101c0780410300000018030202c1a002034414489291036100d0b03100c1520b0104103458100030f003000c0101c808800140420ba07080302840f803c07a010310b800c039044406034000503590300c000100002100080c00b0a10135607400d8a00002d4410f0f651090091084104c00700c03004d18aa1041d6402006070b0004401401045250740c080c1c40840050309401018500c00750b1742c091004402c3c0c011100241120081209685c2c00000d6044012115001e40c01c0284d03000c808070b4060300c070f0040028109030700c4da981c0d83d4005118501e0b240c04110000e0034441c42d800c054498a212050034402c035401941843c00e03c4c60249070030000c2c0c0f607080400e500075106070051718 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 585298048 1250 585296798 585296813
    0x80106031418010b360915070c0b16020d02121903060515091c0f061d011a030c04020c0303010909080d05011811031b0309010e150411030601050d 64
    0x2d644035050b6598070b0744071000c1d6503074441c80c0360144000003569003442c90038200711503040d68210010b8208034a46003804000303400000d11041c40c12203c0c542c441c0c1900c603810100d40340482c044010380380a444006100110500c24042450100550219404c1460343e120a0b44c444a85c1203000a0000c2e0500c40c03051240780100356088118018130f0009840c60302e550014080486400d502c0000090224240c009410680314456080100802d0580e086950396540d50841c05448402403019403240460207a003074030b005038507004964480081c0034000aa8442c01200c000c41031013a8841d05c5000387ea491507080c584200c40c200940d42014618603030070b0100107005044d9170801200c046504100b2034144101500c0351034041d00040c00d006d55911030046178801a202141840302c110790f410070900c08140300a00124000d0140902d4040e10307030f07960b442900d0040c10001d40388102401100340d00b00a51450040c03070b521461050701c02060401c00303042030651300c05c824081d85411098080007c400300d0f000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 585299298 1250 585298048 585298081
    0x304050d081608071103031314040e01240e010b031f03060603080901200d0c1e050a0312020c060609060609130507030f11091512010303020303070801060314 69
    0x1001c101c0d107081c1d000764001c1c982100e207000c103540710b44002c1410020400d4000542c00c680c00101c00a5042c880140703a090051081c43c030446172051188004100c03181c50396049034101e991820000c00000d00305a01404552030f111000300d202d00088400170583c0420441484e050300c07409842103085507070b141c1408500d040040c1403101c40c0740c190200000000c42a01400c0061440b540407117855500060025100421098030b18920350034622070030242e40400103600458050910b0b000c4030082c0030f8203150f002c041c259802c9103d0781241c52300d40018400000390025880348245d0b10420b00428000c401d504a00810123032089641043c2c010492a2401c240001e402400080650b8038004a040010340c4101c3c0200b080c4403000d480300108240240c25201d9243c00700c80b1880d0a02c00585490b900100700d1181003042442001070030245054500c01406030313103080080003103841041d6180e00740a5580d40003101c0c206c0000308140c00102d40244640210607030440100384158291300c03549070580310010f5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 585300548 1250 585299298 585299303
    0xb030a0b150403120e0319060f091721070c030f11010515031605030604120509031b150a1e11070603060510020604020a061d06041d090106080304050d 66
    0x7840600e41407048041008000442c8240441c4154403141d19000d007814145c4003132284241c00405c078083d255900d62035409101a032019000400c85820240100181011003018000c58069800603440105910081011001c4090715542c41c030b4400b21b0011120000f03c8540d4009000400030b0350000e80543d8100c0314607141414440703002d800c0c80c00820f0841380c0844030002980e1000d640350610341404d10040f03004141c0040640c1d1400c4c20007002c80d5442001920080445a04008108400d8401e100340c50821b5802825103000031400382c52203003510425460f29210b0b18a450307081c1e10812441048406122198641a4815680d11941c0301451204010841401002030344204402c03824444200501455100015400d080000740302d402d90141c5406800c4d0740c498000d10025a8034240d000b000c4030701d203192411004440d80100c2c501c12407110101500200c01040201e090002e40d81c0c40352116240d00002c1c1c00907910020400d0a8450b0b9100c0c04e01e043c2c0003040203120794101510200080fa0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 585301798 1250 585300548 585300559
    0x180506062e02071d1005010f0f05031f0303020f0601050d0c060f020c041b020f03040303020c190503100f0b0904030e040b040b031c0f030203160f1101151505040b030a0b 74
    0x83d0b540e98a902c0300c603210700c0c0031040700300b404c81000524001207002c000900030a1914100700041038030050141c0520342c0d80c650a0000100000d01c0003a41035041588030300303c080b10189855a41e1501035a507034881c107000c5005004d224000314043c1000654a8007481c0c216400e0407802e46000070647d20607820030521411401428050710580e215400341c3e2035041d40d0b1500d0440103245c160402410b1031159031440100360000c200400201c0d5001451400c00801281c92504821354240f0700b030840034140e40660b03050f000c1c01c1d15203260180a80d110001510400c0304c2480307540c00715400c025448504560060105460100b2045c40d820241d200c0101c124000c0e00000d0b4800d40a4000f92401014070f408440044110035511184c0750702c54600e03110444a403e05504608150030780310500ba00e15050306c81040074030480540450300c100110a110b1540400801c1608400004101c20080a001c3d5400e10707101c5814420381d00e403281d130480b0226145039040034216200c04400c01c0241050080c0140d01c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 585303048 1250 585301798 585301813
    0x705010309050a061a04201210120308010e0603150c03062803021206070801030b270a1403040e010b031003020907050a1d09040201110709180506062e02 67
    0x10150300c60705031445951000c04514030800170070841030f501c4828044003280466030110b1100c400d1801910985128001c02c0041c81d5210310b100c0c0301100441d440203141148254054090640006010f0b0581e1884000703100c0707540d00c0f0400d00d9070790111001080c1d61200c8001c0003611030180e000203143c00181c003d1030641a4444007510038001e400106005100c0c40494100308118a01000301da5114500100904104d00c1c007880040c20800051002400e074068450008155500c001c180c4209600245614615a840c1c082c8290303a131420402d00b240d070380f51180f20040403000c0001c152422100040da110416a0030700c0341648040e040a4080e00c9900020400480141d1b9402e00382441180c0d03561302c594a900b01e24074020030b24045416040160824414807040036101e600700941e0140d02802c020090400c0c00c1440b034a001107661151101c54030b4681c5400320710808000341072000c1e0040040b21619110348041180c0c5a40f034103007011a42c009005206440001c40c2004100c00950b4010350362007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 585304298 1250 585303048 585303053
    0x1e05091807052209060f03020306180a02090123060c0d11070503010222090b0a23031c020f0606030d1b02030307060608061513020c12070b04051e0705010309050a 71
    0x11483d03668400050380401d00b403e01c1001214400d4000902028103103402e140d140d600801d40704d00300901f088400100e0051001d0711100c0801c00000b08a070301629100056035900754015652002c542880100f03504649042e07420718080c019115803440800c00b401c4aa0010308040c0c0303880d220003041824074000c0640011f19540c2c28400b40400382c40c403041031a401c00c3c8207403600c40c41a15980084038024505264030f0001d44400c5600c6040e507c0401c0d002408003810050001031440c800080b641c9031185903c0f054880c042c0f15070080d5818229002c44940c60004030002e516541d00300c4030705415500c02c915a900305841400c601c050421402c18100444e01580c02290545e4450141612029240d0004000c000790811005601408050364154101c0e04070300010304904216084003401600403d01d8a80203401380104008038134603000e4144c0d900b03200d01d40840000303022034050310140074103c1441d10030440c01501459202c40030010b082202c1c01c1900540051042c2c02041d212486082c0340e4100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 585305548 1250 585304298 585304327
    0x2060f060f03211308010e0c061b0724170610140c010504110603040b010905150a150f020d1e1b141603020f0d020409080a1e0509180705 60
    0x4020159a03001030f902c40208118030801310300c0e82d0014030960700d403c0c0000c00c005004981010b99580c00c580032503503081401d21154050300d403400407440902070b115001908000c80d0000b40c0000b140240b4170002c00c400c440040d600300e40810341a14020424000085040c9040f4070b005200301c02034100500340d201e03800b172640c540b80c00090000700b66a40d64018001480003480c0000c6181070120746144c0346140599420100300010312400b002e10352503a021030a0080f40c10b17460030351000c000e0800d07010f82d55102040da1a0340043c0c0c04500200d10b400303107083c0300c484c404180c03401e1003049034a44440f0116511211851602c1d8490b0550800007484003106903000c222200f00f600c54040c20a40a401d9241840103040240d040e2101c01c88014110701000141c03181d2207015015a0101c4030380031018501c3c00428040c0ca503850000381717a01800076130715421380d8000c10703091041030792424000700c101c04802090fa02441014034040c2e21281149050740c0e50007004000e00e60002d607d151644c100f201d40341640c0d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 585306798 1250 585305548 585305593
    0x10f1b2d1b1a0901030e0c0d0321020c0a12020c0a03030c0c06081b0c010902061614190b0702010b030f0a061b0e060304051614030c0102060f060f03 65
    0x85140788078481c0340802100d0007112602400a40b41920409580d400d850000c1c1d1081001e45814191a0074021508003024070142006040190044050310100d20303005080404030b51a480501841000d001014602803003919034030241c4000502003403903280c0b129925038204040c11021072050f0302c00b41c03034151075410080380194400c1c0c4584900d003a840c9414402513005802c00b90420580404100100c14003052500000e00170700f001c0f6a40c3c1340c0705082d02d80944049100a5044030b03001410008000700d031211b82e00d01500550303a5098004014210742e4030340d4400760304000c1d02c450400d0144086400c1188140c1c0210a0740000076055401b000842d040280385070003000305030881500002440014010395514440d0448407041c1401309810282004a1492210780215004000181040020050906800455404106241d507111081001c80029000d0b55009008008201080d940001810380c0200300c8010201d8042d80c2d00b405200800308211811541031080c420100b01d81e0031025501d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 585308048 1250 585306798 585306803
    0x70c0909141902030607050f040f0b040807090903050913020c060405100608010b030303072007091506022a010903060203040506060907020a05100c090312020c010f1b2d 74
    0x221540490744006410b0440d50004042041c096186500040e5000300d0031582c001d4603414100d13141c0344400403c1086001340d42100710b40c0d080418000c078804e252000034000721030b242d82c01c446855071610505410748131144c4000307011030720a2081d14803e15220b6502e680c040c0105000504141491442c0b52818200340ca00303440365005040304580c16400d42c09100060001c0c44002d018110b004008031b0f0f07aa1000800013003c1084600c030001034000c5031044007401c2e0a152086804072510f84880c5030003000c00c20020f8540d590f20b401d0003d01c1500108840b070030780081e00c20710b911039090104480c1c03442c4540c061030f904001400c100071000546510180d8021070141c402031000b440c0000500c1180b4501074801c80c1558401008440000c0c0c0c0055011450800c000f004204400d0070b090035900c501c904e4000500c08807044a0151001303030f0018445241b00c40c241e0303900e00c0050300488184c800d00c0408850b40f10b5590200e0703d120100d40003400d841d5010f1015000c04c1080e1035135510f5045617a0010004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 585309298 1250 585308048 585308063
    0xc19050f0d020312280b010806040c050304060207020a1203052802030a0e03100606080402180c07030e0a0b0a0201150504060620250806070825140406020312011d010b070c0909 77
    0x10a011ba50303100e000c0c10717031260055504010580e511407015005010060000385440c2d000183e80c01191620241c82d0000c0c69050b41a44000025280c041d290b0b80202189811080361520b10141d142d12400e03011003890030507000f0710b20781070303442c0d0085404402942c1c8598151240c99801c01c002012446060300504160b5a003c2d118200341c130400c07005a003a842101c0e5801003003814465180c9103a400c9422850380760a21844409911020485500803580840e81050010841801c26601034118004030700802e104480c3c038503250740411040394814021b40002944c0010441c5468000030784106020a0010445542200060014119000e151100c1d03402c410040340805c0000780c00c0003110b4004010f0b040c40081407401441140480e24074090f9001041e8000044104c6140540e10399003c10f41c2c010081a0750ba0348402000e9665401405070b44d4070305051200000f00a26041e81807600ca90442c5410021070f440c00d100a0126002580180c4544034200c800090441d618071400346c0242c03140c0e40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 585310548 1250 585309298 585309311
    0x50706180e0702060f0a090f0b0604050601170a0f1b0903120201020412120509040e0d0f02070e04060203061309050601030227010e0c0c19050f0d02031228 68
    0xc034125401596030004480e60003a00074030000a0700031500d01c0e80b0040c03442caa040b2a60703c080e008405401403140140017030030355903500c800303000c0e00580c01480360034262014089074032144011907103071300903031290081900f4460100304800500c0d0440301940c2c2e059540461101682c45003156691640e04464002c15003070001001000504c181d03920714004540000c5003001d25040f0f00480c13440301c80303000800701408291050030060107841643d10160700900100101840c40582584d641801058040070070610386c440c84110388006515020b80c1c0c040300c40d460301a1101d030340e42c070080e420240c005903104003c0d2034000c40310340e640e2060031480c3d8010070091407036503d0350043c00900341c0305a02c01c3c55802201199141442c0002c5e082504550440c04001c089650350481400380d80107007140301007075000394010700c2c10f44810310000400090190701546d003c1030303a000081e540e65010280941c0903800034050340202a8601175050b5201281c0503005148074801259079146044a8008400d01c6640e409c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 585311798 1250 585310548 585310577
    0x60515090f0709142d032e0c03060e070206040605010f0b310b04050a1509120305070b010611010e0304140f04060305011104080c0a031716050706 64
    0x642094100000e41e9040505060001006141081901a4940040403540c0c00c2032240c950070324005500c4048103103225110301c42215846030602c0c1000052091083d0b0348a00c00c41d628249035500d0787d107101c007050304800d010b54004002403d25088004141a0f86441c0020b2500b040c5600354495a801d038090852072238185000811910180c11400018024070000c0c0584004403040b10741d030880101426501031201c0204c2c03d089050008980d0003030912044c0040c0c80c007020000350041e103404540c40c8c0380054896210701d0b0320324031400c0958000744240340100940445081c00c14900e80c001d20b82076103000ca480d00c8002c042c840c01e900040024046a02410024100303100700307415407a448003d9840c1a2074050030000070101142c206210715030000300c0080e80c1e9100e9200c0c80033160300c04020311110020821794022900300d4071071f03280701d07006442c0707140d078107103840d114060549a00c490402c041c0004603455030701070b41014403021854070001c0c9030480800c104200c080010178466135010325804142 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 585313048 1250 585311798 585311809
    0x100e1024030609021f0503161701060302180a08010605040f11070807110603130209060a0e07050d0e16050a060306030510050604091b33030b010c06060315060b0a0207060813060515 79
    0x61882010009c1400c20f40119124528142b0704444081c80c000d41c5480d079103040140b0b00044000401d600c9000d003500082ea503a8103401a0301118411103040050711440040041518540c0070a0941440204031200c000703040c410181c00c0b0349029900541240c02c19801048c0c480d0b00940f400024920341841720000c52074100300c07550f0b10560541d094130141c4e1810700d8440c10701c64042c101209001011a901020302119800b00200c01101411500721140351061412135039078074003800d4003400385c1290109807107001c0c4c01031350210317607202c00184a820040b4103980000d002c0a060f2651040c0c464443e0300200b1b01221364214100491203418203541d00d03144400036501c1c80f0787c60441e03410094110285484100040d00d002c4141d507410046003c00700c0c8001295107928045004000c140340c0702c0b0100c14040c20503620301800940010412080d0744506058456000e40001c000060b84925001d0280e18840c1902a4128100c010030b0007800411b50340f1030b4161082100d480c00300c400c60b2400a080c030301c1d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 585314298 1250 585313048 585313081
    0x406050102030c1c2d03050f090d0c110612011412060402090405070b071505010504092a0f121106040521100e1024030609021f0503 58
    0x90004614240001c3c020325144d50140c080d0004a10300c0350050300d10070f40240d0340440490801c4000d110740c54041c13409100e904100e680108000303440c0c1070001b0000c544041c0762500950284c001850285070950b030031176204d0758440f0200c0c1c10b801e9070070214880352500800303482000050801e15249604040903007107d98404050306200d02c49071204090244c1004c07503216001074041d0b034228020b039200c1c1000752403c1d0079544040801500040c101c01404411400403034200d009200910032640e0712003c000130b84a003000042e1000b00c4800c58034000c0055664610119070b504160f0b041032a6031144120001200c65100e0094140794000582c10044041d004045000382210b0719420103040c000403c0400540c0c101c030741845114200b14107a0010100649000c07000710b20700900040c54011422030311844089241000c0605151002c0b01000c2c1a00c1c01010130200d03401d0301c594035880c64540c48041c0456803010784c1c200301c81c3c0c4100c24811040c900c1100000d03402e0340703c4503601d007010314424070410708 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 585315548 1250 585314298 585314309
    0x42d151103090f0d0f0803070203031608011a03070315080d18150f1b0f020306060a03080a030c26010e0a020703120b0303130f0f0b03010806161407030801050406 71
    0x400c0049402a80e6519400200b0079410340d40b51103070001d1031404c0c00c5d442074000005020a00b011042001d0154000020341c070031000c003411241e40380e1101e441a0f40e508000e0107030515122984051b600030740c448002555002540d0300c2c2c04039410040001080000c902e40d042088540c100c035040750600e90f00035030303110301101c0d2841c5d4019a4a240110318811b41842e032070301008000503200c071078000c10300c6450140302119216010b44e90007030712440d2100a0040050040340a40140c0002030032500e4801c0340c00701102d4000a000d0701d001138404048008007050341c540f205000e1300d0110026291501046a509002600c0389400254101115001561002055201c1540c010081000000e0f4032481c0c040d1045d580c0a0045001d064520009056001700d61800c4902c5801080008800304241b00c07400448040d500c4080c039980d00d07900070203200e01c003d004000c8a503004001180c5c030380590444000711500c1c50f1401c9600c035040d806020001e035211803010740002d07058070011701a80c81d0a1184200810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 585316798 1250 585315548 585315553
    0x10318051e0313030209090a060e0105070f0302070b0f0601050706141807120204202a0106030209040b0711030a030527150612030c010e060a0b0105042d1511 69
    0x1580640f22081d5048036000007070243c00d42501180d080740080000781d100035440707070050140c1707544510100e0091404403030000c0080c507841c1046001e00d02901c201d0390040c1d0841d07000b203074a80c1c070080102c0004001900984c1001002c02c540c40c041603036885042c59000403009007054078240300302c450040040b00f0080c0300035900412010000d1200c0102c009001c3e03541518007040c40e904071140140390301c030842490840b1504c00110704511010802503060558042a601014050f441c601e81c0c0c201c5880d0b001c025008018071000c1408200411020b5502004a14002c0c01d2116810b00b600c0c10740e0410028400841c0d11401030060011018082480b2144202800c0b44040d400c42c0722035035030301c06060b0403540a480617400301d045a1207030502e80010519a40840303580e28107180c101402429030400b20b100780d0081c3c001066040006024030095540c050b501c2074245820034a40c11410807110078507402116251b00d004662002c2c0040040040c2401605503400b07643c0504040c08140c2c400140940c640c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 585318048 1250 585316798 585316807
    0x60f0d0e0f07061809020d020c0601060e0d030309020f0a06200d08130f0b07021b15090907030605180105010305090606100c0206040e04061b0905010c02060306010318051e03 76
    0x28040000e02030b046a43ca45003444c00c4180c140c3c10f0300b8418150340c0004043d0380c0001545111030b0b81a800410011403010200c0342d060ba030310002111400e145100940c1d210700742c8404680400d12030340207204c4d01400148603140111750900080d004404a40c066808100e0280e480040c0d500100307080e681000c5081d001e0004881c2c2c1100080c00b01c01c0040040c107240c2800c040a8081c4052100c0508030698022160f1030181400c0320080d554404041907143c4044681c6507450140c180300c482804010b99520342d160800070402d00b0040442da0060501042540d107001c0010585e552000030320a0030b510001484080d41031800040980380014166201a8865402c0c08580e0301d406c2c20b00115561540707000c014071807a0348000741d202d101c0c65103c07103400d9002d075040c8814404103501c00c109400320480e04000440c5640e8081d52180c94034403c1502140059410b5009410584021544036105150015501d1800640300761010001c0303c0c182c48aa01001200d103181402e800030b08502c016a00040d07040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 585319298 1250 585318048 585318073
    0x3070909030c061a090c030610090b0906030415060e0f070507020f0603070909060902031e070504060305130f14010c0903050316050f071401080c0403020607060c0509060f0d0e 77
    0x80781202d000003000690344004041a480c119150290410002000342c5410f0402e600340300c0c1c0380d82080c1c0d04244201003402030780c00e409010b001ca2800300d074500c03464075040c040240d080012031341006105441e00a41c82c0c44078000d0700c0310740c4035903130140030310003000c5805082110741019041001000281444420804200035a40b80384901c5070810084860b03c2d0359560701581115960300c6940106641401c2c820f0101d1300c458150051480f80b01d1151031030406e0714444031050051107003036916401143c2c082000f0722000d40301e600230039404446110303d0032043d242a40c0e0f280407902c00b01025100d8105503008a103503c0c0082c010250045600d24000e15400e043d0349405072203125400071581c9104e980c414000810a090050300407a020b00019154075607507a000042c0c1c400b140c0120f0318001031000c800100d2150048056034150781e000382a0764100f416070398461003340304c05e0301c8003410300c1414001c00c001c0d50b9404008003018642444c10310b4480d2208000a0103582540d10074413481c0d0000b00a418a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 585320548 1250 585319298 585319307
    0xc06060628110304030321050705040b0724050a050108030c070603051f0608010602010c030c0f0c11062d041428090c1b0201020d03020a12140103020307090903 70
    0x482019000780ca802090604100740c5810401d01d008000d1400041000420b2541049403220081c0440e603007405011102210345044400898071131001c1a010701c000c1c400c3c2c078000c0e40074161143c803442c0c1001d01d5202a440c00c1e004100c2d0712000103030f80394a0307404100008032140186401041100300460914410360b80e42500c440c0e0500030702c020180e491000401131000c0b80f1101041303040c68450407407151303169200100010024080e9034003560920700c600c41864843d03c81c958694949944a540004000d00c00b00c4007840700d020151a0b8008452081e02650384e89001007058110200c40c00d504009400b04600d1000c0e2150042c25200100740f00804c820700d120840824070309012503010701d0b4504e16010310b00002c03c800782400f8201c08800c6020440d01100e0b805680c00324155250060182003000030307011141280b00f0300a00582021090140560282c2c003c0c0c0514075503030520140b40d100c448903500c102c810140481c02030154032801003003542401d00003031024060350b503028044071003161000342 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 585321798 1250 585320548 585320587
    0xf060e0301060627030209070302070b0702031315030e010c091503050114061c020301261f050a0b0310091208040809090403210605102c0f12030c060606 67
    0x6031007078091284c450100d00300d5201e41e4080c581c002c1c011440c1d0304107100002c000390096003003242c100c2880b40128840600010586000c4144145404800350404100340d1a05441ca014a0180364a5034282003020700c081c0110118105903644e400d034041d203000d82008440958038000e00030706107440018010f01803030004078001450140c80c1030369a601d078221f900d648454030303401ea1300c842071010001140c481000c1c84422030030207000480c458100d0070009415201e20304101d81e82c45844030501d55450200c0541c20886d400cc448c4c190000d181800d42c0040380c10044201c03c841035296440d61011b041144a0040389210985440c20340c1c81c62429a0794036035180700344800315205580500c0000d040602c0380c03401c4070554103040f40100c810307001c000700b03003016081a004483c41003c00b00c030b0035000310b44075148041407109400030501500134100350345c04010004844040d001148d030040075280303450b041e0144a401e1941c6008581c5da6800c2c0e00884e00300700014001c2ea1294004122500c0d28002030346411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 585323048 1250 585321798 585321827
    0x70b091b0103060e150d0506040b0613050c0304060c021e060105180709030305090a152f0a1e02030a08040609090c0f080702011d0f01050c16031b08040f060e03010606 73
    0x100701716000c0400203940b1200b003900106503204030010807007085060a20f641c01400c00740d03880e40c81e803003000071000203aa108403595035900030140005408144541c00c401e4145030fa6006032003101ca0750b11003210075150403202c0000c066101100401c081e081100c1049044040004191a1420565001402e4400500c80030b802c00002003840461940ca0300e82c0d070750040c410f440c020000211501d40140c169011030104504540450540210b108141005000c028240368007510240c0b07415501d280e400e94200703010700e48001a0110950040e1010130034039441d24041c103011034940c0e1034050014003100650f00018142410040c0d611215074010350000003003003503403c14800a50310150120300408540c120780c00e0300c119041c0e50409031840400e005c039818040d14020b02540e0384a01010324544500d15070180083d0400342844d000c02e00c112040c440404c88481050742c2c81426031140c409641041c3c00c00c05c020300d80c101d400c00c061900003c51001c0f030142038000b4043d45180c0030004c0c1c112003064220 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 585324298 1250 585323048 585323071
    0x705060309010204090c20063d170708011808031807090c1803080304060b0102030c010e030a080609101404181227031205070b091b0103060e 62
    0x4075040d010290180c0e4081c3c1006071040141c60740308400200074070b003a18420510040c1074909006003040201d0640e20890141300e404800c00003000310502c202c01d032110103812030000b00100009504041e90721200404002d047c500b05000c1c9190036904104066004481680c580280040c0504611210404a540106115031a641d0305118616000d0301070300180018044c1810100d916403c0703600c030b940390640d80c0c0c0c1c445001c5048284142001c1055001c0640008000c0c40040c00203859a001068500b0042c03045e07038100309a1100050a455141855000d42d4101050000a040d40102081d600032412550f1400c90300344107038400101e000500506042c1030b180a107180c4c41c0c0c0c13030341c0d040b100100449040d5407805403202e007010035040b18600c1d000e800180700d40100501d0941594154200c203240c02541d4002c080c40d6a45821074104294040c00c240b040901480d40401c05950441d481005c000c405082d00501c040c4411a00790207840310306041c5440c008083c088801940e00613030340400c400b9003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 585325548 1250 585324298 585324301
    0x27010302070b0405151012061a03031215040c080703090302070b1326120d141305100c0912141606030c03020702090a02070f0813081e07050603 63
    0x120040e22981d00040d06500c2d03203500748010002d0010300c0c2510724840d144401855101d1059000d00c2d04203a2260310401e529462540c5c01003082c2e0351081118004030480080d8034a02c10022034110b400003440560380c80744003030400417201e518040141581508883c1005003600e50b02e00508001c001501386000c15503544014001c042c020000760380a441c6608640d034417481c044810000100c41e6010395004070941031208441000744801601400d4402c5002d041c181c00c0001c0c0d03018a030b800c000c1e03400d8202c54840b652800d410700c003424202d0181c0194019881044218213066240050358003072040d105181c8186945041c0d404680141501c1000c07880001080e8541840880047c0011902e0402c0c01100c0c034544154800030301c03180483e543da8400340036100c102c00090b8100d000704000a03402210450015803150342603801440303158030072010400b51401a840302c04840d08080114004143c14107070034021908100100028003030280100d96414007000b030200d841e00301511816004039000700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 585326798 1250 585325548 585325627
    0xf0504030303050907090608010b030c041413080d060b090306070c03080105100201020d0f05010f080303131e050703081e0c073303060f0905040302060f0703150b0a03050c 75
    0x14005c0104400c0b002070015540310750949000702042009a0701c00d20403218800c034207052500500340b44040d2600084000da0303405038040461084010101c500076420461481f86018910585014003a08090280c07180c140b041403501d4110068401420300400c0c032615000654041e001c070741502d00076070f510001001e001d80b05901900880c1c2c40c244c030f4207050100007007075480594020b504032180114a4402199920f44440d140d10007079a41d0003090300206030010100d065400c01c400d400d030000e0030095884a03151920350800440350400c40b00c2c03040c0001c076103c0000269907506080e2500026403450311f07601d40c6503079035140418803998070a07112403205003842c1c0304044801c415508200000c44141e490b540070040007806c8034012060348940c24030010924518510405100c1c0d54150018081078554aa24890004000340160304042c2c031417203064502d24550703d0b44001071803102462500d9020258003c5c0640344010b0800ca2100814020011170340c3c1107070441070042c10701d007206034104600203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 585328048 1250 585326798 585326803
    0x16050903190b0117100c0e0303030a201317011508070503061b09010815030312191808030408070c080c100e012307140a030905010f05040303030509 65
    0x22026a15014484510003030245011200c50964850452090181e803185904009510400d8201300307580d22060303110300c1446580c1d0091441640701d060049043c540000028650b90044606c2c00c950f94454000c4c0840304030000f80f80d218810300b00010345c1020b81c0d25040d02114119403088001e003d58100007466441c03800e51015034026154854490386644a441a0b650750341c03544030b070740c0c000e21540000413017042c100d078000600c4810b81d00300c0300d140c81e00d41401100c55403000307015502c1d80d141e00035003080555810401072506040f814091086460190309060305000981000b194042c10000b202d211800c400c11a0f10b10117600c000226102d86445c02c01c281c1901407000000c01e16040048081000c010020742d0641c0303d2800c40b800540d01c0c002200c222400e50000580d9070206220110f0240e48c104141c03a02500c850310a005c046c1090000d454888116698140086182e0030200003c1c0501d60b112101c100a0942030030070007001041401c008009100300c0c80b01908050741c4001062004600b07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 585329298 1250 585328048 585328057
    0x1140f0c01050420010e0d020d11030616030e3d021204150b0307051002150403030626030301050105030a1404115d10051e1605 56
    0x4103008100340d01e86071800714005440c600c0e00384964a03e9a111406540c400c12010340d0505026140c04025990b07942072044c000d0303444104803141c003100400f61800303440800031144204054174102042c0343c0344800280407503102d030300107684903040046082d02c000312518400d124400307145414030300384003014184c506070041e6103c2c032400f0a000040403580541d14095042c0901d0103080480b0b8624072401c50f20301128064000c2903016008400c0400091801c000601104035107130054810f04824682400601a8102c5045001c286d44a60510070708000026542c550583c880f510034040c07803140750065403800f0510489041010020004420181c580c0100c44004c560550b160030f51b003003074613003241c002c06414081c0d401840d250404843d03104040281054003140d02845480d03603200031444010359040000101402c411242d01000b800040b103a042c09287e6005024141c82401c40c02210140c850140c5103151081d4428425002c0d41c8600c0c9030b43e80c000100b103410404240c00c503202514203014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 585330548 1250 585329298 585329317
    0x150f031509120705010606080105010507020a05010e0102010906020f1218031207210605040f021602060a030209030319020610060e010804031e0e0a06050a0c08090d080d15080c01140f 80
    0x2c04140e0100304101500000c0a42d0103944850886a0b220001110a0302503098081e40c0215448801c01040d4059101c400d0920300c18800441c0345803864840c00140c3e0700c414140b50341c004000500c446440c1c3e4202c1055000850340302003000c42c1c0420004250344c0d0040400c020035420101001c2603045000703650300d00c0d0458142150604181d15282c02d48010106446a180a141000d044503000010382c821074054070100c510f840000e414a40070700265800c09400407060607820400e49010790740401c0035080c182016241501c28003560300009081400c081d000501a01d0240824040c0c2c941000400395180400c1c6800e100641daa410102c030280c071204114000d4909000401011683c404803003d003c1a040d656003040d5075844008489512030030401500041a00c654080054004001070424100c0145680482161601c4400607139005a41404040342e542024014800c1d49140010040041c00c0c0540300740c0c80c1040001c1c0011082420b8140e00031000580880b4800d01c1d4400e8584622 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 585331798 1250 585330548 585330583
    0xa0510080403080c0c120c03160804060e04111204060b040510060206160e0d05280b10060e19080d4116060c08150f031509 54
    0x1951601800e0303008103a8041c1e001611080018465000203800c403140e00e9a204001d04021a101080b400942c1086204c0e80701400b040001000e4610302d40300f803194250040a04a40d200d03d000000342c142152203034140e00440c14006400d03a04500f44098444011368122a19150380ea9880c02000401e04030010b254403601d02004d004480e0103040401c8141c52943d0200d508584070442ca80300703110284907289000480740407a910503410051015201144101e0481d000c04035040c01100350070201108564188a1001c0380320240b142030303400c0d0f90700140354140f00d500c01400d000008040e44078101a0a020f80840742100078014964500a00141183e005852060441420040071403414050b2501c12a60120018800c3c05540400819a070741000485100d041c03c5140c080b00307600005143c0d200e28a4401c4a400410303458001e051400d602030744c0f031308503500c0c10160400341100b508540324060200b005020040da04c0001d108449420340754000020b039981d41e8030f843e150619080d41c841074403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 585333048 1250 585331798 585331819
    0x100b0a0902092809061406090d0c080307081e0a0f1d04090b071413051c05030c0706030e03090906040f020903030703080a0c08040b160e060a110f01140a0b0a05 70
    0x24443c40c3e5a8000b640d407003600a02400e035503852030240e2000c0000e88190300c000c08102c2d038403e604e422013003199043c0c8622444144959240030160440e040041c05407110700000551201d02241c050812680e46c01002c541800c0200c1900010100001c0306c2d081d07018404000100600000e64010f20034151100510520040245250410400c0c0302a6403240c00f10704e0340099200004019401d030b52542800c13540d8421254a4201003144040c4071104a141810303280c004100410700510003080f04109090040c164175161070341c000c080319240501c14a56403c180102d44203a5548260707143c00010484000c5880c81c0316020101c02032250641142e030612000400408041c2c02c240e40c00c0c03103012410010071048a2406040d05c1d151800c8400415500400c0c0020302d900010300080070003088180341c440c018140850101e9110380c000307507295000c51081c1d640c1542901c2c08001410000c459007000b40311251148400045030080548844404ca441d001d076000c65495280307004006080c0100604105c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 585334298 1250 585333048 585333109
    0x6050a0e12070801140601030e15310b010504020c030f0c030c060708040b060f0108060405070306090c05042607060c060902030d030b03060702060c0f090103140403030e100b0a090209 80
    0xc10105c04005110340420002030000c2d0f00030301c1100f402c6c0303d841c0047c244901104002c1507040380c000701181503401c190480a83d900560114030491000f040d0b411502d5140c941c14005100034050b40143c0c41140104141d60000ca0080192110000701858842c2c0b21541802c1c010300710b000702d0401400502c910300030130480b01d6001c12168082e0b4050b002d400c1003500c5040c14442c8114008209a02043d001c1e004070f0500d0910703a221907480042850002040b0342c40c0d60300c40c001d4071069090040000d80101d82032008146181031700c0307540b807003000340c852039442642e2209880f040d5511618052108040003442409140d0700125240e0341d0040c2070359074000c460000a0300810610810034082c0c41080b002620050000501502603003d03908032034142a1025410041d42e8032804e152410141c03100400701502c1407150364240540d2094401059040348200242e01d000280502030381c0449c01c0141c580d910703440e07045000054401c1c402c0c016036a0004040481c24a1079241c181c1000d50106c003450000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 585335548 1250 585334298 585334301
    0x1b0412030e041b1e1b1e060b01021b09070e01020732040902011403090102090a0e06010810030b04082a2a280503030706090506060a06050a0e12070801 66
    0x240700300b01d45a0901601810f10a644c9850504071800e003c10088070046028050107100d0500300303442000c201c54041c0800b4102040ea14001c98200c2d292510f480948100d982c050141540c20030104081c520301c6031300d03000003440d22500506a8018417a81700f045090f50b9200f40110409002080c5030080f0200c04091005c901841d200e01a00e2900d910001900c07051a0500075011400e80507507802014880c0031100f404107520203406144c60707660070000911310f9190f607401107004215409402d9114034041002410000000b0070382c041e41a0403c406000052280019540080c0c00c84c448648411510b10859030f034424012024001019118030701ca5010000500c0303840c107d0594014112034088016204000c0c4100a80e00b0342c0070070300c03064203402c414440c07072442100a0182030f130614541c0d076180464115802030509448040c0c44811540a00c4020000d090b005130003507030805e0a4600e8004000d2042c026959001c041107101051103090b5a651021018014042c206441a00e561580c02e40d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 585336798 1250 585335548 585335591
    0x10080403090b030f0a0f1d030301031707150f02160b091e03091302130e0a060503192015070303050105060a051b0a06110d051b0412030e04 61
    0x4002405850002c01c0c42e080c0c21094a0040d1494550b401c46038590341042d04c043c242905489801c1941c402002000743c0c14420017015403840f60000d10369a504500780540c040c0e03540304d0080c500d00420025480043c034000c42c083c0000c901c5203800100b1007550b000c0032010f407280040000a0002c00700800040c802d5a0500600926204044a102800041d0001424034103032015400c242c20a000100c41742c00d2181264003640c0030803100601d4013190a003a0040e195a0b44c01054107410390104019802d075081c0301d02c1c006071900301e00801403c038a0b01000e0560030f24288008117010341501130740e2071251815855551fa100c0c024281c0007074034071904001d40260080d0030240c00082c20076000061500f460700846500d82c04a503505864581c00d4a10b44044140c0300740c207040a44206d54582c0f000c1002485a420050005000144e03a413a080110710252900175014400f080c6000c045081500080d000302c4003200d540f1100941002c5507410240c90111031000072a81250400030380c2c1410100141481 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 585338048 1250 585336798 585336803
    0x21305011805010e2715190b031207060212010e070201181109100902040906050f040c0c0b0a090b090a17040303090603110408010926070503030f06030a02100804 71
    0x70110800815255801d54800384100c148002c40000032031814925801d0710040c030b1640040825150a20300714003440d003055844000c0920000702c043c000344c4520292070240e521102c550a01103010b4110001b03449106d455540c6040d40300015600302044041c1d015a544907625003a11002580e40b0740880c600100229000d10040d4600401d44050501c3c02c00d1810000780c00011401c4d08022820a0140014018001d00c2802030072500010750741500703000070400f0703010064003c10020300d80380c01c0c40400301c2c0c0c00780d02c18461b5042020358003030160710080045501c1d81020043d41c031074a070220410002c0c08140c40280034a021041080400e15001680d0503900b48078003103040c00252410007400c884d000c0c90000400103400240304200b841d100f03401090a960034201da041c6410394070035007142120144c00d400c9a805141c1250310780d640c0c840322840446c0f1030300351750000d2400456503149500d138840184244d4261030711030003040c46900d040009644940c0d0241500d040c45c0483c6002412021040713808 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 585339298 1250 585338048 585338069
    0x5040b0a081b130e07030605090316080406030c05270a120b100803030f0a02070c05100810060203090a120c05062101061817100c051213030903020607030c02130501 72
    0x5040600f4001c0c49015682e100702c8002d000710904550b507442c00780801800a0240340310601905c1000c981800006102c2841020030b41e6841d460414003500ba0b4413016080c2c0244035040c403000446a258440c1365400324031000c7c00003420700010002402c130840c03a820120090f80c0204401d130410206024642c0615900580d11628980e11051143e0340d02c81100c40040645003030f0081840d00130103802600210780b0a2940000c45512000850484107072081a80001000241800b4003040d44048003005410188055468800c0c0e200100e800703c0921701c00c1d102c0b03840c3e0650780750007809819201032001d00781c001d08090707555500b460741d29500039940c407074880f41808000001412034003a95000b199146c5071081980910310304a0801e03002106405103030414000c10040320382000041c425950605143c3e200c40b5216a2480140002c1d11801007101c6030111400d5482c1002c40e0700504c450b0300f10303541101d080daa20381036450222002654184002d420007004202188803249641026042e504001803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 585340548 1250 585339298 585339319
    0x90706120504020609011808010218010807030c08010b0a0504081b0a060e0108130503190f020712050a060b01090b070506010e1510050901110316030806120705040b0a081b 75
    0x40e001165001d42d0000d510080c20822160154015900d440707050803900c82c14410541e84119150aa901941707104061000310300303246519682080401c2d80003483c918040080309550307200585440d50601420f0184180840c400c182144194212009001401d00340c03103045103030301e1b10303c4442d887d004c05492203002c0603c40841e8440c40340e610030380c8c5104140d44114554680840304401030a58400a0700c043c0420002504042140e102a440c812002e95800802558408000703003070402032b4014807111405500c81c10082080000d80c008145d81050001030b48030300e85d80040e036514819074009000c0304d1010440100b80600421000d040740c2001c1240c08642d9102180c1d03a501c5040c3d444d107143e106030392202c08e014641c40340d0064a40782c030040c101040380400442005283d90880348403040c45041080740c800030103030311840b07440d04840c041d070f004450b80300070b54119a1682ca082c041e0a002d150380b66000b940f2940c80c009144000c0010301c3c2521011880f024a40c00d10803160030056005065529 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 585341798 1250 585340548 585340577
    0x7021807111f020a030924050c0c12090a0f030303061505070f060509010b040e0a05010e01090c0303230c010c09080c06070308060a05060c06041703010f05010c050a050303090706 78
    0xb42d40d80d5005600d9260605440010280402500a070110108040d81c81083e100007540c9074040c9480c41c10b14035440c041507c81801ca2000f035442c010481c040030b2009018110f10403600060050b8498000404503450341c00440c0464201d022660040c000d1805110001041c980c0540c040d5059a02c1035480b02000f0041d60000d4032184603281c0d00501d808400144140454200c0d03010940080a50001088110120300000d0a4842c001c0e01c03041c0d6900007420f1201004001d00c1101441c1e0036900003413010300080c0d110424002240d02c0060240b00a00c0601106481c1c00c0c10000350400c800041070b80c0f140c0c40f041c0414000d0952031425004902c4100020481d040000390042a604004088500d82034241c0d804440100001d030402d40c0003003040b0301c0400c90b40c0e02c02018140961004004064901e4642460039112840184084600c04100014480401c80401f800e040d5402803c002610902600c2e25500e0608034400140c00390001000340100e0143c0480c91000712141603031001c2e6240c5555 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 585343048 1250 585341798 585341803
    0x5010801090305090904051c020f0709112502100f080601081b0d060b0a0201090c060314040b0603030909070806131a0405090f0d030f11121b0702180711 67
    0x782406004201e090185920301c0c9045c03104030340d010348074100f41c800c1c034041107c59003004500b02c0030410140c2c00c80c0b665130804507801c01440004000d45841070040c507140205c15404c601c80c6140c054140300f40c090445050f004906568264a41d028022004540300c00700002c21640f0030641c4900042d0b242e0000c43c54070b603c81c80115028403d40540342c04000310003e05581c2c2d41d0700600708900f02c951541e40006480708100041c1c40d009000f80c001041240c800d1818110380310007034001d034040c5403800c0d4690320043c056083d50380d4015032000003003145898040029145010b040001a8004040c45c100b18189902400c00c40c05400142c81107494441c0c2c11b4170300c5065803403046402d9003a036452980000540b030035402c030503044020301c010f507081c494044c1e40340c604002960204102194858904400401051149040128062000a00348882107207d0300f201c0f2005030400d41c050030411200003a07401d80b01c0c2101c660641c0203000c05015901c986403150248000c649a40225038080000072101201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 585344298 1250 585343048 585343061
    0x1314040f1e0f15140a0b030708030d050f100807060e0f0405160e0301110706050705070b09061f0b032a040e18010917030415020f07061d03040b0d2a0305010801 70
    0x803040130380032941c1c078240b01600510480603455410301c18414001010f26090006148501a601c0046290300d0641d108c442410000391800303003c0b4034450000c0020800c04200a02038070140e1130864031051251001500c0c4106120180e0713441440c000900811901c031049004445642f62901c030386c5000c80c0400c260880d02070401541c20707000c0400108001801980c4140e500c00c1e410b083c102d040c214103403900840c1200442c0c1c0a0346a5100400f800b080c3c00c18000703000c000543c0243c03c4080c142c02c11045580c2400064400300c0d5a42c14070160348031340c60134000044449419400c4158a4136540d410840a106080c2c1d80ca000165004881c0440000c040c0610f40340b00b5000344403403250149611b000074060b40028000c2d24850402404110010354600050000000c003161460311079071641400e20403140b02444003003030080314864074074000070044195011030385c40c62a02c2d41c80d28449550900945a402c00394003100e18204122030850018003004200100d0740d035400c10250381c985048178203e680 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 585345548 1250 585344298 585344321
    0x30d18022805060306040216080d060e0705040e07030e0f071a040b03070c080d06030605041a0f22060926090108270604111314040f1e0f15 61
    0x805407003072200e41000002150480c40c051320051501013280800e0b40c01c02d4009074100c9400030001045061100140a0440a080c4011007844682001c10019085101c0c1d44100c640440e0503000150b0b106009510440c0303040b504006442101505900b4141c40300c0c0a402080b1030b18031031420914010011401b80d80c117581c5400400380c0766454071301094603603034400c510803124180104540c030a2a802401244001c521803000800d25062a28042d0042c01404855a400030700304400c00402042002100d07401462502c0d18119541000022016291030250050720361400e00c01b2801c100f022203880e200e01d07116441e04041980c1c00a0508809174070500840e640050343d00c10200700da0600c4008090004600c1780c5030400f01c076a00d02a0141840e10844050394100c55162841c01e980c1000d1680f0380c0d191401c03010401104030f104030340e010351100203040948a0000120f480003040ba40405441d98030b0414101c100c0500020315021040e4105010202c54480c0700c0010302c0803104083c000e40d0440607 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 585346798 1250 585345548 585345619
    0x61416030e07030c1205030714032809090e10110c010c050c0c130e06070306051906021c090b040e0402130b030a0f02040609060611060f07170702030d1802 68
    0x1894140e64010170011680207891a0008000450020f000a294405043c404030040d644615141449203ca502d40c0c4283c1c424030801d0405803131030294086144816500080000600007070301c015442d1500c02d45404003c40c16117006514540b103170720080904154082c15000707010800724804119418051550b240c025640300c6092400113150403000c0122031104da030700c001040c000d07100c5e00d43e103010400d441e4240800d075941c500340443d04090b900780c180b0b40c2c2c860f1140203c09180180081da91141c640010705003101d41c4105070303aa680305160342e000501e10030b542030780c803140c0303c216800c0e0390079094408a215001880122034034031064054004051002809440031030302d0358480b0059101790303170802c0345c1c4559951404100d85d0a140700c2c1502600c0c182d519032002c0e0710300c940a07a103030100c05001c00382400036000401155942c001c02181e11414542c80b4a1403d441d41038007030785903010350b80d0a60319203810041c030700809124040c0c0e03031410113008440c03a5062513151500074810b203210030682e80042c13 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 585348048 1250 585346798 585346823
    0x2010e16060807050f130605031603061208090d06060305060916060807050702040f0f02090909010504021f0516030e100809191103030310180605031504061416030e0703 74
    0x46004c0e0b0080c1c009005071a450a1400324000e00640300c4030041e070480e001151001c0b06002d94030454000c004105032041c102085800d050500024200f40c0b5044000e10594001947d443d15840d041403100d5082d50000c0c040c4003407600c03850a5515064211003031291489046860091800f03941c20320b81c00c6444507141c02c145600c07403010444182c0d001c4007060360426203641206600681610588480c0f15070b600d030060703d60aca0101001080c8402800b54001a07040405100250791018018a901c9410005900500c507010105540500424032a01c0081c080d24200c2000c1c513030030441500700d41c0e404071040d9144003140c801c10f0713039611b006480b04074003070b44152940c1d03640c0800075102e2003a090040342808050f5203c00c0c0024a150300480e020f46a052201100704013801d100b0580106886015009103d230900f0300d408a5a1107200d4412020f1400d410008607003480055031050700000c0c040327030251701c240c60044900c0341c0c3c101500b114440041e1820300d440c40d0406000c40c020b01500da00c00c2c1018000e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 585349298 1250 585348048 585348061
    0x2090702240c0910090602012d091716030e061314120f010c0e100e040213030b0403030902031e1e12130e0a02040521120a02010e160608 60
    0x260700050148108030301c1004003e0555413040c500400c0e4108a903902e0161a080060090a5524940c03160540341c8902d416403081009851030750b070310541c00d00d60004507c80c403420b2882c1c0c01c01500340307094076191000800c0304140520140c82a0020302a8584c1c0520b80520b03800d02055104582e4481c5005140035402d000151302e42d0f0400201c18801010f1004010300019824109044003801321944d139540c00000520381d4021070140d01c80c03001121000b031a48041540500300c8010588481d2190b0b0b400103520b908111408000806107400804c6100380c0d182924010300104468503043e4072902c1125046200040c0d54029220088200805401c18048000031409044248075000000d030241554804138090a0300240c003400b80d00b043c805081520703024140c865904054800c05200e40100402d00003620340400c3c2c2c0c10108040e044002050b41c02202180c18014400d1120707003040c40c0016400b0380140c0c1504020070003140c0509480711010320f0184400d0010103403040c039010500103000140c2c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 585350548 1250 585349298 585349363
    0x30c0b1206011e0c1b1d01060c0b0a09060f020d090b090105010b04051302071a0a06060203040509060d0c030501020a09050a0807050306041e1b03030206070309030e12010b04021602090702 82
    0x200c141714811810304901d110207a03120000700b50f0880e049800d0307864140c0741c4107180c05030100d004182078200061844a103844000494000800040d50552901c60321000c0045a5005208144480a085403100603644070b0074040c141d120000c0c0c0d0640c40072400301e941d540043c881c0d141201c541c100300c07070724041c40c050074445103100d0b80780401c5085a0901408004c64464040317030000b60541c40c4422020b1034071a1450080307480030303003008046620621092109482c0e180c0c3c440e4022900721920300310a680c0e07161100286100360001002d035400030900395400ea030172250703d0f010b40303100301c480d00ba40d00d440c1c42d4003613580c0100e4410154564802c00204001c5004a0b000300758030200c0c1003040009103925240c0740c1c0d540030850800d0f00010302081c4100b007815810302065400a10038036041c02510103688008100740c808044003071255803105201c1482d01e070254058200c00b88040e000350b407201014403c41c0d00400615900340d0103007124500180078244089039001000c03281201b400540b4000400d00c08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 585351798 1250 585350548 585350567
    0xa050d0e010b0901092003010b0406121b0e062a010609480e011b0201020a29090f1c1205040c0e040b070306050d0b0a15030c0b1206011e 60
    0x101100189400440c001b540c0000314003030a015aa164ac0d0b803031038100c004160240691000328049e2501d6401d0f01e51300008940a801600d1524004024039030b1840040c0e1244188103444a150001c1724040b260755910584041c0c0480e1444020480103a844001105445005c0c8aa05504818a001050f25000c0444280c0308840044941e004150b80f081c90300940714a5807518004034441c00d00b0500f8540e805410050002c541c0c841b246028a950760010350f440300204001070084d9030000350945c1402c2c018101d810b000000e4022a00c003420302c1270b003264940843d140280e150f806081c4401140340e250110f01100101c1564481c403038684200c08000c0101009402140e000b500c0020001c1c80d405501003150249000d90206000c3d070603c1a000760807101c1a0b8412805031107062008004566240207581d03010070400008201d549441042480380002500018920710382c45002040100100d4050182003807990b1105460391901d20042d60000c0a00485c11a0011400c00301c00700144580c42d0b05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 585353048 1250 585351798 585351821
    0xb030a0309030215070302340627080a0f0303020c0d11010c0509010c03230a051323040513081204030f1b080a0e0406090e19050a1403040306020a050d0e010b090109 72
    0x65514040d071252401a00403e940f0880c0052b060449408002c2030030507202048201408012403075070710307003c103568032160340b1b46000d0a04800003440405041c040c2d0116459918560256604085030400240c0354603c16208030039958607008400c0c40081c059402c4913031483c3c1c140c698242c210301e1554121008680120704945458000b001d01c1d021005070340c090110944251a80d51311604a0b890070b03200040740b68401050760340e40550303140c07a1000c00c2c5010600c64130140d9001c81d50755262401d0404007124000010140c4000160302005c5986411005010744e2296a0b84c41c00c84880440482d400d00203141003581b81c008070490040041c105c28010086d002e502d09102640d003606400040032a03e003640a18202d94032100c146c1c2040d14180f20512600e009824464144074454480d2642c905207000000e0910710b1501d1525210390080055070f0055505ca80c0a6541d2005241c0c000c0079a00b100700d008518600f02420f20301e4660060241c55400a4043c10720b4000ea0301e03000342000a4170742c16611 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 585354298 1250 585353048 585353113
    0x40e0606131413020f030c09131a0c030f090a0206030a0207110312131d0414070e04030504090b010c240f020f0705210a030f0b030a0309030215070302 66
    0x4028414541c2c440d03081c072804000544039001c468500600148075540d0030414825088250200b003180c1c1c0d1364004a400003c00d940480b4102010300d8030700d00780802c0800500c180013901082080164104005504c50501c60003c034420391a20300000759240700180d0001e40c0094180001892404036502602101340540d18100f1250941301c08039060a5210410b1901030348001019801242200521001045140c0e012003c1c00c036061607144448002030002450300312881508006040304000d4540a010801151000cac3c0c24685000341280c2d01038842c0c3c11100e42049502030440d030003804d417441070b140c002c540032180b0780f50280c0d14040d84801040d03409040e552003506d00e2880c185c0c0d2029280307910140d4181641c8941505000c1e103030081a41e01d4050100706c03082c03035035030280d51001031ba80213a0041c10080b441c92000f1f00d420300601420000340350140b0821012006041c3d2021541c0c00b102d000b62803021000d00d600c000b02007284a83c1801030301591141001c40c0040091841010340117581405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 585355548 1250 585354298 585354311
    0x90e010f170a08040303030f1d151608010b0a051903060e07080103050a0b0601110a14100b061b010603170901090b0a05270301020a02031b07030309031e0b01080703050c040e060613 79
    0x8450201b80c0d100c0000b0380c0503448000c00c40c0010440000203038028142f904182c0494101c05c000421000050294034013190004c20030202c0d40340907506503103c907130300750412038a880c1c070030381c4014000d000a10030201204600000701c1d11840c06040c03014142c9401102038040340c1295102e940b100b100c09042c00741008061840d04250b94014070143d91201d105e000704241240d0740c07050300c0307241003108642455803d103413226005d440c0d920700d0101c44641c0d19203c0b40e004440d01c808803030b90050280b680054070107400d840d082d800b1003034aa0005c0c169007030241c031a4000c842d00e402d1901c11034003a440320790000c10010481144c4020300012105054802c108194600320302c00800309099030040340e4078501590001c120f410220642c6d020480030440d4040c01810030074074503100184002c4c520f20000e41000c0000f00320171020b400544c0103d05090300101e40c2e401c1540d440910301e40d6580740b1300c800d0f5001e014030344500040e890a4002c410100c2c1405c1e0090005407030354410030000b03408a00140b07449655850 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 585356798 1250 585355548 585355571
    0x1c080a1505030708010e0c09091905011407050a0206100f050607151409190b0a021812030c07140906010e010c0510140a2901090e010f170a08040303030f 67
    0x101e2580070741321440c000308000d81201c07049442d1910804925104440f05020071803100d00005113a404500819140d014221b014100140140304410000010b11500d17400c0080c09c03600a4024180c080b071b103600300d496a503514070f803290110280e8010705c081107030402403c02c120b1800c04050002d003800359281902000500940c1821615000c115450000d0180c080011840d030520049510229100d000b00903130f4606d82d03031642d030214024803880c007856010407445080c402020f40308500c154040e26034030142c40742c1903000b9030b05d412103403860300a03114910001c1001501900d000b02c417000050705210407900c1d000015100c1602e00c1d00d12a040242c2210700c8000300701c040120280c1110162400140301514401e090413044004104102d40341c00d00e074501d2110b401c4148408411985410042e102042840041707519003900e900c071a010304102000030454414001114088500c400b64102009941c458030355103840020401818a003c18001080428081d40042881404e0607000040502080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 585358048 1250 585356798 585356803
    0x6011a0408100509070f0e0606030403091e0305010507020f0a1103150a0c090510020c0111030408070e0a1a180c040312020d0e090912091203040b0c1c080a150503 71
    0x14000807502c6031030340c091101c40281800840080e000090020240e2410901008100500030308440e019240c000000382c00e040c03080402c040605a440402c0703100c21900c000495008550380415607055190501148203a40000b40c4800c140c0104800f8104401458441e01c801c41400e042840e01030080c41c000410400900762894807800d045040010160426000180034496a81160740650140100801c2c15500041c1401c0c1702902440c2c940702840e0078090a17810b50046900402480c4104a00407030ba619442800b584101920007040010565204001000c520306481007900030b01d00164540080a00c1542554440400c0000c1454643c1e6030381d410801c0d02403060001c0c0182c1280a00c0028964491404e082c1c0d19001c903401e0449041404405845190070803090700511800500d20030203440e085008488a10020f09a83d15103545444c01c00460748400080300560103401400001c9087c1c5800c0c0b4402c802040d9503c0c031080e9200b00511008100302201034980221565000800355001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 585359298 1250 585358048 585358063
    0x7020705060f040e01030507030501180b0609040228050321040e0a06240206070903021c02130608010b1306031109060303090301050109060603060e131e1e02010f05030906011a0408 79
    0x1f0360060080700d19508100382121700451076051042c0040e4610008640702800103030308164100c46004582d1103e10006540814180711441e406414403091129045607096000840342d0a034140c51030720390080822907040c048040201181da805100502c00c43c0c0140b10441e5010301c0000c0d00050081d11120703183c110030200b0b40c1c4c030340602c422425003003d200c1d41800810380002c0300d4140840441d0031580010703203003e4441d29440c8920010000c54040d95a400c0f07012070a206004420800e45458003a80f5001e02800c180702800791500c0e0f450350a01c50320078410799003100c0d000183c800c80c080121003084100d1901800c0154544000d00100c0e190799428820303603001b801413090003d40f00c1d00e170203030140581e40c8070740c03103c1c58043c504c1003002101d142044c042448203500c507000040070340075000642c4a480d88144081c0082210034109415003c14800264100d0f0007600c8842804842d100c08507903a00c001ca80c05181340c1c0152004014014034856030b0b00100c000300f441c0d5030400e5140c0c80c0c4145807205 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 585360548 1250 585359298 585359303
    0xf070f05031c0c05090a0605031e01030f020f030d08040b041103100605031207030e10030204120c0614041d040521040f053001020d140a0b0907020705060f040e0103 72
    0x34040110400b0031100e102e00b41000e14241840c0e800e14076030303800164600c0010b00c41c2c030080c050000000b82c05849820390500621300e000c02c0c1e1b190156141d060501c82c00c003009134124000c09001c040c00030240781c00210850092840d65a0509507079441d50740ca0740e40030300a40308070b1f00160350016000312a034003400151090f2006c0c8400252a81c603140c00c041c946203c0203100c2040503000c000c82404203074483c5000301d500d40180c403100369040803c08118000d20032980f10610140d400c0303102c0d10411850181c4002100d007079945028000c00b15080c03000310762141d880350259408010701c1084e4043c1020030180e6001c0d0040c01580c024505108081d401c0c040c22110503001190300040c184544070392500004007410007030320a9000c170070418140c086280b4002d881040820019405400c040d0b500350112100d003410340e4000e002c1c511040005002028040d14034410f09400c0030440c0c1d169040500440d032284110303500403c3c45078a00018000950b02c0001c3c00d154000b81040b0108400c160300403034500030341c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 585361798 1250 585360548 585360577
    0xa020606010801060807050d180c27061401262e08150a020408010f091118070e13060806090d08010b071101020c04090c05030f120f070f0503 62
    0x40d00100040ca41007050b0025803c1c040001c090000c8a98828203440300300910440005018440a0301071116007151000180248002d6101150b203851040f00742e214030040541c048291201480a18141e03041401101100c00304641003461562080d20a40300410b42014031405c6940030484459445e501290120a0403444d1080c10407580c0842400054100d081c070074400c0030904162420362150710700c8140ea2240c42d05000820342d103000030317811980140f00c150003c210740540030030701d1f4000d441803200c2074a00b60307850070100449003041c040130b1000e190f030250f00e40166915282e0680700407005140c0140c1182880760004142e20040c071502c0701501c0010003c1410f8600511000c0c0707400394414012040100b07410041020282220680d10515402030b085100903032030500403490710b03648085159025051400610606c000d1140f0f06041e40e005038295407081c0d684061140d5500b10700106428511410003510030f0301380f145009010400d00c512118003d41846441d203d02c1c45d01300102030060007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 585363048 1250 585361798 585361801
    0xa05160f0507060e1801090b0604180f0e0309090705180915032b0e1f030c020c030d080402040e0109080f09040b0409031709030f0d0b0405012112140a0206 68
    0x6613000541c031240c062044450101122420541c01001c0d0418411000907035100d40a0083c5640e42c0b10643c0d0140003a9002003000085c00348458001e81481c52050b90141c3c40c0c6121040d4090300071084402074040078004c060a916110303000c5991346c1c04005444c0e0b0019211640351902c2d5580c0310294020100814581e5039901000105424040c110700c80c80c0c00095a100045034050000c200101500c803181003d095051718079004c502c14512160042021501d6503100c4880650140d00850782141294202c0e051504214141036542410080400102e000000018010b2604e0340000e07a607a4003560010803c445aa0748035007850f000481031001c4814040740541c0c0c5030030144204005403c04640a2000038a940c801510004c030550200d0f40309903440c8001078108504000300c8401c540744200040c0c0c0c1d500742c10716940c000c0078074002e120320447c1000c0001446040c100e2808000001c0603d0f2900000903076650501c030320a03100004024010844106103411022801801c51040382d5000380401c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 585364298 1250 585363048 585363059
    0x726010306051f09020d090c0602150106020115090f0207020d0f061404170c0708070b0a0201050123010c0606051003020405121b0f12070308041805010b0a05160f0507 73
    0xda41c001054000142800d11540843c140c0c1c0482d014221640804016030f29041c50362820042d0a00300809850700fa0000e000183c11075001414140c00b40da010000c01c61642c850313104a0070b81d1803880c1c13041c030b9118082c40309105e0140c1c258840c240c980b5001c80014a421000d0340801e68000420300d040e11454a030248100510459004030900000e016603d00f45600e01951400040410120b02900f18440071030041c49500c0d00300409805005450101c5160301e42d03645091f42c084d8440002040194282400040c0300d0302006855556250500d54401d01c810900004540e058800602590381c503440b00c4001600c0e407070300207100c940c1d0540c0d0340d005a90b070340c144030600605008180c035040300e5911001044880c0d146559214000c508101d07060b00c0302030308220004030f500301200f89600003401002c00000402c400075000340200c81e520181019441941d420304400c03550709210b001e00b4030b00c0c1048a0104a0b109000505080c40d02e401f812980d4039041e2180004800b15120403920380e40a460144803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 585365548 1250 585364298 585364301
    0x14030c0d0504080d080424241406300414060423010209090f040b01060c0f02130f020d0c11030f0d09050f0f162c0726010306 55
    0x403080c40381007451a00e850701c0100d556030310180380382d181040002000f060810a0202c481505004a001404581341c8440038103030003014006c10701e46c10089105440844090a504c4280441d000120007601ca503d1920030700002d58000c00940103100b060492001603e000480e55246d803110440c071414840c50240340003440c0152104003054107034021070800000613a20840892601031410000c40b03141ca66500b00750280c0110113a49500241c05000c0001071503498280c144210b004131100005641e0320801600e200f500b0300c030050640400c0900000c05410001002066150b04003030002d500744410786018200d8000344100c0c0c801a486840c8201155442a00301c110a0b842001a501d007000e1807890707460902ca0007065071021921160681d040c0314041c0300300c005081c0031405032041c03041e41d000790b01d4907010201a038064060f00c01b440441d00e9808505130340c040710200d0711103060001001c6459170031008010452020048089643c904d8170301381d9144800d12008000440c45c007541180f41410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 585366798 1250 585365548 585365563
    0x71e0b060a0929150c1f021204111309080705010f050105030a0f02030109171b1b01050d110406050c0601080c0a0e040f0602270d0b06040b060714030c 66
    0x1091814503030411403400700407000c2c070a51060040d140d60080b615070b0216005281e940c0150515000100c5c440030307914000324944108120b0256405107506200203440d08038040d0a111860500e065000600000c4c0c110381c000b0b031a8000202903155440d40403080c0d9056500c2840c084894200c0450b02a040081c2401030000070880394034148029810040401e58403514200d000d40001c0d5114810300a40d00e0a50101030081d4004460b515030940e0a03544444661007164004000b4210070403441c1d0850b80032841080c90030304050000302408030352004503020b40240f2414162117648083c4c140301403208000410007040c03191500ea41700c01d00d000009041c103c0592010000350001c0c3c148500d1591050821016200400180c0580e6115803c045840382c070252401080e551001a501c8001ea01d0382d550b000c02e90042c1019800c03011901c00078000c5040a20340000c1c8907560b00d60208040d131805402a10704140084c08007410a800d58031160900d100c20340703840c01190800107040f250b1107028003290703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 585368048 1250 585366798 585366809
    0x90c02010606081b0f0307050301051002010204051c081204230c0d03030c1701080a140c1e0409020301020d0b01021207052505120105060118031106071e0b060a 70
    0x80000510b8840c000d44020002803071003c2281d0b08039200b0000c0d06032102a24803440a100049469180900d8090582c1d8001c1c01060720402c068070350000c0f00740c0305001b254207a0707902a20400c81c20800859000c8002200d6030f00320b500c4a03090225101251000840d20b200b213000d00000400c0c1542c12030741035980c03001002c807501c480c2c10800c0c004180da221416502c810a50500c1d000034a40e83c0d90b081140c1000300311020307201c84c84000c2c000051540340043d402a0980c00f0750400018011203044040c1c0e210310034407105801003100d151071040042a00400400450040c0c00403802d284241d000a0890f070220321030001199035106040e206590411204e14108083c01c5d00e01d01d494025250f0341c0e51000410030301c801c10b2468003060011042c1e403c0b5004020500030b8103485440315641d9002c2d001e81811184103000509940245011b0040140c28078112508a04c0400000d44060306204007a0300540061b42c2c1000d01d0000340c005511000070b2011242e000c0c0c0f60b104420f09005041066201942d88032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 585369298 1250 585368048 585368051
    0xa0b330705120906120103050c01080c030f04230307060e0c090702061f03021203030412080c0409020c07050d0f060501090b011e090801060b0a0306081b1509041104090c0201 76
    0x9060020310001120440c01d8030b40c14000c0d445a2900c0c001403818030520880030741d582c00c410000000c104000420700e60080090300c03107044550b104c1411000a0008490007540454180b02190101303103001e00e02c100b40000d88418401b9090000800ca00d0741d0701940e402c03119a950380c0b08120000e40e0030300004191300c0d412a01d90712103040c4604000c0d40c45502508100081404040c400790010518000d00e0003140c2c05004d030362044203503803405034407034100f110300707035902e24860300440e42d56842004d00c40c0c41261002d40290900c0c1c00c05001c0c50007504030100c10406031103401c0001c1910b980724002034070145c1c41103400b240031001a01c1c2000695106038402c00c50a8106129540940e030004010520540390305455106000055400c50b00300c0c0c51a4061341c60b9501c0c1010108542500b00000d0003a107041c2e031410300c04581c0e24a0700e59514018610810b030510038102e00c1c00b50515002e4415213901c1501e041c80e50800ca0030710001021180701407481c0001d58000541000240107601880d002c80307249000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 585370548 1250 585369298 585369307
    0xc140105270d02070302011b050604060209040f0b130c02010225020109060801060c02102705040b1504090e12040b03010302040609090b07080604090b01090c0e03071d0a0b33 76
    0x2e0195984105010003418403040380c1e49603e0038140d0380041c3c19403d03040001c81e02e06003803e00340f4000071f42c004020a8001ca040c20131050f00c500c03070b500130300040250140120104400341c43e00b0500802d61544200c0c1195001c01c03040305c8070344402d003038090b0305594200d071040010303600d10000d4040d08003079204000f071050410042140540200340f20442903010343c2c007031805080e50041154210300d28902004074252800c258100b910341410355200b640c1e401e44003005a00d01c400c00704841401d10421051036614100018041c03c0b01c03513002010b2402c010f10445001160203416114150020b402c000c4841802000400a602d0903015401c001c06d9404401c000000180d110074404840041001046c0300c13100c000329155882c3c980c8002055508580c40c801c0c41d503100c004000241c00d544600400051001c1c0d01c070080c3d4500420341c1070444590160b82654001d14040c4001d5144004003001a070039582c240ca0340040e283d00e00420001003850038444401440b07400040c03003182c1c0c4000000d409280a10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 585371798 1250 585370548 585370573
    0x50316050108010e36010c080a0b0a140f0301111b061302061603050904020c031215030a0303050c1218120a02120304060906060b03250f0c14010527 65
    0xf0009000514103800040f15510f00b03481903171000c0c2101c80c401072a40c60441d003c2e0070320740d0100c003050080e049000140b00324400c40301001101c034201d004503101041036449c1d5488602c4c0052038043d044034081c0000c5590781c5d040b0030300282500300d0b50301c540d071090712040b83d444a464103026280d0300000344042101442a83d0b0085450350045560040c042c00d00600c44038145801101904d1000304000c106564504d611148640c60303401403540303d01c0c28030403a07000c01d80400c1400280c1d00c0681d00a401803111600c103460840260001614941080c0c5003000742c40203403000d2103003151217042d21039004024001740c4070050741f0b81b05041b0360f0402c10001c244040c04c802a800710300c20b00400d0300398004a841e5280c500788200141189030004198500e030060000361410104007541c41005044c0b21f884800b40c00640f003603080e4105803101d00002e50054800519035010f040030b1103441d80a80c0c1c078065804030350107103542141c1c41641e4400009050303a0311540041c040c10300c9000343c9800000603040c000b452a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 585373048 1250 585371798 585371821
    0x80d0f170126010e010e01090c0b16020918060c0405100e100509040b030109030e0a12050703080a0c0605010f0f0503010e190305070606030b010e060409050604110307050316050108010e 81
    0x1100840c01407800d00c10ba804189000d4000e03c99205005008205480702041000d009101002088495407005a8000b40c0c0122500640b441d00c1c22002c1807e1074201e25908004d6141c0000386000070003820000c02560034042003000500c00c1e07014980c0345969500b032601300035820742002d1158007046140c4d103012003180c852105d10090000d4900f8450340b074030344540001e800392180050b01c58040d03281c00c51403c14160b00500900300c90303038141c55041d0140d03207500180c0c01da0115600080d00c9980003400c01c0000420000040c2488078041c0351010b07680c96595a000150f95081c1c0c09101100500f0b20b0521804c0c50030685d48006010880080105c0382100c0b0000e074449089008420500f5103022141003410700501c221280300ea4407150811905450345001104004280200c008600304a000100741c0e04081c490708541c0c0e600040100540c0d27841d40d803500112101e20b550b040c0c250054178400903280c3c40c00c0100d40040d243c5141ca1010081c00c010006201130030580c8007407140b2001c0010301c00a079951 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 585374298 1250 585373048 585373079
    0x16020c060f09061e0702211e120d0c0306050a0f060807030207140105010f05040b0a05040b01090f1d01060c0b06041a0409060b0301050a05040b0c0706021b03031602010614060c07080d0f1701 83
    0x8158909540164409030600f181c050310188200000948004ac82e102030740b000307040306065241006400d480720280680e4912a01605405a100d50740a001070741c000d4041551045040c80c2c05131401d1080d0f901c600e5100f24001d00f5000584d15070005101c1d0003103008000c1c1c081c1000395810044081ca150020b01c0510162107014001d40d1f440742c1840d11039104102603c0500341c3c2070070051030740e40d0b10713000d80c5244014000000c074420b22071000840c0c41e84c8940ca01a0000c0d0b00501c400420340c441c2803c0000400a94140d0304158a40300001c0015484a009550700d941c041c0d200003801980c41c0080c036081d01e400402d08c0e05124a420204000200040c0c1020382044000301c503240c880d000e51421a0081c840c800d921001d40c5802d070441c508214001008521034807030b002c0d84034030003418010242d090315500c1c0100b25111501101600707560070b020340503251310729007001280d41c12665003108500781400c0b1550500011907161041c0c0c00e064000314900c24010060b1108175442d8548000d001c0c160b84d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 585375548 1250 585374298 585374323
    0xf07060911061903051b0301060e0a03050708161202091b0c100b190f1401050712050a090e06180702030903070e16020c060f09061e070221 61
    0x6480440c03205000070111001505000034040030b80d01c2200c8040025504032603114840000d041c00d0008110300c0c1c1c0f01100340e407801c41c2c1c5c013009421a401d10708266002d40c41c401d10250000700851001010400c05c003d208014620240584000c035044d415000d50b20803a40c12134500c01c8108404a40141c90790701f0b07070940c4038500300c490301c401c1c905205065030b40b880303207982d181440d100302c081864080807960b10400800404480400c10040310303031100700344264980f14003a00341d20500000c0091200b980e00b0700364110340525000b8504442e650381c0e0221f100c040a450b02c0094004210302113a190009040340180500151483c00c42c68650000b400802e5a40000820711602c903002c103500781e0080042d10303069400101500c00c495100c40c8800300402044481c46448110201030605440c008144220102e4015080714a024007501c0c07401c0242e48819500c41d0440c0b020401d1400b020b204130074100c0e131483d10f6010a5502c5946004001c001c0502003130300345100c19500d101034845000045e260481c41c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 585376798 1250 585375548 585375551
    0x109050303190207120b06130513110109030f110301050c070c03060c0c061e1a150304020a0314010e0111041404050402150d0222080303070305040c1205031c020f0706 73
    0x2c5804201c0c10030301e15034080d01a140080000c03404010101c07203420f200e054180d60200c080801d401c1c11348241c810a542040650709141e170800302281e03801200c004a46810b0521280d120356035a00c220411000d044251800b0000030401d030714a203800e0050035005448100810300300300d801e460301081c8072030a1000030000c0b65254070700792038180034640d00580d403030b00702c1c1d810011a404240400c04802d5107006218620345800c0700d28500c181504114500c50101500340202c02541030b815081a52000d8000c0e031b4420505200040000c011001420140181400204a11003215070003429501c65021b41c2040040911060101c04034030684030b00b0340801154086660707190707800400c1441070500344045130000b000a0304500324601d6001030080d4820408103c1d21404a1681440c0320340d058090300303000350400c10109130218803c0c2c00c640e4109010b1210900402d9560601a07181d0100321006c403000e410103c0d080d03403251590000072071019500c8505510f001028840102e030381c0b084010080000307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 585378048 1250 585376798 585376837
    0xa150207051005030603060c1608070503220314060103120516021e0a05040204060503240a03141e0309010302160f0309170109020303070308151503070e0109050303 72
    0x11442004448000c0001908404441a041100410a92040b2800d034000e00c1707100c0219032028030b44403c07140d0001d11290040c00f441515529900c10b940070b002d040d2502e22041c401e245c00002254032002440b1071104140c0c0c0000d00c0d40c64442c0b120401d12103000c000e82c00c41c400400c042854204240041402841c0c00384e0b0300e4a0480404c00e13030324403088001e50032003480d10300140e5488506040416080045034420b94040e514410030007a8400c500aa400085081c004a65841060301d444044201c0708165100441c207202c0100300b03000307141d42c8141c1d0302e4402c4080180e00028240a07480700d002608120040b10b40c10055200c1d501d200b8003a0450400d64000703800803154034100c0709866034a40c461103648003043d090400811049590165a00240c1c505044401130201441000316481d03002d005542842e809032425108094000d1003110b006118030b101c022242d40d441050b006062440c18040c2d224180550028079200301c403d4100c1c103004102e80140711a5400109841035a2904c580203100c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 585379298 1250 585378048 585378089
    0x41d161806081e07020f210d050c0c060c0306040c030903090b0f04030606091a0d110d020409061d060603010608060a0906060509010801060614090112050a180b0a0b0f0a 74
    0x19100c0c034411116000c000c0c0814800050b50203e0800a0901140220b0b07040f1f040506140b0f02d410407600c03070305114220402440b80c100701c00d50011944540092a89410030840c115617070b0912000b200e00a896a00003c100242468a44030b0080707206c41c0e5150403ca03ea01c56034000d80340c45400e00615030354a0011038041545080e40c0110b4018513404003062010390ba80340c10002c045c110075203400080f10108025480079060000c10400c4450300000000d0780c03a0040b07410301041200c800416600035407240510408113000e07008004115038212001c80d051a44100640d0411401520a42c440c2e414440100042440025040c2d0800030304c4800182a401a140107802091590f0100313402c1004200005141e620650212080b541180c80c1d11131040c1040052142e01d2184c10f038440e0110710311008150507800346034401076000003403600009a0424601d00301c8810030f041c03201141c0c41c81d200801c000e00d106040c001c40c2c9088030142d403011441c210000026113004182d0049404c80980d0481d0003c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 585380548 1250 585379298 585379321
    0x6150b0a080a0f0c1e050703120f090b0c09010806030607020307061a0d03170a020306090a0b0f0301020f0c070902031b1810111b061e041d16180608 65
    0xf4075041e400d800f008080c0c1d0b40b680c080e190b469400c10b8507581440207040c4282c1c45001e001100c8081c0d90540d1500b150401c01c0a0b400010703e00450740c102000d580b0700400c000100c100d4221030280d104c014940e070301d8002060004026000007400d07240240c0001c4140002181c000040d5440640c0c8080d000c640c50b144031a06507008004400403a80c001d12400794141810380190541d00911003485440e07520f992000800000d900c0241e42c80741c0c0000c0014005412303481240d010f8150701c10024505d00b05840f0b82d00000703007641c02212152609141c0010f4228444000304092002800c502c0c20070350451401c1d0480588200302c025909680c13041c00070381b512081d010700c0840d100c64000148654906900e0120007822540e003600420340d0b51084044074404450780c1c0b21846443c0300006c00b080c3c905000c43d8000742d006140703040004400303202884040780c54080ba041003090f040d25900d0101c0c0c5443c0c91020824004030000611003400708100d800300c0c0b0948540305d440c00341c0b4042d04003645d0b00d4403036200548 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 585381798 1250 585380548 585380561
    0x60414011404140909010516080402042c010b01230f0f03010b12011205100f020f1b010b0919020318030c0708060612070e060607051005010306150b0a080a 68
    0x2200a01d00180200718400e01c0203680c0c1001e032040d90400226036802070254201c420a8032071002c9901100c4280310307140d108102d403e6200d84040d10100c1c0c049980d80d0b00d45680a54450004e40d011058003012807050b100344a062013400013480c0448141d04e041800400311140c00e240b01c0c1e20070b6400140800300b40c000d0412540b201014050301992580e54441e09001608422100081c1404440000400c807540e031107030301c6881ba0000301a0100c0a0050049001850440d604031090758003031108158502a15014000e10a01207070180385094003c0d01f254211340c2101080c501c1042e2103814401a201e01d2142e0700b40d50950300d0001070b566200d10040f900c40c002880c2c810f5409200c0018103080c040300100383c1c001161008011510961038200411030060714440d0320a18650001c0c0c01000501984030410344c05c600040d103180c0c42c0621a488035414100e041ca0f403054141e40704c40040040200300e12544a1302c204484816402c1d6080c80d01c18600780c4140c24696082115047c0442c003c0d021035813004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 585383048 1250 585381798 585381827
    0x18031104200d020306040f06030305030f071b05100e03040e0a0207050a0605010308070b0a05010513092d030206091f09060b1f080a020c0316050703080d0f0c03060506041401 76
    0x3142c445a03010b809030040e610031940c080c012420300c0f032480e00000003402100140c0750b250300d9490440da5100202648000b000b007003501081031622402c0c02681030407a424040c9401080070f41603104c0c1c4440660182c60910820004540c4200000c01070010030340803042d045501071703901680d602e2482c00c08625090f1442030280806191000000c1000951802032030b07514880c0d100e44407550b503000e900c0c82c21908240706154200a0700c1111000d50b0304141e1105180501c1241c40b6054400075030503070082000b20618207588504030100781c10a02d0380400c030440d40450884020300c1c40788510056016806c0e040e10420040b991180440300412040340c20114a8240152102d10b101c00d140f58240302c071002d010703100004602400c02107074052a4500858114081c801e00451800c000e60040301d5114145080640f280d0003481401b000150b1080c0080c44a20404600803940d0081100440d0858405c1303440f29040c0b5143c014100030700d807a15000d8804441e009034000d43e1203900400103850440c2c450401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 585384298 1250 585383048 585383111
    0x1b080a08030c22090b040915020f0f07050d080a0c090509091924062603040803030906060f09251206090509070e0907211203090318031104 61
    0x4169030f00d0100c20a1001c4503104282440100f6038007040c042254000c0c80c014081254194096401026a4000b0400400a00d08181c0b510030403180c002444e40051404079841e801c0030b400c41d820036a01064542d00305040083c01c2000c851800005082904d05205213800f5824400000d00d5043c000c0c40480d1000d4407121504029200c281b4207450780800307402c11003024441c0d00b2102c40c8440801e12070441071761b2946039402081e42c0002800510340c40e038102500060311040101141c00348013440070b14003a801140c01802203050a40411542c40b200981c403602a243c018200300c1861184400e076110351100d50340340d0403103410401045034094542d103000b01c2c140341080301c00541e9040700e52103148101501400e4603840d40e19910401d034001011b46800c01d0341d030700018091200600310084900114410845400307410000c0e0382d2001b0202183e200b210109950724400e000f416040f04819010844403144089014110b076280000b4200e841c0085001e81d80c0c6244041c4000540c01d011404244e05186 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 585385548 1250 585384298 585384337
    0x8060f041209091e051605040b0706060305031c060e07050711150a0809100e0d030b010917030703200a11030a080301030c06020f0d080f0601031d01091b080a08030c 72
    0x240c0b44907200700c0d184880801482c1c00005031b140281400c0c0d40f084680c0d550717191440d062a041901e0100d40240c0c00a68400b40d4810740000054001c00c01082a242001080100e048480a0710003c95010b9800f4894004100c010002e10340d9024049070707001e40e40319038040340503d210404a050303c1110f140c81c114240d40042c0d03000300c0a8000c85614407500320300302142c000003200d511401c107071003604608d00740030b07807014a0681e1a54040e0704650a090701c10301d845406075607100304010845550354178100168100007405001c0c07540c40250040b2050b0014841d98039a08850485079484030041c0c4094411080c0310340d1040d99540512560220782d81044a59032256120300300049866258850032015100d15a08012044000302d01035080203030343e07256004542d80e000050041070000134009030415999800720207170400000b01c03215071180e0174800050200d986141ca800c0003415520584914011030b0802c00c5080e2000911351010340c1c3c0004215141e44030031342e001c0701a000c0c040605101890205 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 585386798 1250 585385548 585385571
    0x8090a1e200105030613021207091706010308030a1509050702070f060807210f2d050606031308070506160f05070b010510121a090108060f04120909 65
    0x10351203505070048090242601045958005000195440c5804030340140b000500500c2c10304551004100001005441c1041d0041c00e040008002c0358640049001c03c041400801c0740d0b604001014003542e001805294190b840e03140407404020450f00c4501d07281c1751440d000301d803a00205001040c003c04240110f042205000c3d495100c90f0242100030801183c001035160f20030b40c00c2074003902172501c400290380c10904448041190340c1c0781400c007854903040c03a90422101d40c85082180e0300b4058001150f00d5001c3c0f0b10910030b404440600c803030303a81440e040c44041e0785d40c1d800f2240c11228030007140c81d0004203403504034094082d11201408502880d400c1280c20211a40180140002e540c2c42d89038040488800751554001c0c640040c0c0311240c400010b100b41d0408140e055003400140c1400320040d45013181c00400c2d692001812041850f0ba43d111006074244600352602400210014140070b14221000108004000340094820311030000503045a034080c4200102412801c0400c0c0640d903041d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 585388048 1250 585386798 585386843
    0x30501020f04150206190c0c0203060703141803161e080c01060909081b1023011d15041d1f05060114130b1308100204140108090a 57
    0x51042038003900c3e105501030300861001c240c852045a2000322190398031221040c20b80200610003110b4140004030070260302507507041180500c00e40040d0390101e51034030003155071181c480d009040c1041d480200c3e89007000c0540048142d0b9000c041c3c4e840b542e0061191824106c041d18081e070442400300c1382c800c00580c1803011801c010850000c0f900001c0c09183e84c0d03030000e0400c940042e40040d040d840144041e0b0114207818104510340c014180807682d845400b01c0840040303c0c02500400e0300c5000d0007401312002c94445848500416046c1e0071080c0c0c01102c600c6e00700b0540c9000780700b0421103c050350145000d40e1142d100791082e020b890400206200981040f41d51074100180c00d8035900649900051000c01c00e0061603c03612043c2e544074200c82c1d05110524280d0000740241001c01c114400200c5d20078a104050440384c04000201c24002e0b00c2c0c120300c14184034a50590301b82c91f500410060103154a1101c0c9520402c2080c604040f003036072078000c03e03400c040031003c0c000c100340030000d8061000d0b00350 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 585389298 1250 585388048 585388057
    0x7050909030706110f040b0307030b04020c0114060303090603010b030a090f1415270a0b07031b02060c04171f0507090509010503060a051911030403110c0a03110604030501020f 77
    0x500b0003085800c0c8240000c0f14a0301490017561000d5104001c18040d03050a513010b190004403600b400700b0481500f00020f41603811018849455070741d1504202100304009980035004503066024525004d0f04002103541444140541c0c55041000000700c0c2c19803d66610500020f50001014802c000e503510740103a0f80e410100b4168020f02c125030703081c0300352042c04509a01807221200018240d4100c021ba40c400446424654001c502540741e51402140d103070b40240d8420255960300084220b0b6031030141c41e044072000300b2001198007c50400c02041412000c1310b094942c401c4483c0d21230600402402c6c50560f05443c200c03030130020840080301c605110b0b00214003c84203511160b0b0400d03120011b0055400f000d1040e01c1d416801070021802c1c80c031b010741c080364010003c0b11520710309101003501041500c58414114017500c90010812045c50b80c0004641c065112003805041480100c000141d14500180000382c150800c40c4c9036060b250343e1b000101c0d401164400004c0d51681624900544290003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 585390548 1250 585389298 585389303
    0x18010807060809030c07060e0a030204092d032a06020c100c0c1e03050c06040f1208041a060103061d0a060608010e15030c0a0e070f02190212070509090307 68
    0x18a404101c40400100613156082c4c200001808640c0c6070a80450f07806c49a01c20180c9c00210340b40e404000b5032200d0140103c80c0f4001e418510542801943c00340c20f01110480040ca894081c0e143c0200081e030240d0a182440c2c60300e1108525510040b15072801038804a41c01403070700d440000c04101d050701c042940092890074140422055050280c2070314030b1520407a0062001c144449140c1100808140d42d00080c0d009141ca2810306080310700780f629081c0141c2e42580e04903201094002045103030a0600041c02039894110002d042955030001c5c010164030b151240c1000725400250203034403e900074001030068001c0d03c2060f42c2e01091032403070708105840d90440142401404140b16001300b890b1412920081440e4000f44c0c0c40200b8410340b8101c030b203861039060141074440c1200d80e503840030020141c0b044943c1a43c0c00e0070101d5002d40400b8032a5000015908808000d1032484501c01400c0075454040c0d40d00781a04409c2030350075080c055650070130b030341c405201c00070f2020000c80040980900752 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 585391798 1250 585390548 585390557
    0x1204060506030c03060105060f031302040603050610090204030f0609022206030b0603061513022218060b0301090f150b1207022b110a08090a051c020f1801080706 71
    0x3d103031418141c03200d41c24001c05070000c1e020007050040a05440c0255805410046d148420040c00d600040564aa41d882030329a0ba201109101c2824219150741d0000c25114408510f454915621041c910040000180070940e85005540564031140302e00c4012a0b103006c4041680502c51040c06d00501050005444145001c000280e0701d0030700240c0c0d20300075608003a6040d80c40c9020420400301d10071003030440c0030302078080c0a002d2604072005842281c418404480320815410141c6030303492012048402150941001010490071030a03004581c155608050041b800c40510102c00300a000ca00605101a10741d03020700103407540600300600007040d00001c0e404469110510102c0c5c2d2024101c0400b940c2600c481c1085003c900740c80308000d20311145041c00100a5079044a541c01c0819546007943c01c0c5500123203484286c54011091009400304940d400c451a1800c0711030603014401000c002e010707081c1349205124036a1440c0d043d04ac83c4d400c2c070000007510340e10f8151703503900d41501e07100d4440840d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 585393048 1250 585391798 585391813
    0xc12020f362208030105092a03010e090a1a0c090901092a02120307032304060b0d0305030a0e070321120c05191101020f12100f0e070302120406050603 66
    0x181480301040c82d0958000200c142182d00700700070006107510140071004880f400404400c500014440c10720950b04100c000a5207075850701c1c90600700c00b0002801c030b81c125004420840c0014210441550305200c2d00441803807181e81d0307080c49607101e01c03501c0000c903804a604000018210001c2d0402401c1e80e100104944141c4510518101a010495100700142c0c000713140902000031050701450740003c59190215444414030014400411804c1d804a11241604100420310515000b087d40400b0159522003110700141c900511601020b007e4480e001c1d00c448103072490103020440f100103590000045852528240e800486507600c1001510100305101c4402e00d0326581392050710a600540d8a4481c50651000600c4a8480c424102d103820b01c00c0084040701c1c450350910182403c91030425405554410300e0817a1200798500400001140d00d4505c400d100000051411404035001c0000d210304d56196600c0a80190040e5408a03030341c406030004205c140a455040240100400e60a54141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 585394298 1250 585393048 585393091
    0x3120d0b0405010b070b040614040302010b460e070210060506130b160507060504050310061a0c0109061107020907030c0e010e04091407030c12020f36 66
    0x303440c0b0074401d8503440e450a015520100c2d060b02c01035036015100d0707100050600400750a040702070800307813819030051390344030702d2055181807103101c8209c005c0301c0c4c50b00c054103080401000405440007044454900a9010014161416841d00680907101c40c010680362803070120f50007513458498544088402e070810500203000d00f0060115061480e0300d80c8120003c0e420000c01c06025400110b4030246012007990080120b0030610903500030741a1580c2d184d550b145407a04062404814107903024159246c074400b0031007441d11000c0110040d4482034016220024a03540754010070043c18040d014508085811f2240709258005000d80d5100306c5840103c2d48504c0011001c0f192080005004204590f898441e103602540d507840541d4402000416988a00d40c0c0340c4201c00401c05141c04503900020040c0200803200849401034241403400d0003140220b074001a00b81800d6004139130150a907000b030201d801904282e02000c0301d841004c050300c0c40d0072403003803c80806002c845005207070700b0300c40e5042c2c0c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 585395548 1250 585394298 585394301
    0x7180b0702030a12211a06090906011b05010c2001020a02100e030904090807050105060114030c132103030f09030c080921010207020901060e090708060a0503120d0b04 73
    0x38816005801001c000b08150345070070803044180300e01c0c414401d600002c48404181d100e40c000740b8051200011403102c400804498510800c800c0513803149806100c0200349032140207000d5400b010920309480725140040d400d00950f2490b500140180d402d2081030b106c801d81284e2117507070403031018040001a10b00304401500f02d0107220400c0005030020140103000d40c4043d008254142e80140c01c1e41d140514440c00102241c549840442d01c0d92400f085c0c14003448020311800790301050a00300504264800c0e000c040140c030006008480040011800c01b04440801c1600e170043e014035003c41550a030014408144440807880817400203007000481300c4001c0710b6015850000c1c0d032580780e255298040d543c0d454060b40020f20b210390802103454401c40c104418140c40520002107100040c2eaa8a0600501c29400f105801c6101800b90041c4042d00039241c0580b65580410603241c05541a21460005080d86c0e113268402d40c2d1502c206001a2100c00e40031004010417407129004200a44000e400d010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 585396798 1250 585395548 585395557
    0xb1c030e01110c0f011e1206050405060105040905041a0903090301060b040503120d020c0706120501080601050d0f03021f0c02190c030b0403020102040f090f0c0206061e130507180b 79
    0x1007a8100c000683d10303d0500d03020104043c20141410414805140917541941d2808054540090001e0250034004501441118080d1405172404d00580c03404a0000e481c900c41d910904030103540c0c400006013440803168000704082102035030941e0504003440003951f0381c2c00c03036402e4520079468904001109940102207804642c406000b4051101c0f9885001040d83c00c440d00798502540c00f003001542000d410f22060001e88100d8491903441c1e80098011403c45030141c00c90300700d90f40010018045565072581000d20251300c504c3c180c00490317480c58204d0409000d65034000407490301d0550502100140e400a000c850000e9003281d085000c000b0300901084d03080200a440341d011040240b002c40c2ca556900384d8094000d0001624080c3e07a0481603030060320580c001702c901a031f1414280e00f01c98940c0101076188146100502103810003800090568400c00b00c8140a4040f066051041d900c6010050480c007a440e01708210306c0c40c184001400324200c2c11402c00603481d001c40c001c0f80d094407540544 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 585398048 1250 585396798 585396827
    0x803041101120c1b0516080a1502041404020903100c021015050d0b1b160201030c020303040c14010e0418061b05040b0313140d021608060402090a0b1c030e01 69
    0x1107a12040f007014580d42d010130506885a005288141e0a080d00080da210014540b50006040320306c41030030980d60910040320702100c0b0030b004210810039030712000d0b205031580c0001c8400581d1410750000092915841c940040002410800c2d01c10300b554000c207c050090f078100300240308030075100482500301c0c6400d0113000e40c0a924040300f900801e0400003816800703180500c1121040d0601200c0d143c0d1070b00300c580c003e0b090880801142046503810300134003c2200c00c5000035800c5040c1036a80c05d00e41150b034000c101766841d0084440380b803603100701102e01c1440005042001444880c40861000500c581010f464642c2040039a20b0404071100b040440c6140d1940d513281003506006070029035520160081034161503c00709080894400c032140800c2003803c800a21a40f5039402c006030800340080d01010f41100100320403c440c50000c501c99501c9541210350a920b43d42d50404140241407103180103400000b040348030905504419014201ca5010ba2030704442d401d041c000445405e01c644083e03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 585399298 1250 585398048 585398057
    0x403080f161202090f0a08032a06060f041517191703060f0a080d0201050106030c120b0310051006171603180b0901060f05190302011b0803041101120c 66
    0x2e000c25032400d074040d04041d42c008180382c1403400326000145408005800a038034a81000031420119603a0343d1944001c450959079500c0d80540e02410140c0b100f00046c02a4000c400512169042c0c1da00c903072011022008014a000700303542ca400b9801d5000b014030010b011030f4444c0158442103d04802c0d00c4920603a8040325043c0d6080c2e180300c030403120750005000242c003c160301c980c00b1215074440c1980c00c083c1256100a00c210000d07004002e0030345406074401800d26141401c0e620805520400c10b04001d0610725011814501040210b45042040d0280100d0503240106000400d5007220503941203038051340c0c03240d020320a60f8000703003945902030311001c0c0080c402a4203003212902a8205070900c0703100030743d03501039040305840d1406000011107040031543d65440c0148644035103007111001034402a100c065198015004508600b1a54040a1305200800030000a2001d140c81c0c41d0500030303402003000f038a1341041c0ca0602120101c500d030f444c1c00308402d4142c41e58503482c0c0348a10059420a9500d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 585400548 1250 585399298 585399317
    0x40807090b030303040212150c03041a07051b1002031303081609030b071b0303061e030c0b03091002070c0e0a0e0d03020901021905060702060f070e011d090403080f16 73
    0xb04181c0174103c0f02c0c510814001c011852143c80c00ca28074180c0309030f49da00540e6030780f46001e2920303c44105200441400c8030b8154007d0107020b5030701c2815500d5004404455101010f2240e440510b01000704a0702c00303046000004001e02410f10300010000140b00e07480e03500142e125603036000059041d0b0b807840400540f503150100040707098001e0300e0b60000c5084c10911004200303003c6100700314082e0b40d01580440d4946004108110110030094010041c013030000e89103074115580c643da0f6010030300c50752081550200219900740c1c030521144a0360190010300b15a960160b1038904071400951181804245110000600e981514064549001d00c0200030b4542d050021206400a4100741041c1d41148aa1128442480030505050f0280c80c003e10091030b05150440c002480c041c00103080c07032008000da00501c01e842d904449105030000013400c00e010455140c40c000d010764100c60b003415074030500d05010300c01450303003020401e070240744940b20030b54040c0d88001d00030550002c0c0c01240c5000402007003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 585401798 1250 585400548 585400553
    0x60504150f050d14100501020c090c0d180506090106050604060c0b1b0f0c0d050f042c041511090a0e10030c030c08010c02070509131401060b040807090b03030304 71
    0x2107040740d40e48007400c1141c1088294041942125021043e0a0100840300b09101c02508819801d1008240034070041456840e0b900c04940603000c00341c00880a084045105040d12078035400c02aa28a00001d030f07d0003514050601c40c1e660101990100f8a9529002000c640c509154007140c0a5544548481000c41c004d660740c0840100000e01d444000c0c0d6042800006884880d4010149990900e00064813620140720b06c60a003000d1b041d00006000302002205141c07035801040d00e044580c01030110780ba402d0414805541000445810802800401d00308010000c0400d41014107140901c401c100c0300c6005003441d151849040c075580c4e80081022004c001d4003050000c101d0f030240c0e42082c0024010341e40d50f500d13811101550000c44401d0740140c018080f1040c24800d11405c002144002c00d045840d203004a0b008010141c0b0180c041c54079201000203000703100425117240c0c80c1010082015594400c02503007550824060b2213501c0c01071071030000383c44c0c4050143c150b4900c0001c003d1891516681d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 585403048 1250 585401798 585401807
    0x807030504321905160302011e02010b1302071a061e0607021906081f090906021303030e010f0203040e070e030a0b0f04031115070302031e01120203060106050415 71
    0xd400302030780800c0114603810031403418000080c454000391089262020300b0318019080c04180c5c4c85541c54030308181d4080015030303031011081d01400000d16080c051280d0003082280580140c8070101c1c1c0115000c100c00c1110034095004005040c000c584071441d4140d4107808600603481510400d40c13150b100c0000321000c0e0507182a081c9002c900801d203e141081903404112440404250281d011055200c02c014880c0c00150a5601030169016607031444814003500341d018130f00e4090381110035501c0c1924000c0120540c101c0303c0700c1d0041794001021950b207141c010104200011a207001030000240c0610303440c000030590341507500c540144402d0380da503800e00701d640b000798240060f40351055001d58000720700a080424000d54484460340c51500c0c10f410045d240c1d0b108250b640c8125402007d002e07541c0407038809081d400116501c1c01507940d40714503000f05494035800d0000700312558500000100010401c0480c15083e2080d01512000d0780da914068906000780d100701c207221641e80b41c084491600c02d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 585404298 1250 585403048 585403103
    0x30209012016030503030109060b031e060f04091113020703120e031309060e0105011b060b1f031a030a0506281e0b060f0d0b04090b090d0807030504 65
    0x48111201c0300207034400c220b06081254019903198000000500c40c0c016180164006002210070891441c1401d00c0c01c0280103440c04042c220b084548000b08604d6500c2d0311514409a4005105006030f81450524994040940d1501d0303201e4144000c65a0700100350340240c0c1c440c40d4050f00e51030304000103822440c3c05002001c3d400c03a00d0340070400090501d4990070311035101521520200094a82c207140e02074240c5581a0052411701082101103a100310320600c20f030a042d98841b0007c02e919a0103000304203081a06035448421110046805030310303582c150300000f0002c040c0c599070110f91601c07405041d1907082500c006000d0f80c2106000640d00e0614403d250320101c990a240803e8008c0c041a207011103600400c1c0c2030310711000300106900f01107e03028100b03082d4412166946009040e0300230748414440c054490321803075251000b04160340e450ba03201000190b0410b606800030f10f010040740d61600003114040300412200c0b03011460081c8a4810310b403040e54000040300718610400c030b107079202d00c1c00d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 585405548 1250 585404298 585404357
    0x806150c0c060f04030302010b030724110f0a050c040902060703111c1e1805012a1a0f01060c030503150a0e0604111213030c050102070c03021003020901 67
    0x54021081650340302c0c1c600030445400e2003071201ea00d590961500138292807513070346120310175800010140240d040c402080d401c06654520041e0080d643e0090507900d0441c1042035803014002c4014074031840310041038500c401031190f0141ca4088100004000459580b0302e8043d4002505101d0800002c0c05122400201c860000445610960303c46140c0c9419006a00389400108a100c079450308505010b0f10300c11103482403c040074141004003162480420310b10a07d410840d40315010b9954012490180d6074855001001c11805a85801c0c50780c0729002e00480000345484241c0060144401d201505c1c0c1612255500c491032200d032524100c0340ea400c054001005c0b0a048910300714659120303440500100300d0306c041042c041c6048420842181c498422010000300c0c2000000f4150070080300c0140d11a099920308a64088203080484126800c010010f110790b00c001550020300920520560071280700315408051040031030700440c180e010344a40580400d400700010041c1a800c0078410740704c0d04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 585406798 1250 585405548 585405553
    0xc091a12060a12060c09050306190b0a03080426030403150f0b0303031602010c09080606120a0b0702072309040b0c0c030d05040b010504050c0f03090c040c0e0f010806150c 75
    0x40d01d0f04a400f0726203070034020441d40c55980f61301091056030420240c600a1004501070141840c089001201c4280002c807110121956009407400a5450315240030103540c00c40900c035280c1d40c840050241440540000480620b418031004050b81400005c40d4180c81e4004040d80003210445160b8000d1305c098084511001c0e100c140703c1c1ea5548080003c0d500c903104442250030894014640030742142e0071b400c011810010351600c140a4003d00007180354004405407181c0f01d150107240269410b043c52017900404c161600001e02000f01e600280343e0060301d41c0b54030300031f00c031440050b100b154041d000d07070307009402c821504005000705d140550013541c0f00780d9030040c072480d150fa20300300340e403d5030f008602c17607890550358105102c1031081d000107141c0909802c0e1010401c90408c00c410884e980112200c1c41100c4200000103001c1d92002d1000045083c03000d0018010a0725550000e010301341d004059601644100889680359072080880318021140548024016a8021400e0005034022031070b004061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 585408048 1250 585406798 585406819
    0xd1211040504140a0b01050c0705130b04060e07120603151a03100614030106050d021002032107030c0315050d0201140706090c080c03030906090d0b0a0c091a1206 71
    0x152036500403146507180107503c0b00c6052402d44541012590000c0303c150411900b80080c0341c5800001521500352a4101c40d8404500c0c262079550010300400c4007080c5c2c001d4240380002403098200c00940f80100070b00d841e642000b00c00c001c104402c130303407642c400070b800d4142d07800c0e0a070112502580101107a18458203102e22000c44100424501403000c1c000112042c1d60b00b900304081d14802d109400500d00890003441120b2910001410407440b482d006423042202e10808030146000300201d80302051880800031442c5843c0072900038071041118170138042420144401c144a2180c0310701c010100d001d84039202c2c450b0501050140110070b03040c0c2241440704e14054054040e07031050280211901c40c0c0c2d000f24900e1501c0c540f461144402d640a02d0695002202c0c6490701da4020013950301c8131030143c5540303484050240000e1001440d01d08003404074201c15080c0802c3c404542c118041c400704a03210322a40c00ea40c2c03003450034035042e20350715507414030820b00c00800440c0006171520741000c0028000e9194 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 585409298 1250 585408048 585408059
    0x20f0d0b0702060a0b1906052a01140c0901080c090604030c080105041e08040603090c1d0a061409040b04061b0e041404030c0b220b180d121104 63
    0x310300e0141c8480703001d68012001c20040c0000d40c0a130700c0380340a05035140c414164400e0b04408246c2802d00800041c4a030200307500155400c1c0829000030100401c88020080c0c4da01c481c5503008103528130018160b99108000220402c07869021a0ac0126040c0d54456007036031038480201c03040d04286080da070b10240401001010401d08071420300a41101c0000013400e04082c0746c19280d2415a22079141c0da110140d48050208680e00300342e400704c0313000d42008904500d4500d0218850383c107540101e0200100d2210f010120010010441c0c171441d00d1401c10000310340c540044c0c41c00301e64200310060384000d40d00e0004001410101c000c2e80c000e842800003140c0e00c010540325040c1d202d40e80390800f000030342c0c2222006880c500781c066070b144440035030400b00190070262801004c8104141020301881d28150200360443e0081060700a840100c441d100c242c0026407808200107031042ea403c1c079507000d41064029150710045183c082c450465180d0740191704640d1001d5018020009240c18a03501c10f0100054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 585410548 1250 585409298 585409313
    0x30b0409050c0a1d130501020405060408012c101d0d0807031b0509010c0c050604060306501302030f091c1103130f030b0702150103020f0d 61
    0xc01445403000d04190000c900600a0103070b490783c000f5001e441a20306844c900d4820701421138006a06050900741c2d50040d040c11401f80c81580d001c903400c00300000d00041e641300103520551076000e10152060f483d060715080300f0000c3c243e103001d80d50b07260000040d425203d50182d200c104442d2008640305805940000f80d2404d01c000d000c0da14003c100b001c400c00208aa0500c80d1702180400050703110b8106414210003803c5004895641d07046c426618601c4040c492917459100c01454000c1c0403a5413143c40d6000140034094610034107c440b5007245400300e045c60003500c1c7c01d90501808501824586005644002d6540503140c0f400c1125203041d03128101d40c54070b9202c9080400c890310702582c2c90510300c91080314908028094112900f00030390508140c80c034901500c00414503071401c4100c404810050504612400301e46d0740488107400800208c00e0250300c400d40480b400b9500e44812130340d88100070b903100d801584588c01020403100c018001803511801d4000b01c018007a003001003c0e6155a01d080c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 585411798 1250 585410548 585410561
    0x1c0501060507120201090b010317070606080d090b1905070c0b2b05040210080a02040b16060509150a0f061d10080a03021b010507020d03030504060b04050c03070f030b04 74
    0x4000799001030403009020080b410250106840d100030800c444042d01c0c0c00c400140306010041040100f032822054610441040e40c002b550080e20401580b80c0d2640e0841c0e441101211060114900d840006082d10201c8140c03101c0840c1b04c8402900c906e03e6050844071684a8903003110044070300030000c10002080005408011030f5001c002406141c04149404800e4411142021103401d101c1044010b8480207400303203041c00346017410042174550382030010180c041c030380103108507074004a6180b100c0c0781c00c03c07200003a981c060181041152100c6903060b4440d803065101c107903040d0b0080041800b090440d882414090304212001901e80e44800d48441480100315024141c8900001481795a904130041c10005001d20340042030042d20355600a0340301e03040303502e520703002c90b441040110403a4055000c5402040e80102004000c7c0c0703c601c1c000e001402c00356030945078a0b10304054160b050820344603403030181c1d8180c00c0035820341e5070300c540444c1c80b441040000c0f810180c495801050680b030324060007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 585413048 1250 585411798 585411809
    0x1d01051917060a06200f0f030415020606030303130519140c01110a0b18030f0307090603061a0903070b0301230603040201090509040c18050105040e010902030607051c0501 75
    0x300c0010100c5180c0c00301440181c101e51060203c40020071040780c011394269150710082c41070390601e243c01554203060405024009040f40907101c412a09203001100500544203140c8000041c00302121080381c2c2d42d641295855015071040003c941201080c1040ca4a40d6101e4001ca8100904080c441c006142c1c01020850790000d40540c91610383d030041c4481041e4007001c0c41c05000d00c446102078142c1d502c4224001a01d0006040701080c10101a0b40b900c0944540c450700f03c0341c2d82c0750850707407681c0c0c0c03944111004030005d0311416000c00c3e5244203004000403034000010ba40c201c2200c100c4604070702d038421036051341e00d840b548100045201000700071312b000f09003c04600404041c140324000120400c00c5e00c00f4842c090800030080183c0e00046400140c410550301c2c03050f00c0da84c903d0001856007403500283d1013224030f006450760010340360b0000c1d81030343c034113540502200e40f51805940c04d0f109000c100a50540112000812082c4200701900c00c02c0c0d081e82c00040c08400c0340021070104d8000780c025 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 585414298 1250 585413048 585413057
    0x4170f03030601020a02120a21021e030a1d0603011e060207060f05032203020705040605010c0f120203070b0c04050f09060d080c120711030c060c0a080f07060218090105101d010519 79
    0x31827015074052080c0c000c4602010f0800141003488000c69489200301d40d45002800740c0d0b0780d09000c1c014400f03c4900e14018014161075541e58494504240c02c2c0c01c18141114101070010003c200d040c13004c640c010032a9080d484140c0a0f040d01c0c030042c3e82c2508010424be103011040e56400d08909c00980040e544640250042c013401c178101803c1c002910740a8100c02e05110200383c40e01c000550705c1c5030803103140d50014a038158000301440100d00394031851f00080c00f150000d8090180c0508802c00038001c0740c804540391251915480305220740c40ca021281140d1000b03d0199000110f100c0000408041c80400d05a40003071819540c7c0c180349411284c82902c1c00120341c00e0b044440e003400c1040200b5140222a028207240481003031940c0c48c42c0600008045a001043d0141400300c0306060390078840d40303d2415074817840c060031040403400300c081c02c6d03d00c0b03000c440000054074106a40e03520408001640c80c0c00c00c45400002c80864900c10302d1509040020402070a030440c3c5461340b0b800c50703035042d9030364 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 585415548 1250 585414298 585414353
    0xd050a0b0402130c17100806040f02030c06040603021c0c0e042d060801200a12090605040b10050f0f040504020d0614101d0412030e010204170f03030601020a02120a 72
    0x1905e91112030001c1c40030303078029030030750701404142c00c006422903206501c42041c03102c03100c0394408030f420b14281c45580d540088022801040403038058000c3d0030081c00c21412902c002c642e09084500b5070301404074403c041003029140e8a80c2c0d0034290000130901070030a1550103600785120180004401e103031090051550703600c0c405e220400c001e0168908000d00604803100841c0c03801c1007102c052084001c85010320004542c000100e40282e04102d59458102c1c104100b00c1c6841e0828003989901111840c80d1884442400310345031504000c0c81c42ca10102800050504042c00e0501008200207003060364002c41c440407060003d8421300038650342c2d8452080d0000d182c1005070701050500100d070007050f02c000c60b07410b1074040c00d00c01100b034690040d004140c03040101910103042e4000c14160b00e950b40294000500480c00380500c200c1c0300e0340840394904850310301801c864080e40301d0009a4001d80160071400700304000d0700d0703da500c1218030000780040c0c400d1600b941d951404008081a8504e0080c900400d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 585416798 1250 585415548 585415577
    0x130212060315070c0507050301020d0614030105010e1311040f02220308030403080604180503090a0f050d02101b050c0a0623181507110d050a0b0402130c 67
    0x604403900440c0503030040c620310b08042101c2040030b200900c4107081150104944003804020444075004201c040d00841d030b11410b040d03124000d07112074080c86600c442e20600515260605100d1b40c0d0407105030503e09000e60715044690000e05121100540700b007207980c0603002d0360350f480e44200c1d40c80209000005070f842081c0c0009a40c158034804142c10300450030b400420100301c144080740d40c000d51500d015070907070340d4110004000b04110245002e2030070741d1542603000c2180000c000e01d00303034a04132900840d0944c0d41032113010b00c00d11405066000039603007541c2c030b0050401946a807084219400c3c40d0500003002a00808000b9005070140c3c2d00d80c4c080242280320b802c000009102502251a180500d5409558000d002c0c8a102c80c9504d55080e0002d20ba44a203041080b4400442c41c0090610300b40c031076a000b610507107400240060b900c2e8410034400c04a6880c0c2440012585070b0700c0005032085080988540c4201c030700041c4180e0f00000c0010a003003420201c0d21555042001a0b03c030040c081030a01d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 585418048 1250 585416798 585416827
    0x30c03040b0f0f0601030f141003140313031506030b0903070c210f2a050a05121c120603060504060509030a0c020603091e06041e0b060603151302 64
    0x40e140c40d082c0c07500e4000b0f12260402000d01c5507807000b02800d0115a4031020203900d0018a0342c5c1c10942000c0c12520148a004140340f29420200c0c0d0060401500140e40d180c1896128400c500c40d60160401e00b4a040000a181e04449101104030742c0001526030781e03e4840500100b400c0b80c8404903a040010000204802c1e001d041c00038000c400e1420044000803011542038460410000d0300c0c00c3c114001040800440a44040000c0031118444007c6c100030803200c1007117204c0c0e000b080d220f41e184050124041c108100340113950140ba400611000042a0707405481922401c0c0560030802c1c2e411210722450343e1030080400552107041d0009151800e41000412140b01510b0040e0a4008014104245922006551007150121640740d50f98443c04020f601d82a4512503000c1c44011106121401c41408144c1d103202d140119901c0c0b130380003d0380c828003d40c2500c1c80340c0208001041008200359042034405181d000d004501120f151100e2800020350881c20303202c040c00321a8000400100320401d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 585419298 1250 585418048 585418051
    0x30f0b04062408060f1c2009150a1827050c04140a1a030f06041704060504170f16050117010503060a09020604032004050916030201110a0206030c03040b 67
    0x40c5002c1103507007040c100184c1117035108030080d44609042c03200140d040c8480062003402d0f641c40174000704d803840d03441c8419005a0380100318511074500302001512085610b030071100b07210401001143d400c0d05008840480405542103119141d13030350300c140626401005d0824150081013405100a50480d180c40c1e4a001c10000c02103004a00309400620480810880140c01110401d8049044070344904d41d115844035000d8944d506101380d0150b281d05800210f00140118014840610744000c0307400b10f10b0305440f0314829100003d0040000f001164584844e0901c5041124291507000283e5054946011306042c00c21140c1804224100315940c0c11800e4020030b80c02c07020810a85602d40400039032120001000c0c1c01c85161640400c07000c550301c1c68200c038080d6501c011410704504c245040520907400958009010f44c0c5040041200c2450008406520040c080d060301c411504540c01110310610b088282c001c94414002c0d4103006030340e40c03000344d40700d4400c040703500391a4581400c040181540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 585420548 1250 585419298 585419369
    0x18080d02012a0c02060c0c040504080d061a04031b09020a0216120f020f0d021002010204081209030613060621020406050a030b040602030c07140102070b0114010207030201030f0b0406 80
    0x10344000d0032507260060b0318030701c03d107404031415502c58000241d10b41c104000040425402807400b01080100800c19000c0c160881e18188200f080d035850b40c0081d00c0b403050803400a00d03098014402000001c3d00b01949596a0b48040c40322a29556144480d40507600548806070150b084801c44440001e400f5071076100500e09002d5a1200d801079868603410b01d107081e034010b03001d24260461004140c540c221100d09243e4007a08002030150a203400a0003500140501100d41c014290b5170224142c0071002e0350a004d030000e01400040d180c030898505039100d443c804561168954000040424151010500d65002e00c00340b0141c02010b4410081200d807590007171445030000e00404d10205a06102c40c40d072082d400a00140c2c2c0e62100c20a00c660b6001d01b02c1c00420740d1304669500400601c0c19005481124401d100300c0b40c5a90300c6201e40000c23400f24403041c0d80180c1c01200c00700059032282d04030884200d44e41c1000034007030082001103015514142c2280c16001094104d4020741c00d05071410180000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 585421798 1250 585420548 585420611
    0x12030a050402040515221b020a110a0e0609041703070e18040c0e04060e0601090b04140105060f09010c120c03080a0b131a090106030e07050a1518080d0201 68
    0x9040000060705c40b41419030b0410b1740f44500c151b00c0c05200b0340d81d0107240300d05641d0192014017a04004002c0d501c4000e0304003141c0c01c8501851603920b0b8181140e210082d15402c1c0640030b0319940c0c0e0f01c14820020f800400503241d810151032903000500440000f58014003242c1d50f503080d1110007070184a400d010900062600701c5503c3e040101280003041d480066900b179043d0a0801c0c0c44608081c4003820200008d080540944000050404580d40c041d1540f008280c5041c403411107050b13800301d0612001d108154103c00c6c104191b12403040d0030340007800e031b1030f9050410000c0f140040c0c4545d03100c2c0c241d281c1d03220301060a1200304018140c1000b011640101003a4051101d84205030200d812800512450000c040c0c441802e0b2a03004181844402d40ea007014150b9401c43d030f0f44c5c01c40140980b07020f10211882e402038a5011500d400c0420000c41910343c0250240c2ca82d408201049410040e212000048446480f00204081c03105211300305088805500104159504625841c0406080305070b000c00c90 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 585423048 1250 585421798 585421831
    0x506120604151d1605040b01050c0d08060d141509160b0a030e01020309011e0207020105030402090c0f0a0f0201140601021f02090402070c1809030c0b040512030a0504020405 76
    0x82841d20800c003903010036400450150341d040d0450409580b00410018140101d141030013919042060040441c0c3c0119418048105040015500340c0b10700f5805007203e0b004914207260b40360192640c0e9400400140a029070b01c1d502d80c6822400c10414101c0383c01903042000f541c0300c0002481c580f9074014030524050441c80045c014400040a01845030114810001c101c1c0d40c511802503000c0240046208000e65a903e403e0304003500815800000060004440449a211106520030b680001da0b0607103895155480da50204603044600800c0814409400c100050141903290043c10a40400380c84911030106200c1740a030a4079041c0242404103014102008140c0c0e078006601e2941d502290807284e608136504807444068031070102465001400003491504010001c12903004880361440d16400c4001011895819203490b488060000340e41c40300380e0b6001c5500194441c4d00b29100300100e5007601d00d4000c400c5819082115841641ea90302c104000c1541098001c03203034840d02c1c0030040c0800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 585424298 1250 585423048 585423053
    0x71a1201060503010b0a0c081908061002070f05120a020a0b13080102091f03240501120212041b03020409030806130606120e0111040b130b0c030910170a0506120604 72
    0x6d00580103008108a61018400c0510903800205d45100d4862a2041005144a040545015411f54503d40540200c080e20000030b0f101250380c0f010340d0313400d46100101924201c01c0201c01e64084280400c030b405103187c03d8006036076210300640104628a105615810541401e9000030700c203500c11007881c0d00400030072555a42d12a010181f61861550449202904690440c01840c00d40a544100340c4081c035400314070600140d60074103d5600340c2e5400302c51000000804103a00035551030003503a60078070021900085148000b80d2a036207005a100070343e01e6513a00041c0c03e035803151405801055481045c070540c0e040052072407901d4869410140000741c070b001c40c0144405107011041001c296a0404020385100a402103000c40b8210b4000c5910b8036202c100d200f0300d90b4490112280e95400044001a580b45041c003525000034000019600301002c0300140005101018000810005500780c0c1c1e01e160045540c03450f0298151186c001242c0c0750840500c01d90346604440c02804e0350103d02000f00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 585425548 1250 585424298 585424319
    0x305090103020d1805011a01090311120a0b0703050103061802010e12030c1005090607080108060a090311100e0c03121e0403050f0c100e010203030711071a120106050301 74
    0x40410207190040c0c1d242200403040c030007000501d0b41c19a410003484019810701405400a01c004c0460100b020005d640c4c110040d40d8000e4107100007808071091200c050709034030b0001000d05174080e0410503544101c0450307403031140004080f0f0b02040401d0b034640c0140184581c501c541c100e289221508003450351140d0b0000f03071100000c40031844c45903003213032600e400302c803004d0044da600c9601a41c200c0d0140084006507502520088412840310b2240720700041c901c5e803007402c2903070403a07600c40041e00881e12290142e03409072040b60f60a80078007100c50201d6144000030000700803070b440584800200c5104048070682091042854507119070b0086108a0b1003030524011589003444004003e195071007c8001c0d40004d01407030340040c0440c001e03801402080c640c0419a6107250504954074a140c4016000503507142850300d103600c0c010390090002910890040c1c5049400440c600c048618050791010403c88000d4140d801f1001c00380c0108089031003070280e8020b07502520300341c248581035606203c4101d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 585426798 1250 585425548 585425557
    0xd150c1e1d01030f0e03091305040b040b0411090c1c02090a06050d09020a1d0c21090109082704060812070f020901090501060f0810090c0e12160603090305 68
    0x420041c42058109680242e020940001c1c0460302407101c003080516494036034024100d558007070300d4040007040014941d803007031620030780e4000c054801c151150784400d40c0c1120003c000b15100d810b00f0050307500b80d80c2d441240c3d078819000c034070354150342c1d1150300c644222410000b8440c6100d24014806016107a035490b02c84c00c04d82d00989040f946170500c03007100c1c60203032502c854041d42188006001040c0007480c400702d00f2255401d40c45101150702c9026180c010380c440e041080d5a0494910341c11500c3c00c0340300b44220381103002c1c800046203e0709680c540f107040343d00ca03c0309100c0f010a01c61600c5e61444542060121296044904100003840e01c11b500303440303031500c0341c0308080ea2000080b540c040212000c12201100c1d00070704101c1c02c41d81c407480d44200502c401c1c026070740031815400b040196a44a021250b21a518032070a00e0300213480e00751880042c0164040075000c0c0300814014003116100e2103100c805401d010360041a9407080546124412500b076000300d4105414141c0c85804030b9040000ca6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 585428048 1250 585426798 585426827
    0xa0506010b070c0b0d0b010f0203090a031104150b0316020a05300a03021209031804020d0e190b010b03070203040b090a1d04020103050c04030f0209060d150c1e 70
    0x2d0341c8814501e8105809031054100d2064144081551141510140c0c07282901850a8842464a10301040140da5030300410382030340c2e4000c04a11090000400b95036144283d400041d2000c14031010a49101410311400d0700031b004699000300402c03001301d0760003810180501080c009040101d5181d1100e1343c4491304258149400c00600340c03a4051241802011181460450b48032611203404100050196004c5a2f65801d008681000301700042c80210803900f01850030980005a05054400d200294000c00c20070141169079003005524003600703000484900b210003489540d00344c024070f0a00b00100060700400c202101c140304000780c0f5030f00041114261140030700310340d0300d0f1042c00000400da2507143d08169a14056000b0b803048040c0d1090f9114083c62007600c0c240aa130350759803010b4580e402213100140a900c000643c04c0c005d410300090080e0400b801401c2c0b45d81024031074136812041c80c1056861024650703900c0e034505e8201d901204400d29180c07034141a803050380c2c08201c028504090321032075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 585429298 1250 585428048 585428069
    0x3050f0a050912030c010f1107060c021f1b0306081b040603120c0c0509130b130b102306040311010905040c05040f0b0c06011518030b0403030e0a050601 67
    0xc0200140034805441d0061401410048042d588858068036500200c41a404a608000c0b1a401060107070059072450800c1000305402d10105031941c20103080d401090805502600404035058184a400203072800c1c145000030440fa0441c3d5441c000e4000340d015600109403400f041440001c5000c1141c000c10542c003205003c0f00d0700c0300340015009008a9000400e500c0f60069000e0342c40c0c0d000000c0c000307285d02503c610300c480c0d030350303a0280841c10408a81003c01d00c03041c0b145140002c1e11b402e01040e0014a20016016a00d01030355070601c83c40b4040d00d4011842c03c4109003042441c3c4282188588071104c44c041200b20102003022404034021800014402003020007244000e03446642d07220002c1100a2007449803200c4040040c109510900480a40301140f04011511084a90458a00842c01c10041030309a2814100c6c104a0783d0032030041f0104007180c0c0d0303002400021480c04138061030049403046000d0804d4500a8115000c100c5080c1160b00503401d0f4402107400800d06a0441d000381c00c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 585430548 1250 585429298 585429307
    0xa0b03010608040602040e0421090303022d01020d14010807030809040b060c0111091c053007120f0e0d0206030615030906040203240a1503080c100b060703050f 70
    0x1131031000380c01582c002e0074450b000c101c1004140503002e00420074802807040b05200c280740300041120880c5580c000500546c0c00320b00b2004141007000c3c0d0b070700b0720384401542101304201c0000245003640d110103183e2425076101ca0200318900210914607004011040040000d42d1135651200341c1801124078451080741d80c4c5c00750940d140c44200031160082070140c0200b1005881c0070240c14590080713449280142e282910b00201068001e01c1da00546401070001d0803005c60402da400303a800c6a4600e2030041c0c1c10000003181061f003501c400341010b50312680c220710904094a000030808003011002104110440904601c02d4032180701d400050b513019142140c0e49d0391000c021580c01c0c1a03899154280440010804c05c980c41c000c10540d00403442201500d60240010030072407800740140140c10450007944010801c00d201c10fa000c44440d00c03805001200c16590b030b803192102900540007511084c1c00c2000e1084c10307007111b4412440107207812165142040096200204140202548441030010004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 585431654 1106 585430548 585430553
    0x3040b220b15010219030807120b06160302031c0e0d0c02010801121506080c0310060b09130e03211003380112050c0a0b0301060804 58
    0x20a0400700c2d12004030128481030034550710781c1944a00780590405e10300090780d22002a0007070701c032103415207401100a41018600c0c0340304c0f1a0315162002211203a5145c0041c0d03401c0d0511006126500489031506034070354170030b550075a600c03c14440d0800901c0c103015000450f007515144162960440c8900e0181c4240094442c002c0c0420890401407052127440c2c80a000c811780200036501004171040701c0c00085a400c1c0d000b95034940c21140041d503040c2020818460540304441c0308000f00c0e464044c40306074900481082d203204224110320440005d000d50840807819841c0001d0b40c1da100000840c6000e2080c0c00303204021300d10082400660648202a4040d08494010300e450b1101811020209010302829000c074095242d0603080d0031407854001c526501034201416481d00140e26418010316015000003098803400100100b0710905244074150b9044840605080315941c03100d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 585251798 585431654 := by
  have h0 := BRFrame.cov_init 585251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 585251798 ≤ n) (h2 : n < 585431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
