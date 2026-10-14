-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1438
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:59:20.287301+00:00
-- url     : https://prove2.me/submissions/f0f65fd3-85b2-488b-a49d-c749211d380a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 258453237 ≤ n < 258633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 258454487 1250 258453237 258453253
    0x52203050904020c0a050a0804150207060815040b04090303050613020f092404060314010504051314010225020306070c0803010905040f081801120b0105040b03040309030804030602030906100503 85
    0x2c82d064000b090b143c1d400c001103921000d40c4e6160b003402e002050008070342402002404000d0000c0c0c800c12900300c6000e90001e4426946010b0010300903ca0041c074040c1c602070240c4805081d0f503101da000444220004d0303c20440180cad14038010307008190940303009129115410340344003181740c0c500807035050000f050015130420340d00c501401039001101a071407101110241da0582118448000b0304000c046994001c1025a03e12018224100042e0030050103a0b04000030881c2640e5940cac12645425807180c400c60f1921000ca540f9070081c0130f074907800c02c074078110520081400c400e01808400b800b8021004d880707064a0319182540d4000380301d08010540c1d50300f440100016182d80d1700050340076004001380c0000103032640d112001c681c8003800c030701c00105e00342c550314900b5607025480b071f03e40c5c5015100030840031268600181c2580101d00c12180858800800a8205482180110025540414100d4580c2d48134600300020b0342045800d010240305040000346002080c820301801c1f0384004d00906210 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 258455737 1250 258454487 258454489
    0x103062304151a0702130608031e0c0d180819060506030109080a0c060b03060108070b0f0c19061104030b060409110901061107050d17030406060312030522030509 71
    0x9421412100120406070040009250500f003c2c00b41903421100710303150703a5443c82e104101c503000d03440c154104107510f04082404007440000484a410401d01d40428072588604100011032040420802c043d0107a14201d0410b04c0c0c104007006c00700c2002c400703001c200503201c0b2040750b0b5450440c803080000b000b4400714070000c92400c3c1d0019820600c05030000c140020320391580500342e44103040160001d8500001d40051000a218012408100b24054801545000c0035540c4d01e402c2030050323241c1078030005100c1c50312000040c2110326040310325041e02c044840e100a1015a04c600800944120b401c154401c01201005070441d41681d50280e207800c00c6869402c02c1c44000c00ea01081101c12880c9002c5107092130741c66551180c02040320795034805200c1d0046464909208643e8040c0e405030018000030800200380c080005100314440c6251912541c2d94140078001e84403d0b130015024441844a05141c50307030680100740700d040d82c1e100100481080380c002c00749a8070025009000103009201542d02e07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 258456987 1250 258455737 258455741
    0x106080f0c01210603031707030504051b0423040c06090b040b03091501030506090d0c0210030506031608031206010f080417040b1204111206011509090203090601050103062304 77
    0x1c10310b00900309003d21144110f825a410990104400d0682585215240c0303c1c1ca03680280249018000790409035109036079078403080c0b41d009001c425100300881944465014140174805201002e020340700c0460703a0911190240c400f07448900f034070b403408200c00b402404402c040300d20b24594203140519160b2080550f4102801070941c500520489854410200181c0c901a50060340640010700741095801c4c1382402000d204400d10103039401705805a511404c0800510100e42004245a0303101c01c006814064940b4050100142080b004210420300002500060b098881e000e403c82c3c542d14010740718a50079400c01400941d840c000240040c8481e00101003010031502c4031401c060302c941c01c0100a410051400c14011030040803c014401158021b1940031001e035401071029140b95801500e50b40305000da500800102d01c00041c869100d00c0e1040002c0100b00c1086413207003496880d2640318002889210b0001e03080510200b04000031802c40c080d0a40040c403224160440907081c000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 258458237 1250 258456987 258457007
    0x40b03100b0a080a1707080c0a061407030c0503160203041509332307050c0906010c0b04110102031204030806010816020c0d050304050303040815012928050c0106080f0c01 75
    0xd41f05405225407005907908004c1c1e114420700c207060100da1044100070301c00030800000d1002c0c08050500344d000c860550080100ca4100d0303100c3d0700a0b40244c4000c1820703880d41c0309541c0b010800c8000d45002400566003d080d490644d8503040224031307521010a2000e190b00000c0100d00300701009100501c00150040c071542e402107152092482c80041d00b0390000311a504600c1094800d9000701d403080000e8900b801f0042c0d44003109081c0100048035a0300c5446009400a0000b4141ca4140107010b65a030b00820607200c0008124410000c249050300d00100b03024800e40381c49010806100c04500e07110301480004440b40c020303900501c51802d110003001000d00031f200d0299400d0008010115982d203091005002620400004107041c240e2696076560240059014850240705c207410282e4410201c00c4022000000c50030054690900c2032100043e00c0c6405900f104d0345548849120b1f4403500715016100c902c504a0003080015a907880140d2a8044403441d00000c0c2c0020f520700d40c079903028041c844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 258459487 1250 258458237 258458243
    0x201020a05180a03140d090e250e130e0c0102010b061603110312090f0d020d050a030e0d0809010c051315090806010902131d15040b03100b0a080a1707 66
    0x2800160b134a03112940b041014040440c0541c01c2a18044140d540055492004100d104201d004901e00f014511141c18800104080c00d0041e00c03041004d507520030000c607260710314002d0884401d04018a01e58004100050000075140103000320503c0c10360040c428406e0b20a000b03014280380070031003841404001645442201030001c800e5091810f48030403c090071440d042c0800d1102541040729403a403401c111210402101d5200c40201003009902003041c3c64000942e0801a0315a0406d110a4015291a0300094414401e0308520100d060f88540f98a0084080038000c002201050804490a10441c124001d1303c11808004020645a405451403010902e10b4001d103150b4403585036600707083c2c080c0d00802c2000d8005c103400701e50594603040b1038018404805018040c208854902c130780c0120080035103110070354026241c121a1140d030010305da106801015981c5d13021131000c3c3d440081462010503801004c0b00719000c00c1d56030001546192241e001995503c0780c0d007181100c42c1d0580d10040e011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 258460737 1250 258459487 258459499
    0x60102070e04050f16030f11040905030d0f0f0605030303040f03030209030616020c09041a07020106050a03030c110609060316021014041a070e1c0b010608160201020a0518 75
    0x26030340d410381e141503009a105a02821410f0208003030030b440d200e0790160914014540b02d00800c002207408030614800e81d0300175440c00342481540005001091004009030060000045601030046070f984244034a1321200c80c200550091f0200402c101c41c840e004454040d4002c0001c034010506810305440c10318424039000d03140c0070000000c01d080040c00e4581c44110b852001c0d181242540502591003001c00650701003186240a8680d07902407550b05174200e44000203c07000c144018800e4103e100600400b400007400e840c0c0ea80f50090025801050940300401e902d25128064580f9400301c900d007c0c8014001d900315251a03440030400300542103140c00750b1241d620b007160407583c5c502071080715800e0303000501c80500d414240b109030304004440b0070325100c01e0324040008840d08918080c004034000e45845605a04486109488040c0300c01c01420079a46440002561580100f05034403505134080000d030b02000c00b550503400e038040d074051480414400d100190b828147c1085904038240e0003840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 258461987 1250 258460737 258460739
    0xe0a02040e0d020c0d2d17130b131a070215120a06051c06090c0f0f060e03100b0d17210f060103111e0d1107030c080306010207 56
    0x2030304540901003164000c1e0001e16030794a0003501440402600d1034251409101c020407982c0e00c030040c1d10310070300d130314a0b2030380722003440002851589074910111b502c14121207840c01e40140c0c480583d00030750415684964001c1022444a050405403451019032207820805281801c0f03120341c110720551190082e8003030078410580565509054546541c0d0b4802003150f80b41c0e11400521358001009210360b541e1810020b00b000103032602c0305950020b07100e586107000611058a445d138041d00b10440d024040d80d124007808141040b074008141d0880d2010701c0c03080c5100c0c4d51000700340d8040000c1c2805d154560400e510342e0003007601c960004881030a006080402c40503a55541c1c400003480301c2c1d4080407090b404130781c0d800d42d91148001300310210500240b0403003600e072041101c502040010030030340c1095150003003400c1e5030350804103a035050000c2001d0341569500b079031000c180540080802118441c24601e0840e45000800300300c0e0740300d40c0c142e0380c1e0304040000e603181c52000f580b01402c00c604500c03807200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 258463237 1250 258461987 258461989
    0xc05090307032604150905060c1e0a14070e01050306040b01050d03050405120a030905040b0603010306021b06181e0d0c02010219080301090f0b01120b0f1201020304050706091202040e0a02 82
    0x4028409054041c1740c44841c0b0b140c00b07200602c80305d025006103005010410480e4406100025426001c6880c444c459a9403802441c0d864100718131a40014229500c80c200d540f10400701080c1c0c2c0096600c20040440c0c85d80c0d8500405550304800d46010b00307802c0c038640050010307060103420104070358003a040070f514041d03950020031881d184c40312401c03007290400800c4004041d48201d044000384021202070051100700c0c0e00003410782c841840000c1070079900040520902242801d5070600300ca07401e05070f80141c5041b10181c1c880f80b0155a0386801d5000b51a4140044010200c804005060480c001d01c10510480400d850441190364281c0c15442102c0700300300280d817921104c1d000b962280349003a4580d40b600c030f41c02c82550b070588200085a070510404104a0b40d2000c94034150010000011445000e09800b069a00d1086505290800400750708041d804505400450181e8030071800c5800c015683c51048801d031056024901441c0140101000989460303008985044800b209984084000da4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 258464487 1250 258463237 258463313
    0x108100c1d0a0b0c010516140f030406140108061f0e0f09011d010c030e19021e06030424060e0c0a030204080f07030203060a020307080a0911030109080d0c0509030703 73
    0x901c5003d1546e45410410103444940d80c9102c90500b200c0c200b482d51103004140345d4001d03001d0500310030500c03030021001a0501405070069500c003220069000c60382d58584080c142c50b01e00840305406d00407203c80c21031940c0340780700c51210100e075454450f40ca1540c440001d640751142010308240015074031000c0812a1480c1c0c000b80b142c100c503400e0000501e80b000084040d05039401181c203d682c0e40c004120395050f010460340c131a510701c0e504680001e01040713000c074078645c0b54084010981d04880c0c04020803080183e00b410103e83c40c8003032140d00c4140e0030a0000041510594040d440c0d99000040100f50780d40801c0020309000119400c0250034161103420492400031042c1c400203140c0c0c0912810010741c20180142500300c03d000c4015884d52038140300141a142c0081d0a40403c02d9036212918103000055950302215040180248400d186a08242069400c0321444124051810051025040c014401c0711507190005d805030005a18680b80c44145000c07800c0c1040079094801c0300110b0420902c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 258465737 1250 258464487 258464497
    0x40501030506060d1a120313140d080a0905040b06071703070504080a0f170c07031b031506170c0913050c0a0303020706080601030c210f0f02030108100c1d0a0b 70
    0x4405040003200410f000c0050b110304d0480d074a0021f0704100003c5205944000c440401d407400640c2080041440102088080744207410252807210003080c618146e0307520922440071a802100e05002000b06c0208004040c414080028203007109100d02d40303403d609610156500c12424180309081c166607030005405c0200b00c1d101102c0340b90f450f900440c00c110340c0001d00e43c03100d0050b00c00a801d000300810b1407541d9040600001c2c0c042d07407102c241440095003585940c009140d04c0380b815400c61400c400002c0182403c1c1c01104900d50341480401d203414400549444105001480b0700703440c0d220044050390b0321461160a43c0d00780035000040c0c605840f200b1822005520950003000b507107203820401415401c010300124101410008100e100b19448a0210783e84501c0350b9040301091420b00d05c28005203105401408502d08100c800081503002d41e000c0e6048907001c0003507842840200c0f03c5042100d20b415641c002050140080d51503401000744540c6020f54003400070f82003643c0fa0b04010a464101c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 258466987 1250 258465737 258465761
    0x108060a06020631150f0204151103280314070203120a090203120a1b0b0601030510090f0f05060a05090f04030c15090203010b03371b050a0e010b040501030506060d 72
    0x1d0896901944540f03200d106c54001d06400704600f041e040192444400b8050200c0500304628418180d1040760b0074812a803200c91010810707072917000c0104e110031559046841d243c0c0402d01d082ca0000594007513652880c460030a5901031483d0400380e2040b03100715600030704141001c50341d071000340c4010b8504001402c07002c0100b1022580b5040c0c1014001d0481c41001e283c110b520201680e02c10004840c0700c6010340021003402c0c042403c0d55200e00150b545a0a9440794000340c3c280360502d41490741d070f0b51021102034054079050200d55104010310039462410321425412a02d80c400098072401d02c03940e103907006480f0b46804524614203850708101c000c4030503207111440c1d540b00c000d9401c5250921405441c10b2007540540380b140c401d0702c0c0104603400c14960486050040c18441c140040d0b03a80d840d01c240c268042400035020801c0c4941d0080341c4003500500340104003407540415905450f50700c80d8100e0f0014031145180605040044000e80800307802187c00c00d20a00007080d10070348502640040c065 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 258468237 1250 258466987 258467003
    0x90507030317010f0f030204090f020904110414090c061606051e01060309120503130506090604140307110607170711153108120301050108060a06020631 67
    0x507442c000e50074140d506074440203400810500c10444941d810041800304c94040b140000d400240382064400e181182c1c000a500030990310400041140840d4004103000341510304015400410302e095000710800d4443d0780340c42e4410000f103021032801c10300610f44409500700b80b60229002d944c4110544001b61005005184074480d088501504c000704180100401c0c035041c4042c0ba1a51140903100f40303070035010002c118002000403400c1c4254960040c045500c0b07403c83e4003500c0e181005540760710040c0c5d011900058840f81041c42000004240c2e8407860300402c496040003541d50401095601c01c071021104110b120506440791120390026003691802840c000071803000d010100058118041c8515401c580305001c1503500d081250700d81d40440340c5407941800d90840c5100403d881c450254004402c902c68008522070709981c0c00e004d94100d900c00e0300c816080340c486208110342100140075460047c1d011100007103880210303031803541c04805280c8804005800241c0007507801c941940040c5c038041c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 258469487 1250 258468237 258468257
    0x3210703030b090402010e01080c04050d081902071a030a110406030e0f340b070503041a0f0a08070908100204211106030c120103060c021c0e040f0905070303 69
    0x160300341c010b0b66030007402141c4941a91406a002804c90401180c0031410001490001000314440c007003110080c1000422864141f05189050642c95200781984075585030350050b03007800f0714000118442900c8100c0b510320b40c29540980d800000742c0008081c84115921a4606680c4480c000300420150006541c0071481400480758203240054800310402c550b80000400000d8240b54011089410280301c00340c1e0100c0e5645040e40000c0c1c0c011f42003600311a0300090b01004200000004000315404400195111007520b0703d44102801447c22801e06098100818000356219600b0705a00c05100d040c044003003a117074107280e480c01348210381d4041d103150b001506000d1410703030036080011880d4100d8003503e6101103035600c1315903007409040345014407800701c082a00c005062007030b10302c0c0c1421640954410b69581c200400504690b21002d03015005608000100320b0303240a9000c0c440c141703500c408865004041c1480010701c280d400c10000c85980d0700b4224001003041c07100c02e0003140250342d82d00c0300c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 258470737 1250 258469487 258469493
    0x1205071208030402040c020d080a0903090e0f060909030301050306192301140a1d07090306050a02190c021f11011b09062a0c1e06020d0c050604020f032107 68
    0xc81703070442011b055501004d43c5941d000c0d032000110b60310055030344010610900519080c0c8050403e508640d043e0840c2d1004c100680f0321000c29544281c00446240d0b4147c1c0b500164281c89100138028250141c000d0340002d07400400403000112000004180018501040780400400908240c4018507240c011030040260868540131811854002c170b40f04a502458043c6145d8250700d003605070340022158400244004e0300424031000210342101c0d061000e03141484484009601007600c2d075061000440d6403401c1c19110380000001e0b2540035104004280f440900c2c60f400c0400549800100300340ca40c004681000203004481100554a0a0740703203c1d40e40c1007000d4805100382d0070140402044000036020080340100440000c9280c41c8012107250740c60400b00c0e00c01d011a041714480404c2d012003100304551030b0080ca800c441007036080d203078040305400d030444110030604005090342d070007400840c0c05480d040040015201008044501419816500f80103501c40402d04c4101e4610200f0300c0424 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 258471987 1250 258470737 258470741
    0x23040e010c2c040c0306080a0602090901140d02120118030512060d03080f10030c0e0a060b040807031104180b1602070b12100b0414120106050604120507120803040204 73
    0x12030000714101d40040c030300240010055441002d0921607074445900e09003560103544070300702801c007140c01c0d1a030100c80c0d400c3c14030182d400841040d000f001c03040000565110b203541145d43c02c41d070040504000401c640c0030001310031914242c0f202e16550710900c8246080c500301d2a0f0310303128800d071103da8694000101c01d00861100800450040300c40712181e10020368451005588404604003c056030740310194043d8000d183c2d40c1005103844072003400482c120200420b000c0c4604440c040070722009480700d2104c000d6000da40308142d8903074000e5100b0710000b10805802084c81c42c2c05840000c600103c1b1042400341d00d00070344103a890403114414030104800041003084400b25600081c4051440c04001c0e003101c1c45400f0b0710141000d500f401148c40782176001550702c010800030011540780c644681c0031a4844001041d62441920b058080702e41c0d09406009100485400415140c1401d10f03000b030340d44020442000844081c058000040f44916030704508083c50b50003503030b551b900d80c80c040c03043c031007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 258473237 1250 258471987 258472007
    0x21501090e061b0f030411030304180f2703050d1506200705010e01020a060e0102040f14060901050313080a0906110a0507140a090518010c110723040e010c 68
    0x40d10303c019042400140034080100d458440c00c8442e0659a03a0300da080100303c80340802440ba515000008002400c050b8a10380504580d05480c0701b041320b00c540d4400e5504880c0103000590300c0c2100345082600e11a0500a070240340e5009040c0140340c02c0d403890444080b925074466108503070849080501c5819403050503a001c0c60b518550088103005140f808030369a005034400e0038100100d441c161640d0364424041c1c41503a46d40700c3d200380042492102110302039081800f410352000700d0b516000415004250004800500180c401d5140004040045600350700c000e140050070a50b0440050025074060000c2035102625034070700c0102410200e0041c03035041d524175800010f07400100030300b01040022801c80100c4405401c0000703105201e41c046446488954041a402d03840d200411003520100003143c800904d03004000c001d01d4000c0813040c0d03a00304e08941c10071810f5005c03404c103101c410013411403940d181203e0108170025a003224001002e0b41c1500d00c980c10940d45a0310080754190b04540810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 258474487 1250 258473237 258473251
    0x501080d0219030905060a1b0506010501020c18150f130903030507210e1f050108190507060806061b0c04050a11070b0a02130f03030801150816021501090e06 69
    0x1102c019142c40040002c0400d0250500c508000140000340501603241040b40303d901402105d807261050400c40c0d120031007449a140540590014000380d443c1c030301010003a9803200780321aa00c6886004801024400c0c480e80c554101030000300c1a03d82e60340d07910207500d0803800341102242d49065450000e041d0740c00901404c080c051a8582c05c070b2144800c101d110240e1011070070002c0d548044905451612008441c070342e80d829602812a0302a45007900254180c50801c001c0326032007118080d5a04c9003414800300602160030156091000c1c1d8403e850700c58002100500d654141085604401c00c40d0100f210100056401480741c00c4035401e16004059000d800c07808104201080010200503a11901000078000082c001c00141034482c40d0341542c5d1a0705a0b9034140644540300d0845004030718840c001500412842d00c00000c0d440396501205040140940c0c854500d6180c0300002d040002c080e81288040d0b0155140a0621402c01d03a5428000c00c031050020444d58407414416040c200d01902d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 258475737 1250 258474487 258474523
    0x80304060b01141b010f060f08060105030a080301031707050d050a0807030605090a0902012102030103051009050a03080721061d0402060f1c02070807030f0e030a06050a06090501080d02 81
    0x1101031801c1806071603568801268518003680c413440300d68010510803134501d406500d400400302d910b403071251107003066400c802c0c00c40d0002e0f42c0341c0040568a500b4507074002e0014000b0401400001d211001e00200c0200340e00549080801907038510b8240340e03036205d950340041d002003080040e16a000c501e10343c02c45081c3c03e0801480e41032030040f910700711008109059040e2644041411a4803590303003140503c1c0c0c0c14040c04c01007031419030780001a62080c03005684900c20482d200c83d105280b8071902000c0c41d400001804c0a943c581c0c2c00342c4580c0002400c560900a1043c4240c4032000c0a200c01c000b400307101c00c1700162650800b842c240780401e0000ba810601103061040100580700c40341160f800355044011240c851081080d0107407804140440120118008503d10b0f040002d08005000e88038820f403140340029100c80380803620300c1d40102d903441c0e040d4820860100828681d50200390845400200807032499107440c880c01c00c0d14000e03032100302143d00c0802c400d46190b505020001d0800400100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 258476987 1250 258475737 258475757
    0xa0201231317040b04030b0402040b0118030b04020d0503162102030409020c030f0c2103090d031a0a0e0109060803090109140d1a040212030406120b120a080304060b01 73
    0x201014080303140700142852501140c900b041c000c10360030f481c014103002c840280d450351680f40c0300f100b400e02650124001c9081c501111500c0d8000c5540c00c41c00a00d0880c40c1007002d01d1a110103030000005030050b40c21101c010200f9020580900040491501320108000060485e20b064283e050342d5030802d031a11079411014002c0194084200d03000c070340002c0300c00368803030907000380c001d00754420f4100d049a0350304005580101d0310804505c24985018061440424401001020703105200440f544030300364000e01812101d19009910881c400700b001c030750040540107800045482c06510b6040f000c07081c910900100b022075250f002e2180035240410155052464210010706104a58043e6810304034800025030642d441e6100a1004d442c1c2080741084001c90160071905816010380c3c0c26406540150304075550004000700b00c50495581c0c1d42da820400c400c6038030380c0780180a400882c6038083c0c0803402000488808010700600940180303d020b0f82c0341030901e00342040714040040e00b8107000c0d52000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 258478237 1250 258476987 258477001
    0xd05090f010213050411090301061e05040209090a05070e0a171c020606060319020f0403031b020102030a110c060316180806060d03051b0304090b04050f01050d03050c030a020123 78
    0xf02d40c07022650156000309248803e95000b031014058600c990380c0640c6414030000b80d4044007074840c002c140c103481e2000301c620f0b02c8070180400e81c41000700803500180d5280c0468081c4110b948401d43c085610b10380050020110f200290039111250310035000d000c5480c10301243d000c0300f4403100b40502140700c540b00881001c10346c069100d0400400d441e104540220005209c08a030980444070f00c00b0321b000856507107510b01000d0849812a01090f400551024a403031b012140c409581884603405030021814854184003c0300e0b007000c40888800f56000700100c80705140c58607000342d80a10304082d0600301c03100c008100248817050480311010361440745203040003030300004503030242c011074180e03200c40c009000c0b42010344191042070100e1110b24140307000403071030032408405041607925070581481035902001c00c12040d214143d42594100300c10000401161030190098100d1714820b041050034209800380003801c640003040310380c0242c0d44070040710208480794203030490310482603260181c903414400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 258479487 1250 258478237 258478267
    0x50a030c051204020607020303160614060306070e040b06070804030602041a12011a12071709010b091503010b130207110409030c0b0402040b12010f0c050c0a110d0204020d05090f0102 80
    0xe803020b4040c0b6000500c6e9025510140100c8520151030400505034184520300b1000400418500204495100011800505d0046070441c021350040e683c00320302800f45020000205401d4510950000040050500040300980900021405480e0041c2c545151074508003d50018040c0c0ba15494010480440c0d0310011110702d9055400e000541c007031580d5481141a414803a500110005500c6030040014131984a07441c06040005c1c4141c010740e6440d14030240742a58031044400d54400e04442c0081c0105000c0228410041030090003c1109219100425014080c401c44603014070740004444d03081c003140a049044040e02990100401c44194a0003429500903a000a180c4100c0c1400301b019540c550300508100c28004103400a0000c0203200103000309030300080c001006003001c2221011138045c0056480c0e0040050252a0b401c80b1941c5092020195401d8281d00440d09903a40c00543c540744040c0003031552241c4000740e01d00380403848a1411a00d0544404242e00411102e42d40c10611 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 258480737 1250 258479487 258479491
    0x12031d0637020319050d06050a0b071b0f030311030415090303020f0606090402010806040605100c03030b0907200f0d090801150f180e0d02070614070308150301020c070303050a030c0512 81
    0xd190480e160b191b48035034030002c3c100980c4500d81c4003ca01304086241c113903890041541d540f08500400c001c10070341d43e0030010040141300f2840c1e8480280c130100046070154115102d040701038020741c0c1c030301900c0d07510446015180809000000c0c0c3c40003414802c154041086803080008000102440d1900c074000400700340c00240024108182940450703103944480c1c00c040064003000b8511582c1000070f02000f0101600e0b07010580c002424111014103904105400b0340c026000344d9641d140042d0807100d0402c2030403084c1003030b1a441c8902c2c4e0000040c20030601003441b80907215a1800310003841d0030001425540001100c0d00c442030303102c2082040d03815206182c0c04945507004140b21004003200c81e00014203a2500001e07445c010115482501540070030000142d402d207807980b900f420500301900c0100c0c024804010085440c1601061052120070020100c070b0000500241ca80030400f4a11070174508960710460109501194030402076030140580c4150035110f140c00341c01c0c0403e1906c2c0380e03408000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 258481987 1250 258480737 258480787
    0x2060123010e0405010803090109050406030b0a020f040e011220090739060606090b09061305030f010906060b2506021209030703020712031d06370203 66
    0x10344400c0340d4907640520701c901c0e400403000b04104619a901c07460603031294004e007116800a41c0d000b001040e02e260900c0361105603904184141940e5031840218030080d800000d40050301ca009001c002140d01202c074540b8083d101b10030720103912a0183c6045280c00c2801c0c00c0c0b0381c3c0542c11881e41600da0b62a201e50041e804074442c5821610140501103030095240c142c02c0350b00f00304810044140f0340241d0048a82071980c4641ca003000b005c3d41d036450441d10b6991a004a07071080c0800c1002c90043d10b88000542400d0b07009602408200340d4500010746803444071045139103940d444449203000e01c0198802d02000f410f050300304a1030610350309500c0170400f115400e8808010740e400740d580240103942d03058030f140c02c5100b040680d5600345102c41650320b4110144c01c50044c46090404588200f641d2941014541e054030b41105124000744021080c1c5c4041c3c90054204905001c6008003030030340c0d0148002481d607500b80f10305000071402038180b1501e6030440c004c2598000c0000c0004903503038841e40c16034280 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 258483237 1250 258481987 258482039
    0x30302040503160e0601080414121b0a0323160303050f0603160303030f02090d031206060c152f091206040302072304060b0c0d0314070c02040f140610020601 69
    0x91503141084c05160900f02c9c4102074880c2822051441551000030691500f092500c45185050540d120b0340e10b0f50611002000114100503400d600c40f008c81c0420031004000c42000d044c130101107818020fa0001602c15000251107000307000d01c0b010200c401d40c1d00b00f00e0a4024004204442034030700310382030b0030380300c010b04050fa1102203500190895041e103800d490006c0a0000c000c2c490308006050411404140300101d240000004560303001c1d04c0422900795110200182c046040500800205030809291084200600c213802c0c09139005a00000803d0300c440b10940c4800c280b405001e000403426480003101d81c00b01042c04042500002c0d854202c0d820000312169400e0b0442c030880e100c1d500001455045420450041058555440606640310609003251035400e0701a408070140c0e0722909000d15444078a4012910305441004000750f04c0380080c10119400c401c04411004540000c04580e058039000014400e903464080c0540380703550380f13500c001d208a5041c5000111158961a03003d00480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 258484487 1250 258483237 258483241
    0x604050727090504050601080609030c100f090210031a03061b03091c032a0903020415030b0c03040c0b07120c0201091e05030105010f0807050603061c030302040503160e060108 77
    0x1824103481c00000d411010780503c414102480c02d607a86101c280100c00c07c42c0211800109044800000d55807400d0303000005082410800c054000140a5074494500613520b9200c0c402c0580c445035101c40c40c803c290f6800050b0317088052049a4000c0400b00010300c240c011000b070020b240300d400c0c02c004024403490400d5a40b9211070075503514010354580001148610074070f48540441d0903034451680000100d0000b40aa2903030500d540541205190090104203060700500c054101039000a51a0000c03030507603035100c0d89136121b01795403040c00c03100c1e00442d00c0c0020801c42005080c04c548802807614842c20ba0a02c4225580d1000c200e110000d40c008201350042ca2400303580c81014071034028004540204250154155101d40400d00c6000340c900035030808d800010881114800602114030380006000c1c824205070810031140c1c0060203060303003c1c0c0481c00c640445822003042c001b0f41c51280c0c070010383c1c46240030141801c4c403c11a240b4114560700d00405c01420086404a40e4404000d20b00340d042030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 258485737 1250 258484487 258484547
    0x3061201090c06030b0a12050d3207020a08010b01050d09030e10030506030c30010b10050a0813120f0c08130317041a0a17100e06040507 60
    0x1850520800b0305412140340340002c19a406500c00b5103c00d9090f1054101da94640c650040c00c5142c10b10024166402940040a00c0b4411102e0140000c02049030f030b501b84d01b44650b1100c51542040300c2011031400060342904628220003041b0042000c50000c5c454070045d100064403e02502200080d025140c51100042610176400002512001881e01900f501e035100c0050090804840c0c3c03a011380b103103800140e0146002013074010803451058000c02451950402176603030052550a103805903480c1c8038011099038851a030310305040d05a5072a55106c1001010081000d44042e25007139810700011000c00c0480c42651030350500030b00300e0500c1100c0750324058046410301c12048000d00360a03c00304840c031154621400e000102e81c041d4490385c5600c0308808074541d9030321691081d59014541c0745200400110444c0c06001001460309040e021070101d20541c0c14a80d2080b03404004145400740706100c280024011241c00410a45041095240000025120a8200192000318a810300b250425 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 258486987 1250 258485737 258485741
    0xd0c0f03020c090408040305010510230109050607050f07061d010503130c03050d12021204030c020a0b030903030105091303020718060819050c031b0904031403070801030507060302040b03061201 85
    0x400780301030200000744c13800f4207003a107158000c0d0004881650900c00800c0070340c0d40e41d01d96601607601150b042d00c5600748407041c01401d0036520b420300d41407100d285400500341d942c501c041c0c10041c2c0a40090824045540d03205400d044241d00704006200c5071141c1034030810750480010102603000e0034801d94039200c52081d04400e580004000b80b4504e000b14000c0300f00034010601c0d008400050b1100224030303800c40c050105a006d03142a0508004184002030086071140956600050007c3e14400d44e071511010108829441140c080702c00f903000000411090034070800c1a6440000c0c0c0301c11000710940ca0f6002502c0f030503a44503c1f0034901905150703002e40385055004000404000080711014030010f8000000c80540500030345070750043e0b0644210508002c124000020100d690442c0601e07082e0040008101e4050f2040d000c10001100c0d900150354084021801481d0b59101c6460304d62551130702e9860201560020001c15006110401c082c043d0b4600b030740d412190440c1d0030040c50755202c0711680 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 258488237 1250 258486987 258487003
    0x120c0506031312020c01170601050705150709050a150807020106050409060e060703020c0303010e0a15080c090109020f16050a0614010608090309130b031c0e01110d0c0f0302 76
    0x3a01200c00018032a07078494008034820031900c02d00c4a540d009200c0c0100341c0e00d4103000d03140c06001c100c40c201040407100b540c440c0a98440014100b090802040e612003070b26041d00300745001e00d942d1600c2c05000a654100c1c0c075842c014030040700e40b0181142442c04e0f01c00d40307842051044080c007104d030300030424040c003e400c8a4040c01026108009072032603801c040d40542500031056425008000c0820906d5119000312444e520007a40118a1a4600384190b00c1115000b845600150741d41d410010030b001940c0500c400a080c40401400a108543c00b0405030300c034181d10030103c19104008a00308525500305840f000c0c0007a448020f4105142d00f403a0f818200b20f00c2c4018440b0f8600080c107000c43c011454580d040e51407a035210100c0303039603801038247e03a44221500b46034800301c4110024619186501300c90025003014060311840004501440741e0000480241808110b015520b200e0f50b50b4403072414500348000ba0000c0030034814020000d840021044005450b02c201da801c8881814003c1020389 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 258489487 1250 258488237 258488239
    0x61706010c05060c0d060f0f05060c071206020405040e0604020f1e04230108010902060f090d12020102032e0501050309071d0604140402280f140f0108040804120c05 72
    0x640f462412039840840303688400002810145400d0000c034280700d01c040d400080d40c1c0d40307164120400c0e0a0108006260f00622103101305442041404954111000fa400000c0b600c43c0e400581c44a04001c2000255040180705c003a040d40140c0400003d607880d040d004020001c290390203d46040742d01c01c051403e450b50b210680c1c20a0812341c182900c1410799816180c246070740c00c41015240d0700c4808646c01d031080f0110281d4400c10a0100c03943c07060404005000c3c4078402014980c800485940394074201c0094a40400540d40c0841003107800400702d9221107030290b115040f004100c9000c048002d014195000d501d0410030b0110000307094940410042c0058409441c01d81c010303017464080c40e000403800300d0384175000d81d041000220b0300101c5000c00e51b000d41c3e030007004042e1110f03400b001c00e80141d150170140309003082c4150340020340ea10f80c403180c00e000d41440c00303050541d0144602400f043c5d040061415042241d030702c08110208510900b0386007611120507000c560301006003011100ca00caa60000c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 258490737 1250 258489487 258489493
    0xc030f0e06070206060105070314090105090409030201140a0213180213030c060f050708091e10080402040b0a12030806030703060e0a0b09070b0406031d01020301170c0a061706010c05 80
    0x403481460300001c401e441900c4903400c5a226540311801100c0900031414000c0100d416210381003901941c0c10040c11418406162050602040c44006070640324551802e9026075500c5400c880d441c071400700526405644943d0030351900707110b0121a029009144030700078030014035042e105042d110700d40480c1c10f9402c110b101101101d48900303100445c60b84d0f602c14400841c055000903010903000d0001c1d100100e1b0000d006034182203240d0240000c0320740c0386049946403524200009030954901c4440d011400b40307641c035003909151601c1880115100c09403001d106020322401040810960201c001c19198145008801602c507100405d10349034080e000200b8003030400d01045210000003a4011240d0701a80c1030008540300e60100c25111070700c1d8040c0c038400c0b201c2008140480ca000340c1010b80040b07490f0740c400d14000344c00e024541c2281c200b03801c01148090b0f8188181c2c452002080140c1ca40701e07048403e290744a00c3c5c00d001400406480f4488060110104000b4140c2c1c0c0c0104402110701c1d8200041d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 258491987 1250 258490737 258490751
    0xf0906040803040f0806130f050a02120f01150b090d0609061b030c0e0306342706020a1103010e0607031d12221e0504141005040c030f 59
    0x5480c1e1250441e0061a50100c41130302e001803400000203005010b030458501c1d050b0401865120100210207081040c0e0f02403059607407003001070b21a020014942215000501406941d50084509490b207480041c1d05010000c501481101d80303940440b401d0348012106492120106c0c500b94000e401e9030040600003d2901e044c0750710301c0c1e43d8049500640c042d6681c04100e900050325056415200f0207140a8159202100060300d0700d00c80c0301c0c200d101000000f5200d2690080740085429800d04641e0b0900050b4008005082d52a400c01024820040300a1b80c00110741410230095562072660f2028040088404428095440c00c0d8041040103ea480036601c1231301d0a00c00107405008184002004100140342002001c240403421412248118000900d403000c07c6c00c6c0d46052000302c070b8512a00c4e04180380002600691a09010400c00c81e5100c0c42298504d800104411108000b021503c00250001045680c00d41e50b20503174140e80048a0008000341e07a0701003100100021403140b4551490801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 258493237 1250 258491987 258491999
    0xc14040b03070e0405040b070806031e070302031c02060601050702040209100315090e0303010509071b03020c03010c080903191e0903050d09081c0201090b18070501110c04020f090604 80
    0x40114480c41c100d03159460f03403103408410301040320011200a0802e101080101e10070320b20503040b046d0450002402c4418220b40c2408134803000c13040c00c40078140c0b40d0080004004504042c8036102400e10b21800001690030041d41c00380d08c64000400c0c59042000008040046540d6541540c20084025120342030103001614003034000d20b5980c64203003080f0b10b9014002848011402010449192000514296441d000c140044214040c0c106020f001201c0c8080910862196005204d94020340c0100b125886441c181745c00c41d1340941c155010030500c601004041000001140c4150b03407540381d5006260701d1400b0071210001400440005852600c03001464954403000f6901a28050710581d0a04040000240d801c0b46162155104c02d4011084e500038100d0070072400c07c007807451400040b038240b00e640d42d07842c01c0940440d0801d6141040803c80d1500c10410003070f2034054102801d040416a202c0038038240d84a4840542520039500040d84a1180c86d07640b00b0b980729041d0103080d00791036a8580b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 258494487 1250 258493237 258493259
    0x902011206060509030f010b031908090306090d030c05120127050705090114030f010b0705010603020402160b06010305010b03180c0901030c080d020712022710090b0307180c1404 78
    0x4038060b41700e0320544840c102040e1041c40b6410f40e0120040c010403404a00007204603c1c001c40c000c064840c2c010030310094029031814130580f40706004500103031459030a86c0601070202d406000c0540204041400080003515442c3c0030303141541c0000d40080d540601000d15581044900001541854141810b01100f03603008006441126000d880d41341c0c61048080c51450180422513070000c1c1896901e00400c80c140520300205860b81c068000418a03035140c3c0c0106040c5d901146410b00021464043c06050011805034a5009402460144403c5d45802c1d00d82559000c081e100c8000c1101559402880080c10451001b04105c05000010075607568103120902c1c070120f10032000300307005000d654000c0910106800082e40d001c40791150340300c0c8160f002e210103109043c0e601d035140c94901d95402814009141103520800c44d5040b14200f0030300307040b404000c1e14140c1c1e0119001b03a204040512500c00d01d1151580301c2500c402c0c2c00a1f40fa910f204044507500030710340b40382701c413000001404601d001c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 258495737 1250 258494487 258494497
    0xf13020409030e010e09040809040c05160807060e1b1c020a0b0d050c04150f030207020301020d050402040b010e130e0a02060c070303030b09010605070314090a080a05010f05040b070309020112060605 87
    0x262500d05d0380041220500010a10441d4014003c1008001c50070903032038158400800260710703140244c10320400002d48800942c050009882c113401c0420321070100100d074000c0c00c2c140141080605000307102e00680c1c0007007001a52805200d0500ea01401e00394005260f10008125001086040d00513507440c0300b68025030108104581d8181400001503148031f42c40100c9040b556018800c9010a140403c01c484401d61041a1000c0513000c01006025a41c240050500685500030000d95030078288100401c40b0240c000362070600c480c800c20075465950303030810700e403000350092008601400392030010343c28005030680003988050301043c041120880016600e040c1d9109403410411400c40d8010400304910920038440000d000b0400d02c00004d1140110380140d044103101035040040300c00001d1000350284d00402480d510021602003172107001d001c0c00c8400004601d00b005941440e440301f04503c40000c1880c002e01d5103426540c1e045911030504024440344c4404d0030040e49441e214010441c0e801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 258496987 1250 258495737 258495739
    0x204111305120c150f040e0108010506030f010c0f080c130b0309070e100612060510110118020108040f11031c031d100b040b03010606020102071211060f13020409030e 73
    0x4a44010b403441e0310300007010681000000d000036000300b1411003400b41e0303a2000c1c003400040b070310511000540c2e0a800d029503000e00b50a50000c0b4480c40c0002c2030615113028010448445da04004900288940100c2210140451460004001d076600812454070348102d4401c0031121240c280c00156101c1504040c50048000905a4500b16a201c1140070030f44803d41d40c00d82c2c4a41034120030042d86014030401c410154035024017154440e034400020300041c031495090004500d8210300301701240800c0c8142a1400600c42c0a03050b150703c20f4000034248180240000c01c6003a066641e00184050500080c01d600c0004049545507140d800202e480078490300c0c004070200303040c0460111a02c00ba003480060b21000311000b800b04050f4012041c000e050b00c1c00109404c2503468600ca410358800380140c40c0075010075000541d444d1213524014080e1186180900200710410a0f80c460a80c0c003c00c0551304100f103603005552946444461140010392504000d600514081c80281016044900b0f2019004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 258498237 1250 258496987 258496999
    0x1b1b0a0b01092705070e090c0301110d1413230303070504032f060d090f0503070b010b1306080403030f1b0e0316260706081504020909070c0204111305 66
    0x152040f03004a81c5002500040c03035900128424030071310007500203042d4480380c541e044070308200c580c0700800c1c21200382040090800200244411600400d801841280040300344184c64900e8840143c0907031071040040106034a1007200b101f101c03126001d0941c40302402603001e8a9403428000c0000d07000703520501c4100d0b004000c41000c205882e010070001c1b41c80c1d00301200e90740d014038210010003070a83d001c80101b00311107640d16207810100d8120308003080240e104100a6545d070415042003021500160f00641c8030782406c0200c10303a81541d9a40d51f034115071b840d00f044800c4c0d4646180c10740252001d00c1103440600e00d00a1b17000c040301c50415035003004180039251000d0030071884050581300e0301c0d0700d03150240201c00c18004001c503045902c0010b00f0b08074a00e036000801c03443c05076803030305180c440d60029000419100c02d0014040f40c041521300385035002c9408600d4944200d0105d10449001070002040c014109414415508c0d82c1c1c004015a490101d01c45e82e80d41c800c2c00c00000c58040d1402068010a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 258499487 1250 258498237 258498281
    0x3010f0302041d060f0405070b0a050903060a060612020705010b13090c080d1d120115090e0a0f3005040305060a0b06040e0a09050303070c05061b1b0a0b0109 69
    0x80340c3c901100c50340d1403200018141994480c0000d00f0b031014050021a800d12602e42c00041040080e4050034207108a56500359032680b081c010180340040140c28100d0391840c1c40d0080004070b8024144803802e80e20400c0144c2c40d1810b6081c030600400500d000399030440d9000c0c4c042c0030508281ea128800a40c0b085400224003521002126503404540190b100800c444402d40e09000201c0096016003002c004c02e50b80c6905a00602242074840c4045101c410090000c000d00c60f002190140610704500d04d070042222501a0b242c0c19000c40c4000d40281040302d10100143c100c2600b0101064000243c5d4800b005071031a0f0a0014415030003840b050b41e4601441c00861560703801ca02178900030b68002021641041e00300042c43c0c0c0044405001c03008882d0f42d4070640e0000a8007407014610074030564652898000060918a04040d0b000340304001100c9410b203c110a0344140c8281d0302c1071501500ea07005031007507080c065032501c00700c503101502c8a80d5000000500d0042d5420020400e2421031507404a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 258500737 1250 258499487 258499511
    0x1202010606081504020405060708090a0b09010e042703020f0f06090a03050a0c0605010e011d16140c0303090706110304080309010503060a090f0f0c091d0c04080303010f030204 77
    0x2100c06000311400507240c0e0780410300b5001e0320030242c2403803280104010320780fa54450004209600c9040222821107000c21030b9000d922701804aa0700811400c16079034604421f00b4002000d41c144031b00c4e001e109a90f2009089541410551481448010b50f80200308640050801035510841c0b24030341001449100703e02049240c5c0030071428003400c1e011006001d661083c0c0d03001d94440d04019402800c01800d2030702c40f008107a59001d004e00800388610241c016506108036041c06a40e5044040c460034a9a000d00a00d101050001149030360149000352042810761740c04020342c4216420f15045100102c2030009014021501038116079807601c480c0b615107003010302076440380520320034801c841c2c02c03c0c81641c00b03d5001e40f0086a001000816100e509921808010215031040b8210300b0301c1c69a0350b80038070b03442900d441102001d4609003400c1030200e103800000750710000181d01c000308a032059004560450084000d45018100302c1003902d440c2e40c1c58003508020304c025440164821030030210480c00d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 258501987 1250 258500737 258500741
    0x609051e0106050406060801090203071716120216140709151401020705030a1401150306020702091f03061d030307020d2d03020705070503030408010618110703140706090b04120201 79
    0x203c8a06451f10102e50b881d1410050082d00003c113607002f80940c1c020081c007041220700c0e2051085001036801032588101c1400200101980c500c0c81d020544100100e0001c09051440c0340405940b251201065000d042e80040c10900b0035403203d0740303450802e017820008074100d05050741519511981c0490313183c0508012a030341c10f240e1054540603003000aa40380402c6146c044150140301280c0003046851984a04007040f180c0ba602c00c1c2c900c181d01040200452a11040044d004654a81d00c0d10424022404d46000003045120040899903a03494400448085c01d1016100e40402001e6944a10b803080000c1d484509015950000803070032403008505595040c4421141d002241001d101100d1041c4c0680095004000686d16031083d04400105582c0810040020303094500001c11079038904891441070090011024451074185044907a01c0540a002d0350101a0107107855541040d40d000580581c1c13080d690098901414207a0707480070b0108010183c0d018034856040302170031880f90b06040342 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 258503237 1250 258501987 258501989
    0x1303150f0515090f0a061206060303021504120f09030b040f020102060903070f0f020f09042d05030a0c080c010f14070e100809030d051906080a08090d0609051e0106050406 75
    0x603003c0610000710b103420b18030007040369200400300000164180c803242103a1180050000441d01c80c1d456400a00800d94184250346101070340122019560034140d45840142c802e025040040012002071790241034403d200100003541c01402078007903801c103410100705c2d01000e9030003640588100070101d1a107500001c21101044d400503040e04d104001c0342c2d11701003408036000e0141d074401d48a100e41d4115580b00340caa180950712079000d138909a0402001c00344890840744100c00c3c0b2049498465010503804000c507034540105280591071400c85144c264407601031a01c2d102c4c0c880d841c0207502014051244d101030722107117185458040d81e60b14410211014490319500503089100c09895045a600814800f500050783d0400c4d00e0900c1d8010300540f040300d00c00c554951640300f0308042c0f4403010f04c0910420003d0111140a400e9103186a10b8850300c0e0310800c81028060a00141c01c9018000192701052920707a0101c2540d038040b6142c0342a20418140c8000ea01d029481d004000032140740500c5180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 258504487 1250 258503237 258503239
    0x70f05220b0414030307030c0b0601090905070801080d1106010311030a0c060f1b12030c02102d0509030301060503040c03021c060b0901080703020603191409060a02041a1303150f0515 80
    0x1404580240e80d0841c89c00d801030042410f000b00c3d134902051b141a01d016403407181081d0b41c4c41c800d096140c00f600604e84100c1c0c8003100140500940140d1b081c441c085241c90669403c184c01c44040019400441d01e045600000506500100071012a0080d4001180c013440e40e41c40e503039004080b444000000301c1304e4545000400c2c0a030100301410916000360050707601c01b90303a8010743d00041d15088004080d41ca90070081d10320300d0543c03180c00040c000180400740040208110403c0245854100710385d807484180114002e21202000090400840b00503040243d54081d083c454000351380803506003648121201100c0d4241001c1450406007801c46845041b1141c410041690619603000d2103034592020b040440400c08103400809190000d0043c4100410101320180d21803034114490381c20200080c280a00480c0100300c10400d034044441e01c144409940c200e55075644205106030b00e56201035a10040001a05524419502149500451001c1c400c0b490500c0300740e807586000d10710720b10545646 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 258505737 1250 258504487 258504497
    0x60105090609040b0d060203010b0406030518030301030f08071a19090c0b0a050708030f0402030f0303100506030a020c01050c030105030d02060105030d030b0303130b070317070f05220b041403030703 87
    0x4008038586038100b42c130340a00290084405225a0300c450040e44d100340c024605400e070000c0c0c00c00150340c0c1881055031110000c4402e9a42194105a0540700e22061102500c14107600034850140200d14084500c0c41354444000c4441280170314952801c140c0440303c2200c06102e070101807101003604c3c080d10120a0348041103205103810a00d0390754a640203c2d000c2d0080010a1200c0d1001400050003035000c0c2c0d03900d4a410507146003600c105031810b44403c1c03504006130030900030f118a10701854652800d58008076181e9803287c1d600034842000b401081c607003008035802d12013840381c055101001941601c41c254251143c08140c11004d81e82c4020a2103002d401d0b0340600c000c0f1104a20903400010b100d04018181d0307142c08500049014100640d401880f034200d00044c0c0c800406801c140100412002d02a020100d4605400060300622981c02c01109004000900c0d24004081d01050510440c105040250403034403581c003400150058000c103003240d03510310590703d03480c0f9001094451956040c1d0711 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 258506987 1250 258505737 258505747
    0x2030f0d0f2703180302040e03070506060d051c030b04051305070b120a021303050a03121401051309060b0301060305150109150b0c0a02220f02040b18030c060a0c0b0601050906 77
    0x101c0b0b00078102d40c4e040c9010400300001000503502c3d8001c8080c2402080e0007581c48a00c0c0d41000c038200900542224400c0d51032085180c006000410b903240c0b1175200780113450080b070121034207a014107000c18001c0c0c1e03c18903100401c00302c00100001503005a0240086501040d03d5804030b000318860181c0740b070030712807081000070004540d6400610682048c0720103600b18594030380d686850604a00d600308c01081042031071400308078891054591f031305001003001d8501c2d450800441d901401c10011928407548410b441c0d000c0c0585600100407000700900208801176690600544400100b00d000488042c90400014030b451180100e80005410a40100100d03141c45218001c0c1d5004021081e0306008260b601d8002d6a00c140410030010041e0780000e0026480803008c504071101c13840701d1490244180024418240140203560070b0030754401c95214110120070000c0c0c90880d90003580e03540004c000400f030b100329070300c1031045440d0b07881800241d05c03070b48a41c001035503540107004c041a042041404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 258508237 1250 258506987 258506993
    0x2190e061c0b030709110c010b0a0317070c05031b1302040501080112050a0b1006020c0114031b070b040807120201050606190302160302010204050a05010806090c030702030f0d0f27 79
    0x2c015124144000c04440004c0d40e19035404003911752181810204120224011020039401e00030200d05643c11105420300f40d00b159984171040140e0500c142400e040401e981d0200000303c8014400341c81d00038100c030002c465160404030100958114103003e061840030994040c0710034020341c1c06840058440d03109507807c3c10700450032503202e09402c0d5114868540341c00c000c99070100803030340241d0301c218a0b0907825081c031038040e182c6203088100c1c03410860482c60300400403120b03000b5070f90840303c440615003200b00807401d10309a90185280127000aa1802c00f40400c21600d0801428114840d0011401c44190309a0076030884004441c02034000f00208038125800301000401080201d035803c0040c2013040340342150104001100040300542c1d40010180028584440940014403091078000c40310318003a404518a440d0107015020071005c08800f10360f4890081c41900c20074114101c005032a49806d0140d18003400d158544021000e00d0300108403c9a0104090072080494456804119011950f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 258509487 1250 258508237 258508241
    0x609050d051009031202071a0105010c150e010b03060a20040b04090903032a08012306090d08030a05100b160f110d03031a0109050d2402190e061c 64
    0x83d508404004071854480c00d0b5a0040c4040c0640b1400f03148800c00740c0c583d0f0f0308070078104481a0005410711101c00305000003c1e0001c500950707083c404203008114010703941001c502503c504a00b09916000d008200a20400140c2c0654602400035803a24031310448e10041e091544150702612400700ea0820041c080c2d44256044048194803030310b0b0014040210040784207480f4590301440e5a030100040200341c4050f401402c15024000d061080383c005003a10102440c074413444043c0794016100481c400080e640c41d4079030001e01039001040726039240f41c0002006c005107001c60b004807040e400c2d008045500c0490703100381e6030030010403c0c89030070824140c2c50300145205a044200c036142540107480c2c0441d11a0801c4d80d100c1d900c65100802c1000d40034507001401d42410030a141042324064003040300d075407180003040040781c0100c000c0c4907160007400b5200f8a09010030b00c0403402400003421503200d0008004ad1908800340f961114003122000040180381c3c880ca0300005400041c0094040038140c6036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 258510737 1250 258509487 258509501
    0x510030c03060c140f0909181519020406020609010c05070c0e0612100209130c090506070516150e04062619051606020706020a08161403040609050d0510 67
    0x303400c10940d40300c0004c00c0c0c1c0c05103522429208285c2003000c19603070a9800c20038403035900449818214407041040c0d400e019030780c2d140e090380e440c014240380c00440e0780c8034800c0d0f0651001507120001556226114500a941e500003503c070040b4661800706100c101307503c44c009441c07815078000750110016144c40c0c43e0499495000d0701150f0301c142010341007551021b04025101003c0385005000d0f071144c60303010412413480640140c0c0d0480605095202004035805000c5000380c0708101c0385d00742c0340c1449040c075a00c1e0040b22809003050b003100c0c8401090110302c131021100c1c0e07042c5c2c0303070303506c10300c04d407090003403006039401c0e44200c0d040440d02501800c1902d040f407401078105102401202c92900d44040b50154040da1800f00340c3c0c1c01c0d008981d8440ea0301c000c0d10306450150480380018aa010328000009607142c5801074040c051940100ea01140414420b020402e45074203d806528100c203150581d80c0c59900c14403d000210300300b407a001840b400d209450502e680c1e04071024140100000808402622407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 258511987 1250 258510737 258510761
    0x7050a032c01050f0c072303030f0d0513060e070905071b030f0507060501030f050f070e0f04063c150e06240403020321071212020708030a0510030c0306 67
    0x1306020915448100b08081c0c1c000b003410148841600405980640340c034040401000e01a0b04104000342c0e200d152401119101d00003c440055281d540448c107004500007050020411030030042c04504200000079050140c6076188020002521181c1055440619030721010396803403156400c200c0400d0003504c450000d84610b04047d80303402c000c0d80d41c9804580d400d0b04102c6986205c100d00c0c03002d00c102004403140c900300001c002c00c0e805007484400666000f0040c03120468044150009080240039008041c00e11800100302c59428071380d00c140e22a00f96908190341d00c402c805001e0b10038108841c0a11200d072440c00645012450802141501780c0200803c1d04c0e4000c00b061100108012404400d8020610207041658a541c25441018204000500c1c0c1401503021100071806900070001203a4065501140001803035425040940d840060740112068062012a140080c0241003000794440e420340c104c10480340ea26103010107050b20250101034010a030034402400024019840b0800941e6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 258513237 1250 258511987 258512017
    0x141023030a020d03090f06051306080906010315060314010f0507020106050609091f0602031305010f20070b0307020a0203071e1505042102090601030603050d0c1707050a032c0105 78
    0x184814a846c1c076091503a00c28000600c00242800b82820200758540c0070b440356160092040c100303102d0050b07a070003040c08083c1601c02000c02940200c0d003642c0c0b00c840295444400d03050025240c94219000303003400b0f2440c0400900300300c0000c038080e2041c4242400c0d076030018419818840d9000a02c00080f03401420443c1c610019031110245105214004c8014810340c2c0c011903a0320350015091040341781c254040d905000902e020802a590002414400300d903580062608a0310400d0500d807030005d403503207d04541c0f0b500106005140d03a011402d004548d0003038044914460b89c1d40c0c14114041c1101c001070510700c0c00c9100601020102254000215a5600c2c100c1c3c1099216490501032040000c00698058031300b6048000b10f04002c0c103031a40c00342c1c0c00d090030000e09213942c80b126101d9215035101420420030261600030071034a4580d0600d500200d001c01d6450300c00d140781c01c41d540c404558042d00070400820100c0703204580c2510070340c10000210b890708a20b09100d40155900d40000e8001ca4a400e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 258514487 1250 258513237 258513239
    0x7140a0314061603020406050301090207020612042a0e062106190e03071106090607080408010507140a090e04080c031c0509010b010c0209060103141023030a020d0309 73
    0x550244040101c1550103014040b5824581d040d0542c4405030101e4005043c0180010800c071030304001520b0445d42d104001603910111440052407902c00c0103074900066a0742400c2c0428464002d000320306c014024807000b405510825220b5544541d41d10a600268a1600000e0840c0c248207807018100c440c0d050810440400d184d8241e800d01d5800ca03030380c8108502d801c0c000d004408540c00f500284c2c11003440907500e0100b4a0711800710403102c0e0249140911000034041d601508c1d0802141e1400c1d404c02107454590303881c3c1c0400c0d03000e040f055414800245181d42e0780e600880d40e06c0111002103825403218060249044000042d02100401c02e0b2000c910910002e032020800740003c0860411420050002c60424016071080b50700103800d100c96a0f24103c0c42035a2039800ca2214000035804503034211482e500e0300d004030080c00c05d0030f2100c5c4401180105101310348440941c000140c40030300c083d511101c110109296003042d4074400c034542c183d114514110141c14852070b0143e9807402454641c00003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 258515737 1250 258514487 258514493
    0xb180f0406180c090e06090a1d0d0518030304050603010e06010201060317030a06060906170c280e0d1a04051203090c13020f0f0d0608010612021804020307140a03 71
    0x140c800c840c01d111560f03840d683c00080140d8802c1054014080001001d01c1d01e04044000ca0308011005115649550365040c140c00004281c1c03440000c801034101c212004601c03207542c0100706400c907030241229100d200313100702a60315000c0165003d40300c0242c29107007103a203032002d598594000940f8050641d5030314000880400c003052152041462085c80c0141d0f207080a90b01141151059401002001010002441071651080e180300d400d00540041c0c5040d80c5640d100321a040c401c00d8030301990b0814055400312844000d100710b4004402a485405400714104140821004105001014a8003003541001e604480004c00c0c0c0e08140600100c40d660508400800c019038001d03514000e456003c210b070411f103490000c140c800e60340d50424041d4280210382005402038019030700303003040035800882d0000c4420f03250b92002c0e00628030200244140d0303940d044041c0d00b54034141001c1e0b01480e411004ad07050101b426541c280183e501500400429140c421030200586000c404030b503000b41201800004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 258516987 1250 258515737 258515759
    0x10b0702010c150f060512010b10050901210608150903070209040809041104080f0115031e0615091113031205090607050706030513110f040204031a01030501060b180f0406 75
    0x20b012000b61300029020705040c1017011a010071060f8400a0381010010040c0f911604511f028406181c01c1c0341c0e464040250040c0d40c4040c207401202c03000c408902280b02d40c48001c0d0030690448218801b03403410105c403500c2803c141344044032030a196510420101005040032140c00740d010f8016408541003000342c0b00018140c4014055003030380020041010300c50082c050240029000c82c0400810000c94100e0b29810fa03155588009040540d010403403140203110210200482684110308020800c80151003840f88085030003240c102c903103005080c0b900031800a00301c4071004602182c092a452a50350b400700b01d80410340d480400c01c81c05005032800398807550084e2410f5440398003c0d00d944c5040c804000c0031030720300400d50b513541c004004005001c0390340380540b20241441a03c01246408040c0003007006840303203600042c0801e22408a078003411050455450507280704030000d00515a841c4514032a034012841d50842c429485440d40e1098076150802d04500340d000340010030040c0e61240c0c4c80d56 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 258518237 1250 258516987 258517001
    0x8130b0720010f062c0f0601030b1002030c0105010b0703200f070306061e03080a110129090a0623130207050604031b1104090c0e090c090a0203010b0702010c15 70
    0x1c1520348446003170140810343d5240001980010403466416640701d0307103810315002c0140200c000d142000d0003061981e4400d8000014501c0094043c0c01c01c1142500d009580e03501c92981200c207035107000008211028000e0031902e900f501561407010309001d2181200300ca08000d13040d00081e07c070b1100282c40d503140502415000314000c0c030000a442d85003c00060090b104481c045007102c180e80300920020312070200b42c400160711440d2640d074101080c180302e401005000c1885249212440290500041401158580d1003056034540656184e1401c80e0301139804d940503c44a440d0703d449004050f140d0380f108880c0c0c003c80100681044191000c0420880c0d001c41c01c01d07903054001000b0081032540207220180c0e1034030a681803002000b0507844070070100c1c00c800d07075252250303807505442000c0c00720f03d04100015010032000d4034440c3c203000c9221560b4a43d0034466501070104103000404d81942482a83d040f10008a000c5240c440e807507004580402041a04440c095030000b84040c5280c02442181 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 258519487 1250 258518237 258518261
    0xd030c0303020901022d061003020a0b0a02010612080a031d0d0c050a0c06090f0b040506040b220e09010b0303070b0c090316060507060b060315090606090d0503090108130b072001 78
    0x5491b809881d1212410b20760b000300800c0300700c0040c403801c0005032541040f0b40101d58081d064580c840c11028022805401d060707102c15203000780302c418142404047c0c801801c04034802d4404100c03194042d03548840c0741c1f4103442c4c55400b5401001c032018041d4054212022143e100b44291850010b2a40d11100c05440701c0c2c01c5000081d40804050018441c10b00c03010340075051344481e042c10b151809002421600c198050b5014058010070b03004c0306c07000700000d4665056444d100c540c0880f510b402a00d805c441088821702100e60802000504038100482243c1e142134002109440340d54030703071007a40c540e60f00882d045601440761449441c00e214810781d4200c0981056625540d5540e03041c100182a942c000c00fa05110300004c0007405140303102d03c00600d0b4500c0303054420ba8040e0b546d10000035140e0041071405a08a1880f08050003004004401000800400d17200d40701161260303401598580c0d000c00c0c000308000060400b191445d40140000d5030f4144074000b030702058102c40b42101e400c2d604810410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 258520737 1250 258519487 258519553
    0x20a0e1507020f1527031b0f010c170a020a050d02010615030203011d07050d090b0a050906060312070203010207061107020a1403030a0c050c0603040309090b0d030c030302090102 78
    0x140c81107103009012100c0030b140498038441a1904e5080782070251240c1340b6855a403003221880d40080350480d940c40c0368050070082c281d50003145085410a240340d002d80246119502481d00320000390b004403058101582c1100c2c0c1205d110102ca4840e03110b5901811085003588204c1c400b5070300150080100b04140c1c90158004507075180b802015000148042501d44141030061006002e580d42d1f02900f2410856a4800c031100c50700d4111043d10b40344130345410340645a05141500d410300c640126094064071204e03500b0400c60b940d41c0a11515500c0a4510580c90341107000c0003019140c4c2500a4400f103800100010f141881c9541c440c0d04450303100412100c000b4011a0b20015450204c224500504841c5085488070001c000000c1d1284207034041c1c04144040e9030010818041e0400c80115400b00c081c18866a0303040070b0501410319001d03445075a0015042c880014054280748a4020f0000d41c1500e4808240c541c81e503069019401c041c81181c1107104040d10745039220360a5520180d040140300d10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 258521987 1250 258520737 258520747
    0x9170c100902031603080c0615060a08061810051903050304030f11040f140a0c02062715190b01020703030c0f150c030b12060c22140a08010902090604020a0e15 70
    0x21070901030010142105102741101915682e100c3e642103d804c00403074945141c880c0d480e000021540c00f5181040e03040e8106010800c03034820700e901c00003800d0702c0c2c048480c040080020755403404007110500000749590418442000000c4824560342400c512520040c441a540400400c04880d103110305455520b0300c0740509070101c01c0c2d244125030840da060310b040c007642d800110003a607541c0303001e041d04a00610100a01c0422070144407400c40c940c1c00241035840d0301d24903a541403100e410a035021031410001c18001c118280807441005261070040c1c02420216185850031780360041241d90a4502c900300100603400589440c940101403050701c48000344e80b401c00440201181e8082a04034003034150020000c03848000014170039845284058003669480740406064418141f411110003208c0d0307482400701d2807841c481e18051030760106480380300a43e030340c8804182c02d07900307904000f0350880f00140209005040036001405104903a00380070b50740ca03103440045134541c80c8408010f0301c0d00b440462 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 258523237 1250 258521987 258522007
    0x32a0d030b130e1c021f0c0906091518080105240a0302010207050d020f100804020301140f04060c050405030304120b01080109080f18120109170c10090203160308 71
    0x3054071880d0703070445402c0101084125910384c4d21103295001040b080c010610400c3c800c0c1c800c01101440c0090329075608840c1d084d070502c0c20b025014036510303200403c034120b101060840c403c181c0c80d03003102c12070000000e113046078980c01c0d5480802c000c0308407400310a1520204640b0000d0003198050481401c041180d2803031400c200b40442c40140380d003272107100145000c00242c2e0b1b00140c4001903440c126180304a020030791001402c00b40700600381c141c101f41801445045c094022140522443c02a4002d110004c048001340310600c001710f82000b140880007001c40c0105916a015600c0c1c90b104d4209281b415032101300007032541c3c2082d40100e0305492008404030030001e158920703a005001c0d0070020302102e441691000b03001d00650307500b02d514200102c3c0a03601e608028039115000e1402609440e200d400130450036020300351240042d0f8420b20058112011094418101d901d080e0240000c0c0003a4007250512001619401805030f81c1403048071041c8031003061210740d0307100552142c030580b541c9643d089 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 258524487 1250 258523237 258523249
    0xf02010c0b04150c050406091809050706021b090103020117090a060509070303030b0d02030d050c0c04021c2004120303141006080106140301090504080705061009140603032a0d030b 79
    0x541300400000380301c20043d41350040a003105031390400c4d151865565131545403800802d054000503115210300c410010300700c0e4010030880c002c410712a51550701886441c042c000000000c0c0310007400500072155958a81d00890243e5400c0b640100070317680200450340356082070390310544507000740780c0102c601041015058031551494203400d0f1f40052043d1b4040e00003a8840c803000025409101c070000300da1958010030711480b843d8200c001e00441d100c010701c1d8062110f4114074103000c600303149808003803c00c4090b24007014940c1d0303840a01c820329150030b061203a0b035480100300742202419200c0004140610030b81050611804902800c81c80080ca0100018a65641031783b000c8103110b241060b80c2034284c5603000f100c0c1035030b07903500c00030489843c0c0f4a8408090303c034801018002d03000710814810501c0309601c0e100110303503003640705100c41d044602c59442e07004801e8800d164035034020004c43c101004040614941070b51002c5e8003071014613442c440c0c58184400b405400740060b0ba03c0e401c0079401d10700a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 258525737 1250 258524487 258524501
    0x60501020d0809070909020303120705040f1d010302210f0d0f080106020307030311070807140706050f16030207030206040906080105010e161218050a020f01080708040f02010c0b0415 80
    0x52030702ca150383c2402051030f51035100364000c0c0b41e41991a040b8820039900c042046032010800080c1e40196803400030001089500076004d0b40301c14648402c0002805205151940f0055081c120780e82d00992855003044840b001c03041d0041c40d040c0c1c40c020980200c0c04140b2484840a00890182241e070115407401080e040c0c0340071022092040c44401403203c00d40c0001507800c40b59141c01d0010780c2000800d4642040d001c1c800c001031075464001100c0c420441c509130821000443c16040760500764517028155554040c3c030004842e00729051142d2040e9903070078820828040d0182c0140e170500741d00c81d004588158001e402c0040e985840700000c0000d84c50912449004001d605a103040c103081c044a505000103d412281e010444001c040308250350899001c0050035180d24601e036a2903003680780c50707034940703072180800d038410075004190322615401501903501c1000c443c1d48903d49662503949a00100985030b2050f810070207130205150000300c40b01c44803170040d80110545030f0f000d0f43c0ca440c0c0344141c07285 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 258526987 1250 258525737 258525763
    0xb030102041d070203040e0106030b120d052a0a1a01091802090a060506041203080f0106140711060d02040915050603010b0f16060b011812020103050711010f06050102 73
    0x20401041120039070100d8200012503402c0d4002c806a00d4400c0b00720710f140910741000200701c00003c00020a260035520228140f6425a03400309541c094146a50300c0b441b1800c0e020002c12010011241b1703e54480c45000300180d01c17610580081c01c00321000c546031070101d00c02104d4015403d00425006c212100a2500401c4050f50611200c40c10090451048200d030400030b000305242c501080207854030303170040b6002d0b00000d007007540c54603501c4a10403c416812502900401c0403040818502581e185900d8161415034841c0d211864200000b03c80d254003044c001e50b0002101d1208900e070352364000003803c000000020241c1c4075814906500c04030b42140250981640d0000c4042026455810549045480e8107409a4030f820524100e0310b014030400d04101b401218054a0a04001b01940581d600034002c0c2d03100918444081603c5040201e0740c020003c90b40b489400c407400540c440c2e08600d60200040c5020340500d050104042d082d98000202c0380a85620780350244480d50341003001c0001404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 258528237 1250 258526987 258526991
    0x6042f010504030b0406140c0d11030603072105070b07060e0c010c0b060d020619090608040f17040902030f01030303180c030b0601020f03070309090b040b0f2b0804090b0301 76
    0x2066001078654400d502c00280180d014600260520086500104080c4010300d90a00d140c90300c0c0c1807502450748810000030321545004201c2903001050b1042c0ca114802c041c000b000040c3c10108410605140500081c103a0420740300414006641400440020007030b1025031900d8032071919114003a10303490000301c00f00e60300c5000080303401d030703400700c40c00c15006c1d0498036001c001e460341008582c40d0721510304082c2d0041400914195441e5216000030500c1072036031b89281081e6140d50341182c0d9031000355000340035186907801d002c001c21100d6421084080d400000c0c0b0389099a94038181060f40c01c100c43c42080d19210000400616805010388181d03450010341030300318102d650b0f948a400340c01c40d00001c1c3c10b901806000610990003000280c5118031103004407901c0e0701d0345180c01800e040250103804015070510649410900301405012140380c00140603003010100071f42481404500780c00c503070012118002104521142c0d80781c2100780f250140c4034603660b542c2840801c000b61441016001e0180e8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 258529487 1250 258528237 258528323
    0x40b0a120903120915110304060e0d050d020d0b0a14010201060b160618170c070f0b0307050c0c0a0807050a1707060804030c08120f1003050c0616050604 67
    0x40c0d402014034081110343c0d41c0c0002c00d1055410305944111080f0124001c45141c01030f15100e901c0e13080f002d944280c2c0304034410711807469140c02007602d500054401303d01003a030a0018050701140c41e0094140700c944410300145001c58a00010b0440113140e20000c50650300d192442c59550342805a20040c0400d4101540f4200c50b107c80504803c055a0b005425103541d1481d5401d18010862000d8941381c1140f060b000e024940f0345402c000e64805124a03000340b089210000318240e0448841c400c942c1744428860959035011416282640a442100b1440c0100041e0144941d605001c01c0301415041001300035050900c014400d203101700350451001520070240140500c2c01c0002c051042e990645844070301504c0340e20b400d82c0c101d076900c0740080c2006c0c1301041c400340c00051080c113103103e0483d0310b04101203030b201d84c62200c40f140194000035059410481454140e814104020030354900182c4240744086d107240c0ba02d900307100d4251400c448d560381c542203200e40002c2501c1c180c0102450000510903013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 258530737 1250 258529487 258529493
    0x4140c09040c1d0114042007080c0714010804230d030507030e1f0b030703080415030506040b130b01050c010608060f07021507030b0609060705060402010815010e0f0d08040b0a1209 79
    0xc50f550b40c0c0031031140b0f80300c448007440c540141554010107600c50681ca07031100c023189003000f9a0340240106071514421b01400044501446131002c0c3c011406031641140d6480f280c6500e44446a180599400c0c2e845100b4804240c000030800d4005151880c1d900061314240104c000302591050400f401c099405404011041403c019082c044070042c41c4000400f00c1c40580400e0400708550f0018111401c0890001403002074286000d101540c1030364100021b0b0703900c0d41000101d55505a9584d0014401c05203185407800e158050714000d00141070007410484843d1825007034907001e030440308058204900b4081105080c10505404c0388060000d0400009152003684480000402a004244e2134800c500120345683c000c940b160310010300b080350f41c1e1003141001503681d14140c90403400a0f070000001425440d10594a030104c1405a451002111001c010811288080306010741d200070301d40b000d40d0003c0c1c030100090004010109000d900e80c400c0100142c540c0182805500200b818a00d0760000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 258531987 1250 258530737 258530759
    0x8072606060309010b0a09020702010311030114100e04020c01061d09030d180f1a010f050d0b1803040f1d0f0705070303090c060504030b0903070b04140c09040c1d01 72
    0x11040d025501591030350f0340c958610740545610b000154020341e03e8100424101415001448041c1c000e0303c1c1800701d0b0088104000c014442486200f1a40c40c00d10b00d40c11113071801404550181825190116074120100c002500302d0703020500c0f00c01140e54501042204000d0b101d54902401c0100c0c4400070149800d00c0d9280e0bc904c290f03070741c3c0e210140d070305c1c4002d200c948090500c1d96900b80d003191014509002c640380003002065980004c17080807400c4c1b4000034001000407443c80903144042c1060070480070740d82d650100c1020242248400502c5524094041001080038000402c01803c110300c0103490320301c0e124942d20b06002540021032020b010030506540c0c03a0350f0581c0069082c90700c10340d24451420218010500c000c07000349480642c960010384250700c0b001610070380340150052005501ca200e0425528412120300400305401c44d0300250200f03d03108045424100c54000380c6911010325400a00440d004407400c9a403401029401d00a20035519600c000580e114452000554105024151 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 258533237 1250 258531987 258531991
    0x110604051c260703020c0a032f040e070312030507020d21050109020309010c0302040e011505040b03071d030609070e1914061807050906030c0f0307080726 68
    0x21034440700103103140401501c400c05241c8850541c29a00c00c1425003100d942030340d80145001c1e00144100802801c0c145041c4020f00101c0344d00001145000c0417640c00c005200e80c4100c100345806e58168500c41b0b0644441c021812a156600c000d804c000d42140703030003c90f80e103480c0c00c0141010316000c03c00210344e40005407903000b20030710b0400e507076840d108000380d000760b01d04001c042e1f500c6418000005102d9000c0c6d000395008261001c000e101d0f004840504404900482c8210000c2060038801006070101120a240c0d6502140c03801c00c2c901601d81c522100d40741d1043d100e0a000031040072250305602201c1d81c03051809602100034185508213008425580c4009004486000c640782c0c02141807290f010070303441220050380b401400500d006440405007003a0407a529800f40c0030040070900351101c5c1001031807107040700c0d0312000d00b044111360a110850708010400e1312201c0007000b044088900c02005544140c1d042e0f92524058a00803400a1090205a62141c4600c4144101800745592000c1950b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 258534487 1250 258533237 258533269
    0x3200417061012060e0109050a03110a020a1703041e1e05090f0a0216111c120804080708040b0a0e040507122a02030717160f0611030a0911060405 64
    0x103c1240c0381000700c01803030503000840a5610b05949682085030101d1251003190082d19020702603851682c495441e41c100000082d1f000791404014400b407002804040c0405224070112820305455105940520880f108001e10001d09007400700252805810f2907403958680209403a0000e18110100d11106805840c040d110100e0800040100d0101e6060f12010700c4a40c10201400b00380b41402400c00180002c10390041460080b100d04c0044000394855000b5400340340b0100c030740070860003101d400d0400b030030440e80640c0800c08400820b0450000d0009491042802a50b860440070045c10b0342400404c158012801c01040221068102f0b100d0052030340c88890204205416890842001940940d50300840b44c0810010145030307030001c094100e0a00c2190854281e42c03208026803800d002c0c01d035845480c2c069140086002500c049000380000d44180c10214601d010340108070087e40084038011201d5a4402e40c2009200c007448466040180c1034441515045c18540802c95600f500c560308 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 258535737 1250 258534487 258534509
    0x201050307170c040503070b03040b04020d1406010b0d0b010f0504050402070f0c0902031b0c070501200d1211030103020d1b031e0b091c030c032004170610 68
    0x74421406060051000c0e044003103408003500c0c2035a8031200a0b00300e070064901901c04c848000c82d080c407448080300e000719000340d080c0c003407551654204102400c441104545105440c000240070712000c01c10075000e8548040d09503110706414015030f0031526803070b8006040001c0e075455403c0443d000780c01c0307601741c400580700540d42d4140c47c00c020000d1101c0c18401001400080000942112681e0185005000904a10210300312580b41c4804a000d00c1c9a01c0145400103002041a5800740503031210001072030382450520303011018003e0400d10002c2c03150000c07031411103510f840b0320217911841c1d041b0180c0503501030443d4195004124012480c2b030700103005548008054034640c2e107030050300009550026640a198a00794001c64450041800856000202001050030745401250714045a40da00450284010312a503044010701080340c2c40000f41aaa8659481e100460300301c420f8040d0381075403103555503501d0559084840030380d0f8030704421f0f950028414401003100c0d9442e000c080307801340803103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 258536987 1250 258535737 258535741
    0x702101a0d1707050f03030604140420040b04021314010504210f050a031d0409030c02010e190303020a0b091c0e011e1707020c03150901060806010b0c160b0702010503 73
    0x682210740703d410030282480c0300c0d03250224508a07000006511030b0401391014000351100c00c846c4845214281c1c1c00510111250403400000c1c0d407010000ba4803504018004180d5000384c20201d03049900099003981c07aa00400401d000c0441c1c4d5960309001c003a23003032030004d03d4140b62100c0c005106c580b40c44c182d80a46040380e000c4c030038482c0841e11015015008400e9988110803032801070042558410170031542d41003071401c40c01900d814031a101e003c50705921018225034140c0e0044410040750982d090740a20241c02c5c09041c420a0481600034601c25001419032000509000341d40e6400107200704956070111885502030103031240c0c88824115241807821481002c6401601c5a500e84481c040c50210300e2540d0094140c0d02c251015400245985e0402154403072010403620741000c0b010960f00359005641c0c0b600c0030801c402a05520003850000040d4082d1100541070a107030b0280d01c078810fa44008644800c042c3c80501214a9004000c8182c880041c1342c101c3c2807000f40109a0040d040c0000800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 258538237 1250 258536987 258537023
    0x105070614040221071707030b01240e0109150c05060a020c19020f010f05040315020910031521080304030e0a06020d08040201080406180318050a0302180912030702101a0d 75
    0x1c02652707118440b159150b07180e03042800c1c000c0444a12502c15441c1410300031045002e00000a04000c060f986c1000040c1000824030301c070407000da565010411044404004030f40248880c6019a500140140c1c0d40d5060058240c075190312525024480007040300c500c00141d84c0c40101505100003805c2c841c10705600207000340e90030301640d4005040200b0f090f154207030340d6101d0f600610f201e050031030310103000c046032980880c201c2d411506148210213418074103124180780c507a160080000010409404606183c0e03441223030ba0070544044000c10844d0818410501d085198040a4001751008203400118507000074a070040240019041c0308040c0c021409002150701b0110007001000070104031000c291400800d003944880a40865a040741000315203890680400c0c42100c0d0000d1002c09640c1504143d010b40000141c4403070a2486104c0e100e00d66001d001020390701c03491441e0040d281e1200c3c026000340944429042c128500000990507100650b210030907044101d4100c0c102c0c0900d190000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 258539487 1250 258538237 258538243
    0x11030a180807030c0215031e06030c040609020406030501170a030f030b0301050f09012316110607030207020307050d120c170c0709060909021e01050706140402210717 73
    0x4000d4801c070390001d100320030b1607003000c00c1400061007030b0707150b526141902e09030210902059800306d09100c4a4032242d0b42418102c0d0140e41c20803c01015180030141d540001000c540c0c007540106c800030703000f1804000583e0548140783c01031204180411014042d000c02d6511887c2c2c43c00024180499003944a0000d80f1942c0050781408001d0001c000c40c0c18070500341050150100da09a105600304901e1f0042000001030f90b81c810751220b0031a00441d00c2c0d125140203101910790441d0200311084010f00d802480411416014803825100160b07100c0090040c98200b0089821141c0103d9516a202c0c001640095103800c4044144c68811119041880c01c0e006000d40000302c5d0664020104600041c950080380c0d0804840c601c900070465039507560400d405540e03910a002c2d5001031076114942602030252078a15500d64142b409915122940ea1900d04551403501c81ea00824040c0003080218108038080740301c00803031107440ea00402c40340c00d00641e59243c5030041c08040b51040701e03003441d044d10030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 258540737 1250 258539487 258539531
    0x7080a08031e070e03060702030c0d21020f1b0d050904051510030b030f1209010503151306061701030b31030e101103040303030b011e020601080c0411030a 68
    0x12a0030720760b460400c9040200390b0355081c24260b12078000e8202140c01180000101c2d02e20100440140c506e10f60b400c803064518245409080303c0c507404101c0c0742901203200c0c0c07009044138bc0d510382c201620b608841c1012030140038581680d0300968004802904016002030079964800300440d404078055490b6050b503944003801851413a04150703220080005660182c03c5420050f4080c1d00300e50381003113401903459407003850b1400316400360400c105c140c4465105400a5a1040c5524882c50b1741d100070b000860390f025810400c1c81611a0b441006100381903008040716052103082c0c14210b01541140c031584c03c0000043d140800450a00b282c1c0c8030004a214074030200803c8181d1541c2070901c190401410041264518500c035a6503000d03217460807030043e00f4890f807070720012008609042c2965002e500509001303c0c3c0d64140107103410590996503091504940d010f10f158090441540740070840c0c3e2410000c01c42d045d1149044c18200d02482c1c9003001669809840e000d008908507187c01040c035022050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 258541987 1250 258540737 258540781
    0x8090405010e060f0a0b0306040b010c0c0f030c140307090b0307090f0221040b06010804061b1206050109050d0b0403091d010303080708130615151205010807080a0803 73
    0xd05000003400414221998030861003070703c1c002602c60043c0204441290b44d030160800719001840815168203296212440070305040c14040002d00041d194030320182a1030340484c00c20380c0c07144c4080c0200054100440b00403c0104885030b10180742d80300190b1600243d00440c2c200907a1405500450744e02000103000030107510340100440d0302101d8241c0086d52010300e04001504241801528081e4803c813641d202d40c0e04007201e603c240e1259001140e49142c00307081641e503144c0350380400504495006452410100f141c440c2104c0c09080948034003551040c0d030009041c80710300c180401903600c850000364a22075006102d5112a0b0f541e160580b8040301c503030800d10349804643e60b40c16503031031804c0001d07061324000d4550307503600ea64035042100c1e60441110141e08508240086000040e850381060340000201e400000d2150381300c03c0091031007207184a28000041d0500e41c100302da03030403520030280074000c0c5401404a260070455080e942c1c0800010040080d1000400900350106848910301c640d51 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 258543237 1250 258541987 258541991
    0x302010f0b0915061b0606101814030309090109140105040b1305100801060602030c101104051011060c0d051302010c080a1202070b07021e1914030304051c030e0c0d080904 75
    0x10100803250392400111f802a000c3c0205581101209004044079030f00d8881c076200e03010750941844082002a451414015014401488030343c28980c0c507503180c07601822601d90000b86602105c02ca080b1500c00690204e030003985013aa12000c1600c4246034491085218071001c900c507165982402022111588512919441c1c83c402149203580030000f4030200b9048001c5401345445d058101040324400f05012918040400c0304201c0c1c1d003000302c00b012240c04241001200b40d006030440e1802d00108441130984000b001446030308114481c0310340c0d5004455805440d03000480303a40083c007140c150300780143c0882c00100300714a02c607228514442c02d60795450429901c07400c0c142b4281c218002d040c0c4130880507000e82c00c401d0144080d607106031499204110700400c446090603841d80103030b155205007601d41e00350315004402c00b660104000d500542c41000100350f10030308924480000d103030381c120000c109410000120802d801c0003035848803000081b1003c000301c1d101c0745011142440340101498000d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 258544487 1250 258543237 258543277
    0x91e0c050912070504150515090d1410060f090c020c1e120f0303180a020f09100b16231b010c050a05010b01080705120f10030b01120302010f0b091506 66
    0x43e45241b411812998180e17620004c07500d1000080505018802000f40c01217020540c0d8008a20200d0b00320980c0d11195007038800d140741544001e0187c1d50903030814103804020b0141080800b0042c4180a0b0500301d502c060088a9054400100d0301642a20141c41d000d280c108581c8960780c40354800440b144144017210200b0003202a156104e030812200c61051280d4804c2c120491440400e807209010340c024000b10010840c201042001d40000d84206204000c07058017180f8071980000405088200d000c800c8c003c08014609111010840111854904440c040144150b00001040c3c16001c0905141400400040004850000a01402a04500c1401c0168050241c10f602c006160036080e40d035850190380d41102906c040c07203012811601900000c0002c0c82200d00c03075089170b41000701443d400c6d00f40c5542e51100395911100303030000482d220711040c0f500f040640900c61000f40103441c03042440601c15580010b0b0f13210000600840085881c200b20508aa40c1c40080b2201e100030071000d001c82c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 258545737 1250 258544487 258544511
    0x909070819110405040b060415090e0a110406060c30030f051b0d0e0c0d050303190612020f120319080912220b04091e0c050912070504 59
    0x4807200a05407081c10602038400550f08090081c1c1e841980c2009844217985c4461090000621510114410030079a00d140031604c0320641c05644080e4003481c0041020440302d050242c2217071920141e1500c502d18154080120507000500140701d2a0000615100081959000c000141000343e0402c0200d1902c8034081015415038400c1c01311120549007000555100459400342c6004994000e44800003401404038549550300800c1e8903004a01c00c0e13401c1c84503c44042401c0c0f05080038101c4544d000801044048190030701e40c0489078459110034048a8030700400e0100350b2070344450181c0581d14800d81d820540e11428030080007040324404a031341d2060503119692240100f000004000390b0110046a0484400103a02c84254141c1f000646080300c81001c43e626140f04445178801c8144181c00020f03042c00050140001302114039010440c00200b00013541040c0ca960741d03612100345041b00da02c010b6903100c0281d95040c24141d0301c0341c0c4061003103d02c80707190440c140e010a42c042d0400ca01c0040c0c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 258546987 1250 258545737 258545773
    0xe0d2106030b070c0b0604090b2212020d0206090601060c020d0203150411030111030405060604090f0f0c090e03190819050a0b040b030708060c070305191e030606080609090708 77
    0x941c002c02c1c43c12015206c0c9000c02040c1e41410102406041280c0301240310f428001c980511a20440000c540031035203135548441d403106515894402580003810318002164041c06000c0e400520b400152000f9814100003908004d090800613006442281c804011501c1c100050303103004030031015000c11440e0901c0c0042441055000481c000d50811a00c1400c01c1440c5080e01c5c042e0f0b6000c0080d00b01d50f91031006200c0101040542a40c000c061801c9800200700c070040c03100b9515028021810740c040c24030510405607040b45d0406100d0341d0041190b081610440451312241c00003915085c41952941c0f518210420343d80002829824035000621458401c640e00c8241c80c0c040070f4a01784400c200c41400c00d6140d81d024458030159400a0000449401020008002d80b40c0700307003402800d0010000c81c50f4881d01e1040d4400c0c0204245400d00e2840f112031030ba01a0030a12903150038000d060071f1500042510700041d05840c05407615801081d420355044c043d0802401c1d0b8507045509440044400240c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 258548237 1250 258546987 258547007
    0xd120b060c1e240903071707031b08120603010e150a1401081203060112051608010510050409020c0304270e060c03040803040c031202030a030e0d2106030b07 69
    0x441d103080c85a1000a400049a08880d00c80b16020741a100d52400f4205060118010802c3c041400108503201c001000e22810060745d00c104100640c03202003a02c0c024100c11226140c000307043d0340c03260210001a052500321103600c83c10b500315000580355400400d0140505a9100c807480c010b0304444a01425034401152045003207001c14048001d00d82c1c0008036122080c01141c00f035411151940224180910085422143c10716140b9000c1c40c000c502c242c12900240c0d84100c04018501c0b00d0301210350b00ca25420f016000c11540a0b012691010025065200d14440d6480a58021580c41c640030002c3c4242e90007009a0300c1c10070108000081c0039800f030070a40340803054061806100c0030010a0004800348540e10f1820b0f41d83c9192941e850300c200541001700211042100c94002100048036100b02d55100c00300c9070021502c85000c0400901520002640c41e071107607200d0700d07c801585074060980040100d0705d0f18603801c0201411000c0c00a0f00c016040600103502d01020b10182e170b540403030109 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 258549487 1250 258548237 258548263
    0xf1602100c0507050402210903160c05040c02060702030a0f0c0f050601050109080102190507060b150a0f0c05060f092103010303030b0118031b05030604080d051006020d120b060c 78
    0x580c07143d80703450800c003c9000300303035814008101002140c0f0b201307d2481e01075900042c0e00000c43e4103100040400403540704560100300e030505560390341040b86007414002c05401d000349001408582c500940300a5507402455065020058503180480b21680909540312929403c074041b458210704074186641d680000388105400030b8030740707080060b4030901031098491003a0f89500c068101002000d00301d405410282058546942e610130226a035507071944014040409040050b84a051881c4044d00c450b80c0f441040050146103840301c8002580414800e5100b100000b900c116515000110351400803035508210040c1400d080c03901801700b040f03000e54101e91296131b050000244100c01143e40100400000304400381c007560070710000c1c10211102c40f00318860650008110b6445000914016050710155050540005c41c405540c24500071180d101d0004c0084105152070700b00002d580b20140003845d030410a1051040482d030849801805039010001c3c101e584950240a209480d020600415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 258550737 1250 258549487 258549493
    0xa11071a0915070923041a0f01170402150c070905101502030901030506040e070306061a1c020306010203070c060509030d0822060b09010324020f0f1602100c05 70
    0x82c04180d022106600c00d80c46980c4807055503143c00c94891070012030350304110313486402802e07039202c5803074610404601000785000c585140c40ba44003801100008a0555030402100800540340d4030f400030f5541d508954140c43c1c401c295502006004120700401c0a4880c1e680100705001641c4c1e51290440c5c1d0040b148103c11400309643e40804914400c110715403c009a00180300d5070340c00350b001e54019944844054804078100481c40e00380b60401079180c004488140d6105000e1000044a40004185400d030300e965514001c2c001002c5500c800c10a5240d1400e030780c000000407045c1c1d1003402502d401944c0641c0441e0301c5502c4503000303046038024813074040c06881440b443e00c40e400d100d4002103001e07244240038600400f402c11542c11081000c0710040d904c441d250070f19030704140ca039001d045009600a244419600c0c0e08100b007401c48901d0300d80c0c46800240180855518901c1c02400c459425043c0081740b0b2b6030b000206506001c5c08080c807070103980840c000c0c810f20380858100c0b0b10b80045038030540079 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 258551987 1250 258550737 258550753
    0x20409050f010b0108060108070c0201090512011a0618061606050703090605060f0a061419020d02150108060c07051e030a0207051c06020304050f01020a03140c120a11071a09 76
    0x1120000d001b1100c042c00621075070045860030380100035401e440d50044c90400070094035030b404103503c1c0030304031f10124650303645a41c0f002040b05803441c1d401250700e044440070302c0c11445c0b821014100b494041540d00c603da0010f400d40c0a40350f00c01c5a594000e80c040001c0c03003a4900058040c004080098023911554144800110140b400e010701c0c410705c08004180010b0f5505101c401c0b1051400075051000000040021440082410a206a2403a425401003417001c0741c600c4000d01304a41080407030022200e410060090180c080342940e885002d40aa19071560f085040240c50420782c4221191811040b50318042403000200c01800e0804094003211a19545d60040c44111950042240401c0e26400307030601c00503441d50000c0d9045802803007201c407138002c00b040c0c0d81e0032030744552910800300342c0c0c5000001201020070b121541c062020700c5400d0400380d00e00854024050003c2002c044039aa1368001950484400c0a41c1c0d02103800c4003003e80c1d1000c00141440c89e880c010740c0d1401c011700c99565 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 258553237 1250 258551987 258551989
    0x30304120809070902210a05040c0503150a0f09060c3f0203070c1e15020f031302030120040f05100c03031808121e16050c0307020409050f010b 63
    0x21500d402001e0000c010701645107000b030013900a4020f240d212241800d040802c5241328030085101c2d014a164030000501414a4070300790444405660090703002c9d40180c1c1984042d450f41c1c030902944a03a00100100e081101c114120300248070f00d0400400c0c5519001030310320095405081f0503003080d4010241c2d0f90092503240100d503402c0b141441c4070300760303644d1005400b04d400340c0d50059500203900f401c2c040c505041a03580c0e0420000c0001050341d41c245030040700c01c140512038901e916002c071148411440c0041050040341a0710006000b03010240d14010178404644095104914010044007401c12002000c82148038035407140c440c0080282c0e24141c01700c3d062038501000000c180f541c1d1103030546203a20780e4040c0d018107a04560754100100d20310102c00442c3c40c0000415403904039030600261403030309000b60f24000225900c05220a60340500304202d50380540082e01c2130304032030705103580c071807840452041c694819414025086803c00d001c01d020040009240c0180b01c0c101c20003441600b142c0300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 258554487 1250 258553237 258553247
    0x1d0a091407020607031a010302090f100c1205090901060810030b15010e040b1011010f14090d0207030c05130f15081b0901090b0301020d090507090c0e060307111e03030412 75
    0x400e03038086c00c5000f2a07801400750701a03401480200c00180040326840d0025000401c03808480c2d0740803011401d81c4001000304452460245801195414418100307502140810800001400f4520a00c20301d4800308020400031090389009580c08031400c4094a4440c1a030340c0e14a0811031114042480d000703146400f40341601811502002c0030f442503001c06013010b422600000f88541081265507628038440d001c1d6900e0095646041ca504224101070510511691038165103410035801c540048006000048020004108444080301c00142c065505079010300140384081c0c192440602c0e048180c03821040754040c03202283c900106640c3c3c0554100140c44294072102c058a078004080c000502110880750f101025031040640014203005000510b081180d0190a0945240c0d00c502c00410541070a8007852a460b2614500703050b501d006007001c5544c2d0300029200d4018428000110140420708200c01c1e44448074001319900140d001e00c100c079807207501c1903406491400d60000c00d003100794043c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 258555737 1250 258554487 258554501
    0x40c09180f29091b18040615050f01080109050a020c0613030f0f02070513060b0a03050a0b0319020f0f180f0c040302180601051309021201080c011d0a09140702060703 73
    0x35002800d01c482d00c401560341358142c140c4055074041c1c0c10010b01205800d10501c8a48507900c03c14002030040440c44100f401d030103036544042d1068011800095940e44e000007a541100c0d0b03c2800482c01d500ca01031520b01a0003100d07401c04c01c61150f02c3c2085020322200140440c4c081c060b80341c0704480c4039010b83c11280d1900300408440580d0105000300b03c942400400c4582c09089a03600240071034942c02440c4403984200a0b100000b07403110144040174800e886140440d0034210300070908455004600005203409000c041c1c41000b2541d43c0c500d464072418044110040018060701501610101c540c403003130000d07a400a880d003203100c0060411418030003114180c0303800a11141d80d503098140c8461903401c00412403410000b05200200d9010703641c0e059200640406400540c984185141000600405900541e0658007044141c11966080000c00890888048a90328502114004541400b000f98440000b681c50b004101405030191000c1c24091030203030382540c0c3e00f0344909030210240c07000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 258556987 1250 258555737 258555751
    0x27100512040b040609060c050702040c02190b041106190f080106090e0709080d090504050a0c050f18091005100206040201021c0207080709050717040c09180f29 70
    0xc50300070a020816034030700d0b01d074418400c05010a000c001c1341c0d030398025510f51040000104101041000840c17910f8016100c03101602c7c40144590080410142c10444400b02c000d03082c03034040320218003031101440361601c1c070f43d20150603075a4420304908803149422140c034040e0001582d140281c2c50705441241564122002d0703665003d0144d06107103a00c2c0380400054440e509000c000c10000846203010301c55001e001c6040c0e16281606403414062005403100205080d0070ac501c0e01c1014a942034108080d280d002d01c000f0001500c1e560484000b180c1c080c404048036607c00c0400040003044c020710281e200603a0b0064507001801910350f6010b81e512801070354000c0c0960814003081c5100c0181003102c080030045441103c1a45a0b00da058500f0654103800c948005611203081107006604103075900b110081d10302c1014036a00d400d4507010314162030ba020300d201e9180c6030f1590052480b10000c1d0044c0241c1c01c0b51030304080180a02d4001007c80350411600344400084001521218805003d00d1240f00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 258558237 1250 258556987 258557017
    0x3070b010e0417031314030c0106090213120206070506040605180d0807030b0f060313050c0d0314090d081b06060f060301090e150a050105090a020c0307020411271005 73
    0x10461010803602e1300002c01c00041c402804580342e02050012480180381e25070f4402450b622484400080e0942e04070b0340000c030415004101c1c0c200ca103e03010080700c045840300d0394010908109071000880511462401400314410001408140900b551001c0d015690741895114004800b01d1100d07118800e0721642c4000c5070261000854a6010350020100e05030014028034219102c0d02c0010050741058070380c0c1485260080d445c40c10064204484003920000300c07056801d102d40c03550000c16400c4040ba1001c590340300420701c0111611008000074406070300050030f40e00c407415140d00048000341425030002c0c03071042c8000703d211400c0c1314202001d003800c0680041c3c40c40c1e0800303031500040c0118a607100028440c400b030250140c281c2102c41d81c00303140140c1d0042444e52409081045528015042d420ba80d44100074200b8010740000c00c50b00c0c501e41c107890204100704405170b40441805160000b0702c140c41524121005074284c4c5031400807a00c002c0f5107185494100c0202200d4a02030943d56400ba10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 258559487 1250 258558237 258558263
    0x40201020d0c0212010e0a0c0f0e16090f141302160b090a1b0317030717090f03130518010b07030c06020c100504140d0906030b010e0303070503070b010e04 68
    0xd2040c0c02c2d02c40824005000b00c004150003000990840310200000300603074009070940030410000c2c0c0d1407100101320302c070034540b036a41c10074003401c07061503014000e82c902158070b440f4151060300800c0c88000030406100c981c1022959905556400310030a0147d82c0304404054013018005014400d540e010302c2c203d01f850011049076070348c01038003070000340001e1424420b08200340000b404d0340350b221014070400d400e03a000162661510803070183c600100007222020501c204400b0303d51015010f0f038a40c8a0201d5042d244c0c842500300d5080941c107960a504a01000880e01c000c0c2590b660007100300c400c01e4070440d2441036074817602812850700b0300400c1e035a100c0030811300f408240306510703004403107000341001807500c880140600d141070300309041d4003d04c540703a804200600c880c8548140070344111001500903e01c2ca010010308000c0203008031018981d80341d14580450748180d91040c036050340902181c0d6143c00c04c1c00c0c00c03950394015050444a844a400000c10340641020809004d90b600c034403411900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 258560737 1250 258559487 258559513
    0x1e0906050d02160204060620070b09010507020d0b01090e0709060803040e19050f1902070210180515040f0609030f020d14150106030b030106050306040f0303110a0f021504020102 78
    0x1a5002940c0c03d1030401001c1003410150b130b1244901c10041c901a00c50f180b03254014412503140c2014284141c00031b030483c1d84100420300c12042202c0c5030650901c0c0c5982d882c401c0d4030015004111182c4050f203815500000414456616808a2a03102003c401c407004142d840301220159003083c050179041e40c10601040140c90340b264040c0350080601c1c42104081d94080c240101100c0b421a16a08d20a485000344510106900300329240701e00111815458504c0707540200304001581d000200c1049540740d10400c03105a80c408490140000900d41030307400c44250883c3e24645c0080c0111a4400c5c903400000a80c070b40503880b400d044aa006e01c101a80c00080d80070052a040c44030810b5802100c00d00440382e089070103120a60300005615039030b00c0517504009004080b9042d05104034002e0303140c0b02007400345a80000721503602942c40a0300107100b46051070201c0141042d071a001060340008580011407035006100d2865501140d0300301c514416030f0241142c4069000e41c0c01a0158001003021285 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 258561987 1250 258560737 258560741
    0x50603040501180f1e020616020a0519080d180905090a020d0303020a02010c0302130515121018090b0106121b05130f0312200601061e0906050d 63
    0x30060280e00002400c14804007080207140c0c1089003101c201a03054500000c2000106512410b0451241e003c02201060b80c0418600c0c4191030310341d904400c034455048215a1000060409840d0207401400301c100d80c0b5581c03103882d03000b6000b040f001c1c1c050440320305103040c42608002c00b48050200c0c0160210325040c0ea0800400d0082c24620007401a82500005a1565107400e01041d2082d03600613a141020707100242107500c01c082c078000705801004018000000c2c2c100368420360f20211443c514818000038030b215580300300c02400480c94031071070420401c2014031145004030b541d4441174404492007507041d0b4003102c50600000788281c560800502050348250607041c4104c818040c00100b4031144000318860b030811544070030000314000b5002079151650386d1020001e02515031143d20407800d540d81e28511603102580300007000205403d00d00b14030000744100c40d01a500406030b880558544d05c00604421071000e259038417103448000707100071511179076015086a409513100c1e41003085074500200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 258563237 1250 258561987 258561991
    0xf0e1f060506072f060f1810120b0402120a05010302010f050313060b060903010f0204140f0d060b0612010303090e0c090a0303050d020706020d1d03030702070308091206090607031a0a050603 83
    0x401103e070341c09a80c04c03c0d10b03150700030808280c0900341345071145080f458521440c0c80d880c40450052240e20a401c40c00c54010700d042d14101c000910100f041591407001c10028055103d580f1710000e484020300c00d001c0030380d50003141a04c1c000c0c0d0b0744801c10100540e050f500e0740720030faa0000306000943c54000c00321712298842d074519840181494030700100d0a002034295134031065140040d60380090100440300303c41040c1000c180c000e994104c1e61814010001e0181c007041900a0310441c0c6032240b02c965a44c40100316880303560030b16800c034810750712420010703c0704225000d90081041d260021524860219040e0346000e58000d0441180600399a000c8584e908403508001c1c445400744401000985180050101e0901112002036a44030510850070001e00c4030041c0d84142c2c004100f40700c003503030740407490100351791300a4000c2e65100d4000c1c1c04112041800340e001403290045005008030380401007401070081e5032a03a0244042121131100803110040d1240742c66120020400410030b604101c00615 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 258564487 1250 258563237 258563303
    0x10e010302090c120405150112020604090c0306051e03100506030607120f0c110705180a0b06040308070b180c01051c09060e060103051218040f0e1f06050607 69
    0x1414000380d40b156804c100c5081d02c0072203007500803681a40f00c038a2015002c07401000b030010100b0b0401200d4000c1040e40c411030003841d403115241c50084800c0c50007904540000c003030242c003200001c1030344084009000340c1e0700085442802002005204100380e4080c007400b0300380003400741c443e5032550082a61244800030011080036101c2e01541043d000d544078418204005844a2503074802ca502200d0400300103400c2207114480500e10451542c590041c0980d000e41c0c0d05500240038203000340002d029000b26407008001c0c0070000b03060001c100c1c070085a00d01070020303210282c1000e0204440c01c1d443e05280c0d5000f900140d001c1c4041c0c040d49020b80f155800f81d4040942c009400030450701c0350360907202d98295180c10707603200800410401ca0104005810050504615410107034161120603040c013034500414400e0340c940c194184040c441d0391169040c43e0444086918514a03840e0940398400216503c070512460198000b0703c0d805e01c0404c41d0f02103a444400c0000c0e41c0c01000ca07020392500311200c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 258565737 1250 258564487 258564511
    0x70b040e100512010207020a120c0e09120f04170703021e010c021201090215071e2f0f010e03030301060302071703010602010902040501060c03020c04050901140a0605090f010e01030209 81
    0x82548401ca20051183e9691001607519429030060100402150f800740583e184549121300101d810b46801109481d404d01c3c1c914030540314080c2c85807401e40b80b9110710303140d44000112214500c01810040007100c0402c41d001583c00c0c040b00754280c135035405100103904062100d40c0d9803c0c07500400400510340350b050501e05d8080301c194021034140f03082010401c4180c0e544008070f106518003607540351091034a0100c105e280041e01c2d035802032448075402d0b92a0003003078120789900401c50b002112510a010f610704040d00744200c180c41c809400c1c08180c00f43e008420109010307409512905038a09140000380c001c51869281003000c0b402544a802c05644d1102c0d07035000076030359201c410000c0d4003c0807607500224055529004105c1100d81c103a120605000d4180f0758440000c0d0045200d00c0c1c9403004032000207003665800c25046c01350260752a0003203403400038010016410301e650b21980c181e03101540c001c64250784d60701600040c0c20083c010643c000d28800e004200602d4813011a55100c04c8240c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 258566987 1250 258565737 258565739
    0xf070804080c10090803100f030c0303031a03100603030e040621060e030304030302030601080609040f030e01092606090c060d09020a051e1002012c07120b09060108070b040e10 77
    0x83d008071800c07a08120b40000c800401d000050b1009107840c0045c0840140704034403580356940720030800081b88001814542c5a42c0c0030410840e9103c05e0916825015040c4d03900e0007017040020004100e10b010850200e00c0011121144c1d040600c034400940b0000c07411200110300300d80503036814001003841201c1454540b0746148060106001840c01107200e0785000d07840b810241c0000d00300c1c0c41c00a2900d030040c0000010070010a0aa00e04441d0180e05802e04001c0040f04200480d1b003100c3d02c0d00519050001d82c01e2210312040004003400020034840c09866098403401c018a407100440200107600c50070a1010b42c0f21901c0c1a440510500c0c40102030701c884550300c2c408200400941109c001010b040e4a600210318285009813122120b0b81e071000304500e0301094500e60110250307074480700818039000c130700000c107000800440000e060100705a8000442038507200c09941002c0700d0010041c028500001403440c000969202601ca04401039402d10b0b0806440d40c0c44000c0080c02c01da81104071841c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 258568237 1250 258566987 258567013
    0xd020d030e071d0f0a090209010b160c08071e03020109030213020415050301150e1e0d0515041e080304060c03021e0a02010e0c0f04020c07080111030f0f070804080c 72
    0x3104a110f20300c0100000c10b1900c40c031402c0c0040c40013000751031070508100300c2100582e500e82119040d5a03441e000603031645144459200120b0b01008002c004015103007002c28040d600154590031506401c1004860300c084c004402240c65641c4002404244220000e00040c50f103005807001c0c00e00040340041c1841d03a50407500305d020310003400203408114000700502084440f04007915506165003407804c80586520045400d560004041608000440b01c0f444a15030b64148140501604581141c1d0203000c0c08a0b40700300300c1c1d02501c08943c6403100c1000c8009880c24000030034111504407502a0441e81c5a40fa490098207400400348205942001144c8840d09003401c07004403c03403140e21150300c6c2c11005c00d002e0b08503820882c80420540c801a4a0091540c5140c001ca0314601c040d507002d81c4032241c1d41510751a24145402211482d400c240c50042c43d07a1100340910300c81d8007044811041ca40b03c1d04914580c1300c0d016203248002900e10400600411041c0e001007089a0300d100454401c0e9419030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 258569487 1250 258568237 258568259
    0xd1b1202090a11131e08160e18100c110a0302070e04080909090c030601140607110303040b16060f061d060a0f03061a0604060912110909010e010e0d020d030e07 70
    0x14019000181d170101c000040c98007401114800341094600a003001c8203400c2200b581c0c01c001c0c2c1710b0141c0401c50f1200040400505164100c40804c5980c1150344411200e60420068460415428001424070007a0148072800003038441d1031039018dc000d04140b508240035014050300050050368440001c0048410720f03206c00039828484c03461140034042d0030904004050400300d041e4031549004003000ca074040b09036544000c407940c1c0e644c0b021041440700500c1c00800d0940c055a030184820105c0030848401d0815503003005405103202e80310400c21086103081140444815005003a900c40d003512080a07107180f080c500c160484c80040949000b20754800d68031843c18a1500121503503500c80da10f65071120071596800312603050484100f030401e403d008000300940745c24860300000500d12185a02442511161800509806000080949090880d050180c204058402c140e903181c01809100c1c0d00c000324000d020104170394094208420030400c200c006d0701940b4141c810501501400180c81c0100c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 258570737 1250 258569487 258569489
    0x4050a0803090102010e030315010507061d0607030b040212010306090213050a140109050601080f0c0904090c05030d14090f0303041503090308010609050d03080702010b0d1b1202090a1113 82
    0x62005641d1425001d000a00f5560b031b15403502d03003590007402030001707c01c2c1000c00c0240960080c600140c544032241402c00c090301c40003000e1030078504021b111940145c03001c909544070341d08030788040c04403101303071010700040b4458140c28103c0c540c0038800500c00514140c110790110f0780010041118510220003060890303609440425401d40e5564200d50100d90002c0c0c400c0c0140302e1000200310794030b441e5002800021008100c4041c0b02d403450700182600c02c02e141500c443d4003001d0310802c9000c0d8103207040881003400b80a594071901c5024054540180303e01601400742410300c0909040c500988280300c92666070020860b49400700b80008200085100386615403804141d07004030742c2e8281c0c3c2c10041d14072001030b000842000207031601401700d40c4940100149180e4186001613256580210032801002443d8100c0da00038400d00b901d4040c001c50b59a24600418001b0030b420031a80d86108516164802c1c480c000e400030040700000f04201001d0f44001108410113594615224618103070003095841 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 258571987 1250 258570737 258570749
    0x40812010608011406040506033103020307200a060f1101020708090405010e01030f08130e0414010612110607050703150519020304110d170a0509190506040e0c04050a 73
    0x5441c010080070304c1c9078014103800e44082c1c0b5014501800d141c0455500e10008001d42101c40e000020001784525842c0d4100200c10030f4405003111242c03525000b5120380c070010054500d4610b0715000800d0f00507e08151281600082041a0340c81c80c00c9029551b40c00080c196806001e601450741011050a00090440902c5070720b00503a41c019040400c01103400c1030f040300d11010404070050001500c600380c0e880c0d055402a03809600c505000304020046143d0743c02c00f403640500901404100802c0e4440c07840b080701c3e0400288411511400140c2d62010038803030182c00c100b2654400700c014285407006011150042055460840e02c90300c0c2e0345460030b5032900c090409a550070400428644c15807038200301c040d0760041980f0f1801c1540b9000c10034420545468400c000100c1d041c1e081100090000308803024601006450311078291020700341c0e4001000341405030701c1048044226460340c0302410142c4600408490a0608000000325451300090080d109014204000b14242ea01c00200b2030041c09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 258573237 1250 258571987 258571997
    0x13080f0c160b03040209010e090705060f0a08061e09180d0207090c1b0b0a0b04050a020d0b0a060c0314070c0b030402030c01081015050d060806040318080709050408120106 75
    0x107070300040c400a80c0d44a0b4088001c0c103005006000041c2d6410203003504543d146487c0d06107035215031160700c2c10649030b5400594010340024024030400c03c0700010b0f100030543c0343c549005517500e4005100b00403480821046590b100c43c070b9008c0c3c0301d180c81303a06140c0003d4024070b40044006480c0c0c0c000c0c0b40c0501c0150700c102584c0b240034200f01081d403130b00422822406510708001d000350841c00c1c2e244484034144009100340350100c000780303840015520180005078024002e10035400c0000d00000258421890741d41d0040c10203c2400c0b0170b0608401c1c10084078403a0344c40c10050038040d1001c45603208140035050700d8071000c009078008220f0f2203001c61f010700100b48034580e490515104140c605081c10b002c1303505200302401000320007070366411f4103412654000300e0fa40c003010040000303e03014810101040c81709490140081050400040c469204511a8444044002c0c000313011b125110781b14410245a41d001a00034071030303400740760082604a44980b4000c0e0600c192034015103c05102600303c100007030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 258574487 1250 258573237 258573253
    0x8060402030f0c0a211a1e0f16090b13060f0c020a051905090c0c06090313060f0512070f0f05091507020d0f03020a02040c030c0813080f0c 61
    0x301c1c042c080500d01c00c1200000382400c591002c081507040d03a0318030071410400800c06259200e44101d8144800c201c5c3d01c00301c41c0080d0454002c41c3d520221050b1589078001e44010400c4448010480310b081c020108142240b0142c1e482203444005640b904003400b08020700701c900020070003e041c0140901201040e80300c6a031905004008242a450210000c200700b20400d100000d070321307240300d034400742c9800380c6601041c2d5040034003500a06400b6448190061441c1c4101300200c04100041d000800a820594815450b1030030740c0b942e00e00444850120030700d03036400104042c074000d160002191b14103041403810140080419028072400b20780100114501104012009c2ea0200340d040380340d03826081083c2002e20399030102d2010200030401c0c0b00d412500184000a650b2907640442c0840d034403180044011955103002903c50032100c100700e0189080074095003005000e409540c0200869980700070030b65840c48140381d0000d103080000e5500100410050702d8880b554002060707105030380c000808a030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 258575737 1250 258574487 258574489
    0xa030b0a1a09060d061b0c06050a11040b090a1211010e030f03180604050a081501050607120507031206090e0f07030503030c070c0b04030303090201121509091a0108060402 75
    0x6940030000e40c50803885807818591495a500c0b080c2c5400480c2960851001261481c00b0310003012058151084407041c900205a515030200420a0403449800280305c0c50301c1c0d40d034424041d6140d405404a928009200038419205030a01030030508800038082c000e216079402c040010900b03810001d807603402e003d000d00407040d6001700441d03030503a0b4190003c100502199038100e0302c9000e45a505501404d2006800019580d50300680d00075000003040c0710b01c0940d907940d6245d50381482d1080d4803c043c1c100e070000a0180350140540e034506070071100c1c0140a0380c8485045aaa600c44c1108405100c40764000c4c4000e120544180701c00b03810060000280ba100000f01507140c010a41003603907540c3d101000620000c2c030040262508003d41003013854640c101484c04000c1c4940507003040360707501404075000041c075605410108229000782c03142d0b0a006522103980058480c3c0f207114000f6000003100411000c0850b07481024120f003d11181c0e039038003900d102c04140403a002c3e4080c50b12540040700b44015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 258576987 1250 258575737 258575741
    0x307170313090b040c020f0d0c030c0b0a0501180e0a06020d0f1104050a091515140f04050901050f011706010c0203010e070501020c0d0f020628020a1e050303150303090a030b0a 77
    0x10266440c001401146050b180c07480d910b14234128107100300318486508004160050030755010302d560025144a0341d02d020300d0420003c01c8248200c402d05200701d0480c00c441d04051190030900c60280010780303c010360390f4884101944c400000000502e644d000c00742c510804911802c50b00d50360048807075582d01d103048100500941d290b000030918a02c1d00c0300090200707608400034002ca6402c00c989600300024130009856041ca03003801d444100303034000343d4004441c03015002041a02d504413502c0c0b010b40d0b00c4805100c044281140c1c2680440d50081c0001c00c0c3d205c1d0760a150341d02000500d08443c803c01e0780d80c04282034800300c8881e8280341d88084c00030b000c80d6806100e43d40c01100b0507151120a00e00607246c2d818801109100a800380100007940e4548041c001201604021985080c1c0d001c10011000255100050f103010b032742210580002800886e90820b1f001d041d103030000015402c603146c9502d520b240090004016034980701c00c000301441c079143c009100c0300441c05442151032502d0840701c0001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 258578237 1250 258576987 258577001
    0xf02040609060f03150204080a06020405010201060b0403050d030e030c0f0604050705091b0d09020a030b060916021f15061d0603040b04030c050c090c070204060902090307170313090b04 81
    0x4100ca0420405101c4140a0f507014001c60ba0400f0300d148900c1d2412480300e00a114a8010b00702d44e000b944803590a01c60f41d0b40080040354002c0e802009629542c04200046000b14080100660040c50490081d94800e80000d1041ea1450096910785070249802c4c0d0f02d172101884400c02c1c15080801040140182400a00c00806e41a9041069894102c2c95800031100d1424640541d0b54080740c403d0b00d000080e4413100d18694040d20112119440c0e0800000083e0110340709171055010314001303850301ca0240f110259090154000300724201c051140c003001900051541500140d69440341800d928002c0503a000401880d20f54008030341c0045034080d100010100d4081c0a00d20401c141710000d4110104594415010300d005403140880749030640c181480000c841d58041200b6003071014600c3d00c00002c10050340300300c070308101160756580c098050f401003005540e0716400c2403608004103d0503008800c03200c1440020b507481c2c44626014405070b44c130190416461655114042c880720300303091180c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 258579487 1250 258578237 258578249
    0x50c060a031a06040f120c0905100302040c030b0f2206240309051b010c06090308070f02010b030a0b061f020703021513050111010b0411030f2d040c080a0f020406 71
    0x545441c0c2840c00200001403036100300d42265080008480034840071f12005070281042c1181441541014109c0b1010300303201380803e0303101d039103402600c03c405070003482401e254920142103000329044086c1042080360342c030604071014004480c0c1c0e08040360400d02c00d9001070000c009048500140514610026600007000441814a4032903e840800c00c000303840d030410550b915900000710b10f03090040702c1002640c80f00821450078002540109a0880c10382842100c0c40d9482d0481f01c001407004a0036076040012003074041d004842000c001c05d0110103010381c0004007a0450801d52200c444810304401c489a04100503003215409004615048502c4240050b68540090031715549a003c0e101c0001103115050503c84450480c184c04003082d0481402444010310030840801101c8100d03010f64411030724a411009188000380344010b0461105060110165407101d03042e02c5805d01200180000d00252503403610010005080442044030300b4109100300400011441c00340305010903a0940e030045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 258580737 1250 258579487 258579499
    0x30b090f0c09091005060406030602070c060e04200304050a0c0f080c010804030f080702011b0909050603010e0703060906060e0c120f07020c010c020607171b28050c060a031a 76
    0x482800da000080306400132807401000100c5450b4807000500030081c1d03a1008181c0360002c038000302480900361100003207800903240d018200c10f001041008580d02d080d2a408160602c3d030740860b520b00140c0c00b840d801482401210f001c42360f50b8640031050034196000c1058480d00c90401d01c1440c0c81401988072440082c2441110350401d40c0c2e0151665214480d0350080103520f200043d80d01c3d10035004848828007400000c041110030300303002409005d00b400ba02e00100c1c00d0402041d0a41014810b03080321182e85000b5000f8281559240c002a043c040b44c1940c0e81c54840901145076903400e13201c54052000d4000540d9034810000b085100f1100c000c14400a0118000c1008015500818071b05404a001d180110501c90144005021030160322806816002280d20500308254028010001c000d040d880700d440c45520f2580a41d5600650b41d5003403000f02d1900184001d079422075020041d003500c0703002038440311a203020102d999504084201c800013a119458480345650100a90000c0142900c80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 258581987 1250 258580737 258580741
    0x11070b0a0e160e0709092309030708090d03140d1e0504260c01180507090603050d1d0909060a0605030601240908030423010c0c030210020106030b090f0c09 68
    0xd0102801d040c443c603901142c891001583c103901c0761420702c015120560080080498400c500c08649031040c46500741c4d0001400400e10410001040d10f40e410b60042c50f503843c2501d010140180031507540d03812002d2107280e840c108025440900074008c01c8044107000240404001d000d81c0030542c4c03c408001d5214603250500010840d20b048100c42c603030914120f00c0058002090b91045440b51445108541d484c0a142c03011003100081e0032070038240608100c640c2e89441e41c400804031003540c440103207554404640c1030760803030160a000343c903138001c2d0701c5100e6403500c40f40100300b03c0c401c1118440e42903040403017081340c000741c18030803000039110660040207250305000010203040c00141441c1503800483c0c080c400294461180303400070b028034030300b07990311659070780419155078078511000b214100340e840b14044954403940084002341c5e00004201d0081c0d1030360f024407a481d881c15401c04219501d810003c0081025100c07440e00407071040004001550304268524104100030b00424454581401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 258583237 1250 258581987 258582013
    0xa09020313110d0602040f0e010501020312010608072105040201080a020c03040b0906090d0b04020a150c030f230c15061305070c02090406020d0606050406050403030c020411070b0a0e 80
    0x442481a840031100302c082c21201c000424008051200900c114000503010804802c0400050111003c004444140740d8840005989038050ba441e40800407070300c8d000410540d84101419130b040720300c40c10119030380300882e451618071840080000750b405454009000031564403c04155001070a41c1c0c00714181801c0721016501d901c96480341d00c40145002c5800409962080210b800c401001403003d201c05207603280c80c00b03442034201c40070b0340b0480c0d8420000451001d40b614820b154080355650200384180b5660a69082c0c2d2404422010094114000401c500d40350794481c0d1040c48030740c0001d03216251034002c0c5240408000040720464201814001c40b6110900c0302e450f4500c07071810221301b80e0b944850894080c010044061752000c00034061006102e11a8002c5c15032028290701401100e4031044196024400c034411303980090000c01040010030700c90304c5c8010f003e0340f00801c0800d02c1041c00c0d40840c0240c200c000140c0f68060000b0500c00308003054413481c0f2028543d54090300c202c6240301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 258584487 1250 258583237 258583261
    0x102011a130b04020328060f0303050c0708070f14150a050f07051e010516140a0212030c0901020f2103090f010c0206011505040f1401050d02180a090203 67
    0xc00c03100e00505858040030119000c0360407a0480410180c011500c0b031800c1180d20040c4115290564010300344210300300b040c2070755402404241d030720301c1c800c0080c3c4a20310ba5080704c0e268458030945181d4040c6010104051a0034440c2c80010101e50884a46084c1464005c0b040b200030561607034818005206200d03014184802a51740e11403403410103a8480e0b202e500c3c58503251052000040c8035004841c0140701e81084800c24881d0541410b0007044541d0f0391620840003182055004030204442030b520243c800c150100420703000045105440b60302d946d103024007071180c20545100c0b0800c00003040c2ca500b1968100315941c05079280800a00300031340300c400081e0821426140441c1241c10000c0002e090034410051403000c641078100800c4485110807000f51900c00a0040080060000f03a42ca0000341c400d9090318180c403c9412500140380c034000c902000c9510b030300440d0b4103002003032005000c004020710281040d02a41c1140724910202001004460600c4e03800141c02c040c4140180051401c40c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 258585737 1250 258584487 258584531
    0x3090c05010c020d0b0405160803091e1903080903061e04170c0604060914030703020c060a09150915080112060e071707170607020303071805040507050c0c010201 71
    0x20700308184102c1060000c240001c00358400940000800d1040c40204040082c0b080b5030741e203402c0d4100b00710f15103c0c0c04180e104c2c0b0030800110b078440d000c03004110258404465042c002c0a00800a1000d00504072181403034841a03402518544004079607075440d03080611465511079050364550090000d604032040d92442d01802c041c00d241040f4196000c499680d0b0100c9205e801114112174103464207160090282031881c2003160016030742c0040c83c4486c0d8000040c0d4100342c1e410f4005c1c042ca14510300921519802c0003849a0410282c42e1001030030b108406c00550003003c49640d032400c0941005c012b01501c2c50040e28001c01c10203000c004110b050002c002c05070400b1b078841804512400041080d5150003210307008059803243ca95034502c000e210000c1c426040710082d1030440c2c5014140c03041103444803000c541c400056041000000e00083c80380091194540b400f5010402258517400800d080b41c00c03c903003420100790002a2200c1842c010002d078904503400348000c0c4207540c010051100403041c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 258586987 1250 258585737 258585739
    0x90c120a0b0a020d0f0506040b090601052b06030317090a1e05070905010602010b0102060901050402010c080f04151205090d02030406050c0109080c0109030801090603020a170316031e03090c05 84
    0x290100360b040301140c040710510303000f006091281120044611700148802d9840a00c22440c05000e40064205036400612400c030584516003001e0040c1603d0500348019178261080f60a10052200f0451440c41a00040c500a541b9951414100d80b400414880041d246000c00c1d0300c0942c10100041780c1c942c3c504030599507088000ca121500d4a08240f03030007050742160314054140340012944560540c800e0364803c00176800c441c1349464082c5054201c032000e80e8060b001a04801901020901d100001d128503c0f9040302c03245043e40c0c580d802c09140f4083c151300d400007000340c05200b03c10b42d506c0c06156003140e0220080c1809150000000c2d54034444e52050409102011070059040c0d1401e5000744030507500203490300e95804164490a0003401d000d1011000f280466002164400c41c3d441800c0aaa83c064110b10b4240d0500c60481e8902011490070f002c1d0703110030070042064142503800c007501c581c07181d25030a010102c40c01412005180d45401d2100701407070550a4008a4000c2880340101c81c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 258588237 1250 258586987 258587003
    0x52409010509030f010c11100e0c0111210d0b01050319050a14011509060207080d05070215070b04051b060904052a0a030c03060506182205090c120a 65
    0x442d580109080c0701c8905056041546000219040d0a402090f51801c9203a0741041d9503a081c420400300c811100204900d80c42036201100901840d4007a02d00130081c0701030441201e910400c02d8566080c000c580c0c0c0804800303648003051038064101a400384803201c0b002400d0003820740c681400c24000c04501540806201500c40e408145c0c1200d0660004141a541000080d030943e100c840c11901c1a8195544a00241ca08540050300e240301103141070a4400f0400a4441030b40700540031121900b0455007641d11000d038126402402d40114028041d0a00c40c0410400074507050501d41d0401c811a0111042100600781050850351150102c0320300b200c084a0009003520340002c81c050006a420843c1390f190010302656603100c04c03803c040c20311620302e59424084c1040c0084101c003600c1680c800d05410500620101c1000c142e40b00d1644007000b005032030240c00881d84010300c00d0800841d00405602540c1c1c3c81031080d000c500340403140349014240c0f4201c10700e90320f005010703951f45520b61000d4075800f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 258589487 1250 258588237 258588247
    0x5032103070315050307080102070507060c020315040302030904020703030f06140109031509050609030310270515060f09040f0b0603220204050f220302030306100203041e0524090105 80
    0x28040c9010f207010b40406002c480605884500090003540110020f542d14402c80e00001509840b0b8582001c5003070780074000d4008801c424410842e0540090030890a501041c000b9100546851002d0a6014001e90300458a4040d910b220412550355400c0446d0900c08400540c0251760822668001c507070740801c1e82d41111560b00c4644000f0461040001c00e2030241d01c041c0151900000702650144500c4a013044041c2c0c3e855001e544c500d42e000b22205207100c1500c014a1194000b0b81c4916400708000403468201e614140000383c0301e611018040124400102d80d645d540d003002d200e01c041800900e01c08102c0300c8043c1c80020540d0100031300380fa81a80c080080d5140400c030703a141500415601902c20700035800c245500505400d411a44006c0405032051042d604550501011544c0c9070103030040d40c81d40d02c90700309000e4002811000740d000d5200400001644019910b4030002c0c4410a42c440035506080508002ca45900044d01c040e51807203940d48118030405038001c4814006090130316603510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 258590737 1250 258589487 258589511
    0x1e0106020304230301050109020c0615091834080a020d020907121104030303050708070903020f01050714030901080c1201090504022b0204150e04080307050408030f04050321030703 79
    0xb81484003203413030b05542490000242070b840ba4010b0b1098480c800c0c207039441c070b64554041d0403811110300b8480f0341c803903443da01251424180009a0200408030401d4504200403213241101c1074095840300000c4e2640032901441001030754400101400c5034101810404100740c000440400e90540083d06c5080502c001c208594012040101c201420002c24800740c090780c8152411500f20f407100f94080b030301300b50011f1421442a1074080c400c21440d00c492030b00d50f040d82c0a20058402d07880f5401e0501c1820010400401c0408044000f0600d1035002035564030241000100000409070440004070b90038010000c81400c03004001e070540740c04210024142e80c4500020741464017060b0344003c2c3d807809204c8a604080031009004a540c001e4509100400050555034040314251140812058056003c60f000450410003140c004490345811418203880395400e60441e4044c0341e44503044070700041c0030452400d060000c2013038041080c030b40440c40343d140b050b034400502c0002d00d1a000c0503036800e408801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 258591987 1250 258590737 258590789
    0x102100b030c0613080a060c0305060609090406110c0102160507050916120b100e0901060503010f03030318060213081203010b0315150c0d030b06210702030409141e0106020304 77
    0x4050b120f0441b0f803040c20a04241c030040055403014400a41004005000c0e810a00c04854040350003800d03400455071242c541d070004150001c044000b6100409c035100802c1c00900142000d80160301e09200d60403400e241c054030700060703640014001c6c04d41030300b040522180d8148551500c181810180700248030000000010100070904a0303000c403090340b1028081e0b070b02851050304214292500c50311790b604c800042e51035010034401e01c8001400c0c1801880024441e402ca6500d0103100c04401d0405040381d0399880598000002d89040c062000d2010815100200442b188201529039850305d954100703000742c00c6900c8024214103c2101100300c00c1002d4655124103030f83c0000085a26407a2081136076100d8644032144010000a410b060071610140b410000b00c0c0c032101c80c980540d00c1451140000c000a8a500070550419404240000241150640200c0c02840201009401c040c5031248000069040c400194121001e001005000c8179400104440c1070314103480d0b94404441c000382c44860 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 258593237 1250 258591987 258591989
    0x5030f0d081e070903031b02130e01060e041a180d0c110306091e241306060602060402040e24060a0b12150904050309040515030307030e0102100b030c0613 68
    0x1545021504001046602c084c090050f0f074800e568400c505201042185012070030f102010750301454403004894030f00d0456000251008105001180003075441013011801c85046909551110043d21000003000e01240a1a0300ca45030480c28100c00d02669142592400d2540301401486080d00c40007041c001600108400300c03000404032101c1d031500c2c48000752115141c8840031a4800c2c1e642900640355000701c0e1800c480c03007284096440240184001581059002c1d069070101071b102140c5002094050052001030160b540060002e4100b80c070520040350b01d5403040440070342064901508002143d15030b050303440c001c0d0307030410b000344c076928000f41c1007030143e40c8080c50300140001d858801c019404c003820302c1000050102c0f4031500100d414403401001c102e50080c0180c00c2000060410300c4c1991110b50441d02c2c80e00b1007950403402c0c1022a1031076010403030907004a101d06c07008a03410340c1d0400181c0f2a641510354248166000c080110f0f581e40000000240b1417440404e041c101d415200700044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 258594487 1250 258593237 258593281
    0x501120305041e0e0a2702130c090506070b09060c040e070c060b12010509060901020f030a0507090f0914010902040b040911130e0708070e0f01110c1003060f05030f0d08 74
    0x20704d0f82c1c1801e42c242030082208040b041081403440001000c07007070045042c0140260007411084440524409a00c001c000980846042c4840b03644040340b2510340c44050a1118800c07100103186040492405292013002407034031200a03070030002031084255885060b900134800f41000301c0300c640585483c1001d08144900c0940022040840c1400c0910540005004640c0c4806450303568942420388c60a03480341c1220310b140c0311000c001150309007040381d004941c44107851401c0b10303500b034403a0000d004400082e408040501e40320500c001c01d00c9000f00101303005000352942180b6051508908122900842c410070085955404101404800e01c404461204c040c401d1002c0f400c0b0b8803074085520402c001c2e990b00c40000e02107000101114010940c003000c10100800307480e01d66004500458246ea00d424903c1c006000b04070f0410070b50380312003040840001c4280c80c0414440c0c1051034550f540c0d442a80802d11952151100e500910400b061b00d480c400c8840c0b424003041d9a40e4000e542c0c2c404060b441c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 258595737 1250 258594487 258594509
    0x20307020a1b05040b03030a0804030807020709151e0503100902011107240504080a14250501020c030106150c0807080f1218060106051e0c010f0501120305041e 70
    0x10780c0004911004490983d10200e030100118034108044c1681c0740110313001c0b038000c42e000201181c00b1134000c1d003009510882500c101c6e0241525240424140d681120b1441004050b28009002051402d010b130320038a0202100002c0b5140740900084c2e07296107000c6032119150356181c034035096901c500040181d500300d80007102c14880e92104680f0405d80303012068000c87c5452280286242d206000301c9044940c0100100300805058440014844080000c0c200b144190154003001c1d02c000e804a89039030400e00362541e003140c03a0000290502209012040c8070ba4034081c010301c1106a01c50f103c0d2103892261030049003074207161522070850f104442c0013130201c036004280d00c411522903c1c020070340000d86101c001903e4690b02c048c0140c402084000b105260031000051000d944240c0150034402c00c03139600c95a2811031013450b1007083c3e100000c000130076510b444072115100140c3c0141d034010956040c07600d1403a481078400030403501660040030807022141070345000ca90308450780800601044440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 258596987 1250 258595737 258595763
    0x403110313030803070905010504080c040c0c05061003050616081f031505011a0c0c010806010302040f0b041509050109031e020a120605063f06040b0406140403050d020307020a 77
    0x102406030405c90b0070f8800074142290124041d446481640c0c01c9510740001040301950180401c0302402151144404001981d0003010204200300105400f840160300a640f0b49411400c0c12424510003c1010364611080c0c3c400c800700359403103180c0d40d0780510803c003002d410042450000c00c0c200300d02c0e84041c01c1e0600c0780c4102c40003680c1d00d52119040740e07944400310303004196071070301d120040c041e02c1c000c03101a03000125100c0302d0354001c0d85040e51000c03051500615243e11181440c0d41c4101c90380100e4070259010030140024580031210340242309841c00d10301809031030600001c0c0340700c5227800000c1030b55070800080c1503804018060707590055401403c99901c6519a100d071001b011540707600f80d400e01d06103c089542400e280d803031012034609503a000d552003030f62042640c220762004005c00203514030079144006a11004d00520740294468010a1180d04280c10400150b0341c0000d42e0001c086150301c14840041d40110484c4c1200d060820701680300e81d5001c40c141d0a02c1c100c0742004d00003a0300c0600d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 258598237 1250 258596987 258596993
    0xb0c0c0607020708012316140f09010e0609030d050a030e01050703020307021506010806150d02120403022413060b190f060206040812090a1203020a030b0108060306040311031303 78
    0x83d4400c103441091001300106448010255860241508006403450000300855070400c12104100d161215a04004055003040920000180d000c10b0f07654a40c2d1402041071000c41d80c0c0b2000104850701c1c203d80176030500c54204000b0341c4902c030b04204641880400a402d81640c1e0080d0007165000300058000c110b1854440f00180c040c0d0300403a18200140100c01e0400c00622507411524000d620607512114940e50390400e20004034840101c0503000a400d000e2484078803618001400e4000940c0904591400c29180c0603252138000b18040b650040c0440110980002025416900c450a00000c1c41004200c2c103105004183c107000ba1900a032074480019055001500000100c4c0d1019441007403840d60743c10304076101c580075a07004251040800a240019001c1081c0580211200055902e410010390781c0704ae05034188961030021a40210b0010901038251142480c0380d0030a0906440d5803401d00002525a44010001400d2008880c0044141da5041003034500640d2081e8184040580700c0c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 258599487 1250 258598237 258598243
    0x909181b0a06030c0f0f050f16020109050307081f0612050606010801060302132d0609030b07080601120c020c1206040c0512030a050d0216080a030c02190b0c0c060702 73
    0x44034a0701a40646200064407846441880704491190350f0300640700c413404004039072900c0746a0b050030400030140100200e01e802d407001001c1c0d2030a40c400e000400c0384240300140407003810350701039072094011071420005690003080102800011055204a00d000c411300e40c0000d003019000160703942c8040f69801d04115000682c42d0182d07009890791805c036aa5068210140e1107015214192806c0c0c00381c08110b00084031000030012a491100c10b40100603424281039107890300d074410400201c07014002c009000442986076004021890008040c0c43c2041c0003070541e103140720b07850082e259641c841d10200e51080c02048183c01004254040c01400718a590307a480c2c40036034013039905024080380010f0a00d010107041507810202c401079410f08880c1350f01a1450b8010030101c8100355002c2280c02180b03100103503202078840c420541c890300e41d841e0b804010216502c01500d6419507008049040c029440c08903504d00c020b0f44581126003591340c03148084420700800d07a00700001e1040c0024080411f07004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 258600737 1250 258599487 258599533
    0x31e07080a1505010e0d170a05031801060303090b0c010e0706030b0315070e0613050a06090810061404020a030b100503071403060114090d1202031c020906090918 71
    0x2076030600c1100c400c0600281052020300c981408210490340e0b8001900701403c0c1d0b642440c0c040e05500300c0d00b46168006100740c1d030004600394006000002000034640c54200d0301e800c3c0400900c02000107a0445da4050300c0d900ba0703030085c00c00306040480d014010310f109411010084000340d06640c2030595440307024018000180c00180309020749213406140b41c024400e545d201d80c01585e114041c03680500d0600c00300d6801003103030b513502c40c080b608003081039144c14010100502c91907803084440d40c03070310984e281070441c2510b0001101d4100a4204504e808030400e10f20803401c120b40042c3d4405500200f5001000000030a40d000544110148407498008002c3c521034400b50710b44000c2c0168860a030442440100d640b5400308009401041200c46500701400d03e42c100540310341c4030004940c403180c24403c08461500010307400000d8059109140b03601c0500b1401a0850960030701c110b2200042c094002c0422705401003071000300041c28499104440240340804000340d414003882002100320404207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 258601987 1250 258600737 258600751
    0x15030a0503040f140603010e060316061211031b090303040302130603020f0a0810020711030f1b030304030c0311010c0b01090606090e0f060123040f090609020c060705031e0708 77
    0x162001500c1c4c0c5404c003072105a41d000500d51031440c0e007006554040440090b0a00d03406104059401c0006883e1140c24405021651110702128403ca400c200954201d4642242c00c60760070f200b40041c40c400c113013142c481c942d000d06200342c031001d812002c43c4c07440c046c03540040c0d44000180180ca0078200d0701d51005051302e0003943c407081c038404240107110340c0c7e58440c03044015562200390681c0400006501400f001481070f100300300081d0076040003a140451103884556144c10520075460302000038480c600e11a202640035606040c41c5444408078900c0910000e00320010322040707089561301c101480b003026039100ca89421656151000754008040382d006c0c078800b1642150303002c152800714800d00b07845240c024800c40410b039207138001100c02d4006084810480c99056603d82c031424002c802a202528060344200c1d005854000d07814140c03038140e17000e048070b58410820807002c504049025940030100e42400c656a0701c44070101118030003503480201d10407299105212140342d01080715406103036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 258603237 1250 258601987 258602009
    0x611010e0a0308130219080f15160818031b07120f0816060e150c03060105030714040b0a08010e0a0b0609010f210605010f05031b0315030a050304 64
    0x200d60024259165040341000d0b012a0303050340095014051403000800507407000d4600f04449641c4240180010354a400000170354005e0340b100d0400410400021181410f0fa08246440781060340e00c0003500c01040654208010340d2030006505c600c1d00c0c1c8115002c900016088aa841141c1c00413210611030f01e05107840e003030048800001e02c01d2803014802000c1c43e0000d040045401566540b644140d001c0940708034446403402e00000490301b188100c200e000f181c10003400e0a8030b1b800d0703151800b1800080404401c1c10f0180306006c0281d07805400e1320350100c12400c248010701d2030f40c11550348500540d0301011110a000400b0080c1c25800f4003d0750403512002c40300e000fa502d4128084082c1d440c500c4071550050750611010a01d58400c0710340c110820400d0910880d020700f0381c1c4046456a401c110510011501c0d81400c0003c0d50344030038582060035482c50210300303609042420946c1801228405001d503840840890749034924941e08003c5400010200c486100642c98107a0b140c0d0024800c0f0301041e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 258604487 1250 258603237 258603251
    0x902180f1e0105060c0a060c080603010f020705030a11070308030907180b150a03020d06230118050d08040e07020c0a0b0a0c0b130f141902010804141006061101 70
    0x74100d03036086014000446000d80a5038203040910009400100d00518144101030300c0401140e403520441400301042c0c0d441031440e203001401d050a4490b0300c2031a041040c410040304001c0380c8088165a044207041c5080c04001700300d900c1507403a240c0e45410180049000000f404051000002c4050446811051400004001d400040c04071040d00c041c29400418000708541e0954a120080400d074616050050500340d002a8920444600d07030402e1108018040c0c0001300b096558000f02205c030001d2174884013203000d40d0f54803240742009115040c0284044211031040250319415034000c0c0c0b0b030032108400145040d1000940d103001c89013110307000c1e0410315404290500050b00b20340500010b1b440b0310015120990f00d640c8941001064812901800c074140d00c0001d441c1c1585012135405551603003440b1010400351824248000d200fa42c4101e00a0100d0700181d8000208551140c1c21201d004004010400d09030700b81405290398214492030400045403440e00a01d80c4d44c4585203a0008001030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 258605737 1250 258604487 258604501
    0x61c0608101401140d0f061d0714061c02130b07030c0309081218040e07030309090f18030f110f070303180f12080c0303070c060516080703020703030902180f 69
    0x1c0004104030329001710040c04004081021644003e03c030a2054000041c1d58800002040c058105045500d10541007004100720420b03094881d04101c0e42e00700c48242c5032440c03a10f0744400d44035041c9402e00c20180c0124945056407282010300008205550036580d90b54128a001807642d0502d0804030040b407000c1001003910840000c0f407070303105051020b1445c40e20020680f10400510107182c0305902c9030715080050701d181c00501010780154465100e40d0405800c1c074581c001a18280c03040c0c0c100461411280d64a41c8911100c40c90003240c050928008427801c006041750f45602d106103061b030030f01c9140e2001584040004a08080307a02035a213180c455801d05041c0c541e45101403103042c1d0080c95001c8144114a168603500310018803c0f098a86000400b00a0710b046400031510040032134a9a42268140031150041c1540583d42412074402070000b050040d10031040a40f070f9008255002c03e0748001c150090307100c410402d40042424400c4600e0400c0f10714130050031180ca010342c080e0007000c5549 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 258606987 1250 258605737 258605759
    0xb06120d02061503010905100519020a23091809070509040b0106030c05040906030309050423070e0103021c0b10081003030c080d0f1a0102070302061c0608101401 71
    0x1081168080c01550300c0f401507032918002902d4016526558404060002540c100700c0c0868601040e07001040c40c1ca040990b008000c07112440a01400b801006106151540501c81c0d81c0000310481040340039000c0c0202710160307030046005482c0c01002c000702c1201880c8010514902c60125a42210341d825114024041c3d09030b800c3d90300400b5891884018003a080c000d0b088031b418810755140c81418603555611501c141c071659131046c1d001c150a0302d020300c55814240290080700314542c1c1d807144800741213a0f0710f4003100401080301d01085043e844043c8680e1194040361407109980f0200030680d10954101c0000301190384149116542490222040318091034045101da0803d5007050136040c907584065604081301c003800c48101d4801c2000e10f120318400c2c071411b03445001401c4001a201140c1a00402081e0480320060656101d10410001a5035520070ac49020841201098480360400c0c4640050000703034105040d01e00038051285c410703039040d6101201d107142b01c1001451030303603a800075004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 258608237 1250 258606987 258607003
    0x20705040e0c180603010e0307030e041104060206040b060f030708010609050601140304060b0301090204020d050702120f0a110f030c160905040f0f020d0b07090f0e01080a020d0c080a0b0612 83
    0x3d0030002140303081020100031030010303a0012000d0008650603089000e51400c542c000e4600310301049210300b94203841c0c11b0620038542e4042d84001164500703401d010300030f50364100c01000142407241a200084164580a000d101d080001504075100340d9201c198490203083d081c003510041c4c80c908000940e4540c481c00528002c00c0b42d4052682c51a00c031611148082e281103240c098141d0740790111980180c55502c000c2a010001c201c0014050604420003420800945201d11000e0b5092203502c0d219031402c1d08541e041e0b81182070941402d208102070394107202810a07a9540c0c1c0c0400306500b05444008140c6442150036490700860854540d0354841c1295415200500b070b00c44401995800514420b00b21031103240010464104480c503983e038000d130a01d0440e50040060807031041044500c1c0b094406001074807001c41344803500e40c10a940a82c2d200380c0850082d1142e01c01e545244140b0032450f0621004d402c00030113440c0c00080f1402c0452042105849250181c4980802401c5075600031484031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 258609487 1250 258608237 258608239
    0x110402030601051209011107060f0b1503060f010c02040603050d080c040e010306090602120411010f020c1e1206010b030105011101050403020d0e03010b060c0607030507020a0308060d060e0d020705040e0c 89
    0x141040d44428240700ba20313100404100a640d656907102d500d084100d40500741c03072803180b0303800701d00c9600207841d400682c0da0324040a802041500000303601c12000005680d4041d4080d20f0030514500b4002c01283c07555800c10001e07410519105010041c4140894991031103012034a40404544822055810b03030311079881000916000c600050002038081c1c2c001d010800e01403003002d401e0000300100c6500401d01510110f0740031005650040065030080218441c108d9035001404440b4106000308000c10140091100011006200c403500f45d1b4400134402e1940c082d540c11610103603110741503403900d548280111400b16418003800f0742c881005000b424401c55255000d44008541c180099030320007950f582195040d5280ca200160399191f04000e002c80e0b40080c001402c19060a01b000740c2210005009070086400c69a0180c0120350008022038000006a8034072200408a0401c40000c1c07046180c4194640140b820071100e6513800500d007415598125010801ca00c1070081c250755030306030302981d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 258610737 1250 258609487 258609497
    0x20309070f060c03031a331204080918041a0a050705160c050409080706060b030c0a0f02190506060a06020102180f0613120b0f060f0f0409120507110402030601 70
    0x1540010341700303070094034003003400496641c0300c52a00e20024902d2041609103000c2d0703c0d141014800540000d002902c81c840c0c8603c00d0501d00880c403c1100e0999200610240141000140b00c0520ba11080b0440400207031031a0340f07980c82c2c141031500841c4014201035581090303c503040491000c2c10f0500c6410702642d5a5180c25141040d041100e282c010402c62042d030b0901e010700d50005081c7c841e0b014801d01a44140e036001e42c1c0310b40614007032007103402a0f08004900402842000000000b0908039444407540b41017007440504003900032032800d03024003910b80700c0190344240329040000c009800f03405040101c40a111203a2244004ca08070f01030303c440440d0315030140d0940e00d07050401e14540e906c0c001020741181c6c0703440e010544401c01a040c66001400c0d8180c1a511441403007084032805404c1900300c4a410094188a00010146224621114031401811440c901c141da81c560003030110980c400b048000c10010034102170607a420482082d9910f100d1040562414600b510840c0c3c8120030507100e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 258611987 1250 258610737 258610757
    0x13020108060111010c0f08010f0608041502040803040e09010c1e0c151b140f0706021c0501080607020c030c0d060e030409020d0c0e010e0d02100905060706020309070f06 74
    0x1100d4060014141906100310a83d011010321000e00640003103103155140c02c1200308644c1001021800142e00c06030590424034005e011855020f10039607005a00119201e002000b110a1b1000034030a40d809128148800280003800e66210480284912602d400070005110710701c0058410819007400000070a0b000c08074a20214052240c014450b8003801c08101000040281c01c4d040f1450307154076074003600303c144d646541c0c19401416820030131032040ba41da05044030651000c0d030601560380e00a10f0b2035008629110109141c029045100c208811b0038022942c1d124105078a1701c2c01560300c60b0041c040e440c4061074904000a80ca120280042c1640030341d040142c440b00300030900c0d0304000c031035804100f000150444283c00903107801c140f2040300044049000304040c00560744200e10505114070030510b21140d54031070151488141c0c06442840500440b6042102c21030b080e50400b0b94004008240c07202401882d9029503c01c0d031980040703c4034551191501011002640f01d45c000042e1880d074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 258613237 1250 258611987 258611989
    0x50d030c050705030d06030b010803041809060e16050f030a0b150105040312260906040f06060b040303080f070503040506040f1109010b13090b030d18091508060c031302 74
    0x1000103945066494014244401035440701e00715442844800d4107203031501c2003401031044070744a150041110358001d5181a01c5c000121500110384030200d4562580c0d50186403d0104a03006004202d90070b07002d40f03031050000111014000002c1c014030b03001c2d4a08480089060030b001950401c4c0e00c0d005003880340b6655840d40407034018081c0e1071440741005024000000020115404086107880d0707925142e059410100b1001080f0120719041a203100c18802800710840f004076040d80c000f600302180e204c000050f4103040c2e01a0000307600414801c50001000801c0c96440002103004821801e5202240e80701c25108650f540415100a403d9400c030001003400182c42c0d40031204400d1081c410903041114800004002d603900741c0c0308049440340015201c0d5141d130071a080c000941101041004000f141c40e0209a4030300410441805001c24409020b03019900052000c0040c114228140289010440380240d050090712403c84184540c502003044103542d84140d03441075101c0c0d60228640150740d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 258614487 1250 258613237 258613241
    0x60406060504290a0c0b061903020108040204090b01060f09080706140310030515060306060a0b030112082a0f061902070f0b07090614040305060a15091b03060909050d03 74
    0x3c0014a241d19844001038841072070002400d040421501c070400b409805060881d440d420040059100769207003a20a00f041e40301d89040029070350203180202507682c95101180091200398000750140c00c030764000180300c5a01210b220065135030703a52150380e0244d80d2165076070b8643c83c6004510119140c07203207140581d81c415002d103a07c144810341a00c1d00503584c2d1201400c041c494984644c1140b00c040801100f4241040015084503041d5800503000d45400000032950006010714608a4110110398007070012840c2543c2240d01c501620700544c8111080c591106000344d040d14406003d10480d404041c00f0101c1c80d41e01c02c01c0f00d481101c6a020131072500c0710003548088022a14044412030341004248422107440c4074207020b4841c1014107040c6070000d1304104100c003d50b404108d0401051000400c0424115000f04c2424804542c0014501c6a0500380c0d010307400c0704c0003161621044a0100c0202840c1c415000000d440800019843e41d210b581070314000d80001d0469807081040c0c0c61010f210ba = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 258615737 1250 258614487 258614519
    0x15050319021909050306070903060e01090204180302070b040b0a03090213090b0f010801021c2a0f0f030c17060402091c020411070201020703060b03120d14060406060504 74
    0x54452440440031400c40380120307000403840440d4040e031080001c1d0341e5500640309034042c4c0800c4006050515006e100141100d1007400001c0c0320319164803220009203001d4008070b441c6e5034020428803618603424407204168852a000303600501c203075600080c0800b442c2c0221810b464210182e5440c0900001e800d40240000190480c0c00100751103690030030721150b00c00c9280c890b2190001c0645424261101441d40206070403606a691041140400c000400d04810072141c000e100b000ca40003020904003a400640c020b00620144903082b09041820b0740040f0f41c0d000c55015448404070344001d204c0c01c40843e40c2c6444a03501040d035a0400455841c01e0100465102074020300241c44c0c1800800801d4080504660344020700b140301070860300f103103014080c0940c0d4000c2540d00702c0c08c028243e00000d5841096200142c0055981c042a0700552803e0042d54004a0746100e06a56640c3c0059114004c003580044620f6800300e5201041940c905801114100d03442c0c1ea9400f818142810364070820711040d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 258616987 1250 258615737 258615751
    0x10c0b0c040b03010b07020f040e0c01030e0102120108060403090f0509060909010b0411120c03150607050102040e04032c10050c0f07031415040c1205340b0301150503 73
    0x10030701c070000710b202c20384000318060b00010104030703110980e520500c495084034401c200d1003281019200c282e02000040d40ba013101c502441d0104002c2599015030b0300a201c2e03a0000130348220804008181c01e4400a1528012440b07640c6d40308005544400031034041c2d000740140c540c00008080801c21070b117006081a0380101103440001030801c09080010101e406485503600001000b1580800300040000703a0343d0b000b00c4840e01c0500e5854417011007421903488448071032007010081400010f02c4000d50548003e00004002004281014240900024124407142010840310240030a148201140c1240d030200050080d121204801409039002d41000c0c02c205e9451003460380012000307000300300340001540105a2003641240a40d5400e007480d103038030707501507060440e80140000914000061801c03035400e0b4148101e000c03146d0ed086400c10350b40d084a20880c01c02c0e0801c0034042911080c0607205518401c0c003002030780e07a40715102803060000f403107070440040e921034400340e02e00d0040c4015944810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 258618237 1250 258616987 258617011
    0x80117060727032909060606070f0803010b0310050612190e24010b070804060c1e0605060a050423100308032806050f1003110703020a1e02010c0b 64
    0x18015118811121480d8010b13a0042600a1050010f5540003070044101d0704800c009002450190041e0303940e4440949110700403003000400c0420f001d00822210115a070140c281c030b50700e513540e01d80100740d50010b84d0103142080d151000003440b494280e085411800b442d01d003009855590310b44948003803411440300301081d611414440c002820900415068240c18030140304802612128403042150580059106820400a20300411184800e4400b11141841c001999142500d0702d003003000d2002d042241e445203a440124104116604918420b050640d0b0b010b0f1007a0f0b031b40040005541800ca00c00d5901010b0b0f00944012540d640d40c055802120000100c00459072030307442d03030000d0384121501c0a95400c20965000c02e04d001a5118448c6480c0090a0120604240c0016403031443c074000248500000c400c510314040c000d410612000c4c14400100b47c0319840c07402d02079104c2c80c101074200e81040f08540801600d02000900d200c286030180d40343d85646503e0fa8034411040c20140026054030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 258619487 1250 258618237 258618287
    0x6050f1c14010c18052b081204140124170a051e070b030708010b0d06051302070312051017030c0a230111090d08090d08030105010801170607 62
    0x30824050000012a150313601500900f4450455800c02901d401451158500302d001039008038603665400300b20710881d654050705001900d85143c8901c10802c245107088c40c0542000148044080031070030384503c950081c85a02185194030b032030010401d10b200392040d950082880143ea6084559038409070f00700455104031456101c1f586407104042501e02d002c1da040740c1c60313213269000784003403c0184806000581141402003001c0c10384c8070140114030f0f07001c2000c1132401c5843c0503504140014031001e0882d625481c541d001c1301c0045e42c8404420b030082140440c0d000e900b0360f05c07441000c0c4180145113240030322a0038483c1d450251001c90300340c0da0f107520040c0011400c4c00800e0200e840d20503c80c00c41e5241e080c0c1000040d071445910242d15118591400250301401d003105021030390b6540c801c5540c4000c242103440d15461034054200701b1900191141d40880420038290029416076000340c0f101d610617a6030740c009021605000310281c90303a4000d480442e800900800c0d41c030751003042c1ca0340341071414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 258620737 1250 258619487 258619523
    0x2090405010b040510030e0d0c03020a0c15031401210203160816060e010c06050705071a060f12100b060d0c0c031115160203120a060303020106050f1c 66
    0x9620300707030030141003200c0002c0d04100614044002c40325030000d90034240705500008a0003034640444818110030b205c41d1302104810140f0a2000d803c6441d4042009041c503034030340c90184580c40328090540082842c1c030381202d8441041c3d0300305904070740441405000f4030307150104e00c0541c800e52403c22a018030484d0102c0540380d5541180740090720f901c00043c203401d071180603440c08a00082e4454400e01c40208025401e41e42d0243c480e003122a00000c01040d107850301c0d1402c4426200b940c0015002e40346c0d9040c05060002c00c4010603000da44104d400034801ca90304070402030803100005040e0746a602860200e0040c2c445a0003542c00c010000b017901d410820307041c4d112800d5503042d8007007000080c0e1a14501c000c040c0c00c0b89142603140d4450000f00b002400460080c11401c6010b003081c0c0303100c1441c40307842c0203152080048480b0442c0d85070b00ca440a04041581e00301400590104401550820030040f403681080c04091207514401003042e56000c10030342c50f84100c26082d03803003075860765130400310a414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 258621987 1250 258620737 258620741
    0x2150a0605030a0f08280e010507110f060d0c110c100906120f020406170a0b030c06031306090302070e010603050f011202031c0f08010e0f0408030a0b190602160510050706020904 78
    0x20b90349021b1410301c258051000001c09800002020f181840010b010320300c045290710188003040c102c2a10072108510426002503201d0150103c0d20409904054481081940c80207551142e48404400c40303814182c42020002076003103005100d4001a012001040820320510014002c00200407000440503600c146041c16680325800c00b00100d800320b600c48080c1c2c0c01c81d151180d4080180041003105802a40019071906081e40c901031040102101060302010000d5074418202d62020080080d08160714001c0e40710401f91140b00002420030b000013400034002c1c00303010b2050111101c03a40e4030760700b03000c1149100c50f1b071400180e8152003040ba048a94910608030382030040709079220850050011040102603000507040b5280034414501408400b0700301d4040d203a00681e000c00c10580740e0340c0e00c505400040190188581c1e101050b605103580200341c0c040d5610640300c0e9642a50701031011040c1ca81140d861900c6407c0c0c1241d4400c4100032000d2056010f0329130580300d15800343c6414400c10000741 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 258623237 1250 258621987 258622027
    0x10081f08070e0f070807090b0a020304050409060c1101090c150216060509040c230319020a0804031115010611010e03040b090a08060c0405270702150a0605030a0f08 72
    0x21122041c601400344003e140c01c41c1983c8041e02e03107000f000714500344c2e100800039440c510030032040e001c2c04a50080360754028015a8060000a032040003041844c0c01e00342c028080c58818103020030800c1108008009043c0244848d107504828010704c000e01d4030480c4035020000c2e6148400714041d41c088401c000b441c048075100240119a50603441d01c20b60420801100c1ca034508803001d110714a0401064055403400c0f440c035040310b0460310703522aa202e489280d60400103802c0c900c2068400568403010641100ca413500a0f802581c074512001d00c680a030566606d01c0c0c0ca4a9200b00e40d10400405c070062050b21414003a03000c0c8000450300d040602120351070b580043e00405191000842c90f0720003801c2c0508001c000703102820050040f420440301c0c454243c031440c01201d025000f030981450303805e02c0c003203074040b422551415580e100c0c0c540810000d4076005502c0d81111095031041c04160482458060a015a5001000ba1502c440c0c41d66449000d905400c50440700400280001d000640103485884 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 258624487 1250 258623237 258623249
    0x2030907090c091a0a030b060703020a0506061c020f04182d08030a020c0a02150a110610051903050a0c032a0b0702030f0102130503070510081f0807 65
    0x1244240c240807401c0d050300e055955100800456403c1080383c81010322200550407262011a035484268100032001703018900d0b90103070450400603c0c0320400d507002801d0640240141d05494050307c801e400c11403844050040c611a0052080c00701c0c0151030708103441d02150900410020ba48180340003600780340094101c06440d8012101701c0c40c0c0000c070391302042c51b027080204036090a14554564035441203010180071505032542c04941c0030310000c4200003440d00d0071b0700180140049541d1b02e003520f806030300c02e4101600007208460b403501d41c0000081c4190040c041c0c04a00d00c41c080c10309091003c4d0382912454006400680800000401e200f804004005401a001035100030304504111400c940700310300031503c501e41c0580641e00002014078000a44022098090343c519080c00024500400904100d0f40b035480052050039444169141c8000c980084c3e0581d65103580c1d030800c00010643c0d460480c00462440f40c0010b0f80440841c0d0700020041c80d146d121400b50380c5800d16949410403540142c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 258625737 1250 258624487 258624493
    0x209010803120f07051b0a0f1101020c10020303150d060c110f0c03060708070c0b0703061e0b070b0c070807050c0a080105060a05093d0e070c020d0303020d020309 71
    0x490074002034551198800c00155940d283c5042c6088002c3c61417148007940040a0703190040c07094551014002c40031340c0ea400100d0401140b969082c02e4025a1042d08198054803507a81145000d081403450300c034040555402442c255640c035121108640703500700c0d04c658894844545d0000043c1c0c20701c1040e0411855030750f0882d4036000195404e18041c06030402800c17a5100706903801c0156000591140d1090241c0b030b1480c480d4542c04030641d54400190001030130408000100705503958503a01040450300b103900030068400e0314405800c0c03c00d2039400f81c5030210302c0800c240804542422042c2c0d41060b411368503a031401d4159220760b4215000f03400c044860340c0116040c2403c0703280450000c0090040040200f100e0706003580007030510714030780c401d40d80103808150010709541440c000c900301040c5240c01d50046c86008112100010820b411146459410740a000c0b9000b440680214810840c503100e070414100c3c47d40070401c8a4070364100032401c054080008901c0030343c4e28005107004514142c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 258626987 1250 258625737 258625747
    0x60503070305012313080708090d14100e1e0c061c050115020c041a0a030f0b070e0109060c080706021b0709021603030e0c0303041805011215020c0a0209010803 70
    0x501c911003114800b8111307141035480103100092544079030005086500840030340d500c110314a000c1c0000e0040e096007650050ba540360500c03d02c030002604030400300c50315059441d8918402c00d4982200e01e0000403010b540c0c061340c2a2250404d604401d180c120b0100402c440c030400105000034042c4d40004c84d112100200c0911056418813140951030242000400b0b0302050500c41f40002c0d03442491840d01c0d4481c684071120709092502802031410b4081028001c030703603050380342e05001c00004074020049071070202c4000020b4600344210740c030030102c000507541d80c1600391070058102c4d1210450390050320384400401c01c0c1d0b400907415100034914460a860a16100341c907000c02607085c4a00c40e40b211230400e004001d800290038141072100304690b4036060000d440c90200b03000d14a00008030803540e406110016010507200780b0b0302e80035003910003003280902c59aa2107040e080382111501c00f000380401080131000d00b10012607005070861a00035000c88040900f50f400061803000284e11804040d000003078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 258628237 1250 258626987 258627011
    0x5011d07050307030f080a03060b0309070317030f06091e0f0a0c0905130e01020c0601080c121207080c2b0e010c020a05040c0207120803161b1506050307030501 70
    0x1104038010301c0c00720081e0800307526580b00c80203081e42c0804020402840085c0035800d441c066403001020b8409420090381b42e15203140e449540c0c40312400141e4214820205c00c000c0b580d809070480e0310030040c1a001015548403002445101480502800341040502d4441d44243c2c0c145140184a084103c04cd040b103400c2000715038080320316464540007007010845003071101741c4070301c0c09c83c48030441190000145200046202402802140781248450251a00018244400007640c0341c5ca51021186041e401c010110385e10b5440801d90500d440e248428050180883c2582000c2d10601455600f41c803609141c0201c814051070490720b65a820200400c83c00041607405501c031002031000b130034100d22148140c2c0000b400b41540348141340c0300d241c803143d490203ca032080c81002c0081c40301f4aa0030200c000b5034541607599810480381c03400300c01c890745d542100d110710901c0d5421f0844800180310001c801662a50143c03000d06914003040e80d81c40c0e20f0300165a4a041240c50001c501500000400a1140d0707 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 258629487 1250 258628237 258628243
    0xf0712080606130509090709060801090b16020a0204050a090b09061006020706091e1a1903060b1c0b060c0f010510030302191a041109010b0f0403030c020d05011d 71
    0x1a1141c1e020315014081116014003542c02802556000c90744191380b0b81e04d00000d18a0315800317410081e600d0341000ca0008800300c0540200c121070384200c036641c56554952209554802901b00c9441c010b80c80b42c01c2c0d03407002d030805500c5681c010a4074040841c100356152564800c03400107440c400cac0d060b8054020003800e0f00aa117003940182caa40e20290900601e8904004c0c1159498010031454804205842e0b03840c54600030b034080100030410740741c003285160001780c0d402500100ba40601d040556030141414a1007031217800180c0749401103460800b4800c500300a0f10104841d544560140c5c0c40016030b0340f0b03540701009088001e0180000349104096005020b0a4030700181406d90003d08007030080c000690045810280c000b00c10700d086034040c1c45824901b0421000c6681040030b00c0640003408144184181079003141700040e510014543d030ba4034409811031040e2442d40150178000d000034000070b4454000c036075805000411011803800a82c48640c00c640c1d445241a800405501903401102c1c414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 258630737 1250 258629487 258629491
    0x207030e031221060d061104061101050c04090207060b090108011e1b300c111f09060605060f03011502030a081b190806010207050f1804080f071208 65
    0x80e01416042c521421071982c425801034150b5a400d41c4020006140c4e80c8031541c415000d1600050107104100c040001521258054060000055140406124095414020741c0e01444817a03503c0ea1525141030303c1d0384e000b5001114105e60030b944542002d03050b541c642c0400382c06040038800001d0b51011003144a00c0d1201100c4800721000e0810751840d4041c006600030140156007802d24241f00500a01c0003100c2c01091448408060040e5603842041810b950280000441d00d40340c020100321601c0e541030741c50000c0b141e4800790940400e22803054000c03581150300c03074910600010645503115000152960881c900b015681d15020004104070500e40080c0c4029000c2c0e070021314640118184000c0404400400304441e01d02059185401d08a41c00c0c100c0380c0e4010014400300342513454000003010420140d8104d40148610320001c1441d04c0c10500c080c0c4000d0700108540e0040002c41140c81d8120002032083e0341c045010f0114042031900d02d401000800d214490345a5120010b0300044d20300100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 258631987 1250 258630737 258630763
    0x40e010b130b03060103080a022812050913020f09280e0705030a0203040c0b070b010f1a07061512051006090506010c17040510080a0f0e060403030504080d0207030e03 73
    0x300b90b00310302d10f500c012030458152504428510380d0384942300c4d0701364607008510380344034000a0112618228005a04010305805114843d0008080303100b002c103c81e140a11390310981d201ca602144000c421081c0d0703000300345034903c1c100b4040c100724003000000c4102107801c41e02c13008000c50018601c81c050809401002803c3d0b0031258040c503007060304004006010041c401100346130300002090038048200c0c000002050240606559280c00c1d01d003001c0c002102b84144400341056003c0403980b01d0b5072440d4034010851541440d0304003a119252403024007a03641541c40343c18074107000401e026421410032120305019000900080d403065000c10112501640644805803034401440706582e40100b181e468590030580d0300c10308070b0385d1a80491452149501241d4444c901110601e012074106040d1440f903001e40d003040190089051a06040e1401106488890b030030581c001f60000f400f070780c04150007600070300d801810000706141103422a841032030180d000c1030382205541540e14080003444980a2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 258633093 1106 258631987 258631991
    0x24040b1b04030f0221030a050310050d050a030f0e0a0905040c0504020c10061d070513030c0b03090c0d0c17010f05040f020a0906080c01050c030702040e010b13 70
    0x202003c01ca005404801d880202981c0b40461811390701d04100103586042094001181e45500040c41498581070390704c004030303031500d8840160940c0380c4110010b08101402d0b08000d09400311039900300c401c100c0c03080d460fa8055268404034104560075444041059121442d100c0380302000c07a049650414408501e109212100007480680841c030200c04100f40c2d0745546001071511071502440848000081c0850920342c403d030020802c407202d00c03098102d89a202e5540710701c17010b130700c0d4490f4144040c08001d1001c80300c424403940c1400c80c01110b105068410b41c3c0d603100445281846208881300109044889007a0290841100c1d0181035104100c24686460601102c486404060340151000b08010521280a10602d4141c640410043c8409800c0c40011100c2d17600c40310f5002590b000c284000b10041e11203000354042540040000b050b1801120103004000391030100781d903881c0b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 258453237 258633093 := by
  have h0 := BRFrame.cov_init 258453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 258453237 ≤ n) (h2 : n < 258633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
