-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1359
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:33:43.935429+00:00
-- url     : https://prove2.me/submissions/9506f488-5a52-4cf2-baf2-65068d43013d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 244244604 ≤ n < 244424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 244245854 1250 244244604 244244633
    0x301110f070804120f03030b010305040b010b090a0308030c1201060903020312030a150b0c070611030301030210020f0604060501050f06030f0610050f030a0b01030608030c030301140f090f09011b0507 87
    0x1041d2410566905010540a101e41404179402504c00482e40201034244c816810348000c203190400c00c52a00d907598000322031041c000e20050782d1000c5403008a603503500403071a01075644032031400e0700d03400c00000ca20781039004584040160060980007080c811b00c2180c3ca14210380c1c00400a141c0b80701c03104039105007035202806030080c203030302c500100740e5115044018400901200d49116a80c1246051503420308003290030110800161200c3c20750241c0b0b00009580c1541e030100c48030300d11407502d00310582c43c00362070005200880c0112400c00c41448480d500460483d041a184200304064040801c1101d100444203021107440d20300110f001818418034140c04a0503c1c01d141c0d1820800b0040e00409030800c644e1124a580c8843c810511940d2500850b0000e00e1a04001d60a00d104014103176101e0105014480c03800343c00d28270318041c90340c8119030458104009070a020b080c1c185500f810140c41c00c12500f05120b98200b10406001d030b44e501c44540303d034001c1541d40b2030421400d03075280d5204040c0e04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 244247104 1250 244245854 244245863
    0x12130e041502090109080a030207080d0e01121113090903030515011b0201020f01090b100b0901050a1d1e040b010f020c0d0204022203061109010c080304020a090e0a0605060301110f07 80
    0x31725010505100c1006034010b0940203070002c040c0b4501d80120185800001251481000a081d4840250380d80003890100e117111710030400718482149a016031503a002e00110000030103402400080c02510645c4204000c2e030103640c00340055600c080c50001081c1c00040ba05000650302504548001104030388412403520510645408091b00362402c2d0a40b5044d03242907901c446200c0902031520300c4010080c00408201c02814101a9000300182c003a0084c0440c550901083c0300c0c231a05020242d502d02c0d0510240100041043c1d1038041d102036000142c1850180075030300c0c00710301c00c81030340c02007007141c80b00523565000307000841125017401140001a00f003260059000d12150039040f40024010032280100c0c02c481c243c091031410400d0503503407200018602d81c20100000c05407079031711a1310310b0f900c02c0d0001c0400d076032500c0e580302195811902c0c4d44460300807890180c07080900c02000c10070007044e90107000d0a01c040d84034501058226810b00020030301c0460304200c525440d00c000b10203032074420b018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 244248354 1250 244247104 244247117
    0x614030c07080714030d1401171f0204081f0c0e10030e0a0203010513030216060f03090203030c07090203060a08120307260f0403120c08150402070512130e0415020901 73
    0x4c0c1c00b412855074100f5120003442c2621803001c41501c01030001114018201d03590040d440b01000c601070b94131082035081c0007a01d441140f80d00c81207540503804039001044420300b16001603100ca440c0247d0b0480b850010307659141401440c800310361081940d000340541c000c00c1402c80c2001080d09400404840304000080d0081e052110050b940a2180c070f40f00360016854003015104a10b0002d0404514001020307500c00701c0501400a5548141c1442c0c50802c0340c00d002848070301d1400040c0c65402441c408800500c030301d50b8085420301194011314055002039501c00140c0b91500001070f03d030520480c2000a4010910000c2c8140b4803914080c000c0e1111503400d86010380c0081a0902c0d0304004031250800700d40c5000070b000405500203c0c1400031b0301540c41c10402c140f240307040186414400741021007280520300d010040e43c1e4031a0704560507680d000c01100c40310b1810b2a001c28064008850030390000104410024420840205841c03056900c801701042004110900e00001d4222100b00c904200c0c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 244249604 1250 244248354 244248383
    0x30f0f0219080301060905012a0c050909071703040305150606070213020304020907030204120201110f25060207050d0b0a0f020417100b150304080d11040614030c070807 74
    0x610400c840e01c000c2c09001c01503940c0d030429001a041e200f00358422030411040901c40b480032050030080c0d4010030910798001600305818108001001226000141c0c40351040c000c1c0b0165610018010302140c4000d2802225a5004042c442d01c90180748805003040d048042c0e401ca018001e40d82e901d40c001e10003080141015060740109001d2000042002540d45c3c2c00018082581740c850380c180d0303118090389800d43c0351908202240c0c804e4481000f000741845403c802c0c00e840300009100102c10642031030200e03403805505228110010080c0400e030303210351940c1c0e0008074115102055881c241c6202829407281c074002c941d6405980c09006007241a5290f8403008105440c1c80790000344000d01d82092110f482c0e0854405032400c1201e07005040700c0d0146441d132001040d86034003070032442c42c41c842c40da01d6849503280d09000115118002043e0b41403841d001c180e04111010401070030944400d959150f08150408070f00101c01d10007669941c2100c0005d00000000035a03900007032861503c0b07120004010803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 244250854 1250 244249604 244249633
    0x160311070f0308011d010f0e06010c061a120f06161b0f03110c0102060601050711030a081c020f0412030201021606063206070f21090503010207030f0f02 67
    0xa154110881c0041c0c03d0100401031842c00000c08141d08500c140c1c5110554503100c05000d1207030052065140d105440320000b0201d0b0b00078050034006a40000003840121500300ca07840070303100c0d0610b03040d20401d101070315441501d5000800031400c880e003030010030a9031110010711701503807941c0b224401040110200070a0025025400b640410703c00c11080d00d01c10101c5c40d01815604503925401010361012a07030f54041d80e80020780d107800010a003040d0b6510701850611501b0720604080b80d94040c030440800e4000c214491008045666080032000b0b802902c044854059100c0c0ca40000c1c1142c50502041c07252040724030790310300002e10034000180340840540350020384941c4c0740342c1078900303903692407040204440c0d00100d202601c50a0f200d0a0b8060180c008000740b08200d050094007c80000c1151020051110646c00e40c268220000041c0c0d0310114410000140c40c1681040018501d2800014241014000e4481cac0c1a80f40c1c840645600c002842140c40b944e211100b5421032046114044606 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 244252104 1250 244250854 244250873
    0x90209040b2403250b0403050607030e01021918050a030807050607080702060105060a1709010f0b04060605030a0e0705150901180b0d09030203040902040f1e12060b0310020a050307021516031107 85
    0xc43c46023001c1d100c40e18202c007025080f00e00d100c4185100c0d900400900740c80b808507001803400d608850070710124550040041a2a903021500051b8102510000200c207001380d00016080c600d116008032034603075036a5070702100c40d01c805803410409a8406001400f0364681b110191045e182c0d00e203400c0f081540c0ca0810042c12040075961300303680b079545450b2105036601a01400c005c04c48181d5042c000316150290040039403000800f600c2e1920364500402c40028818000303200104401017101034900d07a09428110944d0180004034042070380c00d01455070340c084014441d011a0178000340c19042c220a244d8600103000d203a40c0c100c08501003001302103407190080c0f002e00080e00c03031000c440e94a0740c10006100a11424010b4418107840d84440400c500c022540381040703619032100020616403440401720346800c10b010450300c2d01c58000310320b01104503800006540300308261f9084400d440c0e01102070b0445280c06442c1165001e280080c2446000d010781c101c40152401709184920f80015915000f204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 244253354 1250 244252104 244252109
    0x8040609120e030f0d0f030b0d061509050108061006050a0e12030c24040f06060b03070e0f01030c020c060c0a0803040303090309090608030901080a090209040b2403250b04 75
    0x11070742d81c40e0180c0d40e07810300f0041c01082140301e10042c5100c3c140310300040c4c03407680e801e1508003c06403600210652520740c1c04002442e10b50200c002d000c601c27800c400c0010340064600a00000a01d040700014030204006005d81c003442c1c80b030100d2038410703081002c211642ea100c2510001481440f55074104540c4410000d468000d61000c0a162180c080099031402c0010a0072041c21110003400e8500c5844401e0b4011070700542d0050b003030710742c03092103250100140655903c040c103207242c04010040700d0f1360032400c03200c4071100844258660a01c0c40340150101da050000c1100164803800b4070f8011800e1010050082281c0c6504841b034a1100f0340d80c612095204580c102c0001e5200c201d40c41c10135400611000c0039104503001402454180100c066580c014850b42038104099803000c203400407107580c0800c01058000c0c02600007450301d4104a403806900fa500032400ca50380740b010411028050710109a403250040140050000d0425075001d903400a03580451036070701c540400070310740e003142004100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 244254604 1250 244253354 244253357
    0xe01050c1e100501032a080d020c18040c03021509061602010807090e0426160314070308010504090501021c141b0d1a0301020a09080c010507050a030804060912 70
    0x1d812031080501c0c2804110a41c02c400107040600620004021040e0b10f81e80501d4602503040000320422100e0005e2043da02c00c0341e4078040d11100d020300540c04075020450007001d8900680e0324203418445c0d42c01038002c80d03002c2e01810320403405000501e802d42d281c203199a52042c2450a003100040000d2030b075071002c01c2c035059040800d1805021541c1182c0e54980c0001a800c184150b03500d010000c1c1400b081c01000100046100c480e0f241c0f02044098150422801e003900d803d40f03404898070390307140c11800982c1c2600421031001d81091001007070011101b14a40c5591010002e034a02401c1c030010f80821141151195000d200c1180040c0d03007010301100c61162010007064104a10002d82c2c0c0350300c005000c080d468044005c0e1350742e0300203003101110120110f200f40001d1040d5160340652814100c10407071030b850b500004405018987c0403031800d09485c40c800c02d8a80701c451280040d00d030ba114044009256420207210325010900481c00150711600503603000c076101000350784032410b0498140d860070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 244255854 1250 244254604 244254643
    0x18041211120a02010f050f01060818010204150e1e010906110a0501180605060d21030603050d0207090b030102090f1302040306020403151406031c020a08210702030a050403030e01050c 80
    0x178406800d01401e40c018030b00c40010442941403407401070000030000c2884042010002c8000e41c007540c02d504650090221039035410324a41e15080c01000d418000c0e074551b20400c841068000c1c4102414500021540161a940445458501d00b030315000c2512292510900500084070b0103e070082c0104100c210080c01c0040c2c11101c03501d0001c00f1a400509254040c410060020000030b0030311005c120380c85240c130b0768030324503030210380040b03010703011a03000100f6501a10020f00d840a0300010920156200c40d442070018410050605d401c07800740650380c0d50700003162001d41110341002e40120790041c102200152a040e10b0341c42d040c050340d02c25801115154134180508441420305c0c410180c090800d801d000312039080000011fa680d041e05d07d40a070090b40c8035408000711a008211000c00540e00904180d00c7e0403400c018540d011400003c90401c80c040b200c0055040d40c80032084541088803500c0c0c950501e81580c070701700c640000c0c811046043c08030070000d03402c1a200411980406030030f81c00c0d462 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 244257104 1250 244255854 244255871
    0x10f05010b1e0a080a0509030903070306020d24171204140405010503150a050907050d0b1b0307020325020d0b060307050d0c140319050a0218041211120a0201 69
    0x5010740c0d030003600309049001c403e000642c01d40f0350207150a90881c044050104258480c0c4c3e01003030440c828079407210b43c9849480000000c21480341c0150003000c0c4445020400c0403e22080c40c0703409111207080345c1a00d01d56040030302180811499480d240301c944000c07103a0320002c0c9404041103178016088400f50f0020f404180e000b5144c0ba00405014250560140102c1c1d6011a00c002030182c02a09000d0155103410000d00840410404a40207080042011b01070a41d207040ca41c46030882540c0124003100b01c8004240040e00300c104480c0180304c1a03004500d0001601000c007008201821f4075048d20007880306020150b030380c0c50211200c0c180902078181907400c200e030802d0300e000c2c1503900803401100041e110502140c080120581110045c10000c500724455500007404c1c46420701150f0300b120408024002400000650603100c248241c0d142c00300f503490180e820142034000c5078010050941c440c09941e00c1e5120303031b0802142c01c05010807074100788124505c003e0f0540040ca0a40010307907680c0441c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 244258354 1250 244257104 244257127
    0x1030209070f0203310f080f010b1309032f0708010e030a0804020d0c1d0a110301061b0c06230702010503060607170315010807030605011d03010f05010b 67
    0x4650000841d05050400c000700c988040d40301d0041c240e030000c1000c0c5040c50a452041001c07405280b170164501219956030b00d4001d0080d422859015131500b5105911203044040014031942425140060050229251102400015106405040301044903507024408580c0002c3d03208010262070401e81042c1d0070b10000000e1418515a00184c0c40381c4c1403100c0441c9000002c0104d41440340545480c0981d40e40314004541f100c0100400140258680e1200140b56644104070f040500d540c41d0000c0c1858451201c1c0800303450300e1500c5c91400650070001003113203d0107081008241d01100060340c207050803540300c4252840140e40603001041000e10a2498044100d1100038092003151202d4140501c2d50002031250100030141405840d00140035401e121030070480401c403800041d000741d942e01c0c0401a44d4041c00b202c007030b001c0c08158620301140c0c0d21806806090705503041a903d0780700d02d485424035007840c055061240340e01075607101403148100004e80181800b801c103511031159620f0310000c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 244259604 1250 244258354 244258369
    0xb130506240102070e07050c151e0a05010501080109020706092102010c02070e010e070908010606020c0a14151806030a06061103030115030203070e120619020403080708070615030b010302 82
    0x4a0307070440d003003201c4c18010310204506003a044010b915043c1e440e2503000300e0840c645804a00440740d03814411041100782000360410034544030582003c0e04d10382d00c5e8052010207495003801040d0200d801c1e42d005118002450340a0415140100008134140c4841d0716090020f4009040300d02c42010321090f0102c1e41074090249400c48001c030320081c1007844c545007040c5a5000c041c001d8074511301259020a140f5071088000d1000b92890f50f0082150661398440a565148600c1c2c3c51800b403040c66000154900c1034400c0300920b03e0010301010710100000c0c00b080b1003540040d103084e20001803004030f551540c64400142d84140d000f0100094030702e047c0310016018841c195034801c1e107940700300018060040d00d09600c015085d958103016860313440c2c4031001e4403441203103c422034006a4010756104100f10001d0018001c01d154010b0551158281840d00182c0c4128000a03284090400c0010005400b4034014400680140b07800200341411011700f12109500c0c2d4800e4a010b0134240c01130055280142 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 244260854 1250 244259604 244259671
    0x807081b0601050a0b0f07050f030301080607021506030a12230c0709020a05070f050a080c010f05160212090f120d0e0d2013020a1101110c0601030b130506 68
    0x3503510021350b02d01074951400740320b5001e90a19526002c00d18000304030003004a198400e800c60142d9483e5170315081d407544c0d03407601115070700010300c203441c20300442180201060b07020ba10003801905140410380c40d2001c441c5d00702460001084102140c14100401442024038555405c00c0410303900c55443e4403151400700241c100c00207041c410419500c9040e00b20741200e1103aa4055007004200d801e0781030450606d052004090816000040c21020200040d44945010a04c0400030420fa880b00c01102003910f205901c10409030380015940b0f0440b0006030090000e20400400a10324010f01e040419042001031a00501552000481c400b0864109900045089080d2926000c01040c0d858001d840b045401c040310307000021407100d035110384070b0780341c131200440844000350b40d5041d00301c1000b411a140140540c00315440c05940100240030001145e00c58809071004119a0342140c403403012401d030107094002c550b11000d081400084c41404240d1164140e02e801447c030382c0b000590f07014030340c101c039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 244262104 1250 244260854 244260859
    0x1b0d020a0c1a03220614010303080702070501080a0b03161509120f0201030b01020a0203010516090603140c030603030705010608070f0504180605060126010501030e06070e010c0807081b060105 84
    0x25002ca8080e0081c0a064983c001c1103070100a2030808100800c1c1464220b0310000b0b0310003420100c641d103001c0503521060303040b01d01c2a0740c0c400d07169494060880c3c440c0028050603000494503000b00c0e568000301d802011140f103004098642c42c1041c0b41804003160030f0380d40220f104010300b000c1e42c480b05802082c01303801041741a49410050f18036541b0704007038070404d2400a05040e81c92000ca58264401c020b1480c1d07556000e40200914248001151326010041c44103800240340384402041c0036100c0d0054500c1c0050001e0912820b0700d40706952002600018091501444180000c5021403c240107a00c01401ca400207000624100800040c0d200169040240507600b05501c020b41120302c05420004160040000207030794681030012a610412258420400e481952984040600c02d400c807134100c1318241c808100c6c041203079458640341d01c003c40703904010801ca5003054040354000c902110001c1e2040c42181d192126642c3c907114070340c0060344c0610300e00c050015005010502000441c0c09446d08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 244263354 1250 244262104 244262129
    0x6030a09050618102012270703060903020307021009050f012d18320a031407030b070201091b180f02040801060e07020c04110a03021b0d020a0c 63
    0x80301090381c2c0c440302400200461980c880a0b014145c4540c0101c0e14017600300002d690380e94810300c9101c072007000103413103103920707107807654480c0d00f074000a0000c0e00d10a81d072000c00b600c0030600c0c50b2030320001404581c000360294041000401e005a8600c0c13059400c2e480e13a0b480d607104013400c003010b001c8060051003000c8e0600c1003040c5d8282c403c0c081440f00c03241d20400c40c10903d0719101200400c9480401941500c0c1c0078030b40e44140172812056076007110215107080d5440007003004910800b0409080d00c0080107400a22034081440812036003400603400801041c21203203102c1c0d49583d0320903924022210000182d40d50900c0344200150782001c0b490400007840031103012401c0a10b0a001002040031030fa451968903440000faa6003a501518003c11381d8070004c01c000d5a840754420b03680f6204840850041c0280150310016151510900700342000800204d424403d0100080d00250700c414422034000a4562401d483d072001008105681c0e843c1e40e003c1c111003071251610200309501e58200b06542e441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 244264604 1250 244263354 244263391
    0x6030c03191412030a0c0c0816030314040f02060a03110a0903110a0f0b0a0e060406090515040b190507020406060f03200d0c090305060a09020f0909060f06030c06030a090506 76
    0x2907a800e0b45e0708103031000000034441140d02c0c020744002c506248010301320540450346040250307030711445440c506d0294809101345900304501111800007203800800c444a0060954050b081440c00780c0340c50b03e078600300000d0701404124861a40d0b0404200c03440061400b0000740100003440d411484c0c10002901c041c003030700d82000030031054404140224044450049540719800303109650003442ca040c09800c0c0c0c0e6541d070f220b800c000e007148291b010701802007154020301b19100700c881049500f22586a207040e400c012045400075287c0404407107a108100b410300141000d691240304d408000d00c07064449020290608030090180e41d011f1003001880f08110a4407043d002ea0401140e00403901140700055a4502c0b420507109d228003034001801c1880380e80308000303011810f0360040c03880034004c891680302040407008000b8816002c80340fa4000745c10460218074542a001c41180d0000070081c10f84213080f4105001c10269041126145003050711110300c0018800240080da07005075030b00c685c0d081c0008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 244265854 1250 244264604 244264633
    0x9050601150203040e01080d0806060403170f0c24070912150207050601090c020c040903020c091801090503071109091207050102042612040f03080306030c031914 71
    0x10014414211070150300c16128a04038420320032200034001c40100354295503142c05134140c2da1140030805102040e0f95501040e5680b030810142c4085991041c0114100780e801c09403007078540c100c800080d414034801c1c014150152410b05c440380810940c0d181140750340400540e10841c40d04007602d00c030140030280c1d00911442d002031008000554000314190440d40f0003d095900910807400041c0290281c0e50011809000d07a400120b1a20880d070700320307043c44a103101080200caa8078030004016034414450141681480a02103a001c86c0d0b40c6e0580d0890011400c226094a1400004880d03a400018100081244160402c1102101502d030f502252a1080700d5541c1c0390020403100603000004514a0300700042501101d0281c42d0b1486030450100021462559400030010001ca541c010100c3c0002140e1400d0140c038110740040000d54501840c680321a42c895101414103600f6000b03032103441030151002c0040c3d449801c88400090910061820100c00300c0c014200c0854264200c80c01403410f03207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 244267104 1250 244265854 244265863
    0x60708091b0d02040905070f0b12010e0702070801230a05010302090420030106061220030a0e070812032505071e0b010602030d140c04090c050403080408030417010905 73
    0x4510086501407940400180d80c00c02e041d03400030340c054107042c2d5001c10400041240c60841d6000450084110b4860440c012070f40100082c442c03410040b00010094543c00000c100e81040841c0191394080f500c5181e8a801e54401d00c1e803440c140d54941003403440810007804419030114001c00c0810540d411a030001d04103490150002d0412504410340b401c2d0031214907803413804400c008000f041115624a0040c0644990001d0140424502929150b0306000484200110010004142d01c2e503600c148030007004010402d03442d450b0344500240400d01860030011076500c14010a85c4584a10386038950181900000d43c0e03020078040d9400c08503030700300d8000c2c040d50744c038642c0076810342d4411103000c139103e40380620070102900003000c0100005050307402200a1000701200c88042c000b0800c45411054405426540c0300e1086100b000200030168465004c9400014903103000c929107076907501d40200c1e81e0041e40020403607800005081180010310000c00d03101d800d2240c0207000380d6030030361107031030302c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 244268354 1250 244267104 244267123
    0x5040c15030e12030c040b030a0b10020d021f020708040e0103020301290f151605011a031504060209060c1b09010b1803010b03100615050403120e0102031b03090306070809 75
    0x280f40c2c048081141c036001903040e10301800700780580c6070b2689005400b00c00549001240107011b20b482e142000d98003880800c803a213a00c42260014038500b00655000d040b180705006911800076800d10041d80003880f018003c1006090002021096504500415084800d0030540045490403050054100c7d01d90345106400100100c40f003540ca41a0310307000c10b0b0020306903840784800003400180500d201c80b171003801e2468240a18002c2004401d81e205c88071a902103056903941c1035100c9481100c10300d2080110f10380c058030070740d03000d8144400d42c4040f44440e00b00940c1045c440d0003004200c1e011130003071051034640a10464480384294903250544203284074012500402242132480cbc54800d4a00350084190428090111000047c0c0200300e00c0041c423480c021114140d601d00c41e9415a01d12030303000d45054907040580122001c50f008819181d160700e500c1c5207810340c041480a000080d444195102d608600e09020b10340d40c0e000c410415080010007804201846482000c0c08038503440020303004074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 244269604 1250 244268354 244268383
    0x9040c0e040305130306090311030c07120606030b010f150302030609160c08130e09030307021903032003040605060d0c12080f030c09131a0f0d0605040c15030e 70
    0xc0a84450408a406104802d03504180d000c0d10780c40002007042c0c030345c03041075118001d0351030200c092400e542280c1c8900c614589000550b20100c0e05000d00080000c9034a0864460540000c0055032690f48008840c000d0744100e040d80036154082003030341090a2040040d184d6458210700c4c0d0b14012000070100a0050101c0c0030704815840b61b0407889000b4503480d007010b901f201000e40c880c054507100d1030400055014030b000c28404100450181b01000003903034080e80f031a0f00030345901d0048500c10146000a0748066007010340b9540c100000390034000c940c01415084407140c6649240c241400019148080c044500900740c040b4044040740c2c10288a009440c184404454240081e041030303604c6004e6101c1801d001034000007401100c41c8044002c01c521042a5031070205c0c8881c5072810f0040b2810307010b42d0403440d4501c2ca1109080d01c2c240d0360810016a0040031011659080d4407001c0c01c031003044031308407043c0c29601c0090200d0300c650b1220382c400c41c00c0c0c1d28050000c407003c0c014841c1c444000000405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 244270854 1250 244269604 244269629
    0x11031611060c1204050f04050c12060a21020a0819080c1e0703121d0402030a0e010f1517100f02040314010507030507030614090702010f0903170609040c 67
    0x11100d54803003080300d028030350b55022600910229500c41c8100d601c5880b43c00d114944880d44410769007054000c842c4506541d20b051410102d1f416038106c4481c0c001403003603902901100010501c400310b146900c801907069000359052039510700c14021005c1486c0c0158070f4036480840c01c155981502d034290100a82d1020200381c40c0c90b15005051314003061841000c04000c0900c41110111000080001c2228000e00c0482c01010f00c904050701d0780d000c140b1000c2140c0c900a034900c090790525030025504003405075030004141d4940b05101d402c4582104a034507486403140466181101045900c801800300182e0301e03031142040c080f02d50b503290550144900d04948401800340c9042042e415540110707084140b44820702450001d842c002c05003180d46d200400d00c1c0c003020851081c0b292258400f914030072414517040c04140c2042086c2800018448801c540d200c0c0c90122804c0014041c09801038802c3d00c0d403002c20368048a0483c40e00400411940c01004044100300204d0b031942c0385241220b0b0340c04c1c800c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 244272104 1250 244270854 244270883
    0xf050f0f030c0a03030c051608030706020c0a02090f0f2401080405010b1504030302070e060d0b06040609180606241b06050c0307030e01060e152101020a110316 70
    0x2820b00952101180d070100b5980800018550010303861110603103d03d05896910024000c03800407001c9500803440c1a60041c40f01d400010107950041082c2c4425000302c0c0c1410703400e40d0000f408454215440020f00c5003400500198111126000d5000041450f1a01c0002980014030310159807500788a07041080c07060204080c0304080d0f00c020103101018042020f107251246640c02150311900c0214010322544100003104540c04400f5802100002c1c201d801100e06c0b5120384070004409003145502a507034900010360321010f842541880e045841c0b180c8400a458200003044680c070b41c1c00002140300b151812414030036511652003d003159420300748000514400c440c1c1d40000404001020a417a003c140250051014042c52040103c2d0b60103201e40c104a5115078281c4900307128007a022005540414022403025644080e078540c00b41070350441d030140400c0d00403181c540d8001e041080e5400901c15034115807180b800d07405002602c000310300d421203008842d020803000020140281000381943c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 244273354 1250 244272104 244272109
    0x1804060806010303020c09010e09030301030609060e0f010b150f040509040309081207020907052712100c0e01090b031306020912012a0801140315090c0405010f050f0f 73
    0x480190058104441c29580c40b4034002e50f980c1921801981314804001c0006444880708030a01d01c691400b201542c15039107903680d140f025082c000d80c2195400d03200e42503180e180108210f02010072800384008250b01d0580420310131207030003a001c18071883d85c041106004004240f811501164000e907080019a55a41822140c88200350031002c46405102c040d46074034071410b0043d040362030084030303010300c250bd0300d050650310740c40f0b000b6400c4180d4010400440424441d28200d24120101030300c0c411090310a0401d40b0705080501681030100350b540c0c0c140c40182503004078080346540c0b081c28030105150a08a01810360b0000500d19085141441311001c01c00146030182c6c2c1e542031003c3c0c00a80342d01c1ca58054035003e40b07000c1041207004861001052400c001851003000c0301c40c00e80d2101c3c500c40c3d01b00221480021044c0d400942c061141c1f105883d030002c5a2040c80744924000800b800d5203840103000c00058400680c8a00b280343c3c0140c00c00e201d40e0f81e60441009184004407140080807015802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 244274604 1250 244273354 244273361
    0xc12011a04030218060406120b0a0e0f12040801050f040c03060f020702060724020a0929120f06040b010e0103050a0912020f19030f12020d0c0e01021e031804 69
    0x2c0290804140100c0400084a80762254042d0700d0482c0d09201c2d56031209181000c90b0703915000601403000c50300108040301601d034403010418a4403015265101c1d0581d4516150040e5051032581200b000101000204428400c058210700e403030105000c241001e89441940c1c0d44a4000945465500c0384090a0380c00e06030304440c0c4659018040c0c540b01c8565082030302c500000300c1c000c19100c0c1e01880c185000e0914038400c803001c0307900c40d441c1c0e010140d04042e8901c0342030b00b00d9030000e800a81ca401000c00703000301d528080d00c6140b0400a00c2c068503c2c2003442c0607030519000d004640120b040c000c2e5651039030b8020b01c0d0144110800e10380001c4654401c0c20750341c05444103040c00303000040d014004549581d03020400d0006060284121080c840545003480360f42c00080401500003800c040f03100b0f04540c4501400714203000d0040b07026050000303402c1c1c0c11049503580c0c00c10708042a1803080020007940c040c000c06441c101903218071140b602c80703004415103a01c9030749011420000d200001c4401e83e82c0da0750 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 244275854 1250 244274604 244274609
    0x3031805041d0f0718020901050706050406020405120d0804060c1b03030b030705060c1902180f06150a0e0603090708120d0e0735190201080c12011a04 66
    0x20001d00014035002c00024841541c4405200c0358018640d6011214000180107400c0b100c1031055410700d0405099100020340000c0303007003070410000708120710102d0300a004150145000e2a001a0399038609002c1282401552040400030f400a00280d100590400b5443c0c0c0e0040d009800400c3e040031850b800c076105050348500344102030b803c1803448181941540100b800401c15000c1705c0600391034500300130140c0140001c08bc60355008501c05c0c08044c0c01e429039810340f0381c070141031544020000003200b841040d085811030316052601e030800840c3e05c0c040100b40c00b58a680741c442072400e000c8800044c110183c242c0300034003e04000000c00d030000010048100144100e03c02d4440480e02519a88401c1d484041002d60b0f07641014512064a200403d815045039540190384018180c02a4a084110761423030714040440040c9442e0022038905210000c1440c40780d070745120580c115440054156100585141f034844014880500c00041d011a8241903e000d40d9051441c0d60510740003c200340b1854 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 244277104 1250 244275854 244275859
    0x60f04030e030f01060f060c08042102060f0a021506031c050904020a020705040f1103071d04050c0901390807050304080703061a0d03050d110412031d090103031805 72
    0x56003a08640f90041d0300040603100d1941e4400c2c00c2581d106011070302014100e801170700b00f901c00c100030050141032101098518400000003504544c264000609503000740781c007110392240004016a2840d4180042c0440c0c800c00800320713140c1e00304040825070b601c054185442e07001010b100c421581034040c030191070b89000c005005560b075804101c002074039065244100c0d4051070520407a000241e003070f0b0007428120b07041c00300c00a065540c0e000d021240101c1d0f40182c126428186040c0d507501d03071224010300748100303800b44189980b102000c00062070001620404041e90404160072414140b0f02250420160002d49103442d045070141040051071080c0d50b4000c0440c4130004d80001c0068010a02c00c00316801072004110030410f04641c1d0103001c0030061041e61140001400c0c90020340514081c0100003480e02000841ca10b004061010a170b0182d0841d5401c03028420300b44081540c0183d2a4401c0007140e900ba62001800c1c2c404505010418000201130001817000345801184281200c0d0050200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 244278354 1250 244277104 244277113
    0x30f020d031e12061208031b0409060e01081009050601050f030f010f052d0601030e010f09080d0e0307080406050a020f06070513060816120902060301171c02060f04030e03 75
    0xc1d0b102c05001940c10030144807030107062642c001101918107003400c0105400280c0c4a2442d55000301c01d4120005207403c8208040e401e0001160250540c0300f26000f9184c40030700b20000d5410142c0c0305190188201f05a1f020703504141c6200d0000d01c0100340b07141103ea040d41e04503074049145000034149681441e008090f50700e0000e4080c039902103070b04064042e494034080b011b4805140840800060f0742044440400c004240216005500c658444090459008000102000301c2c1101c84199110343c842928180004503440031415554814036200a08030340045190503426510700341c49001314400c0350244640401e0f20740341c440c0284807000c20803c1690070354036145400f01014000b0741001101203030b800340c440300100e220750048207158061451503280413400b82020008035414440d00c0d04200402e070711842001d00580718200514083c003d030781c4940560300c0030341c0403c03031420300000307100d000d00320b0f980c190361400f50340102e0440c9d0810b5403a800701100740c0d07032400c068035610040f07094140c05224 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 244279604 1250 244278354 244278407
    0xa0302061606060518040209060d020d050606010201110702030715030905030c0d020607050918090304080304090605100503040317041a1603050115140c100204030305130b04030f020d03 81
    0x512198601240c2c0c4514410004691240d080c4090164104010741250b81d40d10b003c02d0151406180e2664030090043c8403003000001036011405e40c860380c00c0304446503170020050040320340e028054181d105940e95291418400e2640009a6030342d03c6108901d8400c0a200c4514541c600c42e4001c082143d1304a0212983c0307902482e54070b65229005040ea10040c00340c0004115914451412140b081000900c03500004040101040c178204c40940000c20521080000240c064000c2c40a000142a041c40c0040ca0034038000500c00c1c080d84c00018402009070400070000001c0d04144810800c0d229100e51418503a076914128903154450807808001c11400001c000c009101011001007140940e6818030031640d0b5101141800e000d602c2c0300d04049806c5000000f501c024040181c030452003040100c030b105640c00802c620483e8090780098000400010700b402203001080c240d07100038103030340030399a1425295031944000400c138810300038450010441d01106040c030610700c10084030709607062841d1165 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 244280854 1250 244279604 244279627
    0x150321071205030406140c0f18045702101418010e280c0311150306130e0a02100806100819150f090f1103090706030b0a030206 56
    0x4101310303402c8a8030381c1010200303c1c0c1d140c0c101500d00d004411015019007030500001c0004015003180482140042c464140007180f40c0e11401006e5840705441c418072044642030f00301d0901c0e0001411711510040a80c6040c0150740d4001001481106240500030110507100f8001c03070508085000d48241c2605000d5502c0f80c0d404504c404e00d0049040e40c2e403d0180080f50101c1032300340c409280c2c0e105075503000003030001c90700da11070801c00c840d444031054540c03055100c5a9801000215680094898a642008141c218240005100300c90300348091407c6c1185844c00014041d43c602d00e01507581d040d02c80510319540340b0100102240c46074000e001c145034680180c0000c0c01070b48112481842000d40b0303d02c05106c140100b07040380c002d01a148100070412074880c0d018002e810341c103501c03000c000c003105030001e88540119040c0c8003600080740c01040e284900380e41c3c0c6040e03070402448149901e00401c2031109042001510000300c40c490700f00402c1c5803044600080803016281d101a401840020300b010002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 244282104 1250 244280854 244280857
    0xf1101090503030609090a02030604080912010212010602250b090625350c031b0c010224040312021c0b100302090d141c0206060108150321071205 64
    0xb04811788000441e640c4200b01296558000c1d03802075015040500031601040d0102c008142440700a40f031601188d42c004501c0d800ca03401410b0300110210898014004550306214151403003201c81c025030940b2081c0301400707071022401e00c60741c2843c1c01c0004410049407503a01c1580e9098018520089000341c4441030b5000662440c00211244c541110380143d9103ca503000c030141d8410700340c9035841480c000e40c09540b9542e10000000440748404d00c0058003140c003801c0c1c450642c0007050042d02c20406c440e070001e07142006041d25925558421000c040082503001c1c03000783d002e0b4061626000b096140c181040082c450395401e4280030a101c0f00d11555440640c00c401603100064400d007094911400c0c1c220220b0040d001e156a00c00c00906004000c40c0410071a424500f4006040e07030340912541e09030804440a041d071000158000700b080090560704002039650224030065842ca181040f0780029071904000b07400640446128007050014143d508240c0e04056072100007080050b0300300c04080d049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 244283354 1250 244282104 244282111
    0xf021c1a04051e01090507020d1808030301080706030e030a0507110a031b17071a071103010518060a060b220b0c01090c0902160201030905160306020a0f0507020a060f110109050303 79
    0xc2801c240300021720964644507140c410b01c120350241080d05410441120304031259800442d0380001c04001045000042c0020340c001d0002074008d04055280c200c0207816507032414558409a0130503c020708178190040c040343d8856502074480344040784204000b030141c80c5541c00142c41d02c80281403915102410b01862004e4891110380303e0051603038100c0e010380d0b40045018440300004105101c840c407408403000351030498403550180018a503a803021a003144e80884980c0548840b06007030305680c1c44240035064200704500818407006083c9400103500e88105102c00c5a10121011090010424100150301a01440600c0c2ea5500e0410905601030204188284c0d12500e0011700003450ba11039100321004d100403051a521601020740055005181313408040c1c03400d0180c5c800d00b1000d07000d0880d1342800303141f04207030050300c6041c014401088001c0900e40300051000400089025999510a05007251030a2800703507880031811408a800340700d0035008071768035820701c02c42104110f03011010f5880b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 244284604 1250 244283354 244283401
    0xd0c03021b0724170f16260c04180e060709030f081b1e010506040204050a050d031403090a060b01050a0503190204050a03050c040f021c1a0405 63
    0x100710036504101e4403010544506403511808038001e005102400c0000460150941004421120112030540a14008039075942844601d84204042004034100c0c00c071900c2c03140d15206082c001d0082416950f44540c00480405180d10000141d40116030012180508460f2454000406502d81c811b00a011900d050f4a03040c02140300181e0b03050300c11541d04080302d41140104100040c0382e1a41c104580c00044c01c003110894201c07242c0782d8448100030b141d200710713002c0d0525246100091081400c407a0060003980c480e07401000204056652041c8000a40d001110101e0501d041d614050711000c01c0b42140126119010040004034503020695003c40d600420061184c03824090044441d072260080520201c0d0051001c1010071407412120a00101e0508005290685a10000341d043c09540d00485055205080c00207240c240340c0929541c00b00c502e041075040c144038000b8000b10062401c43e41e901d040ea03660070000070f04403609410400500140041100b030412a6294038408100d4102d80b6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 244285854 1250 244284604 244284637
    0x40b180a201804021b0c0405070504050d0201050c0a020d0807050f0a02090406091103070b0403051204060e0108090a02090103060203041e03020d0c050304181413020a06140d0c0302 79
    0x600c0c00d12003841c6150720140303840e0a501c0c203400c00510612a00001d81081d82041d400e100f0314502a1400341c0130000703e50f5005c01491820390042c10042542d02c01440340d002c001c8180800c00461301c2d1489009400742c3e09003000d90321030390720341d004178542010008040c2d8001c0e100345002042c002d02d0300041ca45030b0301800079034010012000c0701a55801200d000290080040b00018020481592007400b00340e00c40c801da48644400000080c0c54000e554100700a442d2000404101b04070040128032101081406500d0a062030b200e070207040c6040240480b03041c404004005428040203000941c1550341c000c00d500030b1541c4a051000003500304075000c441c1c1604c0081c5d11908002d1440c54002540d60580c0207203c2d04207601011120740b000310004444511040c440407403000e5a0b103820700c840d82c14504002a10480354880c4e404030ba0f901070310081070030300010348440158488200c040150f581c1c0d410720195101004282100314461845521f8100746013204184845030316030024140f00a0036102c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 244287104 1250 244285854 244285871
    0x40e071707050d0e031308010506190302030a0f050f01060609090f09150b01051b01051e040507090c110a0c030308071814061204030804020901090203040b07030b040b180a 75
    0x8500c4000103840c10008614140000c001000458104d0382004407140d080d0b0b0700300401c181c2c001e00d40780302c82c1d04800e00a9456508006a6092098141c0d070800038920303801114919640100e5100c080000e0080e0030000b220b07140005100341001b11030645100d11008010140d594200107110351098041d41001e541443c6182c3d603010154015070b590190000e494030103c0301407000c04001064640d1106061040c10720142c01d01041c0c0340289102d00a005001050381e2410501445050580740c940145100303403241408041140081e203d42130b42c041c820000f07210740c9125000d482c460003c0c14070002070f10074003004104018480c612039040300d01c01d1301c6400f11038a6202e82502c41404142980e50180520b41c420002c41000c000c170701e03170041c00c0905010300d04460f2107840480314904590075404540d20809000450030310340b05c2c66004025044045056007495601e40e03644200141501c0100754441410740507965850740300c85140000280850301194901404000c0100e007194052b0a1a10b0540070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 244288354 1250 244287104 244287137
    0x4090c030c05030601110f03040303052203051b030c06160b0703180206070c09020f1213020108160915120609020f0f030414010c05090f1918020d02040e07 68
    0x9030549486540c035024150361360070004564850001001d44114452040c1e00740b008141440100b0195001c0d540b002d543c0c0b000c00000c0c0001d011705c46100c809034280e4920400c049800130403003108590000180858003081100000d1401100b81021944600d00141c00c401c0d001060003003086440c03103001c40d4443c6d55910b600c140c0c201d030003003850000c420000460310701c0146001001003840b2481a42c0042c40181c43d108194100d0300200e0010040ba180018010220002503482542c008019000721004824660000f0111040580404200308600c446103485d2401441c01001606040340f441500305940c1034024540300c01580da41c3c034003901d0048049154500d500072540d62001e50005a8034105003110030306480e920040c425600484645102440814203000385003880030140da4803a107503e00c050030094000e411001003440740540e80102d0300c8560001d80050210380300124030b0754084201c4140c0601a10560701e103c01440e200040200d221b54800c0b001c1d030b01a8105503100d5001e100107560 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 244289604 1250 244288354 244288361
    0x30b01060e12010b1f0302040b030103030504060809160306091113020a09050609030a03140d020c03130b03041a070c050304090606020d0809070b0901050d0c0309111e130b1504090c03 80
    0x22050340052421a440b021030010322480407110781710b85030051800c2e5540c1c00400c03c41d082a0011400903100080c10082c5560041280782c1060008014002400c102e030300980c800d154504c8004c00c01078440140d2818040b01c021242c2440b03102901c28011310307020000e4000254021242000440d030910404541400d249055440c00039000d4003c1140c01c085490948518032400b101a640340810041406062810300182c0b803030102d80b500071610781032191840303074806c4125001112000021300410011801440403100504600040c0d55680d845413001141c80c0868114003a00301d120003d00001c0740300051740000c04440c0142d007560560903500c0382c1110505020b940b800e401364407060090044801030f00042111640506003c0d24040c2100c40c0e0380161248480c0107030110b0382e1401070b0030034000e2140080103e400b044451a12419440321030304030201004400034024492403c1541e8160050f90007a40340c22002000c07004d2944002c0c90344c9500340d110340034840c2c8507400c00030041c102502a00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 244290854 1250 244289604 244289621
    0xf0602030c061305070f150207120201051815070809150a020a030e210609010507020f0304030611090301050c0703021b090c0304031716021b03030301061107030b01060e1201 76
    0x100503001076150300c007010303c00140110040e112400346200010b02090804072035401802032010180c41c0d82c41e000d0000e030420481d40d10040e050740c20800c040e40180ea1110444001d4022440081c2541111401203001d1040c0da50031000552400103c00f4240065240907040418084800c0c07542e001d40401c000350300313020342c06080380542d000300104000a80a141460107406000e00111180c400800034a8196840c1080085c0181c212500340040d4910a006072503201ea032500040c900700154411103546ca105600c000382045a6981c2c004444001017411203280342e200500070700c158205070711011901d50140354100d02500c0344451400504110104822000d180100420070681c0c48040f144103a600c001c00413130400008448082142056400d414054140158080741c40001030318040e00d0580c40340d54940e883c00c440e42a9500641e000412281940c4e41842c0856185650b4010545091040e800080c82c0704044d400225001c1e0780b12101c0d1000310000c031003a81084941c00c070185d00f03d60650303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 244292104 1250 244290854 244290877
    0xf121205091005060409080f0f09190e06240a0c14030301060810030f0303020c03070501050403020c13061401030b0a0909030509090f04170a0908011806050106110a02130b0612010f060203 82
    0x8c2c00100000d848210282a4844460350301529040c0d0140c001004a0b58218040b4502d1004c120240500003055244640c4080b040e10100c2340c0d1120600030400e41d441c00100185e50120010b40e801c0487c0c4a0700d00810011740c00a54192100c0025090300d46039042406081c000803448000282494a400343c0381d030403260480c0041004500d42c3d01d0840103540402c00d010381d64881042480c00088003440780d90300c0342c0d0203a40030b413070709407843c10811022140003420210f141e81484424000d020b140740300c08041c11400d00f000140510181c0c0418000f4110b0340c8107400d01c0b443d050b4030805054114005200c2c101c001ca800f14034540e1108152821443d05440c080e08181448940c20002c1e4495402407941078042e0800300e50b03483da510900e6081d203843c0101d0980c0c03030918649200070001d00780203450241c0f4a50805211900d4010309103996400380d06800b81c400c800810f804a03201d00c4036403001042c0300020b07040ca81d60b200c01e50101c03078039034000380716503a40842c0c4542c0004a03148044161458000c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 244293354 1250 244292104 244292107
    0xc0806011427300a110405060f06071214040605090d060b06070f0b090312070804031202160309090b100507020a090612030305060307030f12120509100506040908 71
    0xb400310b5058502020302410807039144000e84220540d84041802d4400c2075001d050340e090303104169580c5007440000c0031102c2e181d4060240f942c0014140745660390192030070303100090a40e40e6000000c079000001e611075a0440c0d8001a013006015016600038a5041c99403590039080c42c401c0e040700e12030300c200e100e8413000030700034000040d4602d000c15404207001d0080001042c05104100010842d5004050490301248240407810401c04208500c43e03100403410061400e0032040e004d003041030100149800100480d440c00141094081d24464100303016a8000710340f40d0344410303a07840d010043c40e20240c2c0030500014001403040303414010f0a00a540c00781c03005180c81d04840050b1169004100c0807a40a40e80010120b010601131061030024040c0d4055203224410b1418041c0c00c540000e0400d5009030401a024004520611106004164800064603820304070341c40c11111200000c2c0071009036400d20b410700181c26400280c600d10f846034140d041040741c455070b040004440242e64010102d030070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 244294604 1250 244293354 244293367
    0x7080301030b0709032109050a0503061b0f041214010e03160204060905090309180106050a05070f1703090714090a0c09090507080a0b01051615090503030a0c08060114 73
    0x2409500b183c10615504060000648030358982d0202040700101300500c550140940340c0180c1d100311207000030304064840070b411038140008030340c6031035004126801101050420380c212102c408101d8031a003810120203a280c1f41c40e0b8014085000c40d145050340c0280d60340d1194016800180309251060382c40b05e004616018183d036419158903041441a07070300950714080007603036441c1402b03003070720855024014580c1c8002c4e1008000301c0a00702c002c42e0b854500c10400500400d9003003411608010301505009496451520f009400921080030003440494611124038403001e00f840514080c8196500790b400a0703880e4416481c1e480980c0d51f54a0f44003a2210204640701450b0340101c440e9407241c64255070294aa16014080d01d0040c0c5880b0f0000d032a1320100034040d419481903020590313091910302c0ca4107194040c885c161054111001c0c1aa001c6602000c010622643c00440c0c0240c2c44001d507516407a02c2c52844000706080007607038010502e03c0340000c01d04e620403645d0740010040c4003030007410b00360b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 244295854 1250 244294604 244294613
    0x2100f09090507051b0d0810030510020d020d0912020c0f090c03100b0309070518010e041b09090b090c0108010b0d090501290406060201060f05060304020d0f030f020d050708030103 79
    0x42c0c201c0c003d00004018007a01620051007038503100007070400520210100c03001c0102144e40080a9440c01100984140008ac0c0040307140038100340d00380001750b184c46c45455818024807400360380b1070f4524070700710303907642009a1407410a03001005602a50190110398083c40303c10b000d03c1d20b606901101c10700001d07040300044406550403100192208084640b10490740c401a402036806216540c00a8402c10080c600205c2940750080346141c882c4603549403410b020001e010190000b820141400345040f503c607903a0500741c0c000c2030a24070a00410485080c0094034100a8401003200c1c06180d40303080955014481c028122001e00e1002881c000e55911124001d000c007040c11507039552180007002003140352034042d9000740700100540030040010000c11048036100c1e40f1510a690400c60104080113940307000c1d8084440a4a110365a0303030f114800215401040400100030507401082d000c00e06138001010a001c204a03002c071410891b10017000e17074107401101c500030f000110070001400005c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 244297104 1250 244295854 244295861
    0xe030a0201110115030302161505030a180c090b1309050303070804060b190504050f150f0102030f030a06031a0112020f0103140a1a0d082508070f02100f0909 69
    0x4248000001131070500c021540d01100081354020750059118451f400c004440c0c1e507140000400c00d0f00c0a0290005070400040d007180002040b564140356250851040d0079482d00c1044221030b80600346040032500c0300038400003081540b41c0f55004803064140d0025600305803082500c1c981c0c1080007542140d0351584111a0318100a00071140316032a85031118190f15000882e24000313010401650300c090829091108481005003141010480941031060000906807049696403055545400025031100180d2841c81400751006490000000300070003d4016480602a0703849000400380304190411b010810400a0140e0004a0320710103a40d0014034040190109100060402040c00041c11000f0b80c02814100d60b000300352a103400070306200c032020381d400194842085030750b41014021a101e02c40f41c6c0c011500e01007044020749101100d080b5481c0c08000c0c080d03500400103135480e2980e1030f00340400900300c0c508900440c561030300c075070700075014a804c440074030340603030b11040118a4503058030f016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 244298354 1250 244297104 244297127
    0x6091d070302210a0302030a03050708062202041707090606020304080303010e150612040201030507140910090807150e01031a10110d05070b010621051017010c0f0e030a0201 76
    0x40407032a031000f0741c3c80c1c03d116904c1c180740aa0081e585031054042c019099910003001300007004160705c00c010a07651000035004000b8610030b03820594214241100000f44181d80001540075a881060400d0307010001d03001042d02c10b917060620070140c3d9510705030f070313640558001e0b084503810901c0140101c0c80c2413913940781d1007a40001e204004030650790101da155170080083c06403108042d401c000c1503580500516800031036514040b02a01182c80032001c55018040c0c8952080f100c4c0340e0395201e1280700b14400400390141030182c445041da980e481e890190307180d4a8170401300d103082c08503403104d40c002e200784071a10002414581510121204001012100702c01000621264039040440c40308100f003a01c2c084021600da603a5100c1040c101100c3c0400164843c600b00410340d8461000d80722400710780840d08108610101d0281c45445191400c00e150b500100424160081d4180d02e1003015042100c80f01103640780d24400c940c80110032519013020400864060340007506450040d441800e50054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 244299604 1250 244298354 244298389
    0x10605090103060b07030302030403171512071d01030b07030606050405010c020a03080a090f0801020c0a02061318020301170d20010204050d06051902070b04170c070906091d070302 79
    0x140b80d40c650131015600d4001c1402500000d5002c010041007582240c2e40c21038141c02e8002e031002c0c40c600080f18a44c1d01c2c5941d41c205001c0c120050743e2005000c0d08009a40140003c0c00f859070380c0c7e4a4007452000c1c04070b824801542c50143d0340d404124141e000c2d20580003a074043d5aa05450103041500541d0b5648405100300c0e003004801d000040442e403480040d04a41d0342c0c940c1e40508a904d054000d0b03620801d0740d084800b15900c100840e04424100090009003180d06840e0191079040410140c4510394031035101c80401e5440c401121200801e90340154140ca1090744000103001c2a00e03580c0b580c8a000303000900100d007000c42d031046111940907100a90310605000546000c0e29107020404041031040c0881d0519203c406000c5140903001e10301141c41c00c1040c0841c00e10007603450b80742c24088040e0015104400c0360010500c10180182110034004180085681e41551070703507504c00402c898415841c001e0300d40700700ca10400d449422801c91182c0c20500030300300075046408000c00018210f00170070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 244300854 1250 244299604 244299611
    0x240610110307170a200d08090304080706030902041409100203100f03060e0d05130e18010207200102030403030203070b1005180a0506010c051e010213031415070503010605090103 78
    0x2c0014032501103c00320f40c2c40c1400040e40b10f003030310000039000c1018a6098003d040c02c0d200d01940028000944140400451800d06043e44031500c400d41984507a40007640349020304480462134641580040300c2440c400d80d02004990207a00741c1484180c0c06441d0814203420142906200c51466005075401c19840703000700c4200c0344e5500c0e802c048100315900c00c1b0b5540707403283d070803686036402031015042040b43c0e4140395107401c1e040038840c0310a40c00c60082c85918400000400e0146000081203913504051800855444030305091121221240c44c4500b407000d01401c4480c00c01354400f000347c50849038117400644c100b49882d81c2c0c1c0982a00300a0540c9805004000c1c005401d580f40500400c584103511883c03069824030350403202c10b44400a0a40b4144003500c00703141b0024400007850710709000c4856290302c00c1100c1c03450301cad070292146d19440320303172110b20942c040188010a0168511244d00700c0c1200c14980308000b14112440301101e035100419400d200421070305001ba402480c40b10310514001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 244302104 1250 244300854 244300867
    0x2040c050d0c09080d080105060f07030201140f18010e0c13090b040b070306050d02100305040512180a05040e061810150501030b0f0a15030209030601082406101103 72
    0x140200d460b07040521000580c500020800003605020f01401c0b41c0c140d00d84035043c0e6040c030001c0b640ca4031403807480e0031480d04001a02d0040c14400e40c040d0b59510707482901102242441035124150003c191844074081003400f8981c84180b10503c9180070008600c4042c0001d1141c130702c208000c04901c1903155441d0b40d00c524592000038190021144646e01c512105c442e2400d043d40002c4c11540310390007541c020400414600e025039a13854030b407480c0c2d40182c5400311f00c940e0f50b850641d04000400b80c44203c5d801000c583e04640180100c1070b076060070025039000d00c007603070386000f08001d550354842c094800f500180e012401c00750b90f0010407000c1807194003c49841c00c0c64442c01a00725022541e00007118140c0c0c0005010320740c6e06020b850300c02c0c2800c403040d03030103e1041d1001030702122040c0302d0500c180311810035044496000340c060341c002c240020f01780d401c1c3d507075078000403078072410850801204260500c19182580d804260110f01a2001074440003404a59420550b4242e01404000d40b071f40c0f0060211 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 244303354 1250 244302104 244302127
    0x905240106030b18160801090b0a17031306020f120f04050904020319050c0907020c01120209041e020403110d1703280911040e100902190b2502060702040c05 69
    0x164010b494500c5c0c6005001c1e02481300921000c0180c01c0081c10a08284107904c60769102041c2c802501c4c02c454610044412590146145200d48604000d005c02d080b54001002c50b000f04403c02c07043d1108040c0c6000b140f259070700c44011300c00d02c0a00c0b54900d8040c40180450304000c40b50507800740c8058102c0b04106100038483c10501c11040c3c0881d031075400481a2001801c1c40300b2425004116400144020404003002a09505103608101c100075408907080d601540c442e081000c8803210340200400c2c859400824802072340c03003404155135a280540300e401c100e0820200c10303100a5040348005114551070198401c02da03101030a4100d401c06d29046480301550042c03801c0c5207000c00c0000010b124010f40c03070040c03a40e2181d0f5800c0c91146140c82e402c0300d84c101c03012036260761010000a0010b2280b00c01c0c0b0015140b10103c891034801c84445400c040795841400b801002604207102c1e00c441413a40f020002240c5490340c01d00250041d000703119620060400d600480008000f9040250406113009032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 244304604 1250 244303354 244303399
    0x150b0912030f03100f080a030c03091214210a050f1b15010902030c0a08090f2d0c010516060e12040603140601020a0b18030d0905240106030b 62
    0x207200307210b5407001040c072003250803401c3d00000414640c200001395619041020b074640a0817100076003800078005080c41054030a904510141c043c001024903440c81074100702c9139021008040300700d9403251a03050180845104d070000082000e4120284c075041082038110303003540200c442c540c440c410034802d401004041d804070002654400c80101281030000011000c0b4100681c040703041d403031041062142540404d8101c40605406080901e1140c80e81040c46141212004200210f80201c04e0080c82008490300340d01d14141500460801c190380d240c00701c0b500c40c42902c0c0080c0c0071504c1003002e10ba002c848803c090701000c1c040c060000c0d1002c0d04d003984074141f4070303080c4008642c0788001505000032501441000c01580c8141002d1380540780080000c1d568180200c1e01400303103007411002480311100c58840f40407441d00d200c1501d80f5410b800c461440907208908040315030340900101c0310410a520740f594100005181a03404403030f480c0000a60003810000081d94101c94441c0003221316100c07000323 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 244305854 1250 244304604 244304617
    0x1050103060b0916120903020c0d0b06090709050a06111603050606180402030303060402030c0f070302010b0f04020a0e130b1806010e0d210507140601090e01150b091203 74
    0x1d00101d002440801001403100d4003d0049208240c140307508950113600201c040c40401141e5800601542c8604099107030070311190b02c15522400f140e4080c010405000845d50040c0400e0303a409425441c1e64070140c03100301050050741d80004030490200440b911842c61480146610f1341500e40c0071b50080c201c507041007101e03001650030f41d019600344459803c10041000c0402c1410086100f103040a60001e5124840540b406110b60713004000b240e408034408088402c1e4040a2107c559124500c0c40d001e8041d000d44031016207c1c4060103070400e84c6007414003c44843c4480e6907141202801d0303400411542d040141c0e03441074891b42d1110302001130307128003000c85071401d0382c800501c0d4a440c0c00400108090103041003940110b58050f055000a402d0807a0700741c00e5240102007005034a841c10701211030340603008029001000c41c03002c00c010140c022803d541030f9254480140100fa40e01d081c2582607a601030302c8440030094034078080080b200700d040608410300303000740300905502c0c840010510b59000780 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 244307104 1250 244305854 244305863
    0x303090d020607020a0f020d061503050c030105061c061a0604060504080105060102070315230406020903060c19050c1507020d032f130305030a03241406071401050103 73
    0x50248801a01000b526901c003402e48000c0148800075620280200314030380c0000e018001c46003100c42000495003002404a450703040360809075643c0d0805666445100303038407600039442c100103e600350414024000181880304a030402ca0507142d6a5440200105c03c5141450b00301ca0040c074443e640c43c400200700800444c1d940e10344031414991020f0844902809450665000070020400547c425014a0184201450004a407181940d00708421043c011041018103441002c01c0104011075004d0401000c0607001c5841c69a01c0d020505040d200707920084d5504055036030f20401725032082d0018400341500c6415139248484505454003400d01c159090030140e04000c22051a0b59407500c603003000050361031840c0701c1c0c3c0e44020121080e031071000501c0ea40d42130000504c00e01101030301808200119406411250360b9146044d006006010005070186146100c2d408044586501000d0900780c45041e10103001c00d0440c8000c0003c3c5030b01440c000c440400551280ea4000d800070f200348d50095014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 244308354 1250 244307104 244307113
    0xd061a040303032403080c2d0c01030902060d0f230f0901050f060906120a05100b0901080303070f2c01120e0606060a0e030102030406090203150c0706020306010908030309 75
    0x75071802030b0a6414454400d03010710641805403050040304015281265004440c90341e03503400380070800f411b240b9020040083e0074154002003210504c3c0030b00e040c007500a90410345511508010045040d80d54851019601203c2402a4800e4a041d0303401310400c4103904030300103103d003400540007896034000d107510000c112680d82005407285503044c901e507001020800030800d900c3c0c012004000c400d0301410030303400340f000000003408584a003a008183c003680d50049400020302490201d58070700c6030814000105050941038a03003810b10400c0710341078401140c040c505503618100c00301c074030640d10383c1c40000300090003040b03848000c0240c010403848040c9503d60078024104a0014241c40c84d00004001d00728030b0030000d908190008910540c0118040b20250b5650b02402e1040714a4140c042d549507040d4400014071080000c654404c03120140300f5401d41d140c1804002012982d020226048001d00f0020800394000401c00d50041da400380050400100041d103a1065502d590411074191000360701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 244309604 1250 244308354 244308359
    0x30506060706091a160c030c030c0605310807020f04020f0307021018020907080403020f01060b03040212030909010b0310030b040b070306170d080405030904020a17010e01060e060d061a04 82
    0x102401351a8000303c281d09003456112074410040220070118006005c000c0020385150402d841640c0703041c0c1e26508100c0a0061313003001e541c110302071313500c1184040c1115560003812001100d50044000130b50b03080a4014280107142c0c0a000c007200302030404a500c181d007044810203040c12000614041e641e41d500400706245981c807200c4c03c0f02c1c03252042c2c94580040000140c0180d1311005215403200c03c91425003110b484910302a4a05555240341208075400c040020404400710f001542c82940200d801c1a842448508219182c0c81002e0059403c000300700c0c018411400d0810003143c0000720124101c4d444d0741d807510381000701182910101c2d40314072a407040c41000c650500442d8048c007000e482c0c1425000d072001005942c5c420441c419410710031804000382c00d0010900075600070303030400350081d50744500040009100e0704080041b03688602501c000800c601c0c0460030391606880c25a00c5221030b5100c44400c0040c0b68012050f0141c1d80e070380314038010a03c007104044450f041820f00c0b412513101c60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 244310854 1250 244309604 244309643
    0x60e01080105071e0c140d36060c05030d05010b030105010e0f01270f0305030703021509030f1b07060e12010b06030406181a070909150603050606070609 67
    0xb07401070002c4080040f071601d88444400040d8041c1221007580c20b048450074807514025651388500340d06610f6a01a501a015095400545070b403441108003400d21a00e59002d00800b01244041d00700f200700740e0a580341841072a00804200c01c14500030002c03a4201400500044e050f11002d802141c41c0300f201000400c8103503001f81b01812095021503100c4641e08070440000c18030b45034210000c8210380e00b507065036541114052080050f050001d0351124940d16410b00c0e40d0340764421401107006204034410100003915115009010300034100c084c6280483d0248070b682250403a060260202451940d07121480030208071150080003140c560040035044001080341c0d10010310300b8082680d06010046030185c0c0d40c0303003ca0380c0c040d038070030000034202010100d4455003400940c1e008020040f01c01461040f604101489845000c07181e5690f01c4440d00c691030441950b28000000003820074840080c00801d0007a00046d0f072080e400340c00e032420000951515425602d0350350007550050382c0c6211305607445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 244312104 1250 244310854 244310861
    0xf10030602071b090216021003020f070605011e120305070204110a020601060e01050a050d050c0705060f09071703030f04050c031204030c060e180912070b070207050f0102030f0306040906060e010801 87
    0x1013514120441c1001c0c1c25a21807022101e04844c024842c910082c00710744040c1c080e9041e10711004c04500c00b1916030100e0719004000f04403c0c002c6814070000070707506a14443c4c062000f1020b90303000e40c0040b07540500a80d002d0300d050700100c0342264800d840780c0500d88200c05000141091a91070350040459501d4118040d01c00900d02a5860402c80c0401c520f2070015007100c100d0328480d821680c002100c1d17a40c01107507a030364040e0580c01095406000148101c40c42c00380c0100c0c3c060201103043c0c0b0075440d502c0c003c18030207403000310420403140c04c20b00c001840c0d14000e2141c1c0c0d07400760203417054480202c15800045d0415000b1108021500300200d0140b040c000c0114480d4041c10032404c21040381109a00003440e84007010300200c1c101055100044c0e48038100380100b03545406400d0a02d80c40300010325009400722012140280103200b914400035040c03800c00c54042001c1c106801031803803d0940d000480c402d80c0014002e0f1703081030710380a00c000080c01c45d2190200500d00c20b54190125414415600c0c20f5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 244313354 1250 244312104 244312109
    0x605030c0d0e1608010606020309091801090c0e0f0103030807110c0a0f0f0f1202060705010209091005040e0c37060305071e0e0f010309060906021b03120f10030602071b 74
    0x13940e1401c0380c28000b86400004030b80c165076049070814000c0d81d500301060001200c0d0707884100c440d400c1c0a02001040250304101081d291031440f90201681c03491030105040109100190005a41d48003240f501c0d07000d207030100d00c81d40c6040291201c4000100108900c2c484682c041100071304042020049000003d907824090003d016600800d42e2500300c54040e50340e10450040d1080c0c400041141c10080c0c00d5048952480c0c018103402d43e24079012184c2e10b41003a9074400c03240035178240381200110000100d603000c510000140130f400c04190300c1d041c452842010180161024504401082a40b010000403000401316a6804140d40c075003140020800c00b06003440501500100a2010b24603800007c200742e500000c0c1c0313901940120b40001280070380310702d0801078200c900c1e205d07141d4184091900142820f16920700503a12000d070800d00182d491062143c3d00006450040214100481604110381c1101ca201451240b1545a031038001c02c03a44020000c9a010500c550342d800c03102c15902d040c100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 244314604 1250 244313354 244313369
    0xb062205040f0e060f0c040e070309061b0c151401090b0a05090906010b0d02120a0f0e0a081c0914031810020607110304081b03150606040605030c0d0e16 67
    0xa43e4201c140d49681e61000540601d42481e484000524840402001d0340c00402c0056840089410084d44c00380003482001000d98245c1d003400c54002c00316500c40c0120843c002d10750348a1080f008103440300a0301c1c043c1c02e46180d42441c1c5900103410700c080194a0380b1302074951040f000a410048000304052050b040e48031b075006107084010042d1004012400d6411149482c16082c0e86e440c500d12054000e1003004050740543d9030300030510140c0aa50741c001d1250702d60201e0b0030403d84480502d40e50351941040c4000b043c1d807000300038074410907144450300c01e164404890301066102c60359071101421408a80601c05661010601d0703412000805000910701a09031400d03c005884808003d4490700014841000d11800c500c010101d101d040080745d00401040b800cdc0d5621948a0800d56221102c0b181c0483c40381c40780d0400c507444c49524940343d50040c500103080034503003440c004c4141c0d210742004041a1b0402024045040001d042d8080ca00e000c0d6000c101518121201c6400e281d0721901a810450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 244315854 1250 244314604 244314611
    0x140910050f04032409120804050307020d030c0302160b09010324030b10060f081503071502010608060604060f0e10120b0f0f15041d0322140a090b062205040f 69
    0x40c00300710306c004003c284403017a2030086082c0d07a07a400c0007482e40c4200b16000750816404000001070690104241c004a8840d9003507565400c01003e440b800aa003a002c3c400d18890f080064005560103548445030142030504451010043c1020561340280c1e80d62096500f40404010403403a0310220008002400c2e047c00e0240c0d000b058290010072140e0010b05550701200090040300351590100550402405103400c1a581a4400c0b58005d003c0c10b000d208603022485060046025450103005907016244080a58040145010000c041580c030251001250701c240e000301041701b11242e20039600c110700405400c1e94508204a001ea10810010200c5000d20800001c0c40304104030403280c064044070403180810f02e00030138114503100c2811003100955904c00040c80b2600650801c2c600305101150412084c3c109a80e9107440a5401c0c805010980c004141c5030188021703050f59001202e680c1380504010b0400c22185900c12a48231902c0000d03011440345082003100349001e00946002c030084d0310003071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 244317104 1250 244315854 244315871
    0x213050112030f03060b04090506060706060605091c02090406150f03060902010e090420010e18040501051003030c20041d010c05120103152c0706140910050f040324 72
    0x90b5240031f98020700341c0180c3c07504081040da59800d02911250b541080041200d03d94580703003e00654010420180280c91080c500c95440030100120801141c000c4d101e034107141d903180d494000404c82c1c0754100510303000c001d8001c0b42c1c0c034103e010b00d0005148034083c0003588961900025101912a15006210b0119501040000360b40c00000700302122000b0303809180a005000142e405d80300000e100c58100506010000d0300346032864155004601550080060340c99244480c001e070340c0a4040640410808074080000404108400d0000c40e00c40c400290140f0742d401c006010340c0c000252291114690001d0800c8030307a002e1280d1106c1199506106150100c10b0b0400f01081005200c0034007001502c0b0b0040c543c40681c1e030440390100c0c0c03c00c4100580ca50507452100f2400043d01c0c400c032010700c950300020403218006c500c0c054401c034640c111a800d11150314108112070800c1c015070400c200c41072002001c03196000d0054800755104206c00c820318001c061034000003803186041c3c0c002c1c0780d00700f00c0030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 244318354 1250 244317104 244317119
    0x11100c0f0f0509030a06050a0c050a05070f0f170c010e0102030601140c0c0a08030c06150f0f010e09070203090102060a1107030804080c12030f09060103030207120213050112030f0306 80
    0x30390300d10301541030034404810024410b48960103041d6a440d0507015000d900810821140d011922403182c03640304026804002034100d8031405a005041c0c0842e03820001c081c00710300a40c880c024024842d4441826120b000d030b450030120040c60711007003507181011880c400380c501b003805804000076090008504619008000078030030700080c81d00700326050000a980c1d21145040c0722000c000c80c005401c04c3d203030b40da50700d0a16030740c1d41c86980d200c05c9a0040a01040d43c40042c9120421000170090102c0c00b14110030080181d8402106001410300200c20b44520003500c503150420f103e82c07100e030050343d100e480f90000607061001c000c207096013075031904010090003810001903400441e01850042400d80d9240340922161140c80606001403050380c01c0046a0030b14240158803d030f2072500c101da02ca031104142683c0e107203428000200980c211200138402c40c0d0000002a080c64001440b200003903803080346c60b500b141e03800e070440c0401040c040107610900d40c210244503950032442c6406c22009180210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 244319604 1250 244318354 244318367
    0x402091603020f22150509120a0b0f0a1109060f09060409060305061905040c0b0a02010f0f0501360b0f040c03050f01050406030804030b061c0311100c 66
    0x1400120308910858024039a110380d040d2030040d12048690f40d56162001c03403030481c03074a4074060304400214010001c510a240103204d00c0f904074454a60070705104c0c13080304004d1042d4940031445041c0c0b00b08401480410004e40601d8060300011000c50240c1c100204040300740e501d404080004540108905003143c1c444d0001c0322014100c02195540f03583c0c0e86000105a882240c1c001100c00c0c0c100500442803004c0850024040c0490412070100d541c1e182c1c40c00740a03617208690181c580c07c903000c410054445c4210041440803954400003404034a414042c00480380d448500150b041c0da100010710080c03200c0d0305e0404550040b4105601400b4808070901c040f000c0f00107942c2225070301e07170b8015006525601c111504015009100780000030340604014000c1030221030001213240d14000016180c1481c4c840d540680ea08001c44901c1d03c0d0079a11404161701014108a4000180c11002d00006502d40d4109502d14401c1e61401094100019194501060a080003600d24030340581004825003001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 244320854 1250 244319604 244319611
    0x3051006020a08030c280503010e0a06080a030c08090411030402120a0b0a240602030a2307020d2a140406050109051011010c03200c030301030818040903110114040209 73
    0x11505035514011a403140362400000309010311100c5002c0d071006e185422401840c10f071400c103101954155100f24954055a4130740c89840c50300c0c2c11040c1d031a00464030403000c0340d02c47c5000301c0c141881d0000700310111307048600d580610362041d4408000e100440c07600c48103001c040c45441d001842030318050380b02d0400308000a0300c4112080d5036801450b00d20301c1040340004100c0300410b908400c10303540d0072000c3d40343d40c440c940c40d40000300305001c9146190b000c18a506104018480341c5030038030f840359091180d00d00107050140c420300e403168207103d0a0680b0341c400d0311013200d6155505001514111600c40480349000b5564032031800d040d8207110f540d920440c03d6040369000c460000d0305440c1d1000660340a0708000d40c0800d80d5081000d0ad020301c0d0740503003240f515201c07944071107a03100c0c1e0514089251401030700c17040045500b0401c01000400c40d040d014100d07440728100c240c0d602000040010b01115403000d030032008038045240c4490903070320038460000300c10380050580f0030601d842e50004070303030301e1008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 244322104 1250 244320854 244320871
    0x9050409020f1e030303190e0d0f030b06090303160302060109110d0b011209060510080a1211070902030f07200a06021602150702040615080105010e0112020a03051006020a0803 77
    0x545980c841464800311940d08580040c060365903c7c2005082441300c0d4841c10145c40c0c1c030504113241000020000107c0400920407030380d50010100911108801500711007000310360000040c4440328172031f5020b10082072420410355802c030f880c803107a1801a0402405a000d00b0140d490103541c00708541d00301088848428405000244185401c030050b41c00c581c0d00520006070616102c00c000401c411035000c42d002c0d000c1c0300f00000a0645c0c6220403079030358203244001840307240e4800c2c0300720302640211405c0314101140350503540032035110b08802c0100d03042280c481f05d544401c1c0c000d1050b01d5401506419011109000c1141e0400a00f100180c0c2c2d001d031080700600090b80010742e4401550041d58501c1d406900911007001007681203000922504000c41c143d00c40d5103001c01c0001c1c290284030f240c4a5403d031907210701000f60301c0c010040d1402d40d0a0725506052007000402104040000e00c020301d03014803d42c038001054103006021200500c0345811040c01c2d5803001501102049003003058a80c0314001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 244323354 1250 244322104 244322119
    0x180f0b070c0306051911070507051005070807110a06031a1009080102040e0105041401030302253c0b0d2309030c010b030105070519090512030a09050409020f 69
    0x140c40d0101c1c0c050025400946054030306030910000d0501e0500001c840060142c007400f011020b0f0000f1403461054a034010000e901080d010483c6007420385c00340d484001903003851400c00c00c25465a00884c1d1006034100e4000c581c2c407014031980d191403402d040140042c0c0c9802c2007400340c1100215041d01e20b018031107209400d810007001925114034090b20140442000035900e45546032121007100200307000300e5108030b041003a81c0003103d220206160490750503030300902020801001111840a05130500c0882880140c1d02046609006c64290f841c501240c92400d11202610030800b004540451711101c00484c800080040b0400d040c25140b4807440800009010700d00201d11042020b4500309190310038820100700400c400000c8003034001c04201d80000d00c003061900d004c1500700c4000700e441c440400c3c4180542c0840160210258507014818146207031542e442d031001952041d007440440030b0a600000342d45131625030104803c4010401501c00380302601e41c643c0000c0d102d00c2c1c816480c0b40180207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 244324604 1250 244323354 244323367
    0xa06290c01060801060803070b1308030c0c03130e010509090601030302061801090b130c0b04060507140f011515080606040b090303041203030603060b010c020f06090f0916180f0b 78
    0x30a50000c401400381c54000c1160301c0c0e07110412a10f9401084003078481009036000540511005007013200307a1544010ba081c9581c1c0d035400000d40c0d40d08108058600c1d44818007449c1001e111041041c00a40280041e0428030340c5081c0401c880c503180104100e225421150040000030340005459400444040401041a0755603c4c0c2034010703c0c840750080c1c03c0e03884250a01c038154400004a00d0b9841c002c04140c1001520355000040521541c0706103c0060380410050011501e00100b4500c02a4000b040d103c400d456015000c0c2521505e010342c0d09150341f048020030084260758141c400f050380c0b41c00d008080307151880004103207000340d00c00d8400001c4009031404090f0750510031200501501c06600b1982c600754200103000307125600046844518042180d18650b01032885000e90650061203012500f640805002c3d00740c00a1000c0e68000100c0b06030100103689405400d4420080320f5002c80ca40d140401000b001408002d0451400c0805131800b40149282c1210000a803140315440340d55680 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 244325854 1250 244324604 244324627
    0x171b150a02132c0c0901030c020715050a09050d03020c010f0215150109031202061509040203031c020405041e0f0b0d030c15060b07060e0606010c0f060e03030f0a0629 73
    0x4049004000b803140150f04200700303803090b00d01800c4403880a0360b080016903800300c81a03958030042d0249510b0b02e401d1040e0700071034501c9400100301521580c5800b0803400c0e030b42c0700824900b54000c0c1007180960400342040c641564811030840300040a4401452241c00380c04860900389800b80c007401e0841c074048a020201d0340240c1e00c00d0011a80a40c2034584050b0800e4000d454450a07201000606070340303042010b0070310f811108280500d4000780614a0551030070415a82c12018070150701c00c41c0e400b4040010983c4d21485258405640091082101d2850300041002c481600018010907881c240f200c1c46507496004d030441946038181455650a1740b20300b0321840c80d100323103050a00036070308001d070100300740f69081c1c040c3c40058400d0500b40444a0000199900d034001211600c0c00102d201e50301d00041041c10f141c0551490050000003204240e0803030300c03400c55004484c10110700c009842800000c001c0340c030805000f45640c1d4a07444890490b8000300d05112400120007282d22004a4441c42c003c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 244327104 1250 244325854 244325909
    0x1005160b0603010e030301080d0f02060c090607060b060406022103090a020904031e0903021206090607031d0303070512010e06010503060409140601030c0f0b03040f171b150a0213 78
    0x4c2d50034100c81e00c17580c4d6070101d10b0350341c00781e488941c00052500c07811031600347c0005500d0b0300504203640d81c0c0d13040840c150140500380c0c201140a132041501d8203200005a01c0f4100103001405131540500407280c01e0400381d0803140c0d0b005007540181a020400c110b01e00c0c9020031100350701541102c00c256551a581000c80e201403200f40705058415a04008008203600a801c01086034030980d109207014944944950326040b0480350092103411030030008407190f2190380140d0080a441100d41208400170030111701c2c60300102c913124003141000500c101c2150316140c04900400088096103174501d0a400001d2507404050001405030b52215082c404000c004141e46205000e00001c030740d45581d69040040e0301407410311441c29945150600032603201c0d00e203003c0f24030994102040103200a05c40d600d48800b104a00d0078054421414444810715500361001d1590100e1340344000d103040701c0040f402400d054805400e10355001d01c104071450b22801507041c0d101c2203640401c401c814001c0050b01d0301242 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 244328354 1250 244327104 244327121
    0x90c022e1e0c0203030109051608041401290a0e100302041e05090a0201110a03080c130506070c080d0905010e0910091503050706090f031e0609050c1005160b060301 72
    0x35030900002244070b0b0382c0000514101d90080005020549408009102c01e510a1000c440050641400039002c80c8440450814100500000183daa1300b43c0b82100c52080c190304214440301c0300b42c12809260700d0650b00e039901805d0b82c0001030803541010600c444e03107020b003840f0090007181c80d030360a0240e003100103207580030105450909008078580318208607100d4441c0b07a02240450100e48000c034001d10b0009002200c0ba038140c40303805003901ca000d42e036100b40d00300003d800c4803620205030200f600d031604005018554400c4004085d1382c1d040c46d14aa05004506c42400c040054051040007103030f03880030120300d210405980d4107882e91582480c00301485010380005c0501030811410a40d4010001490350032030b03004070f05450081d0307200c1c0c00886000351548258000034000110602c0840d5809480c81e44500030f08a90010b0107525903600400e8981501040d90b43d5004500e60761618100400c040c3d00c001a2483c1151601400804030110100901d0002d022145180b0007e141132303c0c00d50040c0300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 244329604 1250 244328354 244328411
    0x91008061519060309150c091a0702100c030f1701170f06180105150934120e0c15130b03010e061c11010c0813090c022e 53
    0x4206440f040c000e0003810382010201c80407504c0441014101040d446400350800c800d40e51890b495203410801069a05d14651103c10280100401001a500e10162501c000e9a82d195111801614100609003025007103048003030101c02041042400013980384d15040d2540707605550850240ca100d05454481400007150071031140c1c60900c420a11840302c642240c1e00407500030700048d074580c020102c001d0402c5100030782088082c0f02050050100080307e88500c201c90315248040d100c00036981c1c860305000481103001c41d1404580040210316070180d10f42d000700220050000d041070360081207003500b81c02c5904c501c0280205149001d0355000d4041e400610035103e5054482d40c480508c4c06035810155146881a007160f418072030b0070724021000b100401c0d0404500c1044000034070040d264100342c20380444c1c20040402600b84400f186803004006800605030000f030031402144003a00d4109030841c4409000c1c00c000000070720401e01d01101e11010304030f460100c0c40c1c040c113443c140c9125070358240100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 244330854 1250 244329604 244329649
    0xf0e0403020f0d0809010b060c07060507050a0602030c030f07030902010801060503090708011a0424120804080307032f0718060f03030c05060c090f0409051e0106050910080615 77
    0x8842a0340400311314062031040303008119061040c01013240e240314891245040e908800c20400c41c0714050340240000c180201d040d1105000c455441c44101c0c0e2040b0f8113500303a00c501006001c0c0004d130710340704160721104a0130b042241011341e4001038001d080521a8030104a00007001403840f100c05e20241c0000c049402c001d0180075010003884030782035101030300303907000c2c600d800d1034032500c451190001140e03100380d8100c95005d80d090001401014030902010380e03c0e084100300014081d5000c100501206010b0796444054000b00241082281c0e43c0204034002e901080c00081494080818424200ea49000c0c105860925421701d100150006034001828016405000814944c0180ca103c454038441c00c1910420303641d00003400702c00e02410705030bc2e0300505202c0c41c2c00c40a050540c42510b1443c0540101c0d0984800c5040804c07400c000203000740c2090751a4003040000e42404641c0d103402000c6001c3c028555800c010070113a940d800102a11a1581402040c003417030b40b642411000d80c007041e40500c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 244332104 1250 244330854 244330873
    0x40e1c180b0c01050c161509081c1a130203090f0a030c050d180302040504020f120f010b040506092a120114040608210408060f06010807020105010f0e0403020f 70
    0x52181d0400300d24000d041d428130b800140200751850032a80d00d12180079808010410b503450f80d2050500141c4d5181c06142e1720f502001c00b049502000d060b07032445c14520380312507581c00070070902581c4c40c1c0801d0820403440e42c40c403820b8030b03929100e40a200e000c19240c0141c41c3d030345201000c0e10f0b000c09e040b00c05040703019000300300c0245030740080711090103800740c02201e8034030f803507614111607000041070804402c0d441d8079024001458160005900180001c05002c1c02ea0b03008800070300524a100d00310440355000c4075000c2c039210b0007801501c1031200c0c03c440c20090f41c074114001c48c5e004100100000510449000d6116032a01c00720301c6601c000350241c0c0c480d9101e100d81807018001020a00406280103160f0380d00140604d064011441a6000345001e070282c044100c0049000092100b0300c40031211080c003000c66440c44c10000f8920501c82d860546241d400d11900151451401910900846e4105170040c4101100700d07491404898031805041b0a0740d886040403418081030030100007c500400d0100d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 244333354 1250 244332104 244332119
    0x20d050102131202030606130e060106110c010504030b040f05030f0304050709051315050a09021c030f05040803071104020715060e06030d0e0d0f0b0a140105040e1c18 73
    0x500640b84520800440c520b880d2400000d07a900e030248001c3d4075034072100008107142484207042100b100b90b0100441d44131600c2c5a032900300340090704000001401136500c030246c1d07141000840410802800c106103841d080d0380300c00014080c0140702410300496070070107004118080048910160b0b201d215170b0f480307080c40c1c50419150000c130b12480c02818100800300b86254214060355503803a81c800f200684411680311198003602c40204035104280da11030081c00561a135503065540803e4201510159035600d15003d08a01d102a03251030410209000600c00080004110740442c0c1e0460b402400141002000401902c68510020401c000c0c0140d10a15108171760041c0b410354107210341803035840d03032288189561a0110184440080c06103100107095040c20360f0010348141c0210000291241d442c1c9944800b803e003540d03a0a01c1c107a441030410240003092500a01419048078188240c42203840c00c0b664440e130400890001d28100d0145d1180079001d04524994040c080c500c1c0b1656a65035000f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 244334604 1250 244333354 244333357
    0x503060a0e03072a06090602150916031b2114070b0f030a0501090b030307030804170a0503070207090911060306040e01062907020315040501061a0c010b010305011a070609020d050102 80
    0x1d07400c18135444021030110b000c1d0070320340e040d0350b400c0d07005005070001c0e01e80c003400036400a400b01c60070780200c2c03420b550510700c5000400d000d103020f03260401000b612010300c0c20203200d0950080751084141101304d10709040c6038100300303a0281c201d08070022410a04518a0405200d41c1c0b106200150024904a040c00000003a501c03c0ca1400002c1149a9a85109800755055038103031545c55081003103048002805200c440d60070900500740e441c11a02c405103581e60360b60084480c10041503000c0308100d00030b0303030400c0046c1c05005042d100380708034099961400b0b03010b05041c105911802700840050b040761101e034009110b0403614402880456a10030350581118081648560340d01c0140f0440300450000c0d004841041ea4050003e01c4e0496056402031402c0d400034004540554171000c0009070100a46455501002014074050343d56210122181c212900080300781c0c141402c3c0401085000c3e080400ca00e050381001c1c68640c1e444c41d9034a0041c00400c50000007c1d4040f0400e01c6c0c00051000550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 244335854 1250 244334604 244334663
    0x1060609060206151c0602210f010b120a051f1502070e0c16020d05160f09051605090d0b0408070201030e0609120706020412050c030709060503060a0e0307 68
    0x1c0944099440369114540160b01c000e1120390017030010300f000304c0411545003130b8408140c00344600504221010741c2c0511400b0041d0000303806514006d09104624140226442c0140f41ca10300080c03401801d00080107806000603c170740151031340c0d1030000b2114080b404440a8441c0c000b1900100359485040c00e0000907450007103540140714000010070100c0e0705a1031240a4181d4401c05414810390700c8070034810814810040340c1001d84001c4003400070f0b80400c10583c01c1002040322f4241c0e1803c5c401e100351a8909988011703245420b2900f4001c1c11411203282401905443ca040c0d44d81f4822440401e48032030004000500030b124810400c018800004094200540b00766424041052001c5a503691a1400d554002c1c0c2500020380783c1c9901c07015200140300c400d114440c0036080607036407002c05c11020607408040d035142d082109280c040d842c4c2130003800007400b8040070801101e42414007084d510907006040d41d800e180d6510b410b0003062002c0040e036140551040c400d202c802484c5607031004140348038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 244337104 1250 244335854 244335857
    0x32103050c0c1905120d050a05130b1807180203090601050402070203031204020f100f030b01081b03060402120c13080102041211040b0901082a030a02010503090304080106060906 78
    0x11411180210040b11400c200040003000b0710040300c2100301d0b8407403815400300c81d0f6100e1100b042e038410700310101400c120340131000000740c0b500c0c011007a6030680f480145080c0e10b1234014201c01d80010152140d0f1a0000380202d00b040c080b20034581114a4400183c02c080141c0d09840f1071090050f00640007036104030b2858041d1611070340d0742e0f014007051340201540290304d6003042c4a040003400c482d114260740280001c7c51345070f034178002c4008524011400396001000070010b101500505403d8090800c98080c280703005500d17883c00c41080e8882035a02c184900c4c1189000000ca1500c0c2d0fa550182c9a20609406221090342401c181ca002d5692101071461141548040c2c00140d41ca01803003910111050000800d030524210794a401d000d405004510342c0c0941e580180401d142c40701da003418068600800104216024910000314500600c480302005040e07011442041d0307100442c03104641603082c03c246440c2c0d16075110590841c01150000c1c0e4456182031000500746921900540899419 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 244338354 1250 244337104 244337111
    0xf050a0b09030a0311090108010b0a0324031e05120906070c0906051003090b15030109060e07050103150302030c010f02100e06060922080d060b03010f03020f0a080c0603040606032103 80
    0x4501c141c4081b401031050301e901045101004010b050f0000f00105500d0b42c1900e0300080c40403041004004030f042404800f000d80e41c0b56031051040100100501182c030380c10710b0301104402800d546107540e80c2d10401e0540c00c1818007081940c8107031592001ea843d8140e1082041c10403a0704d42060388002c1c00300c0c0c400c6920541c01000b03e5812540288600502c6980000405e2000d5954102c9170074003011482c00140c15650f16601080898600d114800b403606890b000742084914240c00142134583c00c2c1c03490f21102c40301034410001640c00040e84116100e081c08d00e66140a2a000300f68109924056002101420481d4101c01d1100100c2ca5520480d0100c6220341e05071102122a4001c0146400d110703040d088604940000c17a02c488041d0107424586400401c10f191140a070205640081c3d0000f5001c1c00c00000c2402189003005402d0740119054840010082c541001d4590b1100c0301d45c0000d014001c000007040500404d41c00c01000385401544050f852945080300f40c0050940384005400a4034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 244339604 1250 244338354 244338371
    0x150905160c03020318060c010c080603010e0102180409030e030303070c0218090604151b0203070521070b060f060c0d0905100e04020f1603051c060b070f050a0b09030a03 74
    0x240001501d8a401d58000e604000d442c00d498a080700c8018541c1e0750104080c0861550350000b400b606400100c6030b030302c502c000d04092081c1825280340d21901c0740140d00500041c00801c001220b00c0c07510f07501c225004074003a451420107844850030a103001d038160000104000c0f440d40c21031010a0414820f40c0da02d050410141d003242c2400c10b05030740843c035540001022401103900c0441019400100403000500b10500c12003641c50030081440d81c8c40542c102094080c2440820710800c141c6240c0c003880007020000100032051944202c0340c0060488a01c000850825140c0d090f003101c01e00c3c80600303078582d140811b0b8141542e804200c00c8040000c2e090b10b10104080c184000080c203a1a02601c5030501d101e05581004065004691040751102d000d0040501804d10001550441c500a489041c1d03960040595513494040d4003000c43c0c506410030380c08018242212084500e801c1c1c1044002c01040760926046007002420340019020075400310610000940c044020401e2450300d407402c100041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 244340854 1250 244339604 244339607
    0x30309120c0b0a021c0903030206060603160f03020d02040b070b250c0602130b1309020a0e0d0204020d05070801050f01080103120e0a030f0f141903110115090516 71
    0x204056000700034a86800301041005194400b4081491080c01560507003c000c0c1240c0700c205010b0140d110015251030820814590144011034001401f81c440d20300d5450030300304501c15174202d0440c00003041409034200120621940c1521100c051101d1309545c2c0c0d607500c001030b04041c0c110f0303042610001c110f000401d20031400000c11a4101c110903140c1c2a007454094000d403150181c0c28800d40750300e03408104052014140400207006402080d014a468440c02a0052002e40241c1c028104480c8104201c0ca005504103010610281044500c0f002100040c40854080e00a00d50440c00340c40c1032000b0b00c0046038200d406c99058800c195601c29203d0321080046a0224007031002801119101c02c0010b0034a01ca8440b1295441c00a05929000703643e9a6448502c540c1000341a509140481440380410143c0e083e01400d400041d00100002c1403000040c0e035424040c00c10060034040f040842c504541000e40040004083d4160441012070307036041c030040940380484490b114403694200b07401030705 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 244342104 1250 244340854 244340879
    0x30703050a1803051608040305030c192109170d0e040603030e0609040b0a0b0904050f1905040c050303040303020106050306010803030709180b0907020a110303030106021b0f03030a020601030309 85
    0x94500d140c0842d03a5040c5510180d41c1503100401500180e50811624000b00708010700600041d84074100075952584001c045c5428084440312100300740301c1d0801e0400120701c1410103a4411030f0141c401d1403840110220940b203100d1150301ca00c021030400d05003000c5030b02002c00c041000d0380c0c4980710840b0b0781c441c0c8820081203134514080100400c2140d012603500d030403c04051300d0000405400051001c1c1d00740300140e52001c480c5c0c0003d0300040000b03441260b83c1003501038150031140c080c001c2e14007800e01c000907840000e82c00c0c0c0301c20b40041e41d0700005010702070b4605081c0014400034081d00d036a41c1d1a424000d0207040300f4014a030092288030000124200008201c038400c90096a49580580c20304500307510311400d041c50744460036258911980190348020045d8092009a00245501485440e24104040651201510940044c001009201d80114148003500c51281c01c8000b040c1d090000568203100d5103030100e42600c0701042d141e041d00e80000d58107043c0d074081c0d25241429541e554148414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 244343354 1250 244342104 244342121
    0xa06020f030f0309070803030f010f051f03050709030605010b0c0106080f070302130209100e1008060f2404120c0b07170922051b0c191406010803030703050a 69
    0x80340d200700406400e403200c2ca4003441c0c1120140c3d007900c00d156660005185190019152810580c580030300401100c2d840c650001e004040940c2d6202a082c0d551108045003070b0041603c009241d1070b07000249285108508032000f4580c03006040210796114a440011500241902200b9600e861800b25441c000041d125031903403040c8004140450465003804680c03065503694804894092200c034070141e886541c8901d903018140d44415203890140200125282c0301c0075540b01340038003602800401d031204a0608104081030f60305e200c07500324114008103100020040b1885a86001c078010410215106140b58100c0c05900c5034400f1b107445d00400041e42c4101100104200c0d25405081c10002c0c1d4040540f8000f600201084102c01c0941c444d650f01e000081c640b520a15542d0040040c845100e20b10081d83d0b400c2d40081c141400544240c0c540d480464190103010004031035051010006001d040785807010400e000d40d0020350b035901c2016520380054914101180c20301d000180f90008600c0f85808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 244344604 1250 244343354 244343383
    0xe01140103170a0908010c1d010f02061f120503030a06051005070f06110c071701020a0e1903140105010312050a020a11030118140c0a08070b0a0509120c0a0602 70
    0x894840c601005083c3e02503800003041c41000e040c0000c5a178001e114601c0884525200c0c08003015003003c42c548030003500d0901c141130246250205528503400a0031950007605c0c400c284004140041c94007a5000c40d590102c40d0049481c5000302c100000032004e1801040001010f003c0c4503254820011010070f5151180002801400f401020070328500d100c3c0d90150041000040d6824041072a0500c0d6100468614050340f162800300b217600041c0e010303510981071380c100850030a01103e40c018103100c51031450510406d498807001104004815891008650210141c03001041580c0101d0190a00341b006603031940c0c00c507840c40740045c000c401b140d00d00e0302240c0c007500222866aa944c0c0c162190325282c5071300b543d6241c2c4401040b412207000e095403a8003d00342040381c0350f80e0040e40381c60940382103000381c040c50481c20108000d0b030b0f0000b01c0c41c080d40c0100c00c40039150054804212814043c40300c94550102e040e40079103a00030720100e000c000b0080b0651f2020502910ac03c3c0c282d0342e0722403407200c090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 244345854 1250 244344604 244344623
    0x803041215020f071b05090103050a0203060702161205030409060e0f0702030a0e040c180f0f050a060207300c030204050f0420010509060d020405010f0e01080103020d030c02030708010e01140103 85
    0x280005c049000401c04001a0103c03556985d449002080550340241c10450301c1d9070003003811100354a420040702c0c0d40541d040c8004c1044c081c441c40c074011548014800d9611680044000c40200007040c41a1006008540420404540d9414003250b8940f0140e135011601207030003001c5200d140c030200888042030056207442206005500c03e000040c560614003004003c40403110040d07150021603000014500022031440d20750900426142d15012030340510302c9104411801c00c81a40c005c81c1c60070485000a000003c40b00260745003020000b0303075160200f0300742e120310301c0a01044603440044050b07a00030b9504202136030380c80d400d42500c9582a10b01a10010a800000012a8400d188100c8030b4206262260910548002244541c0c0000c803a9001d129008a410f10040d607215203095280f1402d85403080da08114100080d0070044103000181c0190910403044043c903004d0259004a10b0303000c0c0856101e00e03540e4a060740200706040b083d0800394240710b0008a036180009019050300c0d0401b4111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 244347104 1250 244345854 244345867
    0xa0b07030507142104140109030509040605180c2206020d14090904080a020c03011104150203071a0612031603021911120f03040602010603031e050a0804030302040803041215020f 78
    0x200c2c0f1303075030050007103071004203001001700c44013005e005d8800303c284603865154a0300c2402c02000203540050f00001e0040f000c0d000d00300c0c03024014405180e04540c0309201d5655440d080780c041c804500c01c084000c0c2c0c0c1904040000074074540e001030f101c104220303541e0310711480b444d10740070011140c81205146640810010042408141c10400400d51602c150040fa5035012000c4082404e40384000502e400450001c40c0402000e506c0c81086409034070b091024528009184d9134042c104072141d01041020b124040025030103484001d02540c0710500c0000301c03074680c10295010130060920410480050123406034101d21520440f201d015619884621040c1405100040c0f1a80314001520000f15105400b102c0c5410202800200045c0150341d0000c0b42132421810f0291920a2100e4541c074212181c00100340400d80c00010f9406c0c0c00403030310b0a03060640f501d0800b140079004a40090007140400140011140402480c04900b20700c103d850035a10200700d180081280910240030f410900d040000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 244348354 1250 244347104 244347157
    0xd03110910030b0a03200103060b0715061703031801061412010204030b091e1b0d05100f240e01060c0609061508010e06090715020a0b0703050714 64
    0x780c2441122407400242c805003440c000f800c584101e510a540c201a28515141148800140468002003c4c01e05011451800552810921600401410344c03001c40480e10780340d1010380c00a10003800303091850200c801d00b0450540d1039030701c241c0d41845070300c0030121001c0f4080c0301030044608440e425614544107242400520480e02c038040c10750305140d50300f00404000607a440c46014011501d14001f410266040320003105000da5000d43d1800c50b41c0442d6000b049101501360a0703035420000e4520308907034507051400d40d2603c582c10703040300d00c41c034208136134240040b42d00d138040601213540e2030016000090300107000d400143d0b54050105a100c00ea801408507900400302c014103c0d1080000046185058039490102caa10001854203a052808200250740c3c09000700c00c035103889031014043c0c0b400d0014103036641d010035105040290308c0084180c54517600074403c0b0804540c0240d4030490710716182c5401001404116804404100348184000c1d55081b0001030b202030031011202400303044041e501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 244349604 1250 244348354 244348369
    0x207170a0609063e0a1b060b0a0803040e010b0f0702030d030203091501120311120a0509010914030604150f180210080f400213090209040f020d05070b03090d031109 72
    0x210406000500b0146580c486d4401e41c2d4142c407900030b94000a20310025400c000744d03201a580103400e241d1050105026030340c0c12011300c0341158000c4ea40241d46000141c4148560300400501961501030550029a21501500203610600d0b060055906484540100060855082c000d01c0810510b0aa000340064040d010b0310206c3c0045804880200c103616034a081d9075480313018803000042c00828882441d58001403448041c2c5081241d02e05d00c4012207003c2665010b0060000d40700303e10044045007902c443d41d1100001c555110810311402e00642c0c11100d008d900404100d0003800714941c6001c1403403050b40800e018035100d59a01c885911010001050100c0103140800010706442c4070341c13032400000407041c02040c0c19030409800007d050040045d005080c2c03141004407410705503458016a0b811940d154021b511040742c040641183c00401c401c0303242030000400300e12507804007103400b0080b0303070140d8480d0382824111085d52088220840075942111140c022094041c000075406180603403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 244350854 1250 244349604 244349617
    0xe07032705010e12040e0106030204080d0804030912062009060d050606040e01060e01020c0316120611070305041809030914040e060c0d1b0207170a0609063e 69
    0x70000714202181c07044090a0000c003040407001064000f40801c44c041c003c8034494010b00c0d850400310b0506103010380d030747d072203082d0000303190204440c102c005000c1500a101c210301400c40401d1030070400151780340400081c40454070b6041c582c01c50700c03007400500300c4003021610300b2280604641c1c00c0407227068111002e883c0251845610071070a11011402203000710340f150007003032a0743c1c41d00c04100b5200006824100e009500314025000030b00e0400c0c8114060034010201c038101c9a03407500412803800c221004201007440c2c3d03182000001034402c11305520901070700681d840d900c0c0d051180201d0500a0301250200c15009000c01d801d400c2c10400216420310b0000d40c1303d40504041103e00301080c03054100307542201c00030b41d002000715601180c0070084c400d8800c2ca65045150003140026504040d5072902c40c1d100780c44068070a03412885134203c0611806201395400380c8107201c040d00a26280c0c01410540c19040800914030502c3e034041048421071429600902c094950225803518071900d09a0250 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 244352104 1250 244350854 244350863
    0x307050d031e0c080304060204210203032a01230a020c0c131e050115020304030b01050d0c030602120103031103120609060109050d0506040b0708010f05100c050102130e070327 77
    0x10381c450030100780c13040000c40c403ca208030030050b034490601c4426281d41c42400d20b90303110510856980401a100001110300070886011710b2404a01c02109002a98030a420194081d501341580251300d0610300010510481c1980c4030304506558002001040307014440b082c4005510000b8620840e0500312200100d00c41c3c1c018000c1510b1500c11258070740840e04000c2c518600340d07250b00400c1846c2c80c00c130340b45c0900f140741d01c0175501d0545140c44890300c001060141e6440764400e1403003141000180d212502c001c59110030255241e220070a841089800e00b48403d03004115004200d0507031000c08412035036441030564211116464060900481c50001488181408212803001c00c0320358035131092550891091004081c10b02d0b151030282c10321540580580244507500740140080c003000034201d016504240e40d44941e035200040c0485000c030a1603400385c015440051808440f40301003907140241d440000071300719103495402c070071002c031212800407540d03884002e00290f505c10104030b00300c039949014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 244353354 1250 244352104 244352117
    0x1320603150a03050d1719270c030b13030e09090c0d1a1003050604030c03051303081b0a02180a0603080c0a05010c0219020f13060b0318010c050a030c031104060e0307050d031e 77
    0x52318040719450070381a4150f03848540604c1c10800c11114080309070f0b200d0384400240043d40150341c0c01421503d00500501c0c8039005480010b070101c0010400c50180b00c5008010200c801031508000704001c180d200d6401c0e80c9801c060000e086400c1031a0007108907980040104465620b13501c0031902c502d481d41d000c408100c000c1143c07a040c0700310310311088046c5d030040c9489030365100c0c44051020001c000c0410358026170400c0b19964050798607407102e104010495403980000d90346100554004014a4000510307a82001c04c207584406c43c0004d0038040700e842200200644180b05500366a92100f0600b6101241410120300f401810488840e60f52804040c2282004005403c14001559429007010071102008410803170304603c9841e406e500c020b40c07403000b000312002501c4010030502c1003251030f501b49034a0315543c50242d80710f81c0c05001d0841941e005207441d641c40c0c0800500421004840c00c0c841c0c401c8000c08580380c1780c00c1d10702c00549076041d1152808000114494452010402c00541c1800300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 244354604 1250 244353354 244353401
    0x130f090501020d0f050612071a09030a0303050411030604080f0f120c0a080a0b0102030703050327061b0313140a150501320603150a03050d1719 63
    0x100b400a00705003004518040741d44860105228219040105001d102d501045104008000081a14404d0380e1421000c001c1038980c10724465441c0c0306c0c035840181c2621504800c0000c1c541d25500c0b281c080c51107140c612020000c003200705607850701e0503600500070b00420000031002004603401480c1001d4003c03070850070402005601d1103e12021100114180380006005a0a03913004080540c0b1480c0000204015641600000d60300e0140e41c400500b403010000116000c0d0a100515141d10078031100b0580c441d076a017005190b22142c013500d0f80c207248030104103049520354904050300c1c030989000003c0382c055822900c4864070400c0011070303c2c0c00c074090315200c1e9000c100381c02c54140c108002400086074551501001b4000b01e02e001c1da0440040c1042100da801c54440240104044501218001c0d00c9440d13624044492000c003004440d44403100407000410000c0c04100d09900303400549504401c5c00300440c0421800b00c04076540c080c0c00d030751105001c1c0351079851b500040f060301009c90512503072034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 244355854 1250 244354604 244354613
    0xc0102070e070e090a14100b09090402010504090f0c02011a0f190e0a050615030106050d0b1c03080405010606170106050c03120717090d05090f0f1504060e01050405130f09 75
    0xe105a507030781440b1b601d82000d8100c0e10100f0380e0894210591554941b007840c07803c588564239028000071144900e00590129066a10a10503200030707194120080015140040e504001098000103400242d42050907204c00031030524102c511044016150b440142510003c01010314140c01e110029030000000100320608140c0342c0900c00c202d00c543c0003496082c90010826100c50500304100c69010420062001a5009065605940714010089a6007140c5000035204091000c0c2d60355001062154100a065200003454042c0d8000c2008004a0307807901c80440e0350031020301c44542000700344001042914480c0300185960035000c015207003400c03900c500d44040103100f0b5451100140800300729450320780c00100b10316003160303181e4000e1100b040c0142001e4a9130041c002400d02c41d021a4400444988502d240208007081c020000c42c152a440c04000c5c0d02904640205400101250b145480c2035000c4c2089405491000f040001e81c03800244141c400b80c40e00410640c841034480c0e04910018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 244357104 1250 244355854 244355869
    0xc0105091b091504050402030a0203030c012004050108040b0c0c071d07020106180908070204140f0f0105030316050a0b04080315010c0818180f16020c0102070e070e 72
    0x20006500a0311404045100c1110156500000d0a200d00011002e0007041d9401d00da4400f4485404c0e00d0108850f80c840c0002803c010203150003940602001402a041c43c0d8107500942e0542c58006041000780040f103e10f1486010342c3c000c2602040300e040115001c1044a030209078031000d95100345150680c201c41c0142090b041c0e920428803181d404910b140e00905076010640c0c020107910007001400d140822542000c040d40251031401543c8170080c0d824801840125204960041c000380910501034004c0e21489004941c1e03070040e030510802196095030881a00342c101c550080042d424004841a0024030f00d080200c125550311a03d00f4002c00180500346c0b00348104cac0a60350711a12894884000703103041c1883c201c43d5040150308984200016021010749003500e000008450640c1d4031280840c0210844040e070510645034882000749200502c144944908000007000d80c010401d0705042e03a03110104882640580c0103514144403404041c01c4a60b8050114a441350a0000300e00202d00728 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 244358354 1250 244357104 244357111
    0xb06060708040b090f04050403080c0f040801020f04080111030f010915080a15050106020f060a050411190302030709060e0a0b010e0d05011b1b0303020901050904020a030e0c0625080c0105 82
    0x402013049a051301e4048808a90300fa000d440901143c0740c00c0e90b0081080d200146820080600486d4036000104102c003038401402c3c1041c001c6507105407030303204100150414480c0741c02c6507003001b0420341000703041801d0320300410180d00e41708256400c00381000c001c2c0000c0c101d0309100c205138180c00030700c1c144104400f024444c0104c10900c1004a5007401806448050300903405640c070030003010142260005800d680400a900c001a803138a41c2d203000c001c8910740342240d681c010b42d000c080310080e64040c070358001168402c9003261261b40d500e9200e0b01c2918038a104082d185c620020004800b103a480d0814074010300c0501d40b095010550340000394180300410410b032683d03996919141003040302101c03001000030640c1004a0410200d1550781c2c2980b8404000804040e000f045440c101e03401102a03c0743c042e0001c1095490701d01c8101d005006100031500319000f0303c100604026141002d03400c8800e02e0080024103007070000b42804140d003504c0c02d000e003200c0b080d0040140c0a49078900384102c502 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 244359604 1250 244358354 244358369
    0xf030702100906141b0405040b061324030b010f0302070f12050913020c0a02010f110303010e160c080f0a05040b0c060106110606030d21060f0611010e0a0b0606070804 73
    0x2020810100200040310b0000e01740a4800b03840501e000da8603030008161400c5820807580170410243c000c1c0814400e008084500640720401940454210355481c4018045c00210050309107101900c08101d080c3d4031441211800300350403108030b40da1644070360018014103000c1d003407000450b04180e9810202c21412000070780004c002103804542c45c0f0340300003441c10038a40000d0540c14500200d100d5510b41c00c01110007410321203001c10307140081d03009400d0700c40c040e007491003500c0d200e6945410444500108441c403004098840380103c0d10036006844d40481d5a4008070f5440c200000c25800c003040341d00080c00740090100900c070000e641d1401c2c000600ca84802e140251105501d41180540f00c3d2100b4141036015411000801c282510005418980c1c46414901000000c804007081c1051103280d0726940c450314207280b404640b0402d03002440c0e08442c03081e690b018501114811440c01c886d8440700f0395074150131000701c900c00320314040441900440b00420f11850520b541d40c075a4000c0d8400d900004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 244360854 1250 244359604 244359611
    0xf141b091e0c1c020306030c0909070e040506070801061e031a120a0605061c0204090303060308160209090a0506010b03101203020106050f0d0807032307051f09080f030702100906 78
    0x40c00b1500f1005104000c00c0384400b503041d0304044000070b460f043c0c8101c4c4a801185a040020200d0740300b0424100140b807007107c5000d04e81464144161510412256000401c20040c0002030741885040001e89900d447d101c0c0c9074108515071011400742c80d500a020040c0c1d608184104101c0da106158540c49103550b030000d002228192800d4810fa46005002d40e100e80c120031050030440c02d0030840d10f00c503558111000503500d2441d00e404d60091080c3d030006418241c01181c0040308014050318904018021154081e0300d40d12100d0095075040d40c40d00061042d04518010096009044003071a0000c40241f4802e005039102c032004100c0d40c040c04c80c1600141c5d15104100700c2420040c41000e05000d0030350700101d11621944170350303c4521030114001e08000c2d060001d07c0740e11108500030a0944d4090f049151350700e1440c181140d86608486004c1d05441403980488074207003052040d81c042c668441e03a002e0409100000c0f4504a030801001c0c40c06600502d031124900729101c1c0b040030000c2e44545d0300003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 244362104 1250 244360854 244360867
    0x10020604061b050a0c03142a070803160f02060c06150415061b060f0b03010b03151308090402030106110f0d0210090c0e040f141b091e0c 60
    0x940d2000425002200e2070341080c4440c0c0c6900204490f1100b0b013a081000b038141041c50100c3d0055090789401a0450012502500c0d5014182510712803c005088800024140481c0d06c0c1c2c590b409031003101e900d60300400041503050710110f00d8443c0076008214224049940d0f4001c9a9180e00484039401d0640000c010040c43d4918882032003c1100103480c100712100e5107c0c1c0801794445140034980a004110001e50310b8160364190b40c9003110341c00701091101042c01d46484010b800c00c082043d1280d428003c4e400c43c141000201071008545920340b814003603c840b10350107914120404151741002080004482944842c00154000e000c19903400c41040112120139080081d1f60320b82118640001c0d40d01c0c588944e0004130b48000b52102e07080045c11042a1400c02580c00c2943d00c1500600b0302c000421082c00001d0b1046a0b1550065407508c05901c3e00c00c3c1c0c865240c224041400014440c82005425207041c07060f2260303031080e1410801c0c2e5030b8980400041d0442c41c0700b00c503400c00f2000c00041c40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 244363354 1250 244362104 244362113
    0xc020a0b0d0905070f080c131d0c032e18060504030504050f0d0b1909020301060308041a07170d0b04051501140f03012c011e05090906060d05030910020604 68
    0x21340c0d00400f0142034080e40541010002900c03104403a090394490034000304040c0400007540c8c0585e0004409901c465641056000569103903d02d00080303031f10034080c01c941d42c1c16044c0b10b0340381d406100014100899440740031032020300041c41080ca0910210245000440000b134841c815940258040c3d115551034502d00410407646004160f440350207447d1a0707103402d002176171105265800c01801c283c5000789030109201007000744040000030398107600745040041480142c4000300180c031480c0e01c1c44c1d4590450740b44007011610035110f004044062003a44500036003901405405200c0a5413030120714070341180d001405850099428280507600100c94480395070b0400c1c12075002d07a07004403200382045045c42d48031016000501c121000613800403a12580b00050312032154444445450030b91255071580405c207145100a17080c59082d07484440c010580303181511916224560b14001000540c0d82c8400b80710032181480b0048810303100900510f42c0980d980341c02d0f90301450080d030051541c1d00d41b5061 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 244364604 1250 244363354 244363363
    0x20c0c0901030c051e030a2303120f060a050612041104050117060f22080c030406090e09190213090203030a1106060603010f0501050a11070e090d02120a0c020a0b0d0905 74
    0x5014030410b44031744c80c41010746000c16a1074880780c0024100003114050b0700c0c1c0440003101c014005446000000716520060307a04114a40102950b04080d0300c51f59440c41845800542d80c0200c91344903e0074000f520503181034a86060b48107100b04141c006086c45040401d0a45000703800180382d0f10303140f01000110306000c200f12503215600e0159001c0c0e81c1402e109040400d07540010000c00d1201c180c80c1d2a080c44800011900000b086000716070391182d80e86001030405001d80102007c01c007000e0041484e001001400003038103203030395141035400c0516a080110460a8600c0420030702d884801450240e6400c2c80508032224094452244c5c05140c800f4840c1040c0300104a40d00c14207003880184035115003a611482922000c1c01e20554030903140303e040c0d40c0c42d45c03003056a01c00c5101e640c0001c51411000c4000d1800f85541100b00e0380241100c0b4801d07611071a0006541c0310b0820b080c0001118079206086440300c0c14005407441140d2603c0703e14040782c5a02208151960360f40743c000e02c1081020410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 244365854 1250 244364604 244364629
    0xb0307090b010f0c1e060b1f09060e060d0b0d05070803090a050108040c060e01110f0706090603020c0c041107080c0102041e030c14210d110705060d020c0c0901030c05 73
    0xa40304c1900700543d594605240c84ea074102042c0c0000d010040d000300a03003503006810703041d4000d111007940751885941030091b0b140d05001d2000195010301c0001e4040c0500796103c03808400900c01e40c2810701d400c0c01e43c1e00a10760689201c0d0f200f0805007102010440500220024114900103155117030983c2d0107226444165038040d5041248000030017010032600170002d001d03102c1c42e1a048003240890001211521101c600090190250010111032264005000400c0340c517182ca65040840e40c8440990403402a1031048000d5003103000300b0b280b03c0c90150b01201d0140c614207040c074186507042e1200d50076a00656800543daa50005043c0410005d21042449502d4540e508000c5282540c1d12203a44800501c60500308004000b9464000c1d500c6aa2070341a0140039204100b0707100011102030703940c600d0f140c0c048000c14000d02c1c04000a0740003041160030360380090121071802d46200d48807002540a1904041140521500483c4ca90348000c4c144c0c1c02540079080111013141418100307c4087d0101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 244367104 1250 244365854 244365857
    0x6090c030f1a07051303020f0a1d010302040b0409020607060e0708030c010212010f0f0303030b0f06030403030504171611060409020301081612020924030304090f060e04030e090a0b0307090b010f 85
    0x5100b140d0078242649a0902921f40c1034450f038034170003107220101d000c0d0000c179000b0747c2c00840c0c118a00100c1c2601410358038103c9000f1070b814010744140c00188400c4800095029401c01c1c410000000402d00780e030860001c40300d140c412200034540e036404150a6820014107141d01380d400240c440c54a50040e4030090140120310503011305d8620300184e41e0703036a8485100050a0585600c4004c40329501d00d00c052803507001c043c101ca503580c503007464000c00030102110112000588000c0c4035001c00b04580584280c0010012000e05021290702c4580c040031182000c15070200c0f08200c08a6030006a0010318001c000c6c5000824111114944c803103c082e400b41c001ca1170780c05c0510408000341e902d00010315001038013240d0000c03107005085094280c141d101c0c00110340504c030000d8009030842e1158401c1e01d80000790f500130020f1b81d0b10703540e0081180d002030b20050300044050800c056035180851480d900205206030009001282001080c104586130348410700c003d41d200000d19031940c000c080032108070140e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 244368354 1250 244367104 244367107
    0x130f050f06010503160e1806100305040804050f030a1b08060f040c151803050606040e03071109070c0501150f080c0109030809030c040207062a050706090c030f1a0705 73
    0x1c000a01d9401300420150794400c43d0341e42160080d00440920441400241c021100810344c1842000203003030984131540a502c81c0364404ca01c180c802c2c420310380143c0c1c0c82000d0528240c070300402c01140e518940034055044c0143e200d1900040d820580f5002490503400280c4002407401c0502414044001c161340c00b030910817030070040050140b110700c0d01600d110250307007130a6180c040400c41da4550490414100500701c40d00102c28408000340140c442d840c204e0f0140030002081c1c3c1d0040c3c483c004c40700003c145c3d0000034a800c40500c0c00c21411540a0018580902d0f2211035480f05420341d00500c3c06c40c11705d003800c0013046c40700f00c52006684002e803450034014000302441100080004055210181c08481d001c1805407081c1d070f00780601c014203a0024029500c404060070030200805800c40d044100140c030003c004010352840c0a40d00d11840d46032145801c003260f644610004e42014581120401c81440b8044009110072040300d012a025541c100f03070700085440103200701d080241c80c09050100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 244369604 1250 244368354 244368361
    0x9010c091e1a040909031e050a080a051812030411010302071a0408130f2c0106110307060c0c06060e010810090804080604150501050603240f130f050f 66
    0x92100d507041103035200307685810070b25071803865032a00d03001c1d60b001000014100007140050640c40f41c00c503072419003001d034a0141a075501105030b800d849003038407a80c00b160422000510315941a0300240d4085c41021075501c041080c8044142003407442c80b01152800000701c140000d00040c4190145200000c0c03e0440c6442c40d00e84448442090110500c510f40140200107800c111400e41682d045081860142c403c498443c2c05d1010b0000103409050500071546244075042000000c03600c2c40312503450880d003010b9083c0101252601c980c4070003480da500c020044003000847c1c500c01e01a4004240c0da8004130510341d0301d4440c0946a00341d204010980001c1d0052001c0a004120010440813001c2c00242c80e40551410074001c0c002da51042125015440402081c001c0d490040b80741d09003a542d04001c00d81c0c03140304008a600050381e44c022010440c0029182c84404070404072040003004080130010650b4400107545c50080b03014031410240c0381d039640c02440605001d00b5410000c200e41c2d2106c0c528 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 244370854 1250 244369604 244369649
    0xa2405010b07060e25060e030616270308030f0915010603020c1501171e070b1c0906060f060804050307030302090d080a050a0f030b100e0102011409010c09 68
    0x5402e0060045a03607410300303030b08540042054000c282c811007050001240080582d148000c0a4440c0c2c10104090100b404402e01c0c012a09070f108848082540444c0001e590701200d010f0500c0d400c500307250100e0035a10000300d8448070008011446610034503030300e11700658041e1010f000500070b03551075070004004030b4a650003e0ba50302d040d145145801a02c40005445962400d500212050302c0b1903280c40020a5414202d60a0b203c03001d904400c40742081120044050f121528075084402038012031018881071201c0e0000304015600c07a00002c108600d032107a11011075180303070011290f9903940ca41c10461000d005062078010100350410603144d14042c0c0710540c5a1150241c004c00b00b540c0040d46c00700079a10ba9100070000c0e90006002a1910860341c000f0740f00f03901017200716000c6041818030b0403100f880ba024482140344081c011840080000c08180c43c1d0800000b4104d040d5500d899a02070458002c40c91984100360b01740000c03460001c05400584529201e410104580007444203980b001d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 244372104 1250 244370854 244370857
    0xb011b05070e0a060b0315090601020313060806042702030d020d0504260307060507020c090103050c0d06180507030c06080615090409170706050f130602090a080a2405010b 75
    0x10b901c0c2e0721030194290f80c0c50108400070b106a8201c0b80460502109004030140400100f0b81000020744214545e85c860100583c1d40f070065a8160240b0002443c050007000e110718542d5030440c002420100300c803612038842c81b050b1840c030072885280001500030242546030410100b9440d5840d03002a01510100110003442d512590240c4481d80301e020303400121050420800d00c001c11001001d8075120f080351f180000140c02c0589000e8010300c030b81d1001508625155446c18101c9901038001d03c0000d04950a11062004004050b1052591550810841110b440080745100c0c0305801415502d42140340c007206c01c14140d0055010080d8020800c019030b00c0361a209450841501003150300c0d80780082c0001c02512074038800400c80f150b000e41141c801d21090015010151050400b0b00c0300740d990000501c500602181c0304081c007061248420041186a0b00600038010041c003111300342502c68409034130b02412120300700c40c00c062041685410786c210304080d50039014a408140300a502d0000c545d50315 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 244373354 1250 244372104 244372109
    0xc020d1e050901110a02030114100503010c120b0a08061005010315060504051203070611030430050d09080c03070b07020604020a0b090d0c0b040f0e0603030d0b0d14010b011b0507 78
    0x11300c0300e5540030f0081c000d0200040300000382d00800070301404e1601c0e461820303640029140341804c0d1030008404525864103010300f070002d080076a1f4031350002ca44103d0702000341c80085038043e0040c4880c1c1e004200400306002ca14800d00014400f0182d40c0d143c10001411582040c0f19007142d080e080c2001d0100580c814101c6084801c216440c0c00b0781c0d041d100206007181b04e00706004204900d810070122041c10010701840c401c1d8040c00211a880301c00785a020140540e81490303d024001c1100c0c036541080c000c1001d007000310703005040081c145009035241d121907800040e141c1c1c403990002c1616000c004455003165800342d1a803002d8141800d00780e02041401c507942c020f20a0003500440d5041d100e071105010002031907044030b201c08100b541c2e101c10b804503902500840d0141c03980c0d03100110700700462158080c0948030241c01589401c492481d0b100c0200a80e40f4210351105043d1409000b1581000104411504403000002c6e4058948005070025a0f030b4141c40d46604000ca0705203000c642c022030309e5000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 244374604 1250 244373354 244373357
    0x6092404030c05030c011a0103140f0c0f04090e330a0207080f0307030f0f0b060712050712020d0914030d030e03040b040902031504060305030313150c020d1e050901 72
    0xa07072198070715006044d8041c03100098440e41c03808a8a2042501c248092041d1000c2a00c040001c40c403102803584650703d04032020780e400c041d010301090800310608000e150360305400001e07034100b03070302e8822010a44545403801c940e0350b4403030855541159100c54000c081800c58100e81e21240d0000c1c00d0320010b8190040409540301d60204540080c000c099084a101e00c5078204056528548404080c00070200b008050602c2407806020340202c401912a85c88203010060a082c01c0242d20b9462040302105240450204001444078200103040d60520810b001901d8020b411101d81401000b48001c485a018481d41c003840b1906421710384000c0340c60360013001d02d4903011403142d00111007946184a00e51007881c21803c0000c00144c82c2e200b130341c0514055840e80c0640707210308018504000a03900d03980009002c680003003021070701d4446003d080c50001e0744228820041d020086c034880741261644e40302d010160f0011852502c290364003c40d484410041c0406506112071026401041405129007d50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 244375854 1250 244374604 244374617
    0x11042f093106180b010306050409050a030f051602060f070803042108010617040302070e01080d090509060102070b180409080705060a05041e0203070f06020c09100509040605040602090d050609240403 87
    0x3004c82e442a0090000b4100c040e1080c00440c40516003a1b41d0341c145105e090740050506889200322520130812603200000e0ad001c0031074a01d040e81c0070081e00360b0050703403a8108660704000c180c0000340036030083d501c1540144402c0c01140c55007030340e20001c00c1c04a141c000804c4100030043c803503140c025208280c0c910038101c20f00c1e1207035034516040e4904422078001e0041036405500001d41c1050004806001811a0f40d42c0c2c030134035580d60300341310000074207540e81c43c05a04a0513051000f10b50388000350505000e202854401c0b00c44180201d0200c82030303030034196450800050f580e030520a080207120303001040380508000c03500d442d07201c0078078141c559650210f280c1d091655031001d40d81c0400500000d00010406030210036130b00c00000e5035564100c82141c0c011940d0800041e00c406080b8807060844001405661507a42c469550321700038400100215441c982c01d100c00142c07600c8072400b800443d407052000b001c250800c16080c034a010b1045c0909041003407503066060308684001081500560b0609044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 244377104 1250 244375854 244375871
    0x2030705010509071d071d1908030c100e0c0904051009050102090109060c0308010504110c1002131d010902030703061d0601120e0c0909010b060304050a11042f09310618 74
    0x880000c104c0750991500d820b0030700085a80c1000ac401042c02c1d81c810000c5031100400c08041c2425102070324030040b4a03400c400c444111606140161660180c811001c0d989161030310340300b540c103c45202009403561780d80400e000b07180d0358100f40e42b08081c01c2035040070130584440350781c014403c03007050080502039500e900481306503610000c29280c0c1d010340f100c29609076070114807800f0020740280708114290000d89000080200940940f0101039091070781042c0130b682010801000b039800542a001016a070b1500058010740d0306000c215045a400700078a8181064400100f00c00c12920110a0003071901e5881000803030700050b00490214162492245551946070720743c018040d4595458002800200f00004c008021071304802440c420105407c14907900001d000407159400000440c1c0c0c101850b00544140804814240404c8130b00415450aa144400f0801000c011084400c150310910326018103540d010b03558070200150031f030702004070910300340c1c0c1448610a0903040c3c0c070505d9660080d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 244378354 1250 244377104 244377109
    0x1b030311090a062c13200c031e0c07090b0d06060e0109050c0901050406030e07050a0b1e0c06010b280e010e0901030b0105010e0102030705010509071d071d 68
    0x19260001c0004281c200d1070303a0740d0003001d4040d0320b80001004041d2150441514101d0181e0000984144060a141c00001d0795000000c001e00008400c402d100b900b00d4138080c4801c1c034810003080c1c035107241c801458483e4060701d0019140c58141d450585940701c14011201d0500740001d04500700c03540c185011514440ca43d001c562000300e140405040740341010700c00310354200050055030490314a21801c1101c0e503688902044d541c00f0305004a400102c0c1080200103040c072a40000c8a44400300302500d0405907034500052044250340d02c2903000440100f9090001c1e031800b27288101048030080034610704860030040603101e46050003058007442c00850b10003588945200e600c0e80b00d042101e03c403804e07100c001c44050880c502040d020b40c00109084803503041800c0000c01035040303a03070064048519034240001580d40c210f0807205a81144410701100001c100e003405028002d240d2100941951030422440f114039105d2035040c1e00000100c41c003441280d5134024400d5800320005002e100d0400940e400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 244379604 1250 244378354 244378357
    0xa0201140711060316020d14040e0411030105090606030c0a050904080a0c1b0f0b0c060114010c05030315010e0102030c15060f0409240b030a0206030a06080d0801030606061b030311 79
    0x30650401400f000f00580c0100143c5c1d58641c02d5816003c8801041c0914030803950a614241480c00d012418001040109000480070b6002881000c41c4507000100101083c2111421140d030313031040c2d0000c014420385060a00095070501d10a40754031062038109804240300d480040c000602075a0002004010310344921280e0080e10740c011101c20702071910300d50803201641c42d4015005907800603d8009802c0744a40100c4910742c002d003001d00056032a007446c0b4110750340782c441000c0c180096000d81c400051030920007076100c0e21901000c5000c05003600d00040a464075541c0d05415503000700082d8100d12000900302d80c401201c0354903101c5956520000c5900c0c82c408a04440d00107061002020800c4070140340c14100f0052512414102840d170b902000a54004110035034040e00b04142c0c01f401348c10441c00a41e0710600c4c0e64404607455a85400030b0385000302c00e80b402400a1074080050042080c1406050000d0406103072007149061036032956800000c800350002c0606550b803161400702801c800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 244380854 1250 244379604 244379633
    0x603150f0601031e05040c050406150f02070f080609070801181e0204110d0e071d100308030906041a040c0b07050111040b1e03090d110106030b1e0601020a02011407 72
    0xb01c0c44c001c1d050705824540e0140c002902d044400d008144000700300c80c24681f055808a030556900c11104015a8005485850ba00c0c0c0200c0214002c10601061510059150340000c01c2c1c8603008218500c0c01800403800e141c0d131600300105c02c0c0d040040b41da01c1c0101c00602e1403d03a941100c0f403207109903c80110444011146030000b9001800c09242c0840c0303040c03d0000d0800c0104544050024a4940c1481511441c2c0781c014413581e000540d5a21130141e41e00d9440c10b501801c404103a07921662240c48207851600111034012555010008000410050510030080e01c0d40340c2110180504060341e030088032030524040d203118104082003060901009400161064030f0240d0102d0340d413a1940c0f050706089c1d1202c1c0c1014034a4910816100031807804000301c1c0d01c80c10215001c0c0c20045140c00c0c0407180c401a9101d40c0c034456480d03800100c085803036600d146002d0603184090321a500ca1104481d040201e008000d181035400150000b00582d8011540120948070300c25003980d9001c0f5403030300042c80e08a50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 244382104 1250 244380854 244380881
    0x60a050c16030201020124140103090c090203070215060a050d0302100f15051215131202031c09020a0b090d0b0c0406020f030a09050f0604030b0a090b0603150f060103 73
    0x1c1e20401056034101c0e00305001d4074001e82c002c0c0116440e1180d203d0600d075a03e4420460300003040d0040000341d068400051101005140c041003100c45500d403a1074410701c5420002c0110750000510401f00d404110004104005107080ca2551800b5030001d550301d01688903640c000e0030419200c4040500c00d0007186c03c02020618100100343d080c4c0d044d50018140e81c003000700000b01a000120f00c03890803001420341141c0c50401492080b4202a6011070100058080302040002d21040d10004044070041c1a038003545034006c603114000c480e10050000c00c07840041c80c0e000d18045600001d80c0310f9aa24409031042c1c030313110550320400c00b00412440f881048015141c0d212400c18801642c0110300207000321013907942107074019603d149003175440c1d01c03031042410086a244071041045040208040040ca10700800e418107199807a03c99000c0d01e4022624105020790f1800403100b0050208038850f001082540200004d02d13000d9914010080c0107048800c90402110000300395a120340c01140356038044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 244383354 1250 244382104 244382113
    0x30c0201050703031112100501020f07420305010906060507030309320609070e1801060b0f0c2b0503040204020906120405150c030c070c08010204060c03030605030102090d02060a050c 80
    0x2c1402c0c02152181980c2003405040d1f50500028150300c005000c15441c103800c40900303080385c60301404041542e43c0040601c042506d0410b82494110404507600d000c3c1d005d820300140c17480900d2001412294160042c16a2514140042c8040e40d070000550300c14507854180040c56031658142485800c02010341c0c040115034100e0303451881c2402d042000c0c1051a02e81c101d44c2d080d2105803070983c562425010382022011018000786180c0010001846c000752100c000241ca01d48030350507407040354002c0712242c1c410140002c3c0c106081c03500b0000309105010070440390400241c2c124007070003205402c47d00b010800038040081019540c5560445000f081c000302066500c500300e04031045185401c42d015503041c0104003541d0603540000598070310661000c40c855166684856043c1000d8000c60410f0381c0038410070320045500318091006001070140303912410300d980c40a10303000301514026023095000741d00502801100751954442c51002d03035170454041d501c601510f40201d81c136000d0502100c400c0d104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 244384604 1250 244383354 244383367
    0x608091e0c13050114010c03050c0303010e04110a080c040209031e0d08090a080f07050c1810080c0a03060b060d0f1a01030c020c04020a0315031a06090103030c02010507030311 77
    0x81c00c030507903800a0302c641c04003440400140c000c550091207400c1c0c190790b111100355400e41c412900c0c50410307403080c14510300b0584100800c40c55600260022980b640f400c10900040c080365031800c110180049400401032402e1000c10758681303c100d06801d014940110354003896640910040030040b1581c1c41d04240042e20440c000d5540403101502c0740480c0c03e603070109860100100700141016041000b0600d00114108042e0042d4403840096a8038040e4003010501540c50115080e07203d04203010001042c10311239030415600d00c40ea40030141d03e0f4800c564142981c0c42d0541c03144101d030b40160f000241c4a0700800410000d10805041149851030800070842380e961503400303c14005088000e214814402c1d00040d8100e03014031705a50007592080304e1550f0f0a2800341c0050140c9625864046482c09504040107000a500e030000c40e0b00030031601a407240746070301905807a800182100d00c1070040d45140c8010f0311551260740081d04000c0000b941c5010b260080d040001c04504a45400e03540d0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 244385854 1250 244384604 244384663
    0x60415150b030a02120106110d0f09080a060c02120403030921120302070302150f0f090c0312030609060103090803010b130e0c0705010c140409050a1113030b071404060809 75
    0x602100c1e8105c61201007000100d003480c8502c100040068040d001000602404001600d00b04a410086800c100c03200e44d021492003002d003d00c11449104043c0400c1107020b0b20000f0f810043ca0b4182141d8421041c03008102187e840380c021000c41d2080384000304007680d0040c100f0882840d4007400351003000740c00d0314000c1c21a41035000b4040c0728000c2d07082d181d000078040551041400291025150210400c011488030781490300034613004480e88040364901140358001c070303050024168102d6988500842000002d0800401c03031503001d40309280030042c0c00000e68410342a0301044c017500000c003402003100c0c0703605040e01c10904d001d08229a212052407802c40c80b107605a500468049842c1c1d420541240e0400380140e40344064070200d5000c0c0d5041c1424050a0300041400500b032522060f100c110b071200ca800c010b0001c04c0b40c0c60030180c1c050381d034a04604080040c0b2901504803c01c00012081d41c4d42c0f040e51039010f560684049180414490302c4040314a40307000135035400481c80280aa03490920701 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 244387104 1250 244385854 244385857
    0xf010c151407020c04050118020901090329060603040b04080a1815120614040b0a0909080903070f030b0a0c2010060f0b0a2313030c08060415150b030a02 67
    0x1501c0c183d0854908402520138041510020710442402034541c00a448601d061500940810340c01071400b03040315585d0351138111210044405c10616010051860180600c010f1103095001d1011b5a00e94030750308140d41d603903021b03501c0208050480800840c60100c0c90784a503151905420411407110151a01d880b0340d00d121024440d07800700420400c9410042d504503c4c01000102e0700d0041006a5650364181440081c10101d4200c6502c102d9010010460044521450564902655030261141c12601c00d15140c0803484c1c2000041c2c0130185400c10024003843c0d01c1c1907012080480200301c1e000c401c401030320b1b142c1b103d0244004e00074036104000088080003d00050160301d000c3d0501c4500c0d0f844403900030b209003c0c0109200c220041002c454014090750192580d150b1644295070341070300d501d4071750740c16420100d003d820f1966045010010322010b0301d00c0c1c0b8042c222000c040c10003803e0680c1c0384143d1003568901400d9140e1140408000c910034102d03824001d0400b007556564a10b04110743d680207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 244388354 1250 244387104 244387111
    0x3040303030b1306150f02150c0a020a08280801030c03020609180a05150d1502031008071724040b18010c020105090607090303020703060225050f011a0f010c1514 71
    0x6c140d420300114a40c07000551203201540c00310040d006c0e4607030812486065211800003400e5100d04002c01c40012030355002030400700020f40c0101c56024544110204110100c4010400c1060410061011074014901c00c0d040302d5044907150307590015800454525011494000100c11011702080b00320545a0402480745e02d8000940d00898220b404001c409201e030074006c1c040020303c54a84040300030581c020350300101e840a84004c15035844640c2441c04c40190084105c0880018414007140010041c60019441c0004004840300070852060090000204081c24103000000490160440e840801036030340040d0000b44240d60780d950001c1c1c0070303141c107403200c52580c444c000000c7c254030720aa04490503280e066000e09001031454440d0341c060b4000d444c42c00024100c002003481d00d1080e14120f884054803500150042051303500310a42101e21655000c1509000e49100c0101660744003c1101c90003000d0030074426036420340c2003800940300a11400320040d0f18007080d030700e0000401501c83d440f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 244389604 1250 244388354 244388357
    0x1204030b07030b1f030905150403050a09080705010e01030c180f030c0b04050d020d050111030414010e01090809011103070204090507030b07140d0c0512010902032703040303030b130615 81
    0x103803a00c98000e01110b60300c400d40e134070300c03403c090100d0003c43da02c40d0300305da03807810300500c01c13501010758501c01e40d1400305050b0703000c0f400705a0000748544070a0708035170120020002900500013240c90140060070b0f42221017009410156a49148040075020329008001c414605808040d4191101d0400048040c0b9000c282d90300341400300c00080407020482210b05444024001e480341c0104c41c0d00f488401200c20303c0403103c0c1d540b03e0300c059185c155210041e51240d8020501c03003120100d094811401c64410210315542c1ba41400389203408030310044111040c060003840c080701d0803040f94064074114043ea004c0294014101002e10080c03120008207903058034002c2c181101c0c1c13600c40000030b44040801c4a400311a0f840207018000174010a68482c080e00c1059090080c03a084002c816880c800800760000088a80d02000b48000c0d080384072078130390102a108820921001081e46a55a070b0300440c44002c08060b140e5800007003031b4444803141c5c20560220384050000e2900ea84c10034000904a401000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 244390854 1250 244389604 244389611
    0x90d060e0c130209030c06030c0d090516080a051f0b0a09140907060c081303022701050d020901090b01110a03120b0f0603150613080c0a06030c020607050c1204030b0703 74
    0x80b84040030700c01c0f01c903103c0000300285928000441070001c1c070b400040a00c071501c0340c14032044010441c0741c0900040544114083d2509411401d00c0780410305181c1c1214020f5444981d1000015500054014072030f90031040d601c01d00b00842c05640e024020000445800c13640b40c55000a02201c00d4100c03a0040c50469038050440e03171824240c80d654150392064030001003140d40d5a401013851f00b0020040c0c5501204007101e82512600031405903601ca9141c410300e0420303660a99500f191034041117024001c2100e58842d01d2003d0b030005041607006014854009548040350981030307008901c500403c40d00107060322103400050402504130a100b12001c0c124509000454810740341504c0b4006291800411450440d01c03040712180c1160340a180458100c141000030300045540e4125200c02400b0100081405501c05014048505025030202090608200030760501540100d80303140c0c0300031580ba006132a4000e4030865031070402c17454404014580001804024410580009403044510340c9003407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 244392104 1250 244390854 244390879
    0x9150705060c0c0a080c0c04021602040605060c1213030515090c03070b070602090a0b030c04080c191a040302041e0c0207050603130f14211806090d060e0c 68
    0x4840c85420003890f02c54004020200000c1c100c1405444600069421a103048581001140499100e0603048050101141c8013404603e880e0148030f000d40700541e4084c1c2850100b48a0a0780c0e480d06e1207011840e200e02054425100c030186102c03200454001044400003940d04c5d240040b1000706842e089018015440454010304000030124222007041d5640ca24003100c81e00d60704025041800e284d07903c01c11024002071280240809140a0007502240036034581ca05a0318901e04409003080384d014810115215400d845000c0214085840c088040c00654000640e01800b134030441c1c000941c85480c00d18840c10712840d03040c2c0500303c290313040410019500107503816641c8101034491540d0003802000003840c084000c5290a00b000c2c41000b604100b01aa03a80f0600040c040b14001c04442d030122244c0589040b041c10b91260030307100780502624124000105c0703c89405500c007260301804c0b0005481f8415101c0e026a00f241300e410090400c41000348075480d07500e450800c07d01e14410328507003210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 244393354 1250 244392104 244392121
    0xc031410150e040302010b1e010e0f0616020d06021305120303090a150b03011b0905061e03042904050f03040f05040b0a0503030a080406060f030302030306090603030915070506 77
    0x2640c0840d1103503034944800a10301000202c21842c024000c5007155280c01406c94541c541690704100089203c0b41d00c04141c0c41c240c00149a07121091400748141e2000b010b47e20143c841c4022545c071a80711448001c900c02e50b038000705205214000b03004110328400a0002100207520151030300351881120000301105241501c155603000c21b0725194616004040002d0014411002d8200e588800074400305000070180300103404c4460140d0794540298907054081c0f0910b5009002c840600030440781c01d41040300503210028842d1805d20350a00f00480040401c1c18401c5142e000d194000d80300e1008041c000440101810b051010794049820344502c9002c0407001d00c004c0184c5040c0c610072078a0008062400e4100070140001c80359154004010800c042600e0301c00744020940c2000c40e840e03c2916060074541003017141c1d92a403119401c91140030703050001036800301c21070b40c02400c06c940c26401a20313504c0001b4214401c00300500e60014100240014034240c80004d13054041c003801c01c2c2c1d20240d445098 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 244394604 1250 244393354 244393361
    0xc031505010e070e0d170a0c0606060c080d050907030c0305030a020606090610201510060e01091211062a061501140c100e010c23160c031410 62
    0x102e19010030a040303440400740c100404100013150042004070b00c40310068002445592006a181c0c000a5000100c0d03030070301c1800d000b49002401e86240018cc1001c01ea11501d0050040c14404100141c8072004510130003010080c0c0405540c215a001803065500e01d402607907640944109405070141d840021514508148414030441c4003500b60b03050880c3d088811030300800d41e0000000c07800b06089440c040c00c801000802080d0303140c07001c88801800c2c10422021000690b40c0070204000030180d1629039668010b03140021203072524607900310b04503503180041003000d0100240d500600003291084150405480305210400e419290b202c0d607401d942c2045403524012605029040c185d484500070b254801e10f0810034081c104076909003400410b41d0f2031030800c910302d20038041840c0c8880f904070100000703114040c0000c00b581024440b01c03095120000c1d1141244020808849000c80c0d01113049004451031201594091000c00001d51a481c0092440401006200c02881410041c00d04c0f54010310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 244395854 1250 244394604 244394611
    0xf071a030c0c211b0129060408010c0e1f0c0b09010912080a06050117070e1216031217240315040606050d030912030306080a03021c02010c08010b090d0c031505010e 72
    0x4039490510f451b140442c0190400e40034420781100040000040f8002d00380300308484854a030391401540b00c0d4403000c000c190327041501d0000000a240c075110840076005102242c080754404101480f81c0d07940e50b001c1e4010a180f20707010340f10754001301a10b11041c2d400b0a00c1440780c00f10000411042da102c07401151440d8035410411b000e403500c0000b040c0414043c60941d0000d00c0010b1020820a6198000034200a40407144520110500e002401004560f5210401d24070141c81c04060110030103c11884144024203407024028802041403100f04201c12524405040a8111008002c49019a011000c000c450960b6150b01d001c201080d185004149407078896051b56448182c02d0400081c0894040181c1c030850a2550780d40303002a11020501000340682d010342c0141c140e148030b00035503081d5540e03025182c80442e4074100c141407005410071081c50640300044600c0e5150f2440b040820a86294107030081c001c0301c01e4501c00010018041e80e01502d0119250090103d6680d56000780d00085058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 244397104 1250 244395854 244395881
    0xb0108010b0d080304020613030809011d06070b0702030f070c09050a200d0b0a1203030b0a050307060e030f07080d090e070f032c0f071a030c0c211b01 66
    0x200b1401c800b19000f9000707503400071300003080140f0309102d040041c00542071651040b2255000890920200e40e000b0411440b20031242c0680c030b1101c0b94030000500644100040140b03600185000308884074820015034040d030031242c8030295200c00d1800c1184030806c0303d20907100c00500780741c00a0a011140c3c0210318900004004280c0c058040d0703481030707520360000305c3c0c1c00301c01c075588107c8813015a035983c5801d0700a100c6a007158114800d1418004c0646640718503041c00340f11000700800031a140020088111112490400c0c0c50f4411400007a081900e040d800c4440c4cc07040700720104801c10045014014404580c641070040b5689480000381d8040841d000000314502c29820141e442c0260450b42c3c100002c00d40000705406001201e542c080c900140190340d5501041c0b40d010241d9040100201131300a10801e51683c80f0115455280340c8001050412804404035000c0c51400b001c0141c02007001006141083d2554800c407085016003014090260702050200c052042c0701040c400d055404114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 244398354 1250 244397104 244397119
    0x60a0e2107080309100c03020306030c04090203060a0f0f09030206090f010504030e060a03020c01050708060a080c0f1009030f15050c0903121b0717070510050306130603050a0c030b0108010b 83
    0x15201c1d50260f0704014a200560300a20406010400c02841200708401c215200103850782400b10603d40b0b00510f0000b0703140039601d0800820056a40025003a900c0b410f10540440d0808044a0400141401c1c465581c280c40c10406150200368012035903501c0341c000ca9084400c090821100e503801d0714010381e400740110300079000240d003d0622100900240d01c440c01c000d450034440030407103402c485c400c0740c5d4100001c0e03405040c4800d602e8107044060080242e0b20041502c1100000056092582d0030703103d5200d0091140030b101803601510300c040055403c0768242c40269050704101c01041f042d4003c81096a182000080044100d01c041c0d46800101500901a203411403070140c800d50b01150880300a441c482d003001340751101c02c000c400007070011300382200301a0070168035961400d010307900594810042c6100f2101340540c00b07010b0741e501440132a00d043d200c00c4c5452011008055542001e4a18051550080284100e00380c001d02140d210f100c0c18100c60781c0e038107903644c2250794850f92503a01156 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 244399604 1250 244398354 244398367
    0x90a03230d0513021002011406010504061b1103060a02030103050d030c322d0f07080f070b04030503250207052b031101060506040e0105040c02010e060a0e21 69
    0x74076804194425806100f16060040b41d4002900b07241c01100510010303911740441c2c4450f9180c03c414140c0244003800d0582c20b00e8104038010b0120b000e107480312424070740041807890500000f4052040c0b1106c002e0143c450504090100c18041c5d4001d0006071014803a4007880d0030503a100e8810074006030070503030b200301c0c0d648a44030b9404820140030340816414481e99410b40e04442c8410300800b0541d000360805c1e04005180301105d24104002c2880d14006841030152056014422040700c5010390b00c0100c581c0d440702e444400c0c0401c0d00a18901405440700c0508110406402c48010745c0501d142c01740b0801c5100342000b10401c031505080c40c0400507008464100014100300b000600418009400c100140b40f180020003400c0c90200d10960019207850715a1081030001e100381d4018000c1620001c0c40d103410070024901d6110103110f042d000e150359008060f4214401e502042c034003240003084d03030321a00f40401d826003e4903080e4001221809000c810242c08114500d02c2c8210641c0c0020343c0f401c000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 244400854 1250 244399604 244399627
    0x5130608040221010606080a140c0703211a09101701091e1202010c020c060705010b09010314280b07090b030901061703130b180405090a0323 62
    0x3500c101c0c0c210301d050b0303189900282051003000f40500d40c1000001e10602e8168010040394020f030224080500c6c0c104e00700380428410f0b000aa01000d0108116952409032404441c3d40501391889610010b0558181b0041d2003107030058100c913407400080001011145c42040322100050700d5241703c2d46400401003081d4611709403580354802c000310001451480c0c640302d04030110100642c06203045c80c10b001c04003c00a1b00d00009041e141584002c2140240306180a540c92000e1601244030700400309201003000030075001040070200c00b5100703071080e503500d240420800c0c40a0543c00320b2806040e280d2001c80d0031180e004144050750000041550003147c43e000b0300c0342000751038541041213150000c14111907440080d4041c06036540000780c0245044071a9100c03079000e0450711080c2d04104540b1590f455070701c41510a540810068a542e0890724540d8444401000d84a5402504140070401c2e03100003c24450340c028025100c3c07000541192481d400028052403400c82c000c4402d000f4103000c03030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 244402104 1250 244400854 244400867
    0x902090a15030f0905070501020d02030711010806130c0206070201110c0a060504020f0d120201061418150d03020f0105010503060408030a02030c0405090a090c060f0c17040302040e0a0b010501051306 87
    0x900741030030005011025904900c0640d180c2d0307142521a544481c1d8104459603041100300010201440507605016560341c030300c3c0c1e200003142c4415040121003400310320701c1d80d40c0d01d0031284021640034040080c02040000030352510303001c498040c05546002c1054a0300c007800d000326514212100051314580580d0b5036010003c120250050341c011003250003058483c1c84082d40f00e5446406005900380c0c0b840d00e200d000b400e4a40700d0300507014034411094003464039110a00c51080e00a411408041e10b6910450881c4201580c5185550702141c0a84105c00740368003c54800750744031904009100384c1c1e0301c54080c10707921081904c0050060504000240480301554055600b160a602040e8905666240084e0315030f8030503107121034402d0f80c880e8140204541c2005000090185090000c0d1890a101c0c0140c081548140d000c4c0008980214542e007018a42049034081c66008004108030700c100040c0c130756140c4512500b26110309140c0000310742c1e58041c1e010b5640039404a03078100000383c20300030101c80e070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 244403354 1250 244402104 244402139
    0x10b0c0718090c0303080411040605010801031509061805120c070302120a0b01030b090d090315180206190909060f03060e010933090209011208070b0403020c09010902090a 75
    0x1c540e070b891182d00142c02d020b0340000450181d601d45071036003001e0403c5d400f04605004d800e4400c1e0700d001c10401150341c12202681c1100e40044020018401d9040414060100715100900e507034501040c201000070725148040c210350254003110722880c211045d0b16264481d811408409611030b807801c00040c40d100c8400c038050401e000545030254103507624a5881c0c1c500384c0080740d003c03140360200000310004101c00580c50281c0e1610160852954a65505801c0070b41d0200050546036458420401500b80042c0580c6501a140c1c558818070950032200b1025200d42c408006540000005039a90050203000300f51007401c401803440034999503618005007070700d04038074020755229191034020800d00c4100004201c1c5405840220300b118070055020314014a0300b11036114038100e080d20244c3c071201e000c2415a800c00900403001404d0f41401000d9001d05a00280500078081c10801056070100c0e2880e5071440a40d80382a050342c0303440c00c14040c5e004030410a82c00c0b0014a204001000340d2072481c40d00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 244404604 1250 244403354 244403399
    0x303060a1511030a1e0e090417090603090307050c031b01120b0405090c040506060a0c120507050307050a05010c0f051801050904150503060a02040302030709050402010210021908010b0c07 82
    0x81c0702c80b0000070182150031000108000c501c00301100e80c4a035a07209442511620300d407600101c11408200010000c050140c006450240407400c81800d116041085900002004000c9070b22071a1606603e640c90b480071008075010f01074106080928100011450a282c01400302c504803507a20200450f0382044044065010390740702c03001994251100e100e282d003d88404405031030819003550512042d40c00152155001c0d40c410495481e13030f2603002055042865120411184085501c03000301c81038000c0040261050000203107a5080100024441c50300c00e2040c1c00a00c011003104030141d03881031000c817007032000c0b400070040a071144218241c00c603568081410028100115000820203c07900c00e8211150a50114410700641c40d0408c0126406551160103502d4142075034042074440c1064401e0800c0e40ea11031000c541160300a02c61610078450441d011511140d0f02c04202da00c1640c9500302c9004618940004150f042114085543d11b0380302100030640646083c9200780105074050b4000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 244405854 1250 244404604 244404617
    0xb04060f09060c05070c0e010501020307060e01140c13090204031a060d150911040513080724050105011b0201051b071e0f080118020d03050c120a0f020303060a15 71
    0x400030b661071007907016480c02643c659481c1c510310300c0c00c01040725454200c130310800f07107000042140380c1c4c2c0003040b120240d6005002203184401c03050300c14054507084560301201d410740d900b00034111480d0300c00f0300000c19070b030308400b54010340e24002d1100720b00c12400007520302040010501e0140c0404071010f5044203014020742c0d80d43c10240c0303640c40b00b5850700003407140a50f124082c40c818421881c401d00c0194000700c404102d0390401200046d15809003c0380103041540216003031051010111240c2c1e01c8822641d805845100d10070481d0008100034000c090104440c0c01000540b0385000703048400407681078503294680100412056881e0b1030003074480560307118030080801d40340c00e405a4040b0320003c0b2002103084506100c000003088446401040c4113a01d0001d40541000d40c0c010100c0305e003501070b01d03c01000b040b03608080700e06109511086100c0d10424500d490b445d14480d008201607821562070821082c501d20b812038480c4000d40311594006450030062100d03c04920b40000c0e21a0340d418000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 244407104 1250 244405854 244405871
    0xe01050609270702061f14010c080c03070c0609120b06040203190207060b04050f091b01091d010801050a02040506070803060d140c0a050a180b040f141806040b04060f 73
    0x4070034030441c1c81c03c005800000500420440d2500c0d5000721800240c15030f071440d400d05468103d480d908981481c1001900308540b402d01c0070140855034502c40c4c2e1010703a6a40c4856003400d9408000034421000040c0c141d980004030a4140411003407110ba108283c02021340b9441c00700406034001510715407074044010340704944145030f80f000340103c611075030f404149070850000308822914014240b050141c565004c1104290f40481d04da00204500b141344010310842500407030300c6d44900e800071103020500c581110100c10a0302d6005049400c900f000b400b90380d50b003980340d109900a074403929400c030a0500125001403240009194000e5014125034480d0460351a4030800b411104000c1c1403981010240d500641003401146014210a880300c40010b460200d030709010030030102200340c0d0269103252070709851795141c01c07805107000105424030800c581c0d10810a0058000e98456110a08a59000e25110008100f081c482c0b0b42100961074581c1e41c0b625800f0140001915070348400f50f4800c0741 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 244408354 1250 244407104 244407169
    0xe010210060e0a0b09040203030a051602150706060f08150406021204150f090c03060b030708030a021e2b0302090603010e0108011a031e01060f0e04020a0e01050609 72
    0x159402845010032410b000d041140c030300821290f10300403041c0a161128101300258400000304c441c0e259543c40c1c12503031402c844941c2144958200340007940003070b0655280e178828100c80041c01c58a0701958040208554404010440d6007061084c82ea403600800c1c00404040300304884a60311030b00030701d00580340c00ca0301c2400ca030713107200308441c102c4000310809284403411409200716107801e042030804005200c01600c0300c400105444c48000d16030b540b501c0a608941e11f040c4190302c024008002240c2d02d41e000f50001944504003001c0c07100c005003e40000c1c414010001910302c0284462a4007511582040070b200d031201010083c017141890b4080022405580394100114000c180c40020800d00b5410039191509440000700c040c0c100f255102104881940c0110707005846030070000b00c001c5008240c0c12040d02509841d8840c0707000c1c580c0101c3c000ba110342d0341c80507148554800c841c03806079140c5a40b003041c000b14082c0540c40c1c0100c41800004050b09160050384040300340b82d0300030b0512400200c00d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 244409604 1250 244408354 244408361
    0xf0a11013009050607020a0209060409050102070f03231207050f0c0328030e1209150403120216080c0f18150103150803220e0403020609060a0203010509070e010210 72
    0x800095499840a1002c2400801d000c20f80d00954144054060441140c001030714050010306902d100e0381d601c031307450300800c00709504803040a0341c85010040e49200d0f0f4140500551016150004107a1007809450311600310f100840341074900c4490602500c6c0c40b4100122016048440180c050107010050b201443e4820405881e00c0d0314851500e028064010f40d4014160000019400a041c10042c0c50500c010340400c4005800d005605083c0c1c640c0070182c00507074518440c030038a006000e0700240100034816140d00c06040401a5000c1344c0e50100d0382499015407507113903c2201219007000300d000c821894548036078070806c50001c0410740d0700105501d40701c001d0b4400703079904d980c002d8001d0310702c10780307560140507102145c000c410141a8151810313002c140c4030b11816940045140101d180110f0303102c140b00003100504200c1e00441c401d441c2618002e0365071001961059035034418440000c00c0055507008880c1030321005000c0d40b4841d142c3c80790640d00d24084c41c00d418158050300c20a1004440d4520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 244410854 1250 244409604 244409687
    0x503030a1830080103020607021306090623010e330f18150a0318080406110609011811130e210a02120f090901030f02030f0a1101 57
    0x1d082c09140d503146061015041d000e1a80304062090901c010005603031020140d034045601511410710404207590724034014a1107400c400c038440d1910401044101a001c2c0300208c03202c2010201070070300c880303074010345021030000c030041e03071000d19914054400052000003280b85606840c01aa0005d400b412040164220100b00c5600e140e010864608424641910304601d11007551004207a0507040d10f6410640729801400c028540c40d40c031841201c0c2d1490703609020300ba401900c1c003502e81d9240c072002000380c071079121310349203e101e01c07404140203c0061160198030f40395a074095007240500d584000c0c15101c044011035100c2d100012070744460030103000b0a214a030b0140c01406001c0c09002c4074403040a02a01d0035211624140304981c1890340000c0c0311015034002c00741d01500d13400d02440c2c2d20064400c6a09540c0c020041c10000001c1003640d1101000c018802c0742610744420b6400d545541d204016400601440407403060302c0c031554021400e000380c0d07004c01545203620000d004110340c417079443e10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 244412104 1250 244410854 244410893
    0x90c070c0e040f060b010f1418042a090f051e030708011b0314010e040f050f16120c14010903060e030706060b49050906010603090503030a18 62
    0x5090f8010400c141c4191150503000f42800ca6101307040410007891070b44203118030144150000fa2074100d2650303400d641039804e4401042400040b41d04400300d49080300e41800e090001c0c0c14200280001c9002d40040e0080d90515021800c140d8540320030400b4071454007c20114541c164078000d030660710140080c20280102d8000400c11026a071f00403000f0380502d800d0fa00030185071503030441c00c0c158801071a504503400d100d0700d4100f43c1c5032424407104518040400909601c00d489020541074804540f0b00518010102e6586000d985c4004100032702c0b250310401404100070030410702c01d400c540c071100c0f0300e41007041c94200429a04c80d9542802c48400d240c280300d0301d510100b0f13040304000050041c1d602a221543c0158200b1150f0282c01441c803010101492020186280c251000030000e00004020504030644100c03207054056843c0082c03501ba1060b02c500d010340000402c1c4180a8002d450310780c0e902038015407542e6101c10344040100740c00c2010300c4a42e0007644240020a00951030600e45c403c80c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 244413354 1250 244412104 244412123
    0x1a090405010b0f0d031e05040e0103030906021b09040204150803040f05150406020d0e063a05010b09061305060a02030d0c0c0b01090906110a0c050f0c090c070c0e04 72
    0x190810419800c5400d40f2040c0700710349168500000aa0020740204540c00c0700c6582001c42c811103005076414041c03600508800d00c12600000103056025401000312101502503d81c928494003000840c01070a02c49640c11868100c003141c014206580001e90070203110301c3c0d0602481e11020806d0541d8440d500040303c0c1c82c143c00c41440070746062111700c40c081c20031b29441444c00c1d20706030001e9286c540704074200c801c0c030aa05141046540750001152245080c00b07080d4170350070480001030881c6910a00400d40c885c0114251410862128440c03d81600c80d104007003805c20000008202117a8494041c0fa1040c101c01040040c464444002500c151481e50700039607240c2074101c42c0d0070704031141c0307001c608200072000300e4500101e021801e00d141512819200850305009170300700705001e80183d00c82c242201c1000070703034100d0040d440310f440e466652040044d504131502c0400f046985000b01951301d07501078020000b050100705c03c18010049184220b62032241280e48420062121004650655000c541c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 244414604 1250 244413354 244413371
    0x81006061b0203060705070602070b04030f021005070519020705060304050c120a150902030c03151b0915070213020703080117010203070e0906010c050a2010050901031a09040501 78
    0x100140e8040030410303158800d1031076a200e900003940d02d03900601428203200d40000d1503000c0c44882e804941c055a00152070328440c3c00e080c580103020b06a83d501201c0140940001400c010074140640ca00500440c4d03a0942070014202ca100100071010f040402940b088200c005000d44510014500c50341c012806842258101014004020700036654000c1c0d640011074000e000442000e8092041c1001100000351344c2c0003032000c240340030360340003625900d03108260300100c4800a240040b0b20416050703009104a4100804184550080000442e48900c904403c65194015a4043d02019000600410803012014419012644a8401a00007a0b0f41a0050014880e10904844031a084034001c600d10705d0102002007084030100352030740c4601e1300b0b1008102980c2c86059102d950b1070700401510450320f01454466542c1c84888004c1400404101520105140001e041a407400441d00c8180c075020840c170044006041c44503522030400300340c00440d205c0337440d001c554a06c04e51142c4000544901d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 244415854 1250 244414604 244414607
    0x1080102040503071a04091e021201140303071a090312131205032701020c0118050d0e1003050403091505090a091a06030a110a090306050601081b0c0708100606 70
    0x130300c1c0e0741000400482c0c25103000d02d1810035030b040328101d4801440001d90b0310004c102c10001c10303a401407072501480c00420940c4440544501450488194054505071110301e44181600c0b40244000603000c3c4101440d6170140001300075105510444a034141c13858910012a4602c01c08ca0583d4a080d110030f503000c0410402545103006800a031407414001c1c2185021039100d111005030606000c42143c00c0c0d588003162003000d405030f0b404003101d0750003408929807070520f0346180302101105551a203c0c2d40d803403040d0b0700d02410700842041c80140c848211410064401e5000d094090412800c1203403da40024065a0300980c80900b00501e43c0c5150740c0f001e945003081480491500105a441d203081c17150302c0c400645c11100020800141c589540780d42e100c400c510010000e403c0c074016032200000b414080d01d5071080d511016a0b114040030001a16420011a5032040443e104210751194078110f00e03266040101401c0012441811681c001c2e8030340b40c41c02d0400480a512000a9454010910a01d03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 244417104 1250 244415854 244415863
    0x2106180b040b090c0301020315010516060e010b01090b12010e1e1312030501060203160501090803040b04020901060305010503060f04050a1b0609081c0f020a060608031806180915030601080102040503 87
    0x1301c5045000b0b40c15801c00014603461034081e00c003c503041c02800a9803103203041242e02c925004a40141040022205032800f0602900203100f0786400034400c01c0d001f013074014032002540c0b4011840a0800300c2d07603003842e20001103040c010340401010720601d0740c440f044080f108040c920603000c0d001501d103400e441d807604803a0b0300c0c1b002003c5028503003820b0060000d540d000040c2c40e004030b200d80c2c4400c01c42c0040c4c205180106070b200e0026100310030010420041c0045070341101c2c0220710039511004186c1c0d0f2004110300300e900078000d00d981600700c2c0000c84ea50100e445041600240130f001034403a050081e50ba1aa580303503900300b00c00901c2003055030801c503060b0010309900050003003101800795a0b0358060341803c110f01c0d092150301070003440a04c8040c842d1080103441d070041d41c4000104441a00c4401082d560713001040c6076600014004042d00d00c4d41480703401d6800c150702d00c0d50b080365485c03910000c03c010440000c21100d42c2130f10000c1008400d035400c00c00030f402090280d00040c0c2d56420039080c9410b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 244418354 1250 244417104 244417123
    0x15030503160201201b01091809050f03070803010614040527011403030d200304050120120402101101090b010519031203240602030a03062106180b040b09 67
    0x130301d03200302d40341d004208049035103810240072142503021031310b481c00162840d507001e401041c0844c0311a01e0310300200300c03190b101e01d8009001ea0115040f0004030a4040e949100380040100b48040500040120314000c1505c500c6070549007881906154a80000c92031a159000320103011a0181609010b03c030b690160b05030161001c4102c21515091000100790390384615021400416940e007070403030aa14a018035000c010b05051502503480c145410828041c000f41a50160040c40c042d5903645605500021a4500500d02004401607500c540800c0720705403035001b100b0280140150f83d98800c0400313204500c00144603508000d065410711050207079800c03880d4110700090007200360a02c042024100101d07541c00341d034507004c40c58249000c5410b41c0508403011035010302e010840045100740d0080003605980300b840d0390401c52907966030b10001c80042800403000c80b20610007a081d0125034640c001d8107114403000c0b143d80402e40681d84a05c003200c81201c003910740a00c103130305100c01c520040c440401c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 244419604 1250 244418354 244418387
    0x1080c0f0f031e0c0406090f050906011d19030c080106060512070c0b0415240909020a0b0f120106051c0923060106030b04150915030503160201 63
    0x288a0403040d400300d50700c1080d4548240c900e000c0001807240f10a04009005500320b82d10440c0e15003400c003c03800c032a0b04507006c1e09010404030080071030f0079034000d8400402c0303542c010041c00c2181c44420040d14409a0444209c01c407144080b006d105940700c0c03c8259081c3d602c0e03281e04c02d001c1071450400080c0740d13000d50440c0304640d040034001c0203503542c0702090300c00760146046c41704a103071541d06017541d80040305c0d000200014000b070100814080d21000001814041980070b00c99121200380c00c0000d5210310105814001116806205452542e03000c400e43c0c520180c110120242c8624640105800c21440710000000000da50376041100d032110f940146150b080c240d082403401c0190700403010200d58081c002c16078468851782440001660802c59415071600798010300c000d50a000d480c2c1209026490220781024900b07002c50806201c0d04802c032a00100000280d8140303808030b0b0241c0500c840c00c0e843e4101400022010032400c0c4014580010503118440c3c070f4500601c00034200b1068bc016408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 244420854 1250 244419604 244419607
    0x203011b090f0e0108101d0703050a060506090712111e07111507110a090510060f210209010905120f0105070815090c0c010207050609100e0d050903150f040201080c 72
    0x10418500041c2004400081c140102e081c00080e500414035070b04003c4038007190300c00c0b40c00009c248031020600020030b50240b503040c0115540e003410b200121009840c00f01c00181101107240d804030a0364010a001145040301919080d820080d01054500040c440301d1503040000d114020408004482c65107220241c90704280a100103800809500407290003814030b242c0480700340840c0d030350054028080d10708903c0421060921001000c486035881c0100004101e0940701d242c41540107582e1403c00c0c4582c00c110070301014444104d040650000a1018184175045402051513074941480c00c803904400002032440d011601076075801d60f2000741560b010303c203102c802d00507900d60029441c1c2251a080d10340e00040c0d20b80c40d0260b80030744603003c5070035115440820b98004100303000c0b88880c01014440111001103002e81c02041c1118680d01c1c4100341a0321441c0084015805400074265a00004040e507030001000311116150850850344506000002410001190b8100b034800790070405034050913 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 244422104 1250 244420854 244420859
    0x504091505100513020a090b070818040203130f0c1203360306050601091a040302091b1b03040504140a05331201020f0c060f0601080606070203011b090f0e01 69
    0xd5800710540646848840e00060901b0b4030500900c0c82400801231810440d81c0c5802c00d040056607500284c42c20a20010340d100b0f481c6a6141c5402501d000f04013040ea506a031054a42ea00042400c0007642100e11071880f07140041d8125007851200660b60180d1906808100c1400e4008a002501c40001d1441c6203190300141c802c5400c014800142c80c0e03c5000080d55844800042c0d41890207070303111481440141460484031005039016000301d9109994605058450b2030000030343c003404c0c5441c0980b02c40203101150034a640d01000121450101055a103040d4440c40418161039895414007940c002d00030038402903950714880d8690001d020000089036101e403243c4203848407549000411486104800305030130303a9824045403624603048000b10354a5540546802c000d401c0032080f034016024082c0003580406032024006e11179001650307034241070366803981000300d81d0b0010b0800360381540d0391310305007031048040c00d00d02d8150400d2900c6402c0b5091800c1d01680c62054240c01c120340c6080c42e60f004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 244423354 1250 244422104 244422109
    0xb010902030906160203040e34031a0904020907091e060f0804150c02010617070f050612061507020d0b01050f030f1207080903060c041410020a06110405040915051005 73
    0x98400b5030f140401c0c25406511600c40302d80200c040915a11000d44d9498900726400303201301c030700031303e190601d403000e116881d08a9900041d40c00c02f160026000700004001400500c2c3c42014a9030107031050500a903c507440e810244070400c000001081808400d000500c641600440718010300a514a465001c0c1e18042d581c3c40383c8641c3d480b002010840d02e514042d02c42900030340001001d070820840301d40c20780d454084c03115603400b401d2080c070300d030f4008118000c200c41c10128200c44050660001440e1140c46038024002041c0c2c2424020040e42802e00165006917a4003d0181c4201d006a0a05119506020400c002429440031151003603103c0c82003482401b40100d6100e44a003210181d482e22008541012240c034462540000d0b4140250010040c0d10140c480c0500103a500300c51900032800c4501c3e050200c00e00790030340c201005da801218004001000345d0040b100c05050f9055150500d0750360301c080303010784101034401c55012036043e0710380c2c001440910841c0d911920f0040100c0c0d195140402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 244424460 1106 244423354 244423357
    0x6030b06060304080414010504030c090b030606040c0e01080606040e0c030f07091a03070309080c0a02090a1815090c091a0406050307210b010902030906160203 70
    0x300e26141084800d983c07242da48442440e24080c1448040f28410340079030003060410a08000200004070b20064850051600020208541c11140101810000c00a110760b00a900c2c05410702030840d404108000044020b0031720fa007882d180d1101064147c030564011240d05106801801094240a001181300700c03c04640b26803161283c01c02165807180b903200e8400180708007110841e0b101544401545c00110394180001c2d42007440e5035850f9070350004203560f007440e0071030046c18003075051012106602001e128802c0203600b007086a807a102c0301504002070301c040b104010000c00802d956108003040c682014444072865510700c01240600751070880c81d02c0c0340d00048440006802c040c0036050035140b00030041c2404605050000c1d813070184580e141d0403015141009040800c070380c0d400260107062503800c00350350385c908903410600c0c0407006046c1e0b0145a40c400d5101d20807990120 = true := by decide +kernel

theorem cover : BRFrame.Cov 244244604 244424460 := by
  have h0 := BRFrame.cov_init 244244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 244244604 ≤ n) (h2 : n < 244424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
