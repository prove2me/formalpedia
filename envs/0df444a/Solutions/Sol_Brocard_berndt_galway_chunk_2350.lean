-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2350
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:26:50.692472+00:00
-- url     : https://prove2.me/submissions/38574a9d-9c9d-4f28-94f8-6945ccd23b47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 422482014 ≤ n < 422661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 422483264 1250 422482014 422482019
    0x207050c060a09050108090c130911150a0c02060705120a02060c0913020d02070b0106030608010e0c0f221a0114130303140408060a0504030e0102161215050907 70
    0x118501040321008500801c0140028809036800c120410b040f40c4080c2840441d603601c820195040c98904600b1961015103100d210303450000d6507000400d164800c0728441401014101002a000c150501c0e02840c00c0003080759a1010340329001c0018180c0c03014200500700b2000380c0d545402c00d54454400d070b80c5081c0120302211803e60400c20560050605601689010b841c0310120350300b816032900644449400281c0030305d41d001c5a034100c1d55056006901c144243d615018010058001c3d803281d500d40d50700381100101c200c040480e60182825000b040381d10010391000600044100d480348201034060301d0050304014484a0003501000f031082401d10b18001400400074124003019012914a402c062050f01c560200024075101a26058186003004040c0c540340d01d061032007150042c100d203000781003d00c0326050441d00443d018501c00d458110310900c2080c01242d4800c010041584203207812201044400b0301c503034136440800d0040341240304141000801c1390549005640d910034a0384910b004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 422484514 1250 422483264 422483273
    0x1509020a360f1212050f0a2102160f021c0f1203020a05030a200403030e0a300602040509090a0c0603020313060b0406030209010e011d0105130f1d010207 67
    0x104000b40008007140a9000d051900340d040820f000000101104800c40c0070703015044c050810b50320002c0c05281c8507a0740d41401c00300103010048581c61005589000808454494814000d84150400042c603d03104624241c540c080c07031880f802d0060380c001c42c0040c8808038805004c040d1580207801141408100c2510749089038480380b5414910041510502000100941c400e007180d400580152002c5030402c18502510540f04140c00c1692000c85d0004002040640003c0d20701e185000494040ba0041d80e036000b8a00044d4030700c4040a180402000303811050540d00b0f8000c2c028034024080141000d44030783c0411404142602c448407070380d000203a0802005402103680002d0100c17458250701713604202c10603544900103910020003c5480d01800c144031344880d40000b00540d0010900c4e43c032540d680e80d258401a80038020f070100c0360701c002701e855800b20001d0000c0307041300c00c003812400e801d10602e4044401019038641c50b1192130744034025600e00d031030a500112401c8074920f0006230ba03400079140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 422485764 1250 422484514 422484617
    0x30906071106041109183702010507030807052101170d200a060f0603031d010e01080402060909040302010506010f1706041d0d0c03121509020a 63
    0x52000b81e000c0c8007080000388070403c040c900c0030300588488406880d80320000d0b030f18440300004050039204521000d0011a00c04c2080c0c00741ea112020040d4000310714a10074803940c3c000c403030040d0101c2c00401142d00005d1040d2625a484040d900e00070f400c02418000d2140e460070030b5000045151a414014000300303203200411301207907100c2402001c000c07030b80e101f000d0105a60141c440c43d11440e03802520880301070070b102018070b00703610140c02c00c0001d440b0741116000b440da40c041500040d242c80710740b141899400e0040c40006030142c462011024561004440050004108a8200000b07101c032000303a40760b107c032281c0170760711030b40011960740f50800c00144241e83d8060f030a030802610302551410040c8082100e504024181d801042c10300c81c0c10441141e800c40700000c940da5219294200340701d0703688460301d07200f000e03c82e03a6400c4004c0d454110100c103031842c4840c0320402c100b086404000e8400c2e10b0340280318803012401c008004d40b445860fa0141c420501f0304d4100007501d258540201c1070300b01107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 422487014 1250 422485764 422485787
    0x1020a08061806040b01020c0402030901050f3106061e030201030e1b0909010e0706050a03050a0b010813060b060d051005030a120e0a03081c060e15010c0c050603090607 74
    0x1e51041541c03030302e0003840c20300500240c440c9001c0d5651303810a660390392003445120038003c0040d009540e2424100260b80c000c19040706c2c003409684038071010401e00c240c1c0c00e4200110705401560a080c01001d08520300014213582e800b140c500d035a440e000030703001118107000038100720044080b120035031a500006d429520810030510b542d4011074070100300c0d52640030031000c0c02c100c10360f00503080f5030314051018010940491041402e2160711000618280d200000b440315134200c0d40d00b4080c1c0d407200003d0320117580907820514049903c0703c00050286030180345004d03a05000d8040411803801300740206190781c0c0300b9110b000300d4a132503408000e2100940300d2400001d0406500500d48c9070950f80301c0c015804008000503080012480740c8915680d10a022080034581103244079560390f414240380c102c0c1c10340003910607020b00c1c2030800002d4100d0101c059984140c0714a840301030008891401110101c10981d0110f4440d4454880801e84d0340b1200b01035031240008400a0180e820120005860042c0c1c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 422488264 1250 422487014 422487019
    0x905030106050109030f020a0b040b030415060e01150c0803010b0405040e0705030a02060c01060806180609010b150a110102030103060204050307090603020a120f061407090602070b1909031401020a0806 88
    0x1681085666444440407080380c1e0048600c101c190040c1c800200882415031181d8401c070000b04003c2642f050780e10045000b14031401c4c0d249401c0c0b496a80550984085118410744180000300400014825801080d641707400d902c1d10503210349503544d403045075820030b07040088800c1d0045414401401d041c0300d801e40801300d5000400f2010b240c200001c0d42d40002c082c00901480006c181c4d1441d20f00c094020780d0152640c00227451803450004605490002e02400d046102d20404003c114142018030422082190107007215080380d4079603540d40d2880c0d2001c1d441c002000f4014040c030126140030b1000c0c5000e103200d10405a07985141804040c03038840c450f0000d0030f1582c0b03060002c2005036140c12044086828011003c0252a0682031081085502d010b01401107400c01010301c210122206070280b26101c0c580f00c014940d529003004980c0d41240d4064000720340c0d010850310705d41d4441c00124554142c0d4518054040f15129a0f0750342095140d840c0c00203040c0c0d0041070201000343c20943d4190b1040e0107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 422489514 1250 422488264 422488271
    0x2414040515150c010f23040b060411070b0c120c0406081603230105131404140f120d0506010c120c0602040b0c07050439120608010b0109050301 63
    0x504800c408510050100b40320b0b0b2030540d280c80303802d0110800d8440e84858407008000d40c40e010b0710110060000382650104803000940409100b0458000c564092600181054419a070310b800b480001c1c081d00d0b000c000118424081c042c0000c0c0450103c5103e80101016a510f136144d04c4580c101600740503003030044030786080c0000e20510340d100840c3c50344a290008404484900d584094004040080d0003150080480c820020ba03405240482070403100d00b500c2b1984081c208105000c200d132429001e0a4003800a00045004514442c81d450080c90b105400da0b609084040c2c02d4628205d000400300070005000706402554055600c039081e0b110713200b8204640060100e607180b000380740010174450240440c014201d02804810780c19034000d080000003003a0344060132204a076030390207940b050300d11681c20b08040c810407020900a0144c1d40b545116100c100645450f8418090261203030010704110070840d42548801e00350140341c0040c100e40000056007807170200010300b4030115030410350281e8103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 422490764 1250 422489514 422489521
    0x21060b041a190e0c07240902100f0504030f1b0e070f1805040903020f030d090b0c04030c0312020c03030a0c0201080610080c09031606110d0c050706050c0124140405 72
    0xc0c11890700e40c400440288181e8a4000b0306e013210203020110241c4070459008000c0f0850715025610004500303000319000001d22980110482e0040099800d00e00026418081040040d09902c4801c07465449034403a89260800407114103001c6805501440c0d40b021450180225160080c41081028805203042c10300d450000d2910200c009403440744c24003d642c0c1c0e00228051520a000b40003880100e40141ea0352031241d0300c4c083c4041c1a01500903180d40c0307407510201d10240403100803101100d902002030640b207840c5464400d06002c0781c4000d2029801240b65070096075409100400d90980e160b182c0d0707170000c103960000501540300180681d00030600400c0b4084a9900001c076103a02c14560340041d030303a840381785020a00b080c4402c8000240600454070224103142c00c0410740c4982112441183c88541e0344160444440411400161070b13500180383c01d2009a10400041024410600000c502c030541c0207048603112080c1924136455405d00801440000510010b2440000085405014908 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 422492014 1250 422490764 422490779
    0x20a0513091b0e010c06060602030a020f0610091e02040e1b030601172d1b0403200f09040f050d0c0206090d03170420010921060b041a19 60
    0x8881c2c040301030074400042030040440e8841c000398040582e02a6042c808290f44c6c0c0d001079503e400c41000700c0050300035032030104036001002815520590204113001c500c6440c0298000041c4903844d440515a410345462504180c2107000500041030840500c90741840d0404e86840b00c40d040c2c0e6084c042240d010414456140e9000004990380c03885840e01009a2f110003007140c0a00660711a0700ca0410355061b0104d0740c07103420004d46407050394404116551040000000c1c4d00714030450000170203590392003414140201502000c8035800d04050004a41800800c000800b00300c0d007210110381c65800342c1d4040080250034072030b060002d440d90600d0082807440c0d80c0000d003940030304441175004034a403502e4101407500c944031020f22000a2030030ba01c89070a250928013685061440d14940341c041c10718648126510692003d011a9101700d08a0b032031906411a4602e408111a41071340c0064407803c1c5040d503542c1d907106e401c020705141c50320806e5171200e501c01d00aa05000201551140e10388074401c002e440d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 422493264 1250 422492014 422492051
    0x2c0303122a12190f09031d0907020a080f0d0203090a0204110a200c06030403020604030e0a0605031603060803041202180c030117030d06090b090619120213020a051309 73
    0x1055804041443e0720542c100301c00200660500c1c507030098100038922090680000042c4003401140c0c402c00420840041481001c1d10181c8240c80141d00408070007020441800c0505401c021000c2158600907440e0201426a0000d49448825070840e060041c214036040c410407210b08083d0f00e0907410719046000150840d0560b4180e20b421140c2403840e544040420b0104141a420091a42d51281417a0070003d654a4040310100c002c81c070740700c00d40311952401c035103046e08982c255901c076895a568141004c40c0d40a2a840820905403681d0340802c400e0410300140015024150b12140b0028990042040b100d000d110072840f1005034605001c0030454101c00c072815504107c40429844105410f064507600c0343c0740700c511241e0300c2c019001c100526140c102240c819001ca175041401d03201c210400032003000003003080790302500000c0c007044854500f10b070010300203000510140000303001d07200c030030b00740d0b4000d1910030300141c000960b403110402c2022180010b080000001c02410869150f2017406 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 422494514 1250 422493264 422493271
    0x203162301020316080d050106090302180103050c12011d0d030605061801050c0a060e1f0c02150c0702181b13030219090c02100c2c0303122a12 63
    0xc480502c1c0804c28081d03004115002d10009403020400ca41c1d6900700100000c046000c00c074800c020407004640714540d82e0032000d050f20b410402800002d4032a008222241c0814819225507540b03912854a02060514904103640480303806407200260641c4003c045417503d802c035500c00c103002e10108000f21000b03030b00740c1c0c0d00c0e12080c00c015035100e0030043c90a1030811103510090185090441c0c0d2480c44002140640142e08040e1200c007004480100300b20585800340742d0640107074000901d03101e03801c40140103c4c0d00032901a100d40d1508003542c0104000c0a0040340301d8108041d12814040d20b960061821114800c210365254201000f8201880c10519580700192080d42d003038200308910090102d841004101a50b000c02844c0890b60019440d0102298407441061502a64640c0c4d03501600018103060514003002400311012013118035094421119560140f00600403004821b1131807001c24001d101800f0008400c80100300141d21407442126843e00d080300038442000d03420482c4880540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 422495764 1250 422494514 422494537
    0xe0c15030a020705010605060d0b01032306090601031b02030c07060903080f09060405040e01050a06050f1003090f0b0f090f01090b0c0a03140a0b0a0b040509040215040302031623010203 81
    0x3e480280d424002e000d050f041c1c0102d5840f4000290415440d000d070b82c80300f9502c24082c0c8061100b2a86030f10300e0000c0f10741c0e41c0c00c845001c2c00789000046d22454a2405143e001205060010f410440980802c03402c060004c1014090707800024240c3c07001208000100080c07000f4038003070081c50b0440e0380320342250003040c0030100a80d00100da0311034a5903649083e0b40250002500412540441c0030066000c4c120540d400030449152a43c04621814015160520030307002a0295401464100045005010340d140c03e803141d40300c4449060006000d58120380c0290503203038190b86141054210982052080601581181e00d09000107000a24a01c0d130f845c0d100a4425030300e40c42c1d5815000650141c0a40c0c00c2c5030090500c00c0b41004641c04050744014070340301e400d6031030110203602c50382c90501c64400c5000302640040702200040c0180751808004030040c604c45040350405075682d001c6884c01c0d413100c0d4030840c8009852800e100440781101c009035840d081201c2060075036141c50005c0c0d100c0c4500390441c0d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 422497014 1250 422495764 422495767
    0x1e0e060606120a0605090a06290a1803080d1e02180f190b041509140d080c01060b0d05090115030b0703090c0b04080705190b07140609010e0c15030a02 66
    0x243d82015507480b0a000b400c002d840030780b05140c4803901c1c40040071240100107404c840210800c070380020304000c0c610307042d01e04011203207403400e040c5040d19125500400e48a62100c190008000140b03813802906415200a0000c200c41101e090003280303500a46600b222880e20501030a1f00340c0403013850303030a20302c48143d900b101021032140119542400c41c0c0359140c104e0b00051400944c0b15200c000030412501c00d54481e51816581e45c1080700c1c51700031882030303503100d0001407021000c5180591003440c40340d00c00e80e0b0040c9042403040784a801d59500e5400048210030210f00c006250141d40640b9030b0060300726000304080303220200289035100c641c1c080a0030b5180708100103044240680d100300d9015800844e40c51459641d00140074540d8898068001103000300d070000103480c18944422480d0280034021301c41d00394107140c1c43e000d00d5044600c040d42e441c84070100e84802e6010600444d80142c1100700049644110042007919015448200c54044d080141c5c025a64400b04010340c0c2d0411118000035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 422498264 1250 422497014 422497021
    0xc0c100c03170c090904030905031e0709020c012903010c0e0306040b0a0b0a0e0412030207080301150207090c0302070b1b1b0309100801030605150918010603061e0e06060612 76
    0x1503554020142c13501d4100070750790244024036402600c20030481d40708808440398800102040d90080e039800131443c1407a80a0303c000c3c40401500d401401c0000d200d000009503507441340100019441c40b21060840700ca54038506158281820700400328070351814141005c180c01380b0780100e42d540000410103403800c58501d000c03d010032400d4100b050940d400074208011207031104e0310f900c440101660304495402134013400703000d15402402030702c1405400c41045801c607880d081e1900036510030034102d8000c50241200204002c20f281c40b51042c11442d030340d401a10b6210030324226444034805040300c030b420941342c1034126403502c00c0030484907502c4440114581300d0305556021403a500501e0708060740b04606075024591540e02c034803040d04980c052602400a511800d8061140d080d096042c3c1d904544840001400d541035034040d1980501941d000041c0503a4989884040303a0100c50348030066540c1c03070b05113081000c0d1800381074104070750400940b246003099400140d051064507101d840284404000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 422499514 1250 422498264 422498281
    0x70605040c03060f0b091e06240d0204050103050709050609060d2a1e09120219060201022214150c0a060209040501060309020109050112110c0c100c0317 67
    0x200d070003035900c40010700c25144840020302c090700c03100b0400382c041e0792110700003a00d00000ea030204542c0e640044002c1201c2d280c000030300a0500d134021110304800c00c045200a140c0d01443c00900c40c0000c100700068440e81070000040c00e070344d4040e0140041001d4913001748107690f03400c0c08440d11003100301d41840d91800e03160090809800751590828219030100c00003500b008080e4a603a181b000280e550601c451203c019007070f0260309000f8400d000500e61407013844907e04606c4118107a500080c003020703040b000b5a5070080c4100150300400b0041c1d401003458406000c1d00e5046030202d55680c60002c403620b042c0068114544c0b5820301e400e201c1c60a10301d00c1000b020005c402c03500c64040003001e85030300c541e8a00380f00000c0c0d4403000c0c030710303000c0c0d0720380400020424842e1195019199050b0341e0785883c4c0b0701e840011143d42e0110590106515a40c0d1500a80980b11000a013203e075042c8010b0f0841c4140801001040100d411842041c00b240880080003e03a0059034483d0158011030016440d4880f00304 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 422500764 1250 422499514 422499533
    0x170c130c020f0a06020c010c1112070f0503070f03121a09100f0b2104020f041d0703030c050616080117032a06010b040b0d09060b030304030807120201050c07060504 72
    0x80650749000701c1d25080f003400f100e07400805080041c50000e000d6400085e00071180c4a0301d0812240c0150020380c9031045c8180d0307030310041060500480340001005820b440c0c050641e07228110455144c2c00b01d4480c0f00415030048848116a9081c200400c41c1c411b07001e00c0c1c1208403001030040c510603404500003966103000660b818018012104203400c001e42c58850000066101d079015500c014040c0d0b00c607071403841d15020716034410f0750b0107001d40e82c901c03100c0000d000242441e81c4907450703103d14030107004400410411040c00158082d03941c00c00040081e0501e40c0c2001d1026007034030b071034208080790100920b800405050450302004101d544070140041c49605501450701c80c4170440b50f2070f103502910341130b4030300c40c2170700b8110b000c030903100141d036581e1241025120751305c44c54542200a21101a814926a00030400180903800105501e108000040c0c21507121b030f00111502140459070100f48440180c0b2490070f61100d0000300001c1c10175440308840d030300800b400240900d4880380085c0030880f6243c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 422502014 1250 422500764 422500783
    0xe091e03090d0c1a0d290f01030b041b0e04050103030206010605070303110301060c110a05150d02070501050412110706121a100302180312180a0b0d0501170c130c02 72
    0x160402d82070b54182803560304c1a400540c1042c100b50400c01c41c40c80400703100c202550200d16503076242000d40c4041c400d005d200b58100700103505050f82c5003c41030345c82c0c85601803040300304040303010303001e14003000c034000b520208000c21494010f42c40d1200600c00280c0000c0e00c03505552407410501d4462009207011000703040b094050000e80e000120000550a0304500c1c640b400d5441001c4407490303480258180003007940381c0d1080a40c4682d000c0325010201003400c0c01000c0c3d100015001600e0a021034940d24250340c0281c4044845854010061560a5120b000c0341074034503062025206241c64584001c20f048191408508100c1c0e8078003007079013102403c4088110082d805000210404e051510150094002603286190070815a04060b4585004100411085507007600c1e5400c05440c0700002c07038541c80101c3c106800483d503800108844210304090103210300070b0040460698107040000707060034220141d03482039921246070140c1c15603a41c00301e0882c0c43d213000c2e80094000c030418012440d0500e5003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 422503264 1250 422502014 422502029
    0x60f030213092904030801080d0f200a0503031806010609030b0c0d15150905030601141503041b050a15120b2e08010308071217010e091e03090d0c 64
    0x2200c400c01e10028609540308174001d85071280c0d182c0e178a540940d04c030303c80380f282c00713000401504241c2c54190055600d241032450003100041c4400718680c0f05441c0950b140000d5980703510102c00c1040160b81040c1070786c440004000071340b100b13500d403a001400102e0035000c014540801400092106008601a030b6900c1c0106101841108030882c00011001440d000c0d0079413044100b070311300d43c45502822031641160405001031102e03078640042440e5080710f0069065114503004405130480c2505400365004a0250b81210780c1c0d000300055030002c0030b10344d502a502a0320a07402c1040105c0d2148001d442600b5242020007111040d201001e00030403105007116030000310340002c1003949e51290a5140c4850462007848a90010580c9c1501c00640911000305900800c1200c0400110800480050403c0c24280500302c443c0c0c150a004507002c098011615101e01c00042200b0302900b0820010858080d0541400a042241d0680e840c1d1081c001018040e012000c400310400456181c15001400d51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 422504514 1250 422503264 422503313
    0x31407060c110615150d020d020c2a0a170c0a0909020901050334050904030e0102151515040503030705070e090f06070e0f0a060210060f03021309 64
    0x800040c00402d81d0802000d920b01c40d50f000030340031040c0c0c00651820010002c1c4200841c106040c0e0b40d15207548503c00c240241d0781c080c00080903041c5a40050038800550102400078032030600d007034285c04914100d803142c0e0000800f9145405403101036090064517555220682103141140c25503282003d0381c1685038112201500000e920340460b400881d90703d200315040402640d1301c10170540c4d64007030311a1001600c00c982c140c1540f01e43c429415880c0c480000040494001e642c0d20018079440c10848065020600c0d0302c0200e8285d61b8180b015540803811003400a000c2d040246100c1600000022441c1c062418013808000181e410b1040c2d4004100040441c3c0e502c80151a10710744501c900e21403203034004121404100040c401044071024032078002c0082c40680d0b100441140c91214880519030800ca0000c01d210080d229082207401501103034000b0f000e03070b0720498000c908840c0e4540c403040050482c44c03018401661071034124050107410013408074000e040d5050100c18481c5070b42054140781803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 422505764 1250 422504514 422504531
    0x708090909010501050a0f0e070503040507080615040507020d020c06090d150b0f06041503360506150112050403091d01030309050f03030306012d08010e0106050903070303140706 78
    0x1d05400050503a03109032000d404441e030315240c961805285000750a0405002c200045540d0700c10000b075640304e4052030031151034564400d25035044c594291603d035803001281d202008182000e010b2550002041d10080001e0404400000c1d2113829000d20284501000110703c44c0c2e568420221215190f002441509068034064030781c0c0c01030400c000000d01805040000490038900b600688046500460142035440c8581100300c00412a20707a0300d0120118941c007002058600806d4842008005240d2000d88806401c0903803421000500350101840fa4000180080e68070035a0016012039580b40465242c48503d002d54120302030390440c451002c00e0781c0074800086003a54450703049900070349402c0001d41d00c0d6030a00140c0201c144c00759405d0f07072041003c034520394800c4031004140c1c1d08040444100040a01018141107024054280000c60744d000601140c03403031543c01401030a40307040a03440c065540e800f00f0f4a48040344006018004078444018805410f0000c4882c2c40354004403c1000c0034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 422507014 1250 422505764 422505781
    0x506181c1101060602010e0c190909080f0c030a020f0708121b0105040f0312112b0c030207020a0506040f061101020c0a030f021005010f090e030d060806192007080909 73
    0x203a9a0314047c41d1b0301c034840801d2420706045003c4201c2c0d00b11540c0c078001c07203424500348001411100808481a0341b04000114000c01900050924616410081c40c2d45e0344288030001e10300501e54002e4141d540042c402004402c1d40000c483c4081210130003a1521000d094240658407110341c010b12400d94203240c104020010700f95900d4050f1446526140051134149826a0444410b015099603501c3d00b0000460007801415840212020411907041c490608110590a40d00d460030b40c2000b007034001c00e244085141209540016000c1030351614105031074040c02c1d00c0d0100d034910441052010b0340c10906500c040c01c1d0103d4a0701500b1208403203004400d41b90080c00082c10440c103034014005d00000c5034446140d4082c03107040f241016040d918007410329000700c0040c010042000002d2004000001e070040c03060180c08001c0507028050900c1d450000c0300004544607400c01e1444642c503018000c1a51052490b50014020864070b00945610389807a042c0e42520440915075070006080d0200240702 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 422508264 1250 422507014 422507021
    0x9120106030203122109060106030b0d060c2609060a0504050a05030f0403030908010b0a09020901020309090112020306091204150908060a05100602030702030a0602071703040503070506181c110106060201 89
    0x8121010a02200c0384603d00421792084280c58024050b0030940c01000800c0c445e4000502541e80104207607284034859580404883d848141800441c44840700034a0490081c806220000c00b40403201c02c1d10300d00706e01d080d40c480b0b10007407007031207440d545178013040500008100b000b082c41c0d4043c0840c1e68404031240741c002c01343c1080c0700c21400900c1c80000030400c0f400c18002d2a00e02c1e0801350800c501c460030610303014040c0d048510311504500c01400000300a41e07418000f54001d10031401c00d801c13450b0150040c14100700c80105689059801060321041d415412001c0f00c0848000f856000114840003104441050b4030303034070240b021300c10341e414000c542d08160b004a0140b901c07010356011450ba82d05060340c0701d01500034040d515070020f030203030000314200c2d40050000c14820704840140c041e41072450241c542003501d003a60150b102040810070441700300f20990f08030030a901c0d0b01c060390440c1507206964031484400d03031a0108400b9514440b8600483c1d1043d0320700b0440000b40505921000028000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 422509514 1250 422508264 422508277
    0x3080306040506010c031205091603030e100f17060112090302010510060206012306070203010905030a1202090f010309050f0d11160803120408070512040303230912010603020312 78
    0x700d1500d00030441e00d42c0103041e01d42c0e126526403510b030a00b81d410a02e2a008002c0204000b000b8011441c13071150620404440c04d02441c8240c84200c14100c44005010030405511050b105104981a4400e9066040190b40b19248440c002c4150f850341c58800403203450065044824003e810006100c0401da019000140b00d81c100145110b8070b15980c00d4200d036545400e200d210074480d44005001012080d03258241d80d601c0c0050306140c0f0303181ca16804682110721225054955070400300e40d85201560004000340b0f00d0a2404c025401d000001001401900c0c004a0007414565100c0d000d0781001014001d44120f50100070594407564002c0384098100980300d513800703406005032504403a0a010a4001c1c1d02514904801182803800c0c0400a026501001c1c0060324655400d102e204001103007000503281031107d00a855403038a103586806065012100301030103100e016041d155644004482c1a102560011141d0035580c4014040d403070300601c12500040e4050056400702d80c102680b0f0001040f1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 422510764 1250 422509514 422509519
    0xf0606150a091a040509070e0906061602090115080f04210c02041b260a0903180305011d0f0606280e01050f0d120807050f0d0501031e0302061b04080703080306 70
    0x8061fa12440e0407200b0043c2030018aa00030034102c04101c09080c408003a0240010f110003000d2000c540da00000c034400e109a101c4900e0344255030003405806d030f1203041d0b141c01c0201c80880c08481d040075035075100c409100d14030003010907601d0a24600020311645031944980e4014104100c0c42c04080200300070000c00a40c458003144000001302d4140e00403103001c0710203205081c4075459640301c1d19071400103405407140a0f420009140100100907070749100d20701c0194071620001481d0340040c014030f00f0190101180320701c00d4014000d551700f041c4000c940d295001a085520b545216000007064558540e007044240e04c2652000012a000308007480c403d041e5001111294642000c440070040c0c0300120f40d400400d0f000743e6920751003003940101c06941c2c2024640c02c00070f0a00100c8100c0b0030342c035080790043c1c240b003d485200400a000000c459000103940036081145c8038a0540c8029594140151100720034980c10140070402d4030407901070314054003000c03041d01c40e1180d42c0d0a00030001e030415100d0a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 422512014 1250 422510764 422510779
    0x60a06090311060d0f2f0a0c140c060a09061b08071103031608030105040b120718020d020705212104020604120c210210032316020f0606150a091a0405 66
    0xc018a001b07416942c0c541425a90201d00c0d1040d590340c0d4140704141c1d00b8505d510f204450b00e140f00d6595802c040c00c03500c00715646201045203002c4c1f0040c8682345035003032048910160001c00c03000c90b101c203044414180d04100c0044201060f80007007440d6210302502c15004026050885007000400c000440c100c0728100d81c02c0c8a8141c0800420880031203d6180207500e511071f04042146107266203ca0039401424030300141440030544131041a41d00000c03040700c02d500701401103492490380484203902223100c01801410f040d000e040b10905100c80e04000e000d02030040c40064215614401110050031481c0d840360103407203451509120705085406005440c054074607070401e104a040310002c02c0399400070301c400200c04820a003680107004054412030790444013400c0e8840c8180410405004800c0e034010465000300c0d01c0c070000d00b00440c5844140f2150400c205000303056440304182c40c5011301a1545c2c07551010140303015900600d0303079840b80180c92032001c5191800c03003040c000350040714010350703c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 422513264 1250 422512014 422512091
    0x70c0506152b0209011d24040e030f0c031b03120420030a140c04090c0e10030b250c0209011701020d0e06060a06090311060d0f 56
    0x1c1c1c541000da00710319085450052844404080704410b980c00c03000044840903165000d4001c902400d1098010008402240c1c078204e8a0009449003594011505104125210307038802d04240da2a114202175481981c5441c0400c068a03000d108581d400c40d03504285035903403032403a800c8680701d8101d42145d048102c680010008000c00100032070f8000995421030141d10380e0780e995441c0c5d001c01c0c01103550900481915400d074071030300e0800070380b14031500509282480c0301c1600d1109240c40800103050b07000c0c900b400b140b5000904140c0009056030f64481030480780b0380e601003015981c411580d0018000751458418840004081e41a501129600004043c0806980407041d200d001c90083d00070f400c203400d080104040508a107c90f0380325030804002510b8041c803c1d07144015144040000f03145508201d0034021a4908280d84070010302c02c9040c1041510702d0f54070780c0490f032881c091440340102c0b800101201150016404481754418a00d000c00c016220308004a032413000c4c45d04900950740050458 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 422514514 1250 422513264 422513281
    0x209151c020127030b2502150601090302090408030717150f04091a090f0d020303061c0305030406050c07060606050702090903030c0a0e0315040f0b130201050702060a1403070c0506 79
    0x20400c103e80c296400516182c0b841d44c2e100c6041400500d0410840c05da54520f500300080940c00303075040107079940141140e802c0c1c8060410419009000c9a042c850800b90400041c0c132180d4540e6401504044107030340320356506809030341600212005000144451b8200f10042c200d81c058060224803c1e1135022040014806000841e207840d0300140004c2c0c401070341581d11515024000b03520400201c103984800802900e260f00d4881500350b4680540c0000c010030004c1e080c000510305880409032100c0c0002d0040e40c40c09026840003a0010b0481da480d00001504d80d1164403c484166a006008100455a4010092058000c42d01c22440344075a00c022034010540002520b01540078542801d03d05501414191140c3d941301700c0d543e0709401124440c46040a1200b5102c0c4228015406802d42842919007001d54840007003003e104141200e43e0000543d038020140c450341d84e4180c0b11141d4804c2c80d1402a941c3e49220984104410000820481c1080d8800300d2010000d105500310352580d00e40811 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 422515764 1250 422514514 422514557
    0xb18060a05090f0316080102091f08060127170d02010b0f0f030f120903210d020313060603150e0106050603041b0e01090b0901050603060d0209151c0201 67
    0x108440080c8040c0840041c500c0d050240e1030020f24000c086603100010800c601e5030598582e840b004060758007182180460401e40c081400d240304403940c07000c0141d0200005020340c03201410b001d040040d0840800274100920051002c3e040d51050014091642c8442444502005c500303285201d024440c1071500041c0140140b13490f14070018617200139000d07904180450801c4031803c00754148114400c001a440c000d000c0c040449502c2c006455517440d140c41418035040318042c000a486025808044024150b0015614030f20340840000d0382d627444502400442c186001e601805181c41c04000204012811703e004079490205841400850709010810b82252114860b0940050b001c1000400090f084c03100d0800182102054401458032441c0d081a044401d1300301e5043c40d90398034510503862401450150041c00100d801038510700c0c00c0c20100c0d00b4607a407030000900400e1f1032400b10b030140c107640420b402d40c44000b4065001d5441a02c105041c01c14a00a05074003003402200803100c40e01c03e110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 422517014 1250 422515764 422515777
    0x120c031c06032f091e04050106150206011d0604090203151b0a050f0d060e01031101140a0c0f03030608010906150905040b150a0b0423090910150b040b1806 68
    0x2a0100601c08880e0f052040e100d5004003070100480e030890710799004185924416008501580c0009107075802c1005821001004500750340c1998000001005200456524030304004203259003845e03107071901c3c0003003406000c3d0040001d626001d0f000c0301e42d44014408101600c42d420940c0c3c280228115015403030000e20071046c500300000d100b0049070398228401001025041c14106002401541c3d9002500034543c0a800c01c9442c207105154260440d81e120510400500c0940061481c00e04503410281c1541d00d80c041c001c0031880e99242d807200b40740c001d50000c070003862200d000b444040c141d881c0c04001801c90516403040105908000300fa005c4a91041c680304a070300c064464099181c007101c0700106407296001e1a070084000c0804145008114082d0004101000103d0745020607586840f010382c1030310205a002c0e00c40d034010032030386c1400054031035a03c0320002000900000c00c900c1d100040e18094018151710440001c0028043c00201c3c0202080132024100182058075941003107124480c56 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 422518264 1250 422517014 422517083
    0x9090c01082505131203120509011a010e01090b0c03070203160806062b030c02010305090d0e130f0603110910120605070215040c05011b05120c031c0603 67
    0x5208041d8003e010b98002c1c282e10100c0c081c420710003684c0b003241c010404c03a0b0260440018060340750555a4041c0c82c000e194001b8065030003800170b14601d01c080000c0b141020102d0341040003403050400d032a4010b4030004082c1c186a107106503148104001d160380c0f42d224810490191160b060b80c9a088070414183c0c105888403600a001c458952100700205c55104d5900e14118070881c01035208003c04054140300721034402c0e01c51100c0160507000140459078000c01d04c584981101c16403000c4290b004845040d000c3c4202c8070030071034150030b070a500c0c0149200501c20030031916001020080c0003030243e44488444044031401080c0d6980400011883d03494420700071004166060440003560766003009510042c9071048841000b0320000c903510503c0140c41c180c912a445a00921172564003028409100c2800d598010111342d05507a220f542e10004032080c450b00c080458988140c1c0802d00032900b202802400c1c0f0700340341d00740700400002095903202c1114400e04d0786050405030303c1004001c40d024200c1c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 422519514 1250 422518264 422518321
    0x40c05120f030a0c0309090203071211090d1b0512030310150807140913090c060504030209190b03030a110c01091512020d060b0c01050606030907060c05030909090c0108 74
    0x80441910300601c4800c04806001381b490b4003090148080c80614880c0400d40d544044641020b80341301c044030315902140340ba602c010070071003140d41c454200e416400ca80c400c5050711045141100542c0b22041500010b5115510811200c9a00c3d40000950300070130341b03c0c0c008003425568a003906911070389280d010008c9000000007a500c00c0c040d103403440841c185080035516100b005000071300321a103001c3c03078110b40139681d41c000420b01804001c140c0103800c80d410094a0b05085400050003001c1c01841345945071800c14420380404900d4211b41d20344000503040b01c0e03c0702c405820140008000076842d21482c41103d41241c00c540c42446000211128200758a540303101c10314003119690030351120740c070141760204040510710526105440c01010041c00b035036103503108040e049080d5900074205610613602070080c04100744000c40e02000f21519424180b401081c1490001d045000300c40c41141d001d101c140400064120100b01401c3c803c03400d80e2401c9080d6650803c00c2c01d16581a412070380340710320 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 422520764 1250 422519514 422519527
    0x20f0f0d0f0213020f0309070614070b100e1303020c01021b0d11100201020405032406091911030106080f0408041401021c0201270b1518040c05120f03 66
    0x702120646111400508030100c0342c80441001e600741c0c0d20125a91040c04400030810410650620004015101b14035040100002c1d0b4505401d06008003600500822000808076000e4580e0006183c0104014602100b2030b18007032559618450b4a103005602500407048840d14a41c800308205421b61b0a1310180c00c01ca03207404050041c8918584012200d080d2070134106526a0b8820181b00320211003980056502e900b80001d05060400b104020001c0c0702410758420802005846682c2d400101940c49a81544e40e81c100f03c054203a07801c0e0101501c501c3c4c00611100c5000442c021030513250181c503180e02d1071316035043e0300c900d00604a401034980e01043c0400d10004404000c14080c10700c0500c11034443d0007403500c415202da042d415603480541c3d920105030801e182e040d075071800c12a0721802c10303903044440c1e6200d188507101c0080020140c409002c07503d00080d980c0c4c20082074041c03054a141e00d02071030300780b806034441c10660282c2032249030207a588504580707002034404002030a44000e0740c201700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 422522014 1250 422520764 422520773
    0xc03080c090a060c0f1b090606020c030d030c140703030b0a0503030304050a0227100e0106050c0a110105070f0501052a161118010906060c120f1101090302030403020f0f0d 75
    0x480c1003c08171000c81068000502040c81481c200c0e081101445c00a100e0b145441c421038101e80c0254056025901301c007005003c0c035640403d520181c014681004036001007440412105002008103443c594880031a068050580c19888076029160030340308418041d4491041568030f00017150001c28640c404813413500103046c450041020341d8480740503200751048054003190409000c80e800750340c0c0d520401c2c0402c5051a1184d4007401031080c0d0900b945400c1ca400f409030745030b45440002924001052501c83c046174031650448011541010310294600c03660301d0030502030300c0d09454140c00071001d156130144c606000420300c2c404045511800e460a850702c502c2001c0703106080401c0d1040700700d4441e0f125050b00c1d0780c4801d00e0080c00681ca00501c2e981043c3c5000c044400eaa0000b00411403080400d20010303d003c1c501e01130000c91420210820a01701c030048900c0b0b46031040c041074950070003440c03100301a0000064003d072031003140e8401d400f03500036003070040404190f40d90702d5206200015803070226 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 422523264 1250 422522014 422522027
    0xf1407060f021314040c09030510020c15040305090406060206010612050a090503221a041415040902070b0c0702030c1e031c0f020a050c04150f060c03080c090a06 71
    0x40e100315070054240043c0c5403c2c030200c207090307078424520b03c026580c883c03820781303881e10410211074014105015a10305649400b5903542001800e10005640080c0c610308644080104041001c00481407000500e001d14000307209270440728800d40240e041400c0401c1082c000301d10981078880a54504182d860342655041c0580f1026203002411a52440100b0100e0424801007144400c40032100c44c030b65103101107004203181e045d44804081d00060060780c1c0b10440c050110b50842d40312000c1c9054281e00c3c0300015040c1d41882168101101001030300003a078503416005040b078180901522440d0342d58448100c005071196003002540344e00203d414034014500720100760003000c8100c04001c2ca603495040030074600b48041c10050405140d401d90304801650080b114a0781000c94400b904058415540d032694485500c4041ca00c102e448a41c2c000040c100d02401340c4c000d0103900201c16015980d0710010709007507050360050300054929000200e12074078000c1206c1c180300d80a441040032034580384044850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 422524514 1250 422523264 422523281
    0x120a0504090c17070305040503030402280305010e010b01230f120c0909160206070f02031210050a12080702132912152a03090a02010f140706 62
    0x51090600c8041050141032044107108109500c43d400321081c0040c0400089000a214004050500c400c02000440200c10b8031707001035040d40c0e8903403051b0401140c02c0d415800000140c1d44080c000350004144003054100040d00c48203c00201710040080d0011603646c07440301c082e1800d5480c40c020400350080c00e0303401850104001c50388107082848080d056a07540800303607102c90084802050701040744c40d22000f882c0d00b1040010030700340c1d0f0004c41000a91141c0c001410700c410301c000c2c0c0302c02e0800d8030f000f401110320140c0744030f1051a6614040d40709520241581c041c01e07005291034000840d4100c0b401006144040e00b101c404e80c01c1c400c5590030044680e50310201c4d8400b80d82c80c0c41c5411107181c903d121901c900c842451554840c030740b200042c480f40c3c114061444100f60300c0041c40040d0214403803040ea412000081c00350f400c9400c030b095100c1480e8560054510f000d400001040070a02003ca00e81034201e01c02d0381c8044051507500c2c012503180c0003541050b158201c4c108800c03000968250b001400c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 422525764 1250 422524514 422524517
    0x111207050910020c01020601060801120f020f0d03090e0f0903072406030b090c040b0d060209030c100207080706021f0507020109020307080a0c0509010b160519141509120a 75
    0x58008580085842128400c0c2c0640150380304940114880d0f070144001340c050183c500d0004a198500810361070001400c50000c0c00c540c20764018001591954040b140502001410002440c02e00d881c0051204c1503600c02c8080b8441c007030300440c4061300c00012050050518600031402d040c46600c030080c0f030050b503c64080080e58400a4140003041d0350003014011130082d40c10507074510303000c0701060030000c00c011800e2140c1d2030014554002c1d61040010201d960b001000140c440c44100003080c500740c1294141c41d07000540340008410070303a0006081080c0c3d4107090540740300d507507107610981e900d01c405c0030070f02100e40782240c40c124107030304550003150711281510000c41c18144030380104c0d0800c2c105e5080740090f50003541141042c00005407040000b04410340309850301d0340c074010111206006480a000000742d0008420303007031020800c01d4041c2003290742c0900008600c4c600e090f44d440047c180e8421054050258000c8030070940c095002d1042d003140d000b5105000185240b4801d5334040840c030310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 422527014 1250 422525764 422525767
    0x21030f0809010b0a030b0a0b030d1b030509060711150306030606011b0f11150903060703090f080d02030f060306070206010303180e010801091a090304050d0212060702010c110111120705 81
    0x2465030f02c44c54401c00541c06411b505409040c0724000c501a65051302c0358038020f51000281050583c0d00400900000f13141d903000c10b002107101d14040750705114090815602450100c0e99000384105901c2c4c0550001c03080700c001c080c004030f0f05c45403041404103d486c1907042d040707072000038429401000d0844004c2c3c0800300c2c6402100300341c2c0d00d08071307101d1000805960030112044090980e050069500303003640e42a205880c101074075400069031307600b0001d10140403d80c03901480d01c1000101210808003036440350034152140c0f0544a003400035042190080850f414201c081095424049a028021109640904050780c04c54600b076454401106010f000708480000001d880501c449041d4040c100241c004103a42226080c41c0e0b03210b007a210902ca1707070b400403036040c45140c1d1400000c40d022a40160342c81483c1c4415800002d00c1c04c401d0f80003003241c50240303008200000b5410760040480035410b4484440070018481c84a00722054400f0071090342c071f801c11840307450542152003503620004500e40345 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 422528264 1250 422527014 422527031
    0x90724090816050118230a21030201050a06290910020609070f1811130b07260403030c0f0203011d060c0a0c02010507020a051921030f080901 62
    0x2189071510701c00020746500c2d2101d106208941c1d002424420f21451660001c03c1542840c51142e1544000d4041520408a442d400012030b00d031559600001d00302c44d045c3c8441418041c060b14a45001068110015440c000000e03c101c10280300704000d8455045014003c1040001c050303149144107258001141018020140c1c0c44d99140c1001c02078a54540c0a0859410f006240a1030b0600c15002141e00c001100b20a201485182c118138002c3c40901c480404d21a40c0302c03401c640c0c0c1e4410080d40e015880003510021407051240300003404081d00c200e4a000100b8004aa82d8079402c5030074440030030004041008002003407241d9080d0310413501640781907824951721b0340000e08544003048800035540340713603400401c103a0702801aa5844008850b01619100740c680c0024075000303114800034103110001c120b60065440d00084400604009030101914400f40002d07001c05001074803450440002000441c0051386100c040d50303809a506440e4681510240c02003030320074400017815006250740c0c40550 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 422529514 1250 422528264 422528279
    0x32119021b010b03030313031b0b010321030e06070c0204060b070507240e090405011e060503010c030b0a1202030f0a0f020a120c051003110301081509072409 69
    0x1030500c00e012840c0303451846880c48000d42520303c1c6144a41c03080d0014010810300080e035201c8681102d03490725014401140041056609060303d46002d08005001c81c00030040103511444202010754040e60014990325490702141586d049400e8072000380c1080b00480c6066010700318480d403580c4001d2011a549440da04480384a401c5000309945a81c80300324100092400c2c0701d00300811207039a11001d000f81c0c0002d40c6c09401c415141042c90b005a16000000301480020343c030a07a40304881c0f22030b416100d44500e9070340380074007818040c1901c02d52a00d5080c0072600d000c0d20800141685c0078185c1140c052402c00100305440355580144e81600940b030135a0914a018042d080c1c00da441040030394400003550051004a501d20341010380d02040800c0c40740d000c980401c90030320442d14111a503560303568200d14200c0c003500d80381000c02840c81022001082108000c10404c1c0901040000b1501590b282802c0681c0e0b0000d031310403100104001180084000707480101d0f001164524240510015620000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 422530764 1250 422529514 422529517
    0x2060a11282105100b0408070b070f05060411090106170a0b15040e0709120201051c15081f110a0e010e06031e01090c020c040f090c06080f070203211902 67
    0x111080040d50b5104120401c50304001c40130180c9215040181028100506260303103990728025000101300101c0d401c1c0402c48031880c1202100e51180035070709a418540707006600d48030652851403080c003407a000400c0061003002410100d4480300f9269016454000c0300c0b10003400d144071582d80001104908602401146d80244018800720400d0911440c2c02c000050204c0c03000e41000703101071038003c6502c000d030780d0003c16240c0001e5454442240440004202002440303105000c40c01e005000c80000351040c4041044c4000202071a80c0003540f100c40180d075401c6804040e084d02804006000c001c0c00d9a1240282850b42c0320113040162140d00d00170000b443c40e40044511703000e08600c0b0000d8122240e8860038490042022a1042c400301030007007070103074541c10310315490f40c0600d6075402e50b05012403040d040034070910b40100b504011140c075140b0080c2120f6040360b50450244020307020a01540c400000c81d20008140a40e6800c05e000d0700e00115404040030b456203102800035401045501458030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 422532014 1250 422530764 422530817
    0x3071d1203040609060e0a0b040e060d060614010315080703030c03112e1104141809010c08100503100c1106091605031b040203040807050a0302060a1128 67
    0x8407807030600e174038180004010860f2483c94a0044d44007400c2040004069002c1d2000e40790050380a03070096030303180c1c04624001115500a40305600b007040014081a48201042200c6c2d0700b0307a001d1040704113510319583c2010341441a15440d6008100410100344100020040e0030b10074034250007c00140302000e46418038001c011059581b0440e400c400c00c1c1040c042c8200b803515101d80c01e00c44001d401c60b18440c0350040384944840a00c20207100c098139a1480420500311480c04a10b1049040050741d2900030880c0c00035800100382500e011682103072244c2941c40460344014001d09007100d000382400098405822803030184101c1144210394a40d050080d07a02c1000c40030000d18209001000386140c2024581c0441d0194000c104600480400b03042e00400008081c0c40140c0e0343d894518080d005840740070f10192035402150249400c2660210b010303801459245800c0c029040c2c0343d00790360391b503105801400010701103822030150040d5102d4050450319a1034200444121401c059081e8108a600c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 422533264 1250 422532014 422532017
    0x21606051e0a0507081503010b060c06071704051c09030f050d09090c12091403070f060501140303070221120c1002041206020705072409050603071d12030406 69
    0x1503182200700c40d0108010b501c1581042d082c40349082102028048a00140c10200e50035030941030b03203203192000d42000d00d50880180107503960300907840380c103611b5100565007140010110b41c03d070002c010001800c58012500080500307850b000328442c0d150b07000400c0582a080c03204040700000824544058128801d020704060580380340d044000421003030258100c109400e10740302448a405601440c0c0d00e0b424140890006482c0240782080a00401c120407001d04920000503941c1c1000035014142a016100c1c210900c1144d81302c940405080018401d401c3c3c166205006240140c070780601946904c802110f40100102046120241403000700545058a1040041c1f5485041d9082000215001e0095821400c16042c4022031841c801c100402424442d0086244424417205011000040c41c1ea509000c5401191b90004c860202c00311502002007031015200003090b041c00c5d42103901c60449982c0b20020741202240e1094403000601c007094003e400818114042081080200701904c041d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 422534514 1250 422533264 422533291
    0x503070203010c0f090e06040f0c051c09030c020618090a0c1b022d091602010f05070806060a1205070203030115110a0b0c1303061a2202160605 63
    0x560041c5030035504038004101c03c1010144004034010750207450701003a503642d0559503940c0c0d242e00002402074003018046840c2a464002c181c0c4039203400100510000240e1000e8851b09807543c0040c0045600f45080a408150807401c40c03001882c0000080110f01d02d004802e02a004141d000b09078000e0044820810103076441c003140020540001a95109440320b441c41840d0842c00c1c4d01180700d504000c542000c90302200d1501d001c1c10615207000a100c4100540200c4c6145001c1c040f0001003503030524400c0155180c0003070380384c2060b002d002d4640303c1e100c991112091500c80100f400b20b1a441040c05100700100c0f07c40c0b0f020000200d0090134007513003950303000315125414990f5141d94140c40b11407020038031190640703801442401240342040c07150088485c826940d00c80ba078408072441050050480a0300140c0b01100b081002e0744140c044504201c80c010404080c0340070701c0a0070201c00180094602c200141d6100308140703400800e550300400e89a55907010007a03481c9002c0da0300a982ca43c412500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 422535764 1250 422534514 422534527
    0x31608160c1a0c0a022112041a190e04020d060b04030506070c030e0405060a080604050109110105040303050d180f050102071e0b0604050603120414030607021614040603020d0503 78
    0x20410040d8044111405075180040f54580141d4518181400130b001e000000d0300ca0024000d0040111005c3e0054000e0b500000341d980840d06140c0e010340540c10740c400031031b0f12680c000307241401560038814115404444014a6910507900c0d20500d0300d01d250310540811400201078114000c000007020046604d64a1f107065261481c14400010701840c1000000c141c1200440d80c055010382540c801038500003407a40320031002c9202d4502e00c0c0c0105030b142c4611405c0c4020040c2c1503000ca0304480c09480383c005075a0003c0d00450301ca100f10b00c000380003e0303c1030001c0c500705800e87d072003418811000940c046002c401503440510501c0407041c1914165030210350b290601400400a0500510048002c00c5150306507546440e03205010b01158041c0d030766040096010344080120a011b50030318042541c99507501d20b000c00c100e002ca1100f0307500030300800300401d0010f400055a0032505c99904a110050350600c1d6140300d81c05c0342000241d80c05900c80c040003003d601e0302c4424050450040380510354540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 422537014 1250 422535764 422535779
    0x7150903030c021201020d0e01061a07170c07030c080a0c08160e15040516030c03050c031f23040608030909040b070309020d030f031a0f040b0d0203010203100515040602031608160c 79
    0x21003800191a42f07120402c442c00024220f0800300007801d481301c0301252a504050130ba9494003a242c1c2000f00140142000884c15047c0080c07005041032040d20700c00e941e40c1d110b459458451881c00c1509110720800141071040c0046c24210a500103c0001000c1520700b8140014094480583e51030419079036900c400c00071643d05004e4074400b03400700c0c103043c00a401c040001343c140b132100804804c000302c40c0d02e1100d0300c01502000e00c80001c01820460b40c40c0444032503003400f42c000b4004d803414440e030700e450000180d10f0401b02c147c51012800a10036030450392540c48148000760000c0c0200300f00b50382c8001b00001039540c0f44014200a000341c1c2c841c6813100202002804a5040301001d070362100720003003120407a980721540c0c00e07c050000e84010602a2000c0b002c60481c2c6501c4400075815400481006006d400000c2c400007282c00460310b4100c00c5054090004041c03065000d0320005030001c01282600c1101a0105040c6510070200e951425680380800420b48a00c0d007012680180c1c8210104042d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 422538264 1250 422537014 422537039
    0x1109100807080106120e060c0903010b010c0807060b210d0f030506102304080f0705090702030315150703090f0b0f04150302070b0907150903030c021201020d0e0106 72
    0x240182010000d50405000180480a051089404114007124400f05140031604004d81c4a85440c04540042c289030140103425001004400d00030740c030b00000c404242d0700c52030078064010b402441842c6807009a441e801d029012036260103410a54100c642448960340b40c890310b00d810764074409808035980d40d01c0014406020400190100350800307081c08155907446901440c8000107007403002042000c1c055241624244401c0c0c4000ca42010500041496000c244c2c00358100490381a50a66600d0f6810042990340c10b844c548010f038414070004184809071140200c840000404200c11480e40c0c1c01150061390004030708600080c9070960800c2820880c41010018100200e0f4090918111100c0e2030964012445042850312850000480c0c0314020350482c1c001c1130300f00031740c040c9a142460505030b032150707039114142c07040420458201d5694840c1c810401903039459610001813001c40e8080004441024007403070460b5508015244404080d0300c210903074440f2900011890915000340b56000307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 422539514 1250 422538264 422538289
    0x30706030504150c170403030609020f0403120807080c1c11070203120406051e07060c080f0c030f0631060305060c0406050a050f0403080403081804090818060d1109 72
    0x307641461041c000c4c06420207110482e0b0f0301c0092080c005a595070404030040d00c200e0740090380791440003411255400d440030051090707a00510a0105200d00000100d9185008035507030b000181480f0302144100c3e001e00d0080c08411141701501045044100c0c11000f140c4200406843c0382c040007600d0401c40c201070100385030328000b0004003403c1500d040400b030440c0c17040d110003642309984010998142407074074040d19043d54012400300401c1d401e85101a2945a082d964014100a0301c0d0014150a046004580c418500c0070398008041d03c41e0380600c1103500b082e403581c1c5005115121101c04200c1c1070745848000010760380e4041102807070360605509282000c0c049100300344003000180800b0f03400100b124108003075454015602c07140348001d60305a000711342008012080011b00001070003030f1070b40034048102000744003205d80e1001108120845a400c00000d04a000900101c0800242240131400f0454040c1210307141c000d04481e500201c0e018400c40303403d0108042503d00c1c1b24100390b40004003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 422540764 1250 422539514 422539553
    0x4060b0411030c0a0c05100204060801170703030c020d060e072309130c030f050303010e18060c030c0403050102070c06030e0304061704170d0e010e031317010209030706030504 77
    0x14070075011a1048651200400201100d080041c100a07035078800c034404018503030454295000c004110420318013942c09441400d00242c0c000001107150b80e01c0703800300343c2608000001410420300e160740075559284503940c107a9201079818591000314140380540151a0010805000042d003449001c0daa0310340d1140c3d0884d8403a0006140a94030b440c0c00c081250000394070200c1d08031506961a0142500419420060104030516000c004000000010714161440400e0740d000e556210422201d0510207035009040541c009c0001c0b03800350078503500642e04054601495071400340c607511005d0a9070b106603c2203580c0f41007582c040081c030f5410f1060248404508015505d02450800004d004020451140083c61040070101d002c0040c0306440b407245c084500f04141c0c0700c0c144044c48000501c082d01200b1803e5081c40010080030001000311182058904829074525051524484104005508a1000d59070030454040103590800521004021941e0302203114982407a201d0b001c0300c020a500e81 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 422542014 1250 422540764 422540771
    0xb0403030506191e180e01050c04120809030f030f0c210307030c09050a06020a05061b040e06030c040f0e0d02010608071701060302032d030403020a120204060512030d1406091311040c0804060b04 85
    0x3220bc6030508404182d150030412103a21861208000b81c2000d4102001c1e48a9110004100405201450141038803074405c030f083e24a890488490320030080d00100d02c034000e8203010400a0340103030107584041d082482615246452644840101340f18814542040303000d030b401001c2010401030700300a0103901c42022645508607400250911030b280c0078030300640310780c428510b000405584040200b034544880040060141c5082000b007400113040d244507100c0903000701d09102d5009401400b41d5021285a44020300d000c038a0f0080908140c0b0a01e80000255525494000050b030b404028400442442d00007100c184201d00c1c42164504251a9114180b81c10600040000d0b030b440e11a01c0c41100c1e111403104034078065510000e801041c46402550344411003140c0622103403400405094071484401c000c00a041e01241c0c440d03510324044070f40ca40d21480c00340000715000c62140d600d035252403054440801071128940010140d50f03180100d1400502d0040412040c007600340206416503000b541c040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 422543264 1250 422542014 422542019
    0x15060e330f0607060b06030103061b0c020109121a040b060a0f140105070807020d050336011808030406030219031401031e0507030b0403030506191e180e01050c04 71
    0x541d542000e51550392003607501107290420700c10303941c10400b070f42c03503004101076500d6071203141110003040304072002440d49070320b465154281801b400b01714240300d8058480150040c9008258082d082201204907698030300a12411410f6044400d02c83c01940304808a4072640340190900c03c4510a55204061000100000304404120a0042d5011900070b10345580d541e1032a0504404512408000030b4005281c0d40c03100c1e0500c00c011000d005032032080440784001c034408100f000c4103d00404034503072540140c0350740340510b0741c0204801010428070003941800c056030780c002c00307045030040d41c8200c4c003107a000601203032071101c0c100840d41e00c80a14242000100079644141039025014040200300b04100c083c8849070103450351503a0310480d8000708482007582c60303181c20840d03e0019035040740445e04040200f4000e180040240b403001c0c130218040c83c032152810340d01085034a2807500c200360400101c40c0100c0c1c0e03101e0303070480e100400080c0400451128016962182101c1006001c56103010003032009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422544514 1250 422543264 422543269
    0x11403070f0519090509070c0506190e07030c0f05010503090606040b01030635030307050d05130210021e0f070b070213060f09060503030f0715060e33 66
    0x559401a9003450449500e280307181c0c0664036440703007021580003100b890a5010882d42c1c08000042950010f07184020740ea21041019030b02c190040c035000304281c02010005d8215000c1280455002403500e070081090480c0d129070340d0805c0d62513001aa0700b0320344078100740300c110300d24003407100144030a10300580340d0b2402071011610f602c00501003500c144d40303441592403903a1081d0040d13005061036940700d030900c02e58031240400300c01084240001888640c601c111004d400841960705c0b4032000e8960304d2601c01d49013002d000400c00240b07589002c480f11524200561070b03100e84821101082c0e0010842601c0d880c0304008840480304003840540d112742000b42040304007180700b000300c6e6280b115071a150802031000a90740c401040940b42601e1610b5400034080c007403d00d080040740c040e60300c10882e064a070f405240d20b902c510701003508010010049040060030403190b8140b040c14501c40003034042d8658525801401c3c068581c01e05580407011920300c19100d0070003683e0004140c00c03810300e841071124007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 422545764 1250 422544514 422544517
    0x5120a0308060d08030708060a030602040617130c0b0a030f0515030609060103171b060a06031209030302030f09190e07090f080a030f170106030207030f0513210b04050106140114 78
    0x4000c040200c1c8401148e41c5468007141040510342c041e00c01c0d0b407110b403501c0b0001c0034200075224030b01750615a10b0100380c0c0344040a240c1c81d032003500050886c1c0345a082c0004284c00c1ea1007201c0001c101503640d80c1624a2090901c5003900035a10320520251a40b800c1007054603140001d03005032084d401c80d00040000032031049609070010840005961a0107507056219000c08044c4030900b0180504020410b0a403d15030000f820b0742e1140724a0040640c14000495449005000c0140941d20810200d14548019005004e01640085ca0380032200844e0f030b00d09802844d1a0302c810f042d014090184403001c0c1d042000c0101030070365680a4500e1901d09031441e40c0c0e46440300da000e002d010302d080180f01d01c4e621070681740c00701d441c000d03003003058a5130369030300013802980508802d07800260040000e0444500c01d008980441c0911a040500241000c5000790700a80c2d448690421807040c0504200040070320203168800c501a0000103a01d514005450803d040d1031040c5504002c10b1380c0141c0d5140e0b58190 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 422547014 1250 422545764 422545771
    0xc0e09011406071a040c1a0405041505030d030618091709031603030c0309170d0f020f0109030320090607060509120705031e040b09010c080405120a0308060d0803 71
    0x15207182940c50600040798280c03045802c0645004120500b0032445480d026503640034a100ba040381004556460280020145001c11400e041004000c1004145000d402c41d00001681400c845103650fa1000003901c1c02410107000d10210b5203030341d002c000d40d00b84148100c0c140c1400b0a002d01c200c0c125980d9143c00c002031350344104480040800d500a964404010f4519803480011501a50a403a410068540104602d00314001400d061010400b410391614006240d038040f402403408204030841900d00c0281d07200e50200310302ca5100240b801c10b03c02d01803001094000d8400240742c2c000f4100038800c0a200d0b1241586a41c41006100d1080c0c450074215810203411880000c0d4580380c003042d882c1011440391001c4110003021800c0014000040003c21111211114140f49200380203040020b41c06503204010580b1320074442500e941d400ba01440c4045489144220320703040d1984c000804080740b4400d820f01e654440612041011b411800c141d403c0f54045484038041d03482942c1e08a540e11004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 422548264 1250 422547014 422547029
    0x40203040f05011e0e0102040608180a0c060f1d030d050708070605010308030a05250c05010209090108010e0d0305040803011206020c06160315030507030b370c0e0901 73
    0x18280115a0100760007158090001d00c4000c0c021001986000a690050f076011441d0442061a0050520803035003160160740b40e80d1541d689000f00e6907181c0f9000c21011136a03000303c07105800080e441401e404081e1415844002c000500c401004100060b00c0c1c14404010030640c0103188941d5001407103910902c81031070695641d401a02e8404401d009002000305003034103240c0040104114040958850b4214031005c010303c7c0e503008a03100d80d030440f41c002c031803c0c200007419200805100b546e000700410700640001d0324104000c070200390103040c00d9000f6812079541d00c0101e02c0040c1c1c1804202d010000d240350074880c6003000c1c0c4440d2030074030041c417030540352111403803000d402c1001c00d0b01034a10040d41c80b020b4035aa841c15003681290000d070708e40c0d0807000929204c40701c2d0017800014403407030a41f41c10800400c4510709581e03c10f210290064420b040d02d0300c540054141e00c3c402c0c2e44c0b03000d01c0c0003040c0290a20034400381d0b80c84429038a80c002c40c0c100340590350256041d2500d811203030340e04407445c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 422549514 1250 422548264 422548267
    0x824040309120c03020f040b18060a030f0b010602010c020f031c1e150518060409171303050c010e060d0b01030b060f091c031d0a0902040e0a0b0406060207050402 71
    0x65140075035150015030721180702468805110803d010041c40e0710b0003200d00948010400b580a5400c20048072501043e0a500007010030400b400322461402e00f50b0b03c204060906291117880b41c1f14020035102241d000c442015840c80184241942070280d40d0803814940020050041c4070001c41e031312802075071100010b000a0340d905481215568000c984800c000d24880354080ca402c4203004042c0c9540f00c10044442401800001c0791700785481d207426958000061445071751180c00406c000b812141703400f5100268500104030148070050014002c0c007a030911301113032486c0765150841c14211403150180c10b0092a506080e42e03a00c0e440d088071041900c4c05800281d8443d0302c801600240584040785030001000702c0da072141444004000c180c58003003203541044840300746070342160205101c07000400017180400d0b09442c031383d4110044111190004e1070b03025201d8890b01010100e8002c3cad032001007101400c20500284400c5c9104070540418159414400641404406546d4181501c40c1d00d000d55070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 422550764 1250 422549514 422549521
    0x61b0203070f11041e0b0f01020706021b061306021005071e0f02150a0603020a050d03090b0307020309091608060d052802061204031803021e030c0d0b100824 69
    0x111a0300151402c17200e40010014031410248204c010810008240d020702211a45c4410541c0001000402c0780c1041d401080c0c0107145038060702000245070801504801c007401a0004c121660114402401303596004207800d070640804042074510281908003031002020200c066126141103441d04401c00d17042550850a44007012841e11250b2040d50344c1310710380300c024030070411303141d1f08007004882c000c54542c141c940d160410801c0c001c01950b0024049207601008000c021761443c043d50380719040b4010380c0e0511105101141204904540c2c4040e081041244e000403a074006950766081901546c1c213110741586507a949648443d150a900e40d0540c0c8110800c00401c15040160621b541c003030111529000180d0a042c0f1095003540d00f1404202019452807011040c3c081080889800510701c41c041d45229184181d24850380b590b01c1d405020f0b1002c80302c05622140c04170100144140d8030308500e403500700282443c0c9207803074201c00f41642107245d0800c00c118801d4540d14900700b004000000303030b49 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 422552014 1250 422550764 422550769
    0x9030c0d110d080c07080105060a030f1a0106030510080a23120c0709200a0c0611160201030e010c0e1009170102120114061204110409061b0203070f11 66
    0x2081e80d010140d0158440360b401e000c100500e006821806148011205081d0300c8803292400da440c1118520b800c0004941d040010401008078142c08074019448405140c0726800034101c00c2e60240c006801090312070080c01114401171581c03000400101c409410301da06581d440b5800c1c1c04041c81601003003140b80343d100780390721018032900440c401251580c0781c1c0d819010030a951160041e03c19541c00924005500d010341c903039403614101c040080004030b4681b04001038160f0b03d442082c0e10a40700e02e5074441152100d071424a0041200100b10b02d51180b00503014400107040d210302c3c001e50109a410182d1911070290081c50301c080c1c0100440d02000c22041c491401c0700c0c140c2c410340c003403103c50300d0000749880a00e0041d4024031201c2e50b64450070380c82c1e030b0701c841c110200c0903529460980c001204000c44407141c0300c520545034005101e4080041c0d4400510005415180704040a40d41c1507520700711800402c02d03509c0f00c400110903a0014604082d4640c03500d0030422805d19001e000c80811405a0300c40b076 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 422553264 1250 422552014 422552033
    0x130308100b040305100c0807091e090606021c021902151207090f061809050907091505030709050903030103032303010e090c1806100c05030a030203100b09030c0d 71
    0x42502451094403143d6906145550390000c1d15004410782c500074003188154402c80846100c0ca1140d03c800542c41d29000e01101250450a490583c04080a102060b00103541c06a1300080c50329500520300c10034070443d03000d201c00c112241789055501040900d01160540808070f03aa054041341d1300008255038004012580c843d992605000100b00410410b40f550040d803000e055981441d0784a4030551240e500741da404400040380c0c50250880d0f40208001140d540007135038000742e42000c1d42c3c040b5030307200418030a441c2d050049801400c40c01c1c1040c8803605003044918000c0044490910503800e203020550340340c0c4030600028080141401c058528410800d001071003a007010904140e4960b07450f40c0d00c60145000359001c040500501c040003515140c81c541409220950025400285d15100b081160034074166142c80e082c0300e4020411030104600340f02400e11210240c03000b599902c7c0c03030100c41c58840e90540020080a00c00c0c400c0b08070a803800240030158403410b0352000412000c41c1480b41c41d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 422554514 1250 422553264 422553269
    0x18011e09050304090f090c0803160b0601020c030d050a0e2403040305070b0405060103032601090b0f03011103070e01020f0309090c1b0a021903051f02070c0b0715020313030810 77
    0x41d0342070909441085d403103a4030001d081d40c041c001d094409078441c110b180d1a032040c65014181311402542000c0850f46181c040da80000c4140129001601c429000c40c1c24240c94100c0030000c50000702d5104051030300300840c1d01d5206003c5030103040400c601c041070410706441250488407402c011000030200f40c0194215482c0c42d0f0041c1d00565589000d1600650702c00d000d000c11000112140320b0011400c0016012900000e071031075a184a981c00c22106100904220401c6a80f05401515400082e01e00f84500121600c107a01d00300e80d2403821107c040c1c0b556901441031411540700a099040204000c4203441600034101c84d00d01c0d1b0b1f0f03103c030010300801c0d0090102d0004890405052010f00180004000c090320380309449180d0100744005a8405030400c603c805011604060b0842d449041022103d40300b02052440040c00d01c605a00c8107403071021150864062401c00180c01414050120b0700484d5013120f4400552551070000300c44e040b684940b440050a1207088804078804c4400281460302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 422555764 1250 422554514 422554529
    0x50a032003030c031c05010e041209051005090414070215070306030606081f0e070e0912070b010303080130060914011401091103040221060c0318011e09050304 70
    0x4a40c0b842e105155103170f40c0040504101c441050020203021002409064122006102500c01c59661501c54064599901c042a1b04000510341d0100d51a81c81031460210407040e80d84880d00c40c058582400f084891415101d101c42490404012605038009140d03001040003040440c09500c43c02c0307065000e000180c100038001410244c02103100780d00040d00b18508020403140b00301c178941c40d811080880b40313070601c0700f0110b030808001488000400c4c40c6807034101034002e0403102034290101101205030400b0f00103d6050724010010803d02d94800f44990141800c01d41e401940b088041012280d5031419a00d40d034059150600101406030030303030281c00c00e141c10403811540714000720b42c0180284030340412810b40c0c5c10007400114020740b0f107104500103180c081c00c1c050710390384440e02089071442c0300720100038094100925040d00b40c5030a109441c06064015039068032070400212160082c403200340001e01513031400d10036a0304a05c000c1c942d4075405825000000303134550305041c44c5049d446240c00060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 422557014 1250 422555764 422555767
    0x290607120c062c061506041703040b0d0207170a0507060507120507230c06060105160f15050a090c0314010f0e0303010501090501170a0506060405030105070305040615050a03200303 79
    0x140e00b81800d41c0b0034155081c036410b458155031692045d00e0403c2100e668143c00c050305000500c40704c01481c0106c0380302107041e022681400d580d081031a20342c0d400441c881e0913958002c14240704003c1015484200442819450f500f860b2085d8801005402216809000c80c0e440d400407548007401490251001c03036114201b400b580c81c2840014007201040000303c0c0c03940752030380340021113140b0303400540b40d4421110b0041d000c44c2d00e81c20011a52504050729400640c001c1e200441b00040171164070340b01c0188034201c4c04600304812044030007100d10081400c0071241c1850040d100240c121080e00b1300340c981c000c5c0074491010814407901d005252030303100c80d500030385000b09040c4500b03000009107040710800d0341e8a10a0315103446c011510240d114240c49803418000c0301203400042c16402580e8000c1c0f0150120341050380e140002400d50304140c03820804070b0794540620061080500030104c0800301c410401c0640382ca010049078400c920740c4000342000500da011215019260440361180030340050449 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 422558264 1250 422557014 422557061
    0xb0415020c10050423100e010b12010f060501080103080909070216061106060102150a020a020316061d120414030309030a0b0a060609060903080a02010e01290607120c06 74
    0x2010180d800382c40c90b420f000101c2c4110074038114200c400085c1d40c0042c18202007000ca00350050700f06c507800c01100b5501ca039007003625500c0e0100c1500b00c910703101b4004991014059000e10823594540c0200d81001102170040c00031500082c202c2e42c05500503540d400182e540e50300b04a04210400301980b603002c0a001c00000c01690101441400c11050700c1500c850b5151a0300581c3c0e502421080e047d62030010800244484106a0250404402d140140c0c3e01e400100701c500ca5440420f0303203045490075070340c0c11605509094101e50081940c09000101100c2401070078003c402e0040c0d10480410806081c003400c206d44080c07007aa00801030140c00c4840d54030b0070349480d0001c0c801c1112900c500628241d800143c45118000c07941c00c032112901c1c1c1c0c1942d1411521841d269510040d1144259904c0380921032401c1024855170088212010101001078400c036100503607030080020652052106200c98808608910fa140c11021f400f820089600c00040c506a0080c0c13809071000ca00b18450100d50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 422559514 1250 422558264 422558293
    0x3010909060612020306041b05030102041706160e0d0201090801110309061311060f0715022511010c050f01020a02060412030911060c0c030f070915030b0415020c 71
    0x31521040c4141c000380101529541c0883c100c036643c00d4080d50540c007000100d00413a0b00b820808a04040b43c00d410b0108030348a101090a980c403541c04510185030300e4003144640e800500c41e091700300042c07056100d1040045400100280b1808480c64843d07194041c0810271a0300910b000401050940e00034440c0c0900d000c020303100b540040f201381405002c2c02001801518807481c100e4030403503200d0700c000100c0714950305020540d0008031260402040400c10040850152803000c400906901c10150303450041100c90003080080091020242d610444030070000385404910303110081080ca000c60b0003141e2401c0a900d0105007802ca42002c0d4400034810389007590110300d0030700c1035020b0340c0341c0c07189400344000840440720381c2d080c05008044030202c401c05038a4160700800141a4560440d103821480c000060b0410315a411242c81581c0000020080000c044c01a40400c0c01403000c0c1c084164070356290100d414000410042c2600311000d401d1498413403d0f0306a800690034401102d0203100c07607405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 422560764 1250 422559514 422559521
    0x604060503010906051b12040f021c0b010f0902040b0904091b0e040201031503030c110105040906060203030603060c030105010f03020915030a050a0f0b18090a1b06091a0703180b030109 81
    0x1007a084240e03880c51003018204d807143c100c90b018201101c1c00701082d46c0b1600c81107110038a00341c0807a0302808103281203403d01000d030302c20bc03802030003a041c460fa9949000baa42c0060203407944985c61307031401400200001415441a40d81c0c3c1c02082e90007141e45000c03403074404480d40b1340d818002000c0050074030200f1078a50040503644a18403e0301c0c108a0b16a017651201c504403011702c0020002520000c0b50070014a001c00301d1605858181031640c18152909904011b84055030400d1006a00c0031040080c035181c1000b01d1500000c240e9034003403965050400003045844965203c8080c943c00051412aa845407410308d40c0c0300e495900c110740ca0f42000b05194024200070744032032485c41e003048950345840c0c3d82c3d882016000c00d03000340040000c00340c40f00c0722240d0f9800140010014000d0248a20200d101c0010080e00111031240d40030409081440261000c90203800000c007100342d0394000d9404803100c03000c0f02c0301c03070b605820690546422000400481d0849401800000c20301000004104c80c8940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 422562014 1250 422560764 422560771
    0xc04090509071203050a0306080708100f050928080307082e05010c020d08030a090209360c120c040b0103020909010b0a0c0501021c0e0f15060406050301090605 70
    0x20140050703260703080810381d511050300640c070086146414080000340241c1c02403903040100c0c11701042c4181e48034419030418030198054050368002800f283d052001d01d100d004006802140104101d052050348036036103031080b4401c207651002045628800010b0400480007481c0d001030919070303e00e09098000c7c240e0b01c0075600d52040b4a294441e00d081c440c19901c007003040d86510485018605d207080011a5145600344040c0e0708991a0801c98020442d80c41c002c40c42040140804101c4400510510561010051030440c3c0c4100d800e10001014111102084402c4d1a84041c042c0c4048200c80d8641040e1040e10a03d03400030b081b00e0240d07a107090108103071510042c112410401c003940c440042d020391203410075030760703119114a005100e240c2440c40645003605441c600030320f42c148165070741d5089034040541400c00e40e5190f60300c07503010071150040b201d045262001925002904075440b0755503888a00c880c0c07a40500c00070000311580c4865120b02c004000081c001c0c824042c540c00d01c5401854140d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 422563264 1250 422562014 422562029
    0x30903120c0f120b15070c050604030302060105040b041b020606090a060605070f0501060305060a0911040603080702040b040e0d1e050322031b050c0f010e0d02270c04 73
    0x1104160420182403094050a0205450700c2d04181600c2100316052142c1000d001c082d60b590f1300b1202d11907101c12500c06445034100010b15038808842c100401e9002569000c10302c90082084280002540840c5013030440b001600c000c00d41d004c0c0d08000801400750446c0c0c2041888007012040002c03680003424a0080205544100c00d80d15005800002d5800a008640c0400d81c1007015400090009400c82040c0740240b0001411540343e9a445060210994045501c00c0e10b0b400c0c0d2800348024400020101802100d042082c540b45580341c49070f500030210f010340b00307590310175803515680c841da00a0340f400c0a4035801d80300c0c10418840094258404420380d0040400340f00d01001009004400f10f034000d04080d251107244c0c40300f410303041c00780c030b50040c0040301003103a0450311702c114000007140e000080b07101c0d402a0101541020910080102c155090350400006183c00415501e5803000d007460560103448001d01c02c10b41c641d600d03140c0d0061503030a4408540c820304100e4070b01d2681d07016006a0300038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 422564514 1250 422563264 422563277
    0x302120c04050a03021201021b030c01110306180a090c0b0a020705030c01080612010609020f09030c0411040b3906103f050c0a0611150c19030903 64
    0xe81800c0241030099024450b0000c48500040c000351511440c0c503441c004021002614064440305021400c13100340b40310101c103034004100705c2d0854001303010b04403111181140e05801d602c3e10030009580c60307401b0320039891409803100120740381102c4d640195503140d801109002c030f000c0cad580c3c02e4203095a00c0110480300502900c4c5010902c0d18010030611380030241691042680d0300c8000c10001c4c81c00d42c842a0480a6603100300c0015651030340d0001d4100300c0250807000707454296070401e0605169808640074030881c64400002e54111103003003030b5415908901c800f241c42d1090407812a511020b5044142c402c0340c41485002d403201d400490780c030501100c81c010b40b4200c0c0c90b040581a500f55540c000d1090402110b1800d2458450001d0071101100082c8004001c2c45070154a0141507407840c202910349070491b0b60018070702d08081c0c400c08020842c2e0714080001c1c110750007a564a446400c503200c24003c100c00c0214503490104016103900d01c0e641100300c10f5069045001400818403004202d02041c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 422565764 1250 422564514 422564521
    0x130b0315030f0c0402090d0c080307060501080102030708010b09061c09110108090309240316030c050c03070206070611030a020a09062a051c02062e060507060b10030212 74
    0x9021407401c0c81c0c42c5801c001846030102c0442003201030740100601e6900201c8610185010070009450f400007014554051a5180b601381840410303600160040c1010342c0c010010311002550000c41641181c3e45400015200d2041c0c030000750040c412030001d02081d41300722803d481440403070ba10007401240314103034890a4070000c100548208104032403032041e54109200c150180d051180d052500081540411700f11004070702d0b0300c03203055001500d110880c9424800c0301d68020390148100d140d4071182c1d007002810442d000c440c003a035034800c40034028021440400d0709001c00a60340c1044010800b81c00f2526120302d00352036000001d40040d101c0b44002020300700000b4401d80202144011068800c110058401216130240c3e10315081400480d483d10802400d00420b5200312105040c404e80d99001d4202c80c00c05200380d03c486071020307001d000c3c3d040000c028203000041c040a81400c851090802c00d0300c5206500303007040181190404550012031144d02042c80c0e5078141e000304001000240b03545120b4a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 422567014 1250 422565764 422565769
    0xa2a09020d20041e0f0b090f1e120f03040b070c050105030c030f1509070f021c171305150726010513020f1303030215150405090102130b0315 62
    0x20390050404403000e5040006010b0700c13540d40d407800b00342e030a07040146480d95582c0382c403050301e0302c425401803684c240b0100c1d1042040c606014240042c2204031001c0011900c01f0389180018260b0321406849005004000d202c0300c2002e00030004261011415a80c5469039036070b000b80c9640c41810100e0740c11110403c0412658007a070140e0b40104441503011741182d5400c0341180b0211000342c0024200032040200e45000d0362003001643c414000d40d03031081442014114060b1800c0c01501203100141c07814900d01030180c1c2d211803c4880b034002408132000076100c0014444036000030b21000740040c007420390081201101e110392540540041d640c1d6030610101c2c1070000c01407004501c101a01038404100400c441e1520f45c20900300c10804030001442c00340e4090803080e00e40e01c50300c44010140003480c820000d05406002c3d400e109070005e5040340051030030042d040c450441e141d04040c4a641d503880825441c1c58251b055501c04488420145006a102c041104190304201d07904502d82030b000600c005c0a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 422568264 1250 422567014 422567051
    0x519020120060402040902060c0d05040810050105131515050316020a02031b220501030515040c150e030a030306090f0e070509250c031b02030a2a09020d 67
    0xc0c4041c0c82d142d1529803c0002416a140d02a68468418004104181c80900545040e21025104d183d55149001c1055080240310003144041c14980f00041009480e6144c040c1d030030000d844400550740d11403846442d41003805401a4540150210f201d0040940082c01140240300c2d03407080210103540000202c0c0c2d030b5072600700001c0d0190050466407841c00c000300c54041d42c0e124000d121807490b040407d6603030300c807038800031400c42c446480d040100b0501c041800002c0100c4803942511203180b41948a480c0009554800c42e090440e110803075804c80c902c41c414030b125254004040d101c0e01c80c202e00300103000d4442c0c2d00a03404d22071710f4007090a00041140c400c0c201065106800b90803c02d142c44200414200028598443c0ca600b1551050541059480071000c10380617031601300381040c96090080c0f05100302844909100c02403400070300540e60004e4400c03026071b48840e64400000c9801400d01e00151460f029180c3c0c0b40002001003841120358000c1d089102c20203004000400d984038880f511b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 422569514 1250 422568264 422568317
    0x702042c011808190207090c0c060f0605011d030a021f110c0109180207020a06080a050c0f031603091211250501051b030a090e0f0907060309060905190201 68
    0x31500c1004083c0c20704d610240c010292003041d006403400d6a81d5808118140c407209042c200005500440800c204480d0b4410603050068110041054a0030b20001078160504121403520811601030359100319a802c200d0401180d038041c20f564518800c41d8208051000362178142c0300030551000030305a09110025604c40c41a030f05940d01007149251094442043d0446902a004681c003044404096164540c03040001c004590300c03c0320500e050705d205001c6032030291001901b03200402c410011146ca00090300d80041c04200340c003a030b0030b64405090b0001d04000341c00601c45035004003504c80e42e90308423501c032035012846030503118081c01000301480c0d000d15000c04210305a03010724091216521900140c4044201143c2d1950400e40465220340b55400503050034001880702542800501d40c031100345074119031103042d11441410440e0016484041e60700070780d01010398901010050050a8000544036031f001030540d010701403107030f00784480c40801709010b034040b0b15a0b4006101c0f0030400d003001580c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 422570764 1250 422569514 422569523
    0x509030d03051b09040603020a03050706080702030906040902030c0706090507050a05090603060711160b030a0c0c050d260c09030d0504030f03081306050f04060f0e0a0204020702042c0118 82
    0x50540c0844144003501311426a540180e44c5440100c016213170303504144081e602a0000341801403800100a240080040010007103420900207140c0e01e44403141074800b85d9014100240c0c82c2d03903038808600c045001c0c481000d4821400c0c9a154014072030048ac901c41541c5055038181c02d0b11f510f40b010b106101106a4901c0d0301360f0300107400105024451f180e117140c08005082a2441007004192a01c4087d8694110300d900f81400000c0c80070200c0e00b0321a01c4004605402c1114070f21030a40c0b203090701d5a10206410003800450441145400400802c00150101c1103032010b80e6410f04007092031068001d0181e9601070710500300c8041005020b1b100f40d4048980c0001c1d4500b81c81416a81103c01d00009401d200c20380071000f44caa0001b6500740150f51207031411071081c1c0b00c4c42c030b02030a10000388c41200044402051038a98020a5071501250010000fa0103440241c3d4031003ea20124008040b51b03c520201042401950048840484c400c40c2c0f000c00000002d2100c88080070720f8808048400e0340092 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 422572014 1250 422570764 422570791
    0xc09010c0605070504150807020c2d0f06040306090605010504020f0a0c060b10020d0806010503190917040e0103060608120d0f0608010e070303181401050c07030507060509030d0305 79
    0x100091a69000183e0203101860044d080540e2132040341c0c403e2102150070307804250060b080010f090340c10800c2621458045072012070904201c0d1040400b4040241900901c0c504c90403200c80e15260503420569401c1c0c00303800e0781d540306e0b0780381840001407030ba8507000c450590a00d800003c0341e10341402580e0440c000c01d45a6481d281d00d080d0251191140900200c8505880c3c1d501468a5950b80c003030024810310540141c465003003010402064130200810007414030000344180841c9c0d42008800d04201490744e10005070407801350070107032018103000d1040c90b481000042c011403c04103003070701c0c1412203118031010f00c1507607241c03030065032910440200c1561510051100000452a50304520141003100e00300054045d1506012030035103001f0481d8175040e030705c5400100101548004a01c1d92aaa0080030660990078442d03081203044104007650704008001c02c2d03509120100380300000045902408545009540d0318002d411900014581c41c4680600c0f402e000f00c2a000f406000d10034800f003103110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 422573264 1250 422572014 422572037
    0x302150c0c0c0915100e06030a05040519120c030e030604140f1513150609020a0f020705030d0c0312240509060d150204030b0c07050c0a0b1905160c0504050c0901 71
    0x200a603240140c2d1300c4100071b2000c001918030303140c2000450081080311004201071a02c0d040c02e92400a54050031152441c01d039010f44c2c0400c2c0100c14100c18104107141c945072301000307070404803000c810300c5140503814011001440304120040d92440282d0402c00300b80c40c03010580b0014582c45094110b80e075503030b0607900720001d4801003e403521881170620a650004500c1c0c080c21034581200d1090b0400242c059000030f1000c1c59035007007840420f5400c0544000c4c0742c01802c01d00400d13100c000481e0b1038401d12120f021884105805880e0004840e1008a03040015030074010b0f0074602003544802003407403c0b8103841c0c00301d503a0800c2d00c181e912880e80540130740401e04c1c0036500c4092842809009440040d070900010001034240c000d01d9000d0020b030505246c07640706030708055040c000c0000c002d501c17450404208105251410381603500e481c2440c094222182c0c0c0c000c1c410340f054820a4113100d80000543e200038200038455060340b06490041c2c07001c00c02035132482c3c00503085120b6424054049604080417 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 422574514 1250 422573264 422573269
    0x61e0408090a15090905060406050a1a1c060501080604020f030f0c1905120109090c030b1003300806130e10060315050702060f0609040302150c0c0c0915 67
    0x1000e21550103025a0702c1c090781e80c01e01001c802c420721045000208510410001811a8080e203a00668122410080c440c40c0100103603070320600740314420b0003890109400c94072480c2e28041e1154003a1903420364042c001480c3d406402081e880c082d43d03011070210000302e42c15003070a1090382d221518051109103142c58085280003004001014400c100c6d0742001201e00e606072440404000603480d0312a2602c1e002228118601810140c201c1000b8a25200e004030101359803900c1388040725000781c141103840c0c40c0d00420580d0358445803c0030b0041810502d42c0a030740c154600307840c04640030076850f40c034050100301401c60b1944010f4501650022964101c0c0d084000c0543c03010816070b40304421a210100f50340d000c1d01c03d03030381540c0c02030300c0340100b6020040620155010b0035900c03101a03c042c020500c0c041c00d480c03500d00805810680104000070015007098020000d86000224402c0802050300d080044070019900400c8030f2070781c601840021030b000b1308100391140e0141e05460520641e0b9240c0c0c07002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 422575764 1250 422574514 422574517
    0x31908030a0c021513050f0d05040e0c0a02070312050f340507060e0d12030b1009031a09030c06011707050d05070501080718080a06181109070c02030f030a02061e0408 73
    0x950341401a9540d6078292401041102c003180f90545410762154501009a80000300c0140b62480c03138402007010337520302b540c085005402d4030b5001000c036402c12410795080300e650085003401100060002400d805121180004a942803052620343d1001d5103203043ea5034a0300d03c2800010031075440200f00b40b01c818094010407600c0d0f0000f501d41c034041c000035290b24840100d404400c00100380d860105002d1810003e12a034550052414071020451560f6620700040301c2c60440001d030380c2d9040d03000c41d282140900071915a000c00b03804664081d615418240c207008400c8103005d01c94410f20f60001001d041c0b12250f1208140c210019050780c40c5450015641a4001421740d41002a0114102040c0302c056511401030440701c0020481888145007030400c81d03904007840c010103006032091400054002d80500340602c0191024842d90b101c0710307030503607040800d070500940c0b501030200110f2143d24000090410360349160708071104e0340c0350000c694031241c0181c0c0548092120321000240881c04610 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 422577014 1250 422575764 422575801
    0x80705042301170a0501050f0403200303011206090614190605010e130e060c03070f0305010e0402010c140321010f060203190212190806010302090d030806031908030a0c0215 76
    0x3c081d210b40e0031031940ca403404c42c0c1e8102e84c0241880c00320403e0001b415800303808d40035400c0f40080d1036184007520025607035072404140b04154901c480d6840324001c20510303030000021603500c80c205005d0109042e0302c400400c6004c903500300803206540421140e68216001e0042200c3c01a101d15205174088414014900d00619030040e490740c9071081180c422004000080c80f94140b00949512810480070080c15043c0c4541d840040508200041c0140300341c40c8542a00b095090a1100d00d8a50030310b1320007951040481d80f0080c40c000861310f411890300d80500403208445d1450701e141b0503a02c6880016178120640101d00069005126412200303100941c1c80c6080851401140e06030000c801c503440880d88881c05030a04103040d101c0903901241c105007a40d4100d2000d0900f94288055540801d041c182035400282c1040005404221151800c0c88152004104044070002d02702d590b08082c00c20754030a0303900c0d5485515103031803035003220f10101c0c0395498410042030340b80385501c0b4000f003a80480e400c034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 422578264 1250 422577014 422577059
    0x1209010e0f04090f050d11010603030e3d030b03010e0c060c280201030c09030308062710030b0708040c0b0d0e01050f060301240b0c0703050304080705042301 69
    0x180108004600c610812031304462088008201c2502c600340b0081c200b82086880c07641581c1040e07401c0c80002c3d046401080c0c500025505201e01d02c825004509142070712f0178081407410f518aaa6901e066544007401d1020b90390f03078400784164400382c0e00341801c031428404425010f400c0205407400754038101008100000650081f110b40041c80c2c558000341c07420307040e001c090007506e100030807085503010b024880c40c81d40d0a0401000c0310703107541c8014142c06c000800c0c96102e451444a0784d0b0800c103a800105011450b411152310242c6800c21284150704040c0c082a540072a405001400302c5106007081c910a40d80414000c02841c50320030b00b807261f5003082068190060b220302902c44034100902c601c0c0c2c803e004400c2ca151503800e194060500311400c09580c08000d2a00b0642000080045560402150240380700a036a6000580d016410f01005410090060000207000108801e002840d001921030450b001c1145040a41d03500707001034096043d41b1306203c1d00e8030040045c50502c901844e600c1880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 422579514 1250 422578264 422578271
    0x7150f051c02090a08060f06010311041e0603140702030d0b0a0302061611010c0b1302121c0806061602010c0503251e02130b060d0c020d021209010e0f04 67
    0x700700700c0301c1900e111007840540041d40400c0c0450246000b81c48a00148520303000703000130f8140416003482c2504000c1443c0d040c1a1580701940000d880071041b00e00510750000d0007803d031812403c3ca4000052284200c1000038101610b20350a1034214005030b0281070390350001c2d45411070101e00100900f0b0383c03442c0f60754421021100040543c684400425180c50480152000c40300c882c504200240041c0075158100304c0034030b11400008085810060300202c1700204000002a6440040c4001c2400c050b548014058083c0d00c040000b0441c98044410055071038a109903601c41061201601404403194002640d1a0020015500a50880401d80e0040c2e003903c0c9440300074001c2000e204981e524445000e44102406010300258217801c1e52038402182c144140c901060300010130030700d5840e5000a04541e5184120110381d18601103403c9504440c105011090314044040d480380c16412161016014009904540b03100d844110394540d00141c544000030301041c42800340c0d8100500703286030410358 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 422580764 1250 422579514 422579527
    0x12011a0a081602030d0515011701050105040e09010e0a030203030405012403021314012303150c1b0d0e120d120c02030405060708030412050c030406050f09040c03051807150f05 77
    0x3c080c0900381c424206480070480c0307d8001c100040000d00b001c4c14912800e17000034010b10a680c0c3c0301c411201101d4186211258544a11700c5250043c143c003030389101c040c030500d0800f1b0101500071014510440c000e2001300144600c19556220001550414016800f141c8106000610b841030107213261480c8140300240040e5503030400d45009c14280c100340d949011340680d102e00d000d00344070010a250b40a4010300700a90305601e401d1001000075013401d03070380e00d030100c0e145141d03500b40700303160b1000402102150030f98080114050f0407602600c2056009088200c80d0091120001880c03080801307442d580e07a03249064002ca11130007411038a07448021808200400201d41d51520302409841e802404041e50720709003803404821880400301814140a0240801c0d6010907000c002e80313003154058149140e440607400c800900e14864000725941c0549049031084200303515501c154414100c0305849208040f041d81e034255a00043d108111002d02c0c02e0071241100d62180c14100ca4a40d0a818042d04128 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 422582014 1250 422580764 422580787
    0x11202070f0c0807140607170d0c0c060b031f020306033a0804050c2709010e0d05131505120108010b130606020c01140f12011a0a08160203 61
    0x800000c82030b2809100c1c0101408140b006101e034400a14004450343c0e000c909070008a0800c0c01003010152054803940017580d0b04e811020111500314443c01000c101540b0362240240002c4400c600075501c540c942044e2010500300000c00b000d045d16522484640d8000c807040000103913000805907601401040f40007214401d1484041148103980300080c901c0742e0700c02d182c40c50315625010802040002c404280b0020407000b1a914a0080d419540c41111325028183e5012010f8469102c0420080400030001ca0980641c01144800e00b00030940720b10000e182e808a900c0d015a0940390740782d4941c00030410080c425030201d01180c0c18035090185c00d1415006018240c2d4409038007103004d0341d44582c2c1c6042a85000c0c0802c000c0400e602c00d0400c80642068002940d450b00c004180d030500c151a078a8014032801e80c030650301c80c444a00781e0300f5034031140f00b240103030401401e118605042000001030b09a003d00402076072050040703542c030708180d0b03610003811808a5420350199029800f080144440b40c0d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 422583264 1250 422582014 422582033
    0x8040302031e0d02161505060a090f0b1e01030605012c030118080c0c0306100e0a0e03040602070509061806090a110a03090201022515050d06060305040c0b041401120207 74
    0x21503c945c504449002181400054851009a403410144c9003408000840c0e4415100c141600d00c02d000010b03106491500507001010446003640e4401180150b5059844045110454017003082e40d040c0104d594130401543c01c42401d000c0000d1840b560f031800000000003155441c1d0501d40103002152064018158100b4a20080010780b9030390700029008020a10400801540460036801424140341c4101c10014407002c0b8001c0b081c00035520008545680a0f64001e4005008000f080d82d41e2146d03140b2001c0e64408151003401c0c010720503e000507842d45091542107101c40020b0901040c140c2c0c601082100e42c04005106080c1140d55400411281e42d90740301821411030251400205000180006882c20321000c0b21490b12084030740844050300441021223041b40c0e0140c07a80107469000c80010b03a0036015408890000c00d10f40740340028410b038180c018500441c0140b49049019845d5403690980d4070550151148802c0031105540495226500c80180540711080050401840e40e65440b0907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 422584514 1250 422583264 422583277
    0x2010020c070b0f070203150105100e040e07060f020d02010204081e0a1a0f06041514011103220501020706090b07140604110310020702011d01021e030301060f08040302031e0d02 77
    0x218000319140b001c42c02e0130015607c0803e075552140c40d0380e40c0342030001480f00e00d0650542d01006400c0c4a411402d071502d41000355600201c00940d44207607120341d0018940500030f04940010f10407210740300a4103006108590030b44032481e0181c40c1820b00342841410b000c048004814840c400c02d003280b00450342e480c0c00d4001d0002ea4050300d0f81a0704150150700b052030400b5195611840c544400305900403a564446011580b950714501008051000140e4130301195548000c2d66010004903030b210300041c2d081070440031080c0141c00503402d84410049a40b12101d02038030340410100601885420002005004403903c50b9100c003c040c03080b018864141070003585d0441d02d0340000e0480c0300300b91034140f100f4003441500322000c50410140d80c000802090100682c1086a10100601c000c030381d100b0300c1280d004903041480c1414070505410b0a5581e64002d1207400000b42d25624041c000038071030341c6880e009582550056042c1091a24034202000c441300310241001070800802480d44410b0014006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 422585764 1250 422584514 422584537
    0x18030307090503010b0f011b0302190303321b090d0b0402030607110c060c0a02030a0528080301090510030210020102040f0803040e040b070207030c0b0405012010020c070b 75
    0x1600c0b03191505050940d02e015020342e104d031080714040300c01039900c07100904030303044490500340031039040b410241c3c2000d019001ca40070000d0881550014560944c2099012500003100c04517a144003e010301d034802d0480840061650200000c90240381075804000f40725a110040c3c0c078500b140c1a0f00042c40d03042025001c4071824800c0c2c007040b042d490144000d503480015400c1c02940306900001090326078802c0041780b40314440101e00c1c80c00b030000c10001c00401c640c1c040c0c04c44034454450304180b42c0c0e0701c070202100045801c403114500030032040304c2c041c1003904d0740c84066a400c6034280f240d03800c0605001481c6490041c1452800405a6220071001d80da008841d000165543c0c1040c0004503e844990409100c5600c00c11040000c480b100b02240e0340a078114000b000703a51256901241050802d80c400380c035070480350a000c0b44991602c1c00510485500343ca80941880915415045200400800860700d403c0b007410140b8030895500105080014a0f0984800d5525206403241c603401039215441c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 422587014 1250 422585764 422585777
    0x70506030a06090b030f0c040e150a090507060e010e04050415111902010227061308030a0e030115031214040806010521031606020906031f06031503020918030307 71
    0x200110710914074013000680240c0383c525140f010040c0c1c3c0b1055000c03864052130b924030408a0408060081c822903a0f4142030040c00e0341410010350780641444038003030360f850041000000720309006200000b60000180c648074100e12101c0104001800e0040c416074240c02c940080b20b07080c100f18170427914040d07080c5424544614004c2d660756044000101c8400035688108081003004d080852440340340b03100340c16124025401840412074600170a800c00240b4a182c2c6004200c003400880600600c488966855507140310143c00c06090f5540380c40044090f440307551080c00415204080415007035001c0c24980340860805041090580c8158000822904070030014041454a014000160013034802c200040409504a00d6142d2103a00408460700401440d80010051b80790195009144010141522072500c08105410fa0242d4102124011030b5038402062040c080c0c4200f00700d0004090301c21138007508550a2100e502d402800302420950b010350003816050042008501c202559503485 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 422588264 1250 422587014 422587019
    0x30c1b09020c15130b1f03020a030503040e0f0621190c0e01060c03021c0228020f040c020c040b19060528080a020703030f060f18050903091002070506030a06 69
    0x60030030f9400504810390b007500144000d00410144030003183c01c1040b18480c645a112008448640c090407980020b400a0b403e003800000e01c2004800361080303c800010003051035a91051300ca04611080711465402002e100c1106112200d04401c1c0c54000000000c40d42500024000c00d9107416030420125004e464040050001e101030702c0c00341d030042040d810010445003c9580294a4850351404141451a0741d12141c80a45c8200300c03d0408410801c035100c801c0640000f1400c10414080040e402001000402c14690038548500c206c4da40d141d6001d41f6104420f542080064030003807040c55400a5020000401e203560000d01c81c1c01403500352140ba0b40c90400c0f4001811801c1002107960342c10010903403071090340c2e412079851079200080c4040182d4860041c0380603401032001280840fa49813410001040151582c02c2070401e0342c40c1c9140035501600d406002c0010f85404441040054205003c90300c0c0c642030260f154904a00c01d0b00540e12440d071180302017202c641085070303000c0105460780b004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 422589514 1250 422588264 422588293
    0x40b040213060e120304120804050a06110c01020a020102070b0f0d060f1d010515030720070f0e0108030702040b120607031d0613080d0605060706060e1003030c1b09020c 74
    0x400f4081d401a145030000c0c41461205035201d000364880d2100c50240a20749208004001007194094000200f01000840c0ca1310002004140b4080301c04205100c1c01140210540c000103100701143d905074001e22489080c641c030044550055490b4a8010100380120000346050340a580c014241040c800385e056441c14001d00c80152224800001c03c03640040184015100e0321280f85c114108641440d640761208001290401005000c2c03034400145000d09900d0409c000c20540b0071185103d8425040980311f60032040420001e10980840ea44100441c0c001800c094008800380040200243d0421010b65081410800c0c211751000001303a4418800072102c549041144040002070300a0140c3d1030000c0c0c80c48248600c14602820681d004a0f480f03d030600c60350030150103450040d10381c54464045142010250800c0e0060307c0c1e052500305d0000d515000300d600a04c0c101c94040c2e441c0030f5201c03221b0300c88a03411074071007004040000750113201041c02d01c0c003030006001901d003100040c1001c4500381403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 422590764 1250 422589514 422589527
    0x6072a120314240607061b09050a0608150a05101215030210110c0d080405131815021e090a0b03190f06080601081006050f10030b040b04021306 63
    0xd1450002002c8014440414044001804400d003002980c0782e0401c21000050440c0c0038148000304a50305001b401001c100010003504059051912014501a02e070010044203032594000c03140066100707400100201407400281e04444c4002d06011140350716100031601120305000c4e0b0f480403400c08428107004962a00c00d2510541d400031210f051142194000f804070582c0c2c040c400200700300c032145c046080106101200c1c4019008000319801141481c020220750061b03c1000c0c0b18606441c0100f80492842c041c100004054010801010320540d81e411a00d0502800d880d43d034aa00788a950240d1a00c80020f10904d14a8a5050b0711a40c000d81000840d400340d81004400c1007040c024020b00c84100480400001014200851b88240e400080c0000340001da210040912800700002407154011a2140c108401c0c02000e1280545130003e01100d02c4180103551780000d140b24a14000b0340c840d40c01a8900080100701280d180f84400004050f43c000b0a850101c590030304104201c0c054000a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 422592014 1250 422590764 422590781
    0x8071206060e04050a060b1b060603070f060c03090b0f0327030405010c061b030e070806040507060f030f09030509031902090606090a0905041506060c020306072a1203 73
    0x8414010541010401040d110407242800d0080f034032074020480e00d05490b04400081d14010a07281c1e01c41c2d041048090201500c50f4104c1454025980450482e08002c1000c0054545240710940c050746030100403505a50030302000d0b81002150761010401d15100c000038000b03054910314250701d17820541c0007151010751220f10b0b5102e409148400b07100444001c400d131801c039682402c200c03008034090b051040180024802a080707040f4203021802c145a010307400080c486070b90008a0307c1441d2282040e031b64a050594000d00940e000500400c01c603032240d9020b0b021164980360100d404071200c19100142c075501e000071000300d403000c03515031658141080055441c0c00090040c004c0b100c515004104208800703070040e4042c020001c0c0c1480203490300380c6440014241c41008101e03034a02400c1c031650b81e002c01c503030003040b4600f40000000c41314451854100aa80c005018140544a21006441d030b1190b01d900e4006103000034560f0107104007119941030405005105015009049a40040440301c1d2070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 422593264 1250 422592014 422592047
    0xf07050a0c03172b0b03010516140418050a020d0e0a1202280f0203100209040b0402030118051018090b010e04170c030d0504050d0807020c0303070b0606190807 70
    0x1440707244c60341400001100541102860f0280c4454080754800d0040c04505002c0c1d0782660821080c0006802101c10b403001c46031095840f2001c905002401560030700c954454145840d00074919034807040b0303a9074840d81e08002e1160307005180000022400b02501d107551000140f0360440c103849030600051000c0707026a41400d20262074401014a03503450703140800c40360542c40e0346401d4101410031070302c0144150701f160003c00b29000751407004c400c44061750090281c00e020381d0a10315040410308150007544d041c1d030a811380301d0712190061041e1030003d1500802c08003000b501000c0c00101c40669100310000f05004880200b2000441d00b0b00c1c203150903040c1e0000e481c0320b031070b00100400300301c3d1402550004241480808c0c0c0d03034150242854954015803c544103154034020601042180c0021031400f0001282c07107060140c1d481460603030b00c52100e014410f4040d001000003038001091300341d40d43e5010100a00700360a107035032f80005100d20801c0d6054840425002d0b01800b41c1560000808000740008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 422594514 1250 422593264 422593267
    0x5091806120c2b0b010b0403030e04020412031b0b01090f060f05030a14120d090b240f060403060c0507020a141305060f0409030906032307050f07050a0c0317 69
    0x10302c010803014515107100d00c0d03c480030500c20310b9010080c014100206a0400c105290a503140d6148101c16441444101e01188901c1d028904a080600030343c2c080b01d0b1000814080311070300307403000d459003810340410940810b407a05000b800140c0000c2164080d20130702c4000910541041028000c580903031308808520f0610140c10003585e680012106d03440f40d0f20080220303a208104404a14241d0f8000f031851f185a8041581c0052912503446031010034020710b03190403162101200c082901d800742c04c20300c4c40452122001c440074104000380c0a00c0c0f64000c0e0039280342941d2501c903a8115452041f580b00003660002c1c1d000705510302103840c44046c1c0405d54080c0714107000a00003800f8120010844210140c031400040d01d1999409041502e500000d00244100f150510b1b006046040501070740d40406c0c0f601c640c0040783c2c0300706800d401c4210450880f0b584191a42d46040c2c81503000916104040c0c20108940340010b601800704800d01d034451408894003600318585034058210b280c2401d1a0b6450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 422595764 1250 422594514 422594533
    0x905070e0a0f1403151e0a14040303020901021f060509310303091202070906090605030a0809060405131b03290a0512150a0606050304120509180612 65
    0x401e808034101c49903c88a454640100004a0301349289412400030b0890441d0400c4602d0b5012174450400305095061444c050b43c034000007604030b07081c5064a0781000c0c805000600086d020364001c03d05d951050044401401000080382d20310a505181d00320b00300e8031407408000398284811103681014800c036080c1651106200700d00e1400e451204041007c804800a99003814000d510242c0210b030403414040710400d1981c1c02954803c003e00c80d030910a46000000903003504607110310000e03100001c02400700d80085803035410703842d080103079001d0380031004000000301c03a0742d60100d071418200518008105003c0c2c00305520466001c080310030040c54141407030f803011701c00300220241402060000c0b0726074004210001c10304100460b0042900012180e0914040401c00281c1c1482440c01c002241e103195038030600d000c00d030f030103030320880007c14024404500051400d9101885540076850100e0a0030b60980c0007928000751040c0000b0700d400d03540c041c171031207080c4180007400d4840810000c141650 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 422597014 1250 422595764 422595779
    0x90218130c080c03042d050c010f020309060d060807060f02011113180b0909010b041a01140f13030b04060b04090b0c0d090c06021510080d1b0204060905070e0a 70
    0x48000c01c5002007410000009042101c41c030a5000c40c20302c500d052480506c2c0c41100459508074203041a101031050000340c003c00d43c49100d6140c9596860341c040c41c00d0084080138807140e600300035031103400d80b5114200811030220400000c1d000f0701c1c2c55581d0300c0d0408003e51001e800c482d40140148603800c1c003003045009451000400348210340121101c0654000e405481d14014080c141c9030301d038400f013070300d0070f0003034403a015001000011000c5404100040300c41130040b11362882d51500c580494483c0000c0307010340310354401808415007240860f5141c5548020f030388260814a0b0802c4851100074030500c001d00c00e061007404900b0005490400040f01c26441380c10489000400030707402405d0010302c8090108d000e4000303105459011030602a02503c444020703440b0155480c1401c41001400002814030184084400490b045040a040d0340e10888104443c1e040402070fa1129441c006400040142c4031403140300c0040c050600c0c001118100040b00800640b485145148182c1a5070014040ea0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 422598264 1250 422597014 422597027
    0xf0807030c050412080909041b12050d05030702120301030b0f070c020d12030f050f0105010e1e1504180e07061115060411120405100e0a0b10090218130c 67
    0x84035004001349540040d883c0c82000340c131030240480d030403a20002c140010440c1c08003041c0c580c0390f60200d0f0b501c9143c0d01c498500009034510031000d400f5500c1f101080190901400085800958510690b40d000400c2d059580d01d561080c0c1c8101c074440341001c20080203036142400c0c540c111044e885d00d41206822070f0006440141200342c05072540d04600140024a40298403001e000c07104150140034034030b005016564030260074415503000c15104d005401280c07a20f80c40100c14030700c000d2800013402080301c0500184260020010406900401001c1802c0300031800440d0340740b115030004254403a602422508204503503200100744050340c49070788442c10022901080074072007191003608580d50140014054a025048003521840004d6458030060841c1c0340244224054421148082c030f40d80b4080080b544011101003458100c00d0304180050912400142c0002e01800c24504954603010517008030b07800301843c050042001682030b2068180780d1074104040130506403c00c5466140301d00901070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 422599514 1250 422598264 422598269
    0xc1703030a0c090f060c0b2d040204091502030612030405010c080904200c0d0c021503150406231005160602160305041d01270e0d0f0807030c0504 64
    0x1542e07240c0030001a020b104491100040c40c207074950781180ca503514005000c500d8022403d80751094180f00081c2c0c4003900051b1000c8102d07141c000c099015440612000f54084d021344102ea0082d260b00f075a402182c24044683d402d6040c038400140c0c0c0e4103082c010441c8801c80d26601e900300d078000f030000300080c6e0382000e0710940040d04082c0c0b2139503a40b1100006002004c5482c1008040d6072150004503911405c0d034068115415070300c0c101c0300d000100403010b030b404c084840002544030448001c0001c1201c1107101442d000644c00074000c843c0340703050b0000b506640342a000f0101b10300881803002203100150465a4418400362050f503194034804000800a22603016030005100403056580d04005a942c1162482c05106903030300d80b14103551030300034000e81c0305210f01d09030702556000268860410300740f850f04076140030a890315044814946c4c420b540b000f03030f01010324042e9170b030510030300c41d01d005e00c110409841c070703641c400d0f07a81214004050491400a4450b4040600d000c203114085034001d01107600b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 422600764 1250 422599514 422599531
    0x80c09040905070b030405071502010e0a1e02090a0c0e0f06030106030902060d050f01090608340f2c01030f0308042f3613050d020a0c170303 62
    0xe07a15071905042c0d1408a26900040c2c03c414004100000e200300030912100b500c070a04039200101c42165800c0f03082c1c8000c13590300c1d4a6500401c60807800503019400c845907418030390405840810041e000504900c0044a8241e0a55102c0204c14051903204040901c882400c851000300a00c030389010400a0105019600506d981c0b40c210381c06541d00c00d000c0d6040c1000c01030081c4818a0f200c4010001000c082c842d00800ca800c1950104503800e0200b5090b100d042003030204600417048451302802301600c4405910003401c495404a00b18110f044640003410f0031410f01c01e00200c030300c00c90005a180341d030f00352820840d08500620016495010f124241501032a0404c0691642c0c00c00084070300e80c40c00040600b0380003102111842e02e14560150640f030084400710041c03422400030242001003480d608019400c800c40d0002083c0343d60400641101410404411702001a69003d142050525103032016038440f100c1442044070000c00400a45501807281040450100d14503030b503408090411b02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 422602014 1250 422600764 422600771
    0x30906030501060302210a0e030d0f0614030303150a090e0a0c0e0f180c0402040e0403090e07140f040902041215090c050f032b030e010203010b03010303110c06030f0f0601080c0904 79
    0x4480390416000f10045130230800580e555200300780c2d4188020220750882d240e14130306000d80011030500c0c07600c102d01030b6234016014600d90b0760ba0400345118821414000c03580700a04240208803099184106030041c41e5540041c90740303070128105100e811902c1d500110703a1203443c00c00c12807540d04142c80305421a8042c0c0100d03202c41c0800d03c2540c108510030007c10307001840070030006030234410340e2107443c0214060746038415815181d12000145240840b24030011a0307545c2c0c0201070149041005207d519036401515040c01c0c1c44100d00f0040e60f1281e0310812145a046032200d00f0302031000200300c070440300401c0801a40764180d94114044480348aa107100300c1e62a4050107450b20280203005001c0c0c405441c004800c1c1103090034a00302c05484079800c001070f04d4104040910381c014404c59060342d03c0340424908580c61983c2c1100c000000b010189054012071503414a1500c0b9400a180a800000c200d07a0340f900d070000180400c41c40041c500707810014540144400d00e11900110703a1070440035103000c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 422603264 1250 422602014 422602021
    0x26040608070c060207080a032004150504122f03101806141815061903080c0a1a1005040509010b0604030f0b0f01060e010c030e0d03090603050106030221 67
    0x640d00a202d100e800341c406400042c0035010030400311300401d0040704a45003040505000502d0008404482424020b242c40820090120031505054005035030000d20f1b15515094840060070030944000c14200c038520590310442c940301c42d402c1d00010701c842008407507194089600000985e5441e080042d884c03556500d50756038212140511000700d102c0c0d04034505210b100480ca0007200c45000485031078920200c0b01000001c04580420020700c034901644d142c1041d070711158100890ba803540d20700f4a9140b03020b07000010029030f100700608205551640500103614250500b11061003c05040c0b0f001c000790041041500c6004046400545030160f900080c04c1e941c200c0700078010700031505040e41c0035401040000800c486140780b00c00140c0b1891000e021a2910000d0400c5107c0a0040300089001103d0100c029486482c40a01c190700910b014004145a031002c0744147c072a03c0425800180341c5078041c403c85070103006441c010301e410f1400310702d071028071003507400b0800c404644c40c0111460715010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 422604514 1250 422603264 422603267
    0x70e070f0e04060b0c06060f01140414180403090503070510120b0a1d01050f090f010e0c090a0b1908010b0703051e030f0a05010b0702011b0212030c0102072604060807 73
    0x20720151411076112955049071141c02541c1b02c004480d84d81c0b0032080380101c0c0c0202d5107d5040503c50058565806040c1170400d07141d04568288600b8140d0040300301c1021900b29a80300d03000034016802610b41c08442e6041c10241410950075400c510301030040c1e06040041198499032001003103241440000b808c051420001710464925806407a00c5403080390f09402000760707000240d04031101141d4120382a2078031400d004444801b1200c04500d01d80d8100100000001000b1a80e4480481c909035450405900300040f4034099940101025003008120301031445811400080310b9105c3d414540a55032406602140b24401d0390001000c00c03a0200d041c665140341d0303285103080c0c01c000c480303180d840349048015140d000400b03c030320110460900b4000940d16401c00100c458040e01a5514040d103810b8580415844a10000803a002501041c0c01802c0080170300150000c1501c0354005070b6545004d0074205000100304401070320301602900d200c61181000b00c00c54049652a0600c40e1055807680c90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 422605764 1250 422604514 422604521
    0x1202010e060a110717032205130504050115031119030606060206041506032f030105070e0f030105360609070609080c010e04110c15010602070e070f0e04 67
    0x909500180e021440440a6801c09210481804a10200c07444d103596800e1909100400000a40090b0000c100011070314260240c60030040d214225444569561040419080e102409081140e299503100788001c2240038059611002c4030a0050300065040d511001e4089182c5402c03a0f100d80d1484441d0000201a2a0b00710021078201c04108a010b0743d543e0065242c600132681150505200b0449468101c0700f0321694040d41e4205c0035103164121403d43c14100081120001280301c0d40c1c1517a4180940c1d02405807030702c610b50325134900515100d85410304c12100d100084541c401d904007820480d00b0345803c80d9104400c000c07051201040a1500d01c8454245580001103420b070181004201c04d240000030380c0700848a451340c460084950f01e6000c9910b50b840745007000d00041c401c525242c0c451506811000341c13040660881480c001c03a80d04aa8504007102c14120490f4214400400449405001910041c80321244d8415a4545528000c02910040409005000e00b42c44071407840d45880c2d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 422607014 1250 422605764 422605787
    0x120b0109020d15030c080c03070311060d02041701090201030e03041805041b030b0f0703021215131a0307084201080307150e2a0d0b0f06090c04120201 66
    0x81103c10110303264205004030514601031250f2510640940078403d0400141d01d204070307504904c504600c202d2003000c0080641c0a030601c000340350780a0101003201c0f08003482d5006414081c0e000060f41c04a548005800c3da001c0d801c1304003254000380000c1024081000e07412002d90311807500000c0035626450003d2495000050341100e0b000d50080c04020001c0d011410303402a800021103c601d07031f0391443c00320b05a10841e044803020840d0034001c1203106000d109000e450740340042c00c1c8407d603250708096000703c41c50942e0707602c0048004400071840313050620810014204000140000307881c2450030303806001501e407503008030001107c01a800d078202ca860744c1c5ca0284115420b4000c55079111b4555a581d000710106880e8128060061500b120343c40c0704061400071000007600c0c5480b280300190801184c90b1802d00070b6008490324512860b66594895240c80c1d210301d40d00c3c526401d002c600707060360440052145000c0c445c84c2003804001c0c00d1b41c505940031074040c02111058040207100403220813810a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 422608264 1250 422607014 422607041
    0xb0f42041b0807031a010e21160603060b03010f0506031819060525031a030601170f030a09090c1b150c0c0c1a04080d02030a030501120b0109020d 64
    0x60031400c89501064150003010f113940c0034030600c14840c904c20311031101801598045000201d48001c1e07400d02444400300480c9800000c0030220071fa461440c201600c46000340000703031101a00340301030783d0140b203500c2c05031001a828034150360406d81c074400000041e002d00c9100c0d24011000928622800300344540031000c9005480c0f400000c41540805d009588000704d40d40703403c0c01e00103102c082c0c002098100c0f0840c4ca1403620840302e2002425001014001d141c4054189600c0701451203032420401a4024081111044410180d000045060070450f00c4101c03001d42003000030650441e40500c0e03079002d0390341f070800c0040d10014011003940e0714200b050044070380d140e060144ac41400741001d6422580741e100c0d0401e02ca96003010a08071240c0c007580d1001000040d4100051124101c40480c10b5800308000c1d80e0203141c1034445d000c4910b000070714080314005a1000441c1c09601754180a150300401e4076400c1c2100942040c2d40d14001840140101100150701248211012100c0e821610381b81004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 422609514 1250 422608264 422608301
    0x22020a1a0d0f020c07170f010e10450f030c02040b04060308030423061f0605030c090d0615140f150a030c0207030b0f4204 54
    0x400c86500081d0400780503004407502d464291180603249000f100c19562102d80035006060619500010103203100030703080505e1041610401c003c000034410003181c040344d40c0c02040702071003140c5810281c41c819007401041c01c01030f20007090f641140394084c0e46000c403c0c001b5584010b080d58003a401440c058031010348003841304032050040c540c214124102d030701d0007680c051110848040600c0309542840c40b0090082c0070400c0002c0c04103074040e039010620124603440706410300010f051b0500d0f29106441ca21001030700c0324804039044840414601c000d0840d401c0980c00d5103480100310009002d002c00c40381c0070b0182108500104100d90340300c480354003007200c5010b0065480d84680d60043e80c42183d2907000c1c000a48000d256840d2002440026450b1400003d10342804500d044015298224401d400e61280b1480840095420f80d0128825145801c0e003044030b16008440c00740280d503001102c48900d500381c02d420b4008881c0741410090304595072a650142550f080454020406845c0800403c200b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 422610764 1250 422609514 422609549
    0x150e01120609020705070803030112110d060e030a0909150302060c010e010c0e0f04050135012310081e16030506010e0106110a0212010f050a2322020a 66
    0x40543c081e1450342c2c00350b012035907046c2d213803843d031680c920080c0501200307886201d035800f0008801e03103034004002d01c01500c1c81d01098a03036641c12054070fa554059510903040410300301500b40d031100500d002003a01190600c0803da0040311015541c41e00d0101074012600001c440b900c1c3c401c25000b640c03409030500001c10800c0c1040a000782041789005449100d2090402201840d190601469068540301e0044034150811034071007003805d840307210603000301d2050409400c0c0841000e10944108040f16028016609203903210b2076403ca030020581469840c1001041c84100000203010510500000380240042c0d82007603103614110101d4515068600034040100400002081d0f40f8100d8018402018050740c1300d9005980507900740c0f080f090203620503081031001d8900030b090f03e04d070271400c68000580104085922000d40740d040701d0300c4644640355542008868031070200d141188003104402401410f000b51450051402440200d500180d0b080001043d0f682c0c441c80c000007002e171000d40c042801c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 422612014 1250 422610764 422610779
    0xb24120c01140405131509151d39070602180d080d0b150c0d020c0303160b18071707120305030609070918050f060604150e011206 57
    0x844012414001109030610505000d141029101501d03c014481e80740d111071700040a00824801c03904050100007480e00040e08405482489050780e005010301150070b00f80254261086001100d4142a0a10380d0400c0040c007010000652a02410b164050355041a07401c00600c2d44450030641d8051080019213004101c12980201050b5555041c00002c000ca40c03020800e2580048001801320402004500c2120a8607804955a044000c100300e00c00c2d0000c124014590f004000c481840c1c2c0e10070103400200980401102c05440412801146020540f1100c00c4240b002000014032410201001c5014840034000664101340044201e4060641e6074076002440601000705054500912901007902039003401500035094041d2070340c4e4a103031580402d00c0100030004001e00300300148000042005080d40084034041c020044000c01c41f420100d900041000d00540210300c41c2100300410032401c4070006103c05090068240580b6092028006840b242910b10011030600d140960100311071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 422613264 1250 422612014 422612023
    0x11070506100f0902030703060f1d0c0f070f050c04090812070c030c0b0a0e1e240c2b0504030f0c1104090c0e0106050a110102070b2412 59
    0x501900440d62141c540110140004849014410851070011403e000960b0a50021a00800145000101c103941c030300c0004100c0c01160040188040380c8448455103081100101d44c104059940c2149400190200c0c854184501c0c080248061410242d010038400e00348804d4542d9031014000740300e4030b1264a001030460f80315071040744c0250481d0000c210710300c0c410440103200b01c0d80758a6119440c3e08603240c0c03003d01c0c4001450354020b96150840803901d01c2e402c1c055030100380580900c8130401c8a01c4040c0909010b41030001c14000b03084075414151011400d007044d6000b5041700242075681092080d00c0c00030000b10b104440c040d0300011407a051015040d840300c0e1003680296103d946000fa2130720101d8030b201800700c015000c0e40c000f550803403035440c2c07690020784a07501c5440003065079a0f9034600850307071000036407007030340440e1010841c14407c58000000ca100344044400840ca070460030b640b410800700d0060581100c4201c4c412024401c0c450790f00403582e603c0310041c41c90003116904610729965 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 422614514 1250 422613264 422613277
    0xe01180906140a061b030804020418060c0e030f07050d020d140c2707030c0903051e0105060d0f170417010c0e04090221120408030304050705060703021e030d11 70
    0x180f00d00030000660144100c2407606081e414a035520115403054404440c5404094001d070303807169a40c0c032002d11956803c4070709403040d48118000300d09256440b1014141e04100c1801c0c9010740c00500a5156042000c2516070a4400c00c0761031034a540584c0c0041059207036a00001814501156050001103030700003002041140121504920b40545030001e00c807001503801114032601c0c01c1c0c000306418038041d401c91440f800007031034012001030b642c0d15480d1400300b611855020001e4422030076803401d2028081c850348a13805032820b003444c1d8140c0e40c5a5003030a0302a00064201004150400c80520307102080750024030310034000074007400c0001041d50081c00d003032a4410100740817072507040300c6040c00d02580b811075400821401c00c807103005003d00700348002164030582c00c6c02800c94401c1440c50202c040c0000d001e0b0301340115102d14240c90112725011894208901c2010180701e0030000a50014040c81c411743c3c400071035051010140d8456180d80140d81d00c403104581041c45c030340141aa0003000e80746 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 422615764 1250 422614514 422614519
    0xb03070e040b060405090f0403050c01180204060803040501080a0b0a1d09010b120a030305040807082b0614060d06090f02070213020408060f040804080703110405070206070e0118090614 81
    0x41c000402c0c03c101480c8514030a040d000054080090381c1c5070400c08413181e0042c00390500f50710340302c0386a49081c21502d00c04030056420b03002801400a509191003118040c040c1e48000794602420240060304542e002402c0d40c071400c0e1074070a0003c1079183c15852a00070041d081031180034225503a0804070210301220140120b40c80c06000d00500d24180000e041c1000404010b0104500c1079102180940030040c07003510868010042030001400400007440c00302c411540080e010840b20f1488001c3c10290955007590070300f400c20500003640007003254144c0150846406580b28421843d00c00580070550122100d1440c0058202c00c030161a00200b00c490300c2220f01c501c14103440009034040703002e02c2c080c1019960115000440d201014861680c1082c000e420341c2d410995124070841c0741c4007581c1c000310340300284901255140e08141c040d8541003645030002d800c0f10f14103003a006040e42d000382007290402008408011405136000941e0000e4540c0311400c0c001e41d900c0712045092013400098550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 422617014 1250 422615764 422615771
    0x1614181804030e01030c1d011b05030318060f010e09160e09120f090913050610090c081b090a03050712120507030503010b030604020405120c030708071409100b03070e04 74
    0x11003c4d03120303101c0e0002050607a11005810b04803030381c060801c115441242c2d4184803040f0901681c4454181721155801d00c0303000190380d45d00e84601c0304010202a03405041d4950306c105c0c24001000d04114045040d20490001040242d681d01c050500d402e6041e44a000502d002401c0854070030080d84100d88034034160b00441d90780009004658003144169503041060300c0d0140694070f8549000c00f08181c01c50301d48a094a0f080d250307511454286801542c50070b10010b803d1400b040b030f0a0460082d401c49045c0341c20150b1281ca4246034500c407440c002e140382840048001484901540da25061102840d000b8045030500350319142001006000c0040913501c8105888081c07111360310a108854100b540340d80c44c9801d6902e414030032141c54001501d20347c1e20540921000c41c190b00c1d00383e071a00110101170300030202400e207001854245a500e4000700c00d42e4104480501440000514280e0164029540c42c011941c406908228110b0603030000518000700000340800ca0798840b10340844844212002c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 422618264 1250 422617014 422617037
    0x210e010306082b02010b0604230405060315180a0b1509010f150c021509041b0c0f050106170601080f0303010f05060a1806030207050105161418180403 66
    0x8035515074408030041400140f000f0705644400050480001c58101400041440540c0100280c610f80050300200d44241c0c1c030041c21011021041100070075610140e0f0b00b041513040000200362100b00040400389144402130125005442031a0010b410505207410703200c0041c03051030000540c44041c1c0c1c400c403ca415850001c20030f490310404444c100c40c80b109091440714504092008011080d00100041c40040300c103200160704c405081d06a02108000c91720341e21780a01d400c0000303c484040c401c10401040c000601f101c150400d0b14080d2043e003049604560044915000740903005179002002e0400505049013460a000108035050b90b180c0429500408a00301e8503d6580c0000d200303504050900d10000c02c4030f4146034009000305c829a1900010640d0040c10402d40021154002000260300007181c4040c8030080c03051540001114118000c1000b071800003d10400c0c0e45420a03025940000e9250031008403100c00c2014400080c00030050340001c4480700515500490301900890762106c2003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 422619514 1250 422618264 422618279
    0x4080a170310051e040c0908010e0c030d030f1e020405091302031902271f05090106030e1515090f060a0b0a03200a02150c0d0504210e010306 62
    0x36248540c0340b068181c101035107031904014010344070200c10080d1107110118503805886901034001c81d0f0083c1d450781c4c00380914005200c1d003182c01c00c1c0346100b1a90070441d01d0021594000c100442000864940843d450312108010401001c00d03003400e05c0803294812040d100800d540c0c000d8822a0812603c521003a511504150540300070040f00943c150819054010491399009280b00038034000381034101c10b07418401e6030300c480d034085849503070751001c0d4413040017002c0c3d041940c02d100400344108500d81252400c0301203030313400381c042c02007800b899102c025181c228582001007030422507020b131846080381811a2180e400390f610211050007200d400d800614501030040071035002e01c0c806021000001d03e400340e80150303908060700050415446403a54000000440c1540d10780b40f1610070034a0f0b4a5030203480203850401e498502c0400482d00c1810056102041002c1e43c00d40c50f441d00b00070030340b562a85051006051009076000c107552050461655003076003c11000800b503400e8804100072511640d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 422620764 1250 422619514 422619517
    0x15050d06200f040515120411031006060e1002120d050106090e04030f12020c0708070503010c171503120406050c0607020102090f0607020f091f050105091302160804080a17 75
    0x4054100b503104010030041810a007040c142c034204420310340c03800c00e444003103c0400d80f901503d0588150a00c04007440c0e080c40c042c0300144c0d0303540f9840300130080f44ac0b500c000941100e0188184078803558080281000d07103402031007109100312410645a0f540c800424442005020038041c800024441036400b18540020307412a900541e00b6450b145002c00749030908030b80c8040488841c2e03104035000d00200482c8002000094040c00003030300985080e40c01c22041c58216440c50310414100030510440a800ca100c100781140c105410704258021900100d01003171034003607540c540b1408030100141c00141554403501a2126440c00001c0c0c841c41e45503140120300f41d014200c1c880381d101031080382c48981450300200030011030340301a004503505030060001825401c01140d0038410800580d601d064403e562041103806490309080c940c0c00e168140c3e02282030050009a0031400503070005400ca84a0300c60f0300da130300c7e0f101c0d40038403001e50780ca44402c921a2101285e04044a220f40004005d041e850800740 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 422622014 1250 422620764 422620777
    0x326040f140103020f030a09060608060114040f09120507050312070f110c010f230406020a140609060f041505010311150304021509010c05010e0d0807050c06040615050d0620 76
    0x1c40303460850301c03041148001400da00324100d6440d40d442c2b0b000100381c1d0f02408a14024100c1c0d185100c5c1c1e0351490400e10081c6c86080004c0060245030540c1040001c0c40d030490080b0306e50107890600c1d00c401003071030010701e94400c46104c0c401045901040180c0c40d44d00051500c5488090341d6002d0100140000c440d5641606034995400b0400d510784140c0c03450b01c16030302010700c000030001100e41107150303000d403444541c480c1d00500010382002e00c50005002040e84460070405c08a0003c000c2e9103859200c154135010090a00b800b8041e805003c0340c1802a9983c5406214a00160800007035950780b030580d158071300307904070640a11824800500682c0144007501e00c1683c001c0c03e58625204121980c401591040009906001600c800c64010400910640c00408117040046c015080581d0000c3c124100081001c001c219042102002e255030100d0328036003140d44850301040e00340406924001152040e00810b40041d9503d40b000c1c02e0109540185103000651045d00307200800c40c0002035107a01c02c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 422623264 1250 422622014 422622037
    0x5160b03091002030a140406020901172e05030118050f0c150f040807140906040b130b120f0304030c0603050903070314070f0f06060b090a0326040f14010302 69
    0xc21030340b0900301440e002160300003107002c0d0010b9521001e0b1660b204840054806441c0c207680800e00304207a507000707140200c100e03080004101151a1030780c500d0001101d14013030070141c10100340800b2454545e48030300034043d14000300240706486e0b00032081c03402e00e282940261030510450414204224021424805201c00900001044031451505103925480b00f06050140f0100b0417000078101c200b48048000b40084040c8490210110307010880c68900103019540b140c1e181c91401700c00c0341d40740d0700d10a140440104010038040b00800c0001c981700f400d0b14185405004000c0782c10312144000c030043c4140c1c1c0c810745d54002130070348a002c21001c81c7c0d0b00f21012844c0b64401c00a00000c41d002c0d131805000420708416081c500603560340c4800c1b0b2a48101c60484406100e1725011081060354000c00001e40b6640c02020b0900029800194000300c0e5844040c044145100342c001141683c5007140d00c400c0c004d90030306030341c403642c0740ca2482d4a00070314403a107522034105100c6202150300c24001c80d19060b054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 422624514 1250 422623264 422623273
    0xd09050d0f020d050c0f1501080114071b050115060203070201030501080f0703022e0302040503190c0902071401090b040203060c070309090b270a06090b0d030e1c05160b0309 76
    0x81030094070140c0c03000400f0301c0c4074400d8051b642c2102c40200408030080c801c280b0003c80c5940744c58211401d403141b02801e0701c9000c0c4182d0411603801d6111901c200140704950005400b0300d07040c28414018001c2460880030130b500c2c0030f03004c14130a800200420f0014401c1c4da04121980e40c642d00103882c0c2c5d581a641c0c1d1000d8000302810409841e00c3c500f0000b00b140038002c072181482103030700c9611011403000603120100b600803d0400561030305002400030400040c80c0100d039810143e84a011201c2e2602070640c0e400e50100c3c05006000038181010b24680c0c1ca00020071042500d414004c0300188200c804a00c244202000104400c550343c050b66515075040c0c82d4044100d007011403a030085c002e01c1282c96000340200407914060043c08500881481030342c2c1a1400c142001c852120a40c3c44a42101099a0030300030300142c0d54071903402060b400c58140ca062102600c000e0002452512080c0c224607003044032044800074080046001080c81151020f000042c80c0d691105c00175034001101c3c000c030b0b1b51300b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 422625764 1250 422624514 422624533
    0x7030303020703020f012d05070f050c0a08070b220b2a1b07060c02130b060f0d0e0613120309020f0a09021201050d020d081309020d09050d0f02 63
    0x640c0240603001d10130b0060b604141045c41a4508603080720a05008031000c01e082c8281c4600c107680c5401504070101e4080c40580b40c600d1025011103030200504082200c00241e040c0151004c0c05a03c2c8813a078001c00075640d4070814200074801c440b040c1c0c2c4e0b180411a6a044400019569204c0340d031502d40d200b039203011156985403030454903086c07441c15041c0d00c440c200710003640c2c00a01c3d402000e545015a56049000044102d114a483d516400c41001d00510580c0c060169072913036400800c0c02c0e4038000204401000c03c01240440c0940c4c1203142050f00701040c981641041c0da005880c031001c01c0d4045400642e100210a6800805400003070142031003400280c171414420380000f41068005003050382c100021001090492000f5407005444c6940460a80400c000c9050040d004003421290b61103130100c039070009542884000d0009084460004081c138080f010304005070f0052850490443d00d6580341120322000d480a04000c8956014280ea0384c10042d02600c0300c2e0604041e40d074000e0002ca003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 422627014 1250 422625764 422625767
    0x103080c12030412020607110312041a0112050c091506181f08090a02060f130810090201030506150d09020f040606030606110109050c01120b030a060c090b0309070303 73
    0x188034891031802805070120054140403020000c50045101c4d40c80c0a0a051142800038101100984030758104594600c3c0391000500010948540040031500340101ea26286000709030075406140c0001038006070400000d56140020109a815004806440f00030804a01700270900d502180c80700411441400c0501003400d03c400a0a0091a401799400c0301d8030800c1c00103251028800c42c900250281d51003036940c8241e1050721103401600c0d803c000c1c114179805034002102e500a80b01d00601030b1402080b62016210390101010042040100787c0f03240c03a00c0c01d01d0650141a842000782e01080c24080420024103142003245c91541180d1409410205000c0900300604206030051383d014040c0003d0120320740c0c951250704020151901c0005800c1c9c80c000d400f61080c01c030070350201c00740d0740b60464287c003298000c126680038100c01d00e00500e040a1402d0b0720b40081c1101e11150f03404d44900c2840340c00b04200d40d8041c00701541c9039140d40b07075666a02d585071521448200c1d5598480d401c602d80800019 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 422628264 1250 422627014 422627017
    0x708010f0e01230102010f091113140c0a02071505041703031512010605090c0d050601050a020307060c120c020c030744031c0c0c03081314070806090106090212010308 73
    0x83c10510022030000008414502591200241036480358215403800203280740144c00c0c02402c2040e80000d00091f421214224448a0001c005d109400c000280c8090b0b407620a11000e805412400700220190503000170050140c2c01a0180440710540ea041c041000e10000050b0b038442c41d0b0040c00c003000d2180d440d05001c8e802940c0141e18001d503403250b802060641d1041030b45442400d030f8110003a110304202c1e1842c001da40020b0031803818000e0410040307241907804000c40b1030b0740d80c10400101c1c500600e0300c011202091840448aa0fa42c0340c000c1480c01e05501040000103140c080301118005502e03410010007820014162501150940d00c00650a0603a0349548125400d08135504408000c40e608050442d0b1200442c031030103c0d1010f103242c212991910880400350828500380080901c02d40e4081c042140180440c0040b2140004440800001d00c4400c2c225012840503180c02c55918640203075120340c240e66010155082c80320224050240b8801d4a41200e803080150450780d20f16181c07600745 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 422629514 1250 422628264 422628329
    0x80f130f05030904020705010207060f020708031302010c241a102015010303020111071e1b09060e0c0f16060b1e0118140f04140708010f0e01 62
    0x140410f03c04080165224030103000b03441d0094002681e110080c0c90040121a4404480d040c3c040c41444104041800f280c10f076540101036103000b404600c030314001038400610505005022500000310040d04902012103a0341c000107020091104a82c50b5100c072050800d00702c042e5400036400071941605501c604003c01e071039080d0644566442550480710382c00d03c820440c15183e0080310600400801d54248106030b022407400009078280011541d030101c5103004080c20b003110124001c41d107010300c24201d2040c03c1d8440380c082e41140f0107694a0340350000d00301e00e2140c42803400311080003a01c5116002c0c2107411210103004442c0c6000c4a03001505000714107100c0a80701c142d550310f45a5081e40b00d0483ca4144845414560524041260001007641c01d8540c00b13034803405000791040181c41e904815100004904640c0e0151079071400f00410700038416003d07980d16140e00b0800b40240690001b030114166400059401e03511070700d51102c655510750a00c20f0081d580f044503030ba80006680348900480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 422630764 1250 422629514 422629523
    0xf070506070e100c031704050f06010b0310060503060315010e060a0501081905040c03050f0102040f05030f0c10030b150904050c0309060705070624050f01170c09120d030903080f130f 80
    0x1003200401c0d440504900c0121000c58041d84020428201c00c2270030804140180003400001d40ba6103041d0025461800f03543c0b00c1c10050100200201d1140d030740610007a03c14070b0049401d000d40790394890580e8007480b029640c05000b21004600031810b5440750b406a442415a44c0071070200140100d10900103100042050f07400c10312401c2e0101c00904103201d5100f1184e001c9002584550078038401e0f13108007040340d00a038840c0d44025441c0308010740c080351400d00381c8400c4402c007001290440042c0c000c1c000600120b0340c003110710100c00d400b2211100240c40540f0040c1c0d82000386a40c0d4900c042c569100031340750b0f081d0a81c40040041d2000b8815002030440b1440b034000070507240c0031504031a01e42504083c699060302e07240807007031195041c10b00120700a00000d10317100549c0f0010482c10070711904054103100010100003100c04291302e13032070302c1c8441d4903414404581444460210041c01000034850450000e9045c10120720007000b20301c0c1081c001c45210129440a40085c3d4905076200c2040c0340c100d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 422632014 1250 422630764 422630777
    0x30c0f0804080c0a1505060103140103020117070e0301020f0c0d0315030b150406121511042903010807090501091a01030c18120c0807120320030f070506070e100c03 72
    0x1300181503268a5075480f03004801c00301c1ca13418000c0014083d00c1c0000b0302d0716100002e580040000d40e900038070182c84d1a610400b0107a1366100d2010458a940200481d00c0d0107600000300c84e514200743d00d008040c1c0c03100e04070541c2e0711801c20b002c0032400d0341c07074021200401c2c0da1001010300100f80fa0710300e02900810000b40c03241c910046480800e0035142e055012042905030540b0f41020700449607a04060b18001305010000f40d80c0d4025006030760702541c0076000c0800c250080300c00d10000a80d01c00781c1d4041d41111090703201c0d81d4410b01135584002034081e451070541494000610544640202486c0b40c1181d1807900c00d00301407000450090050541200c100460503070051548031070611004050241c5014040e00e50700c1504140c410000c4075071206890750300c02a41005001e040c143d40c881440c0d8580390400c6a40c420101880c18120803101c490150300002450161001d4444010400d0701e200e081695890394840106403017011042400680101030308013240001885100402c6026100f420500b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 422633264 1250 422632014 422632033
    0x3070c0b0a090f1211010f1d0109030b04051e0307050c060307050904050907230a0b07030207030804060206071d0f012102160b1303050f031909030e01030c0f0804080c 73
    0x44618580581c0300c00e40e0000020413a0040c45808080a10111002e0034000c1418980b58001030441c200c84103100d180d51803140d4400c605a1160700c0702001035403c20f803500c00b642003a091250f2200d10f510813040e5400030301410b4401c1d004010094610858001c0003078403080320781da001d00855610041961040101c00c010900065446104250082000d000140102801e011420300034180510012600e0120301c0804142651946000c4090f580030070806034440c801d620341a49071900a41004040c00301c0071501041c0e00c1c1d80000c11a201d112540d4030880782c1c41002c00b81c0c2d160030380e00c41022600011943c1d40c00055500442010a15070070151801c1d81151000200304200d0300030348120303120809481030134024080c9100c00b2030341104411444a4203000c45d940c0260280c89140000d81a120303011000640203c442f0a1181505004042c20b010000c02454001d00f680e50f8644046e01003407034500500840c034880d4a1146150507180c80343d5000703880b0b41e199120039403c203055a00f214451010300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 422634514 1250 422633264 422633279
    0x8060103110703090315060806061311030114090c19080910020a02010b0f0901180f2309100b03030d02070f05070f0905070e0603160c0219030b010803070c0b0a09 71
    0xc04241d4020b940d410314003801d5180006c001011010050125414034005220003e400719071607402c020300702c6441c200751002c81907050207858500e410100040c0040000036410503c0c2005502029007241e03002429580d140d0380080f503001c1d038103c001d00c00e0070313010301c041c05507008403062070f04446040d0889101c10b882c840c0c44402e0380e000b10301d4400143d45035074102c0f81c2802c00b21800c500703198049581c0b040301e42c140b01e841c0690302003400140d50b5458941c9421030021403254001c1032100c8044009498000856004004440043d200040248146440410300c039105200301070520100801851802141914130400394010083c00e41da1086640c80c0c203000958108801001000c002c0c44070600545044402c80c1200d40040001d803d0100920000541c1d41d0b48408403584038020b10583e41c4425141e4404640410700d4a0000390801250044200120850510308040f84d1054002020702c0c0c1e00c450019880c0e00076050014a1250352003400d02c10316562001824814802d881c04540d074555820f40f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 422635764 1250 422634514 422634517
    0x1c0b1201050705120105060732030415021614010e0301020d0c02071503110403020103180b0c220b04060c080d02180a05040b010e090601200303220804060806010311 72
    0x25030101048000698211450904e0390031801040d007200c11508006c0c60342c480141c034007407545143c918280240b141070000f406190700c040c4d6002501c000c40f61030301d031145582e4100e8041c810f460000361140307200c000c1a1307403410b071910b600392102488094a0a156200196410b1038500302e00b65041d5000d021310802c5590510998040c903102e54000c245261819046965110313030001a0010035040500d0f044c8041403c000b101c085a80c2840c000542440b80400c40d02c03401c511040040500b40344405001c0911045800360a0000e0800366540001401584080040c100d030300c0b50014851040c001000014060300c0840ca082d4003036018181303400c480805603022a807000c1101c03c0b04211115014040341000390b61341018010940e002c000340c107500c10010342000342c01803440d0f2050310034100094080e485035411110031007042510601840c410b17883d19469800440b00004200015030348500c0341c410f8201d8412050340c000690500d0107040c8003003220765400043c041418151a01e030200c0c2e4005d951030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 422637014 1250 422635764 422635771
    0x220203090a030f02060f01050f180f01090501080f1c020f16060f0305010819020a08030a050903060a060e0f0604060f030b0f060603101815030b0a060b1c0b120105 71
    0x14050080303a110351501414441040030503c0440d4090400c1200d80e104c10251603055901c215015101c584000d000129240b075105444081c6145400c103001051258550701ca0681303410300740c02c2c0034503030301c03818805d0360340c10014000403d69005140c501d81010030203180c030441c0d100703038030543c4c28980120720038600d403140000e11700040f403d0078041080b00b154084203c3c1d650703009614090102e940340c91006552030000c280110888401102c500b000c42d510f110381d402c01824440306603902d0700240328000d01070742c200c4030300d1a000340100c200240c983e050520030101580c950741030040c100d485550814504450080c410760700155285008030325080801c4501d002507105d21070700341640c980103c551440b80000791519000300d02c140280150f03640c03814940002d45131320b400044140b544012858001d0300d404100300c102028002d40c0481070013210804140b081e235060409000246e40c40307010440074401e4411309400c0380d0750008911080b04164200301781c139110007402c0190050480071341a0850314103a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 422638264 1250 422637014 422637031
    0xd030512180705151902030403050606090708041118130219031208040f020306180114040b010b0c10020f191b080d0b120f010b0105030c2a0102070c0f090515220203 72
    0x4501003040ac85d0401c2043d40c82030054034101c044e400c062001900c81c20340900000c003202000500c00070380781c4030710b21070310003d005502c0800b26904101e040c1460000d14040140c2c0907100d03900d800c0c0341c2d188044001c981100d40c0840280c544074241d150450740490080c00c101c4035880341510100260b9010070140b402095607485408482140388110313400c40d0003e08a0f00c100700324200c03c11004c10001d0400034111811904484e40c1c5d5a50140b44900344000030b0001c9140d20310220b24618a00f0925000e055500310b0200c0141c04c6101d40034040e5550031b024091408d9100c40681603900103444980980700c0c2c801e601501284110304000000e9090403408400d04d42c50b40a0035010118017002d000d000c01c20182800c186245080540815495100d41c0307035059401c05a02800c40d02c05801080c50002c040950002107403104a5881c00e1050301c900c5100703c44500e90802004104403800340702c3e05005180a02d041c1c0c007980b1500040c440c044030717035860b00341d43c0400544c2120034440341d6000852065041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 422639514 1250 422638264 422638267
    0x1206091b2d0a0816090f020c0601030b0106110303161b06020a1110021e0306010903020a0b03070e101d2101051603050c030403031a0d03051218070515190203 69
    0x48400e000e620010b503807043c81d580c0d022070703244411070704010040d20076900900004914141034480340300c007910403900140d1180c0b00e03920000040c0801308501c1c5050b541255103a00140d442328a8041e41c0b40401e989001145e20800081088a0b02482c0d0001c8104241030b02e802446200340c0b02d8804a8216850a40100e2030003203014054102c188041406444540401c40c00d0100220b10001d040040f00c7d8106038481001020078071a81c01141d10310011903004020400c0d0b10713203e1010103080e80081d2001004503086984081043c81e01d91203100c58400681d030b401d80902c00c4500902c654101064015411601004134552030b0507003203040425059481001180c1414081500c0580140124190081601c2d00c024000881114022250060741503d000b0828400d14000b0313428210741c162040d580100100240407c040c1c0060180900c0c860f40800030006507501d65481110081a82c2c05218035007088005000700c1c5400034014074a0312036a03011038146003912088071054200a0818030145e0300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 422640764 1250 422639514 422639599
    0x90e072612030f040c0806070c080702040e06090a060e0105060d02010c060609020d091e08121e0711010c020a0b0109020f090307170601060306050d030c03020c100e1206091b 76
    0x170850003400070700502c1c004100c1c0c0d01e03107068004c094610580e00140030b0080060080c081d0340d9950000098441c9082c1951714504004901641d039201001d011611581000c01c40f0300d201c5010322426100e120040c0c0000c030f41c04040e0740111500e120118085502070383e214400f141000162026001038424108009060701003400d01d40071160790042e0a07440c01100d4503010f000504000709880240c402d40380f015007281c03190b403032005d401c941c600303640c1c101c1e0511001005845940540450240300e2100002c01429410440c100c0e1245048400a400403049400410261403a5801001180420040e06d0700700f0390540f000030309200c269400f0316420711809482d2460100306004541c01004d10342800c00529141502041480c111080040c091010035101e000901d4000d00903442e1060b801003c0c5e0700280022071703014060b16a1414114000c8412404240a541000403050b0081d440c0c40c00404400c69000fa488508800900c1c0c01904103807c4842040200c400304a54a1460075070303903c1d518080d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 422642014 1250 422640764 422640773
    0x120715090c2702040f06180b0d020921061504090813032f040f02070b0901050106020609120702090403210b03100b010c0b0c22090e072612030f04 64
    0xa5002c1c10b450101481040300f00140310300300d14408201c900714240b220950750b0340406165100e8055110603840307140065a07107204000c60740148000740b000c50301c0642c006500d105c0c10340d000c00d0841c0000c07215071003100400c002c2c081d1861090003c4100600200f403510300c681c2c448025070080c01d41e4503d00030407010113108110044e60300c44c444d0b400346044d00b50814403020f000300000c450b104c0d44034000c55540760811048260b640403552001c1e04200c0c007005908202044a00030f107002d2003050018060400400c041560104a000c840004c00c4603541c148069902080034000028200b1020701180c100d000000c9007000d1954400b4080c62180041e81080c5841070500701441002004034185ca0004440c040b0781c0c010412051103900486241070954804580c8101407045032910703483d10f01104021207111589070410300c250b40f05014140006891814410f03903415403030160301c070309010184580140c440e20b00e018101c1600e01608503030001d1040d114140300c5a2055070040c0d030480b1020100410300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 422643264 1250 422642014 422642069
    0x270b030a06050a1a061e16030f0809071202040f02090d0506010303080106090e0106080a0f0e0a06152105010902040c08011401020a030e01030209030a050105070507020111120715090c 80
    0x132901091002d002c0c1d00c1800011a10300c00d41c8211a200440b14407070001814041060f07d82c082c402c2c500900c440ca040d400d001c1c0800086030403a0002501c000005580c031200810144100c80c118081c20003c925150f003000040e0581c1c0841c00711460382403110201564402904550550240c0045e00c1c980d415810000c161200580011003400b2003640100b000c403081c0c20842d4115040341ca880d60950f15154040d40141008600181601d0b00341800c0c1c254900001c52040c810901c502c200b0440044041100700b1500c0b104e107e00208075801312000c820112148465041c614826000043d420b18540d0001c1c3c01c03a012080e01d000081d1000c00103120050841d40b804070700c284d00340001e091208203540d00900c0b00783c403807880e941015004031740000a501e0070001c3c3d0041c03a0740000240b02c039140c0310784000c0c140d412144060380051011203030b1034410800400d41c03a00c1d50500900340e6140440540b5006205404032000c4c110103651403c071100425000142c84000d807002a42c804803424000d00c4030f1085 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 422644514 1250 422643264 422643281
    0x20310090b01050906070f021009150e03030702010c0f0b09030304030e03030c1b0d02060c1006150c0201081003020607060f0b03030c0a170f0310050a090501270b030a06050a 76
    0x9007460701c0c00c801d01c01d80c0c0000669601d020100c03845507440c1d581d40f4125190a40f00d00009400c0400c8124491074203400801200a548144509070f50400d440c80c021501d00c0080910140c064104210040165100b06200c11003240160006618040560388421040c00e0840c1c1c2460640c0000c0103000802d503011030300307150034142100114200309030001d23100e0725023074409a41c1081400341c03d00e8640f640c413101541216560001c3c101505d5141e0101541c1d201e210001400941c0d40c607158003c20800c020f00074028407260700e0307074414a500f1a00c1c0c1c015204003001810020107442407007400001a07440e600203101c52407185402083c1c0c41925000c8005880d0255140c521980050007c0611844001a00d04255400c112907031060764409901103190303c600703078002d141d4130400402c02c00d4810703250b2401c40460f001034501c030f480d00d540c0352405c80440e4402e0241c1c414515003808a01c00c100c43c00580c50405642d0080300044c0c0440c110b001a140481c070640031602640c07180e0070440360504a1051244 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 422645764 1250 422644514 422644529
    0x5010e0f061b0705100908010b1206040b07120903050909010e150108060d0501060807031e11010302030601030f050721051302090a090506010e04140c03060114060706050406020310 79
    0xc0340844800164a40c0152520008040c90101c684140820204000c000401000d0040d0301c0060700d0000041061096000340c0e003556003050104110f07410b0030840501500b43c1903000d81901d440c2c40d44d0700071b5610130181012007008102000c3c040d1281c0d01d442116580762294941c40d603150191380500c103807840d05034001780008110300300704044000040070b0518008401d10704250b00d07a45120000300142d0151f0030151896180c034001013031404000800030b0642e40140600f51208000358020b082d40120701c41d00030220b102c001c0c1040f00342c1d400fa402a6400607014100860362154800000c81201ca00b2281c1d100000c4003281c113180c2c59421045c0420075400c0c004810301c05485c1000402d60086c0300383e03000034041c103024000984495110b42c44001c506030700805507985940e403001c818002c1441540e040d9201c0c04100c40c01d800540b4001601142c010014024094036840d01455049501c0031803000c40c0c205004202d41000500244501442507115400c010b0300d13418116100074000d5144d030061700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 422647014 1250 422645764 422645779
    0x30d060801051f090e250315020901020714030327040605040b0604031b21120c020312030a0e0313320d021c0f030e040c08060405090309130605010e 65
    0x20350340e1000b11000c0c403c0c0c038100341e13002c90311548500c030107403034030b0390258080142070300d01c8286218a0441e4640002201e0050032400f000c43c4010703460008078802c0b1415540541c0c0100420099450b98a03401c11300080001c1c1524109110b1118840c00320440041c00c007610619400c4540c02842c0500c12040584419101007101e0400400411221302c51800040c001040591841c0b5502080c803100385c0241c801c260703600e181108800c84020000071901c0c003c440d2000507400b10528a4032501045506580040c010b00d60200c1d0034003004d00030703400030304000d4059442e402e1000041e00b0410050004101100342613001d00e24160700e03000003c2e14800c3e01c5d410074000501e0b0494000b040da001c0c1101e10b008543e180356080c1e1500c00a1084400708042c0b00203055000305c500d062000b50248254450701030f0700c481c090440b00038100000c5804a01d0320b20003088014001c2409810310783c3c82582c0c04890007003100d18003100c0350005a080c1106d0190071a88070340312242070001e540d204404004030041500c209 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 422648264 1250 422647014 422647051
    0x1225020f07150503011e170a0c0603050411040507030f02041409010503211c110a030501090615030209060702090c030703380a1e0504050f060904081b030d06080105 72
    0x10032501c030605c10807182103510300c0e2a09107100700200700310061800151310007500415040d000c1e01c448074903005841030202714400050084c000d001d9a4843c4e0b074460307105d14410304a8000c1000400d0054903c504059840d10b0920280d6510310050010781401d00010f0001c82d441d00030405030350016000140a6000542810602c28041401810b007603007074a0465100e0540c40303500380304e41c4450030b4000945400d115882c045840240c004115142407070b601808036070b81350f600c01402d035200d51103007141481c0f00103611030513030b80300364042e01e280f51004280d20b150141c6a0001900000c054840466136540041070040712030301445110000260074003105003046980701da03540e0ba00d0420404c00c0c0c0c59400f00002455550f250841d48015100d0900940e0a02c042046081c041d03085600413103001d54a003801107141c5d2042d050b000c9100c0c1070003c1400c11030723680f513681d090720325005102d003854100782900000b000b145003400941307082075412100145043ca04000503007942c1000c0e003224054080c84805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 422649514 1250 422648264 422648267
    0x80705100807081905070504050316030b070c0218040c051e0a06210e010b100215010b09061201030f1208040b0c03180a080406110d051225020f0715 65
    0x1c80c0c0e205905041ca4526551081c00141d00394400c001c25035091441d100c108040580c0182c00342c02580c9055007160b1440004030b090100e01e00d894000600b103c1035035400a14928803410412444501c00340096030041142c0c01d200c294a20261401c4400405c0e01000f805181822042d202070400700c00405010301380c2140118107089002e004440800400840c44e6070403540d082d4000e0301200c0901b1003082010380407003080e80200f100410052080e80b0603081d15603980d00c0000d6811440403808880c0e0002c0e4a0100ba03540c05074002d94020760010400d000180d00e107900441c1c001d00940c0900e80600d01d0880c0e41c582024802c0b400c1c43d800040c0704595040c000801d05200d441c5900010070340b0847e03980e4662889000075048010140c0105104003203000d401c005881010f0000ca0368952a0140c44c0305030316104544410031400107400040040c03000ba44c4003581e1018554220110140440306070342150803120300250740c4450130015900405001d0340003101000f550000780406007041030000300c01d000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 422650764 1250 422649514 422649527
    0x601090b0306011b0506090a050d0203040e0c0313080403060501050f1807031a0d0318080c240d050f060a060905010c0b091905060708060402040302060703030f0605041508070510 78
    0x640d07410403d544c60752404083c00c0036040c1c000746404c0012680c452524410250395400d40310411105402918070b8010ba05000002740c40c2030781c1c9144d60000c00d030f0342d840715680c002d42c00040003150040c0808001c000030070b080310000e2028500a030000300780c0d503040c40f045c000180c200c04002c9001d41c03011125200444a0a030741c045d00100135140204514081c03803c9803894144412070541c0c404005640007081580013810310b5a0b10611071890000c1e150307070350b0f005919841c240d103a940d000040d89600d001e02e141501184030341001100c14460609503149010000c031403040315401904010082401854902002e45800800082c03600c0000581080002490040c0080000b0a0103a8a5001c107001035005d1050400380d0151040c45031440c41d5070708100e0b80c1c44506580754004100e0402c0400c3d030700d003081c0c0200d9094035000381c01c4c14039080c03640d80c0480043c20655071060300d440d03460001244990b180c0c00344d416010071204a0300702841c10060f0131400c00c01c107644a03900c50320381d10070921a5141c0001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 422652014 1250 422650764 422650771
    0x70c02062703030f0c0610030f0b0c04080601060503010513050108030d02070f120e09010e090a02010c05100f020d1116081303050319031b0801091d030d050403080601090b03 76
    0xd6151180200640c0c0c410048540d00c0580d410f00021426103100704180300949610922170301100c04035161021000540c60090002401c0443d002c0d010501040c1d0000c489900525140006d0b40f800340d683e480303d400c3c902c0a81101d80091000801000b03c1e2901c50302d00d0b0545543c512040159500d440c100030760741d101c0c445490700495004034904007840440341c50b410441e80c00920300040e121900100410110034240c01c684521310100000c034036103040e129403e21034108040140000b011540064810903003094080303440c0d00c00c0310902c120001090240c45000c00e444000962142400c141c0300b010385003e80c500404205090160024554803900e0341c41c40590042015603507051040c505000c40e0002d500301510074400003408903e1554041c072a4802041c032503600b0096004140b4041202880641c511000601d42c800140120035181d031001100c90342e16811000c04200218095045800c800c601c07140441d0f1722030400c4241a000542c0070b51040742482d21a05050030601410103500025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 422653264 1250 422652014 422652037
    0x402010e1021090602040e1b0f070303021308011e0c18030f0f0206071a0601050c0604410c010201061a0c070e090a06110c0c09060a0909080a0305070c0206 68
    0x10089002d040301960110300c05a030030600075541d442e2a55150007440713005490078140c40310b00d90407103155950440c2c00d540f0041001c1814610381401500c04401070f40007040f080d84554540c1100052440c407d1058850300021403a0000300070100d040e04204a661200c921010700c85415015400c080e030105010098940c80281410201a02d04001e0581c44501000075084580001c0c010188052545a554500100c0d520481030b03681c0c0b140116000c0c0910719004050b0741c00440840c00049007507403031503c50000e050600702070040d1186001c0038100850140c003000c0080103070009520800340b01c8011240303001e0009120503803034070028200784100c070b91216030704580215070807100f400c00703016000040008905018003420300c0703040369459102c0c04400b01c030042d18100103008a04103810544601c650043d0180000c0491402440a000002460749510100c0f642c00810703025054442c0c265842d010341a080d8a504040c08040d04543c1c01034041c0c028001c4482e035010050340c0e40000c03980d4008a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 422654514 1250 422653264 422653307
    0x6021e01060f18091205040f050604050d030c110406060e09010e0c040e090c06030a0b12060705040b0a020f0607051b061333051f031106031b0409050402010e10 70
    0x860031800007081c0c0c041004080c03158041e50401c0e500c4d1b11402034015184801005c0c0b00c1c460707031901040114030031071003641c0d0030500c0d0f0740b0a900030a000e1000e4038203550041c10036121290f4640e001504503142c94000001142d407010b951140303410f007240404d01501d01881804154200701c4030810150107144640800c9030000000140218014002982e00d14405400a5200c0c140041140090000c4024880c000c00c10030b24404a03004000070706a000b40555140c81d80fa0904016010510340d00c006c0340c15065202d1510001d0700d0040400905110701040ea4515803200749543d1070b00748104841c21180040c1e031258050000d1903292a680840c5075910601c11980b400c031083c07007100c41030b1a042c040250308540f1501d11740342103480e070403940c030428080d1101c00004100c90364444107400741c4c0c0000740a6080e400c0055584d4107200d002107030401640001c095801580003100d080950081d00040c155a845005200c115604403980f0349280c1e9085031045803110440b44000c0804200300385521202a5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 422655764 1250 422654514 422654549
    0x100506090d0501050103030509090717070e1504090b0f0901180f0b030610082a06030a0b060c0f0d0309020306070e27010509060f090112030e0a06021e01060f 69
    0x494000d4441000c2e40040240940e6075a410054104c2e0091049207000e102028002804a8895500b02c00c5c51180c1120107103054440040881c0c6031558a2544c980264a882040160100b43c1000e84010070201e2008541d40520f84184902d0b9148500b219014051140041c4003a20740b002000d0fa04c8800703079030006409891118441c014200003203a158160107080c1c10b20a44000c110911815244020211071000e030686486441b0600000040b01d4040d004944000c0580b0b4440d00460700107000076408901e0407800800141d840d40006103c0c0364070340c0010b06007900c1c43c20510a07495450040d0030100a40441ea40200e80c580380c000b0500c0f4104942d450303080704583d40d0490554800642062800340c025a01c0c1e00c0106c8401003801414816030b45180081c0503858100300700e801306080a0b044074126443c00600c801c0862665604405001c5030140640d0961510503058006008540c0103080c2200e40714401a2002007050710103100fa410003409200e140d5076800c80000b15050050030840b02c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 422657014 1250 422655764 422655769
    0x30a020d1515080c12060c04170c041b080606040b040b0a0228210507031101060902072a080c12100504050a0510090314070201050c07230910050609 65
    0x861508100001d8450300c00843c100a0000c0e01001c0f0308019903070901518165205969920801c4a04102922003000140210811180c40c1032070142554100daa004852000140c1903407444010700580121203280b140301207510000d91038100e00242e0f02c1528080c00e01c00380d0b140710f106a00810740da2040005042920b03070704c20899180288010030f10303a0001201500410003e0504240c1a100302200b015802c820f00030341e06808401441d2611034070b00e450110758061340d11840c03105040e51255a11040041d207001c1d02c0c0020010948241100c4000d0b03001c1e060340102050ba0450100701344001c581060013500c50016020412007002c4500e41758107144090850700c8c01c210f46003441c201a0a02d400d0204110000800e10300161103030b802d55086449905d41101221032400340540001c2e006140078850581c00700090422131700614240746054010703012030745040416400300c594843ca844d4044c4180b0403d49149221070350840e020b241d241064605101940981e0040314030482c00002d007a03540381e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 422658264 1250 422657014 422657021
    0x1305030c010f150602030405100806011b0615090209330d0606020607080f0a050c040b13150e40060e0a0501030f030804060e030f0405040b030a020d15 66
    0x104040080c49403000c4207000b04050400761881c150803000402c030200303419001105a0341505d10140c84c40d21100c103403e2003103551107006080c1e0b0f0305100f481142a000042c0102900c00c2c01401a10041103134408145055455070807607100803026881409010015039602c050204a00222900e03081841010512a806903030501c1c25031849000c000b84165501045400c580b04480407502503072035645d251030003901c14080c11104a81c1c94030600000498101d565440940c10002c0130212030300b050f469a0110510f907121800d440c04038505000100700c148483c0b03145c617991b9441e9203000c00b5041000c0700444c0380702d8032030101e2082544400700a01102c660140308040e40100c2c0d800f0362510f08500d082c51000030513403030081c668420022800203103809141d0107814101c03071b84441c1100303102c00e094078121151400680110b61940d15201d070000403000810207400014031205102c0d94851a020030030089030f04010500e8040e8100c0910580503a8500a441a1700ca812140c1c1d1020003120458a4005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 422659514 1250 422658264 422658277
    0x1009080904090c0905010f030819090e07031b0e01170a0e031b010606090f0b07021203030a0e0c0d03080f090a02040c050307121a10030603020414100617130503 70
    0x840e01c0d02c94142c0a100c8010200e004071803041108000c940d80342c3d02d03075207a082032900024080d01e40811820701c1526103206044100350041c9448821507841d50703030101c50718400740ca40f00000ac2e158092020350500f12800349050840314100780380340300410000a4102c41d0003211102a041c1c110b000038141c044207400c00a089050380003540ea40340c00429482211000d84003070314000b90300e0040c0c003248460198a5950940f000f40c1b501800d941d107003c440b039015600c405012a0022010b84c03641d40c1007101000a9070069000c860f01058292910420ba840c000494140380d1046403214001c074042030b0088101a045041141c8001050f5a00d0030303028544100450025009450009562400c90f407000196000e5003095983c802500c0c2001d0014042da41c8070b80c47d268140c2420703842c840d620314041e031100f002405241400f090f080d80c0c0341c000504070f8080341c0d900c004403058401000a004208602d401c00b40205c0d0905a840082c072603541141000004c0100040c41d051148140c00d201081050342c3c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 422660764 1250 422659514 422659519
    0x20a0201121d030a1e020601030c030602030a090b0108242401020f030a020303270c060a17090a050105060109360c0e0102010b0604081209060403050604030305061309020310090809 79
    0x5486400d004c00503c105100c2d140101c08900c2807900805441c408039480303048a0b040500c07241001c1c00c648840c0b00175400900000481c42e078400e0880001075026900600070048000a00042e1900010000b2030032801c1000d5140071031000c0070030150929400d00601c500c005c0c02d6011092070a6000141d15105a504084c00740d0310010070720014199000000f14460000c4e140c00003445000ca604100c0e06090603085d904260b000354480607241e0a00030050200c0007458a030003515040040a1281c0825058601100035000561a582805824040c09802c48400c2c030348100b44c01e14240b03600e100d9040250f06000020341d03401070402c4103a002000c2070114101054108081c4112107005000c2240f041031403800740d400c000d0720420500d811004c4d201210140006080190091020145241e00c807021007607000324240310100100e481000202e220302d101c0c1e00c0019850419a08003c092800315404807103050404182000507200842c078641d01484040d40412454068a40118103000b100422038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 422661870 1106 422660764 422660767
    0xb1e0405160e190e12040603020705010b090f0a090203030d05070c020111060c120604060e01030f1704060c030e0d0506130b0c0310050111030f070303091101020a0201121d03 76
    0x4461101019074130304402c034170300b6244141c026030461000640e010801e581000800d02c10007020410031141401a4540705c0b0604c0074252006001e203032400e40702c00104045441c10003d813118039040560610892415000040005d000381344261300081c0d410072480302c0301c580803682c40d0141a03038650952408a83e29064031001001405003034200755075420000314501620321090185104005051801c0780e036081c40908880c1840c00c6100c1850100420095a900b180321041202d51508214007480d00794000290007444029015259029800400044000980d14070890500c070b2001210140c6071400c1c4541a40800ca6560f5081940c0700c1e07080c00598000d01d8080002800082168549003880c41c3d015003c1e0000d070811004a41c55a5000c3c04015141401303440b084005e20003040c2045040d00024010300b0640c2c0078207a01c13565858120381300c20b10001000c601415070070480c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 422482014 422661870 := by
  have h0 := BRFrame.cov_init 422482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 422482014 ≤ n) (h2 : n < 422661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
