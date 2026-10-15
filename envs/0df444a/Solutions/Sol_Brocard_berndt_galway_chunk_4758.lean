-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4758
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:38:23.972721+00:00
-- url     : https://prove2.me/submissions/2289c9d4-5089-4c1b-9ba6-478dd41c1414

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 855575539 ≤ n < 855755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 855576789 1250 855575539 855575561
    0x20f0604030306050f12100504110a090f05060f06030708060102160602060609010b0f0a050f0c0d17070f0f03182910060c02100332090f03091c06 64
    0xa80e9083c00c0c801c0d402e215480440c808800ea44c90307040884218041a42d90804a51845145e5202e000140400c0040b03056419200b40c05000b050115031180e131910040e0071400c003080c80303c0e480c0c1000981c1910f040c1030580440308026001d640366480e0020100e403e840c00400590541c42010f188017241025524000c0007468541d011704414104031040040b01ca1060b440785080b120180300d07103840e003e45d941c00c85188903c0c0f0b04046a0750b400d071500642050040100c0410180070724607220540310740110f0102d10040107081b501ca8143e0782c1d20b6003500c42440c1800900c00280c48103041907003050082e0300000c810034074101c0e44c0c12000e00d5075030382011030390008080180040072a0340807164006070340051034124403d400c1d202d00190030120014084c4079091406481078028942c140340e100d0099001141d85102600080091904910450b000307202144e030700054021a42c00040040c000031950070024501d10019505e01180a410040c031105544100c190203030201c890a070020b0154810140a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 855578039 1250 855576789 855576791
    0x1c0809100e0604090b130c30060e0115020f03180607200109090536010501090c0e041503140304050d060e1203090d12110706051603060f090507020f06040303 69
    0x40304403800e00c400500506c00200b451407c3c007150324440d54010102c0f007030052580f42000250250303180c2c8080454045007148000c280b4212000c11080200c1844605840004200b03030700508814400b269220305102d4000801c0d0001e0285840c00101540103000301c038001021a403e20f000740d01c034141400180204070102c044c1000515100e5604403866000030600000300f0455072401034070320b40301000e400f40c1c4000e4141c1d0356644082482014603403106c0304a1100c3c020021580c40c1d281602c0109809403590011801c2c40c0005110761500b4060b0304120039076400e84c1c0b0040c52540d6640c16100c048015814814007041c00082002c1e250001e1210300c450003044007180300001405110300b4554201c0120710183c40400400940d15800280c0078820b1985241c40310f41320310554656001443c8803903811183d08400123000c1d060000035040305006540c8808806503040e1001016802c07510705129a426040c40a10708101003070855004581c04032030740c01500d02c4400d146001504016048030114042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 855579289 1250 855578039 855578051
    0x8030702060601120c021903090305060c0c010614060d09021201090b10090e19020d020901090507110d0c11211b06030f0a0c0909050907051c0809100e060409 69
    0x10340c0e0042114800c40140c090030085c00684004c001e4a07500d0b1600341c03900d10811000c00b013040602c0788040304011600b00d0291842030800d80ba0a52641c1c1c002c5910faa001d44c00c0c94000729403201801d001d05c565000042c061803074000080721660152101e92801c1e6444a00004491b111a0003030090111051042454061500e407400ca20004103d036a000340304041e150500348801100c0004011504070709801e4151585d04c0c451000602c6c0f9030002070000d4110764040f00020342000300382c21041c0645000e40b1200e0100030180406555560040910710024000140d200e01040c414032800b808070501030450716007036001a4a2070b894101000d0160ba03164801220034202a461070a203581c1c0402c100c3e0550b2450910034074850344c080d000742108100541d80c00150480e1802103c2e0314006060004060015181003203c1545038115449014041d560f8100d02403840342c041c10345d00c5901c950108060b801c0c90401000d10010100a001180c01d000b541d181caa0400ea5601001c1c0008200c101d40c04256 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 855580539 1250 855579289 855579301
    0x140a031b050307090c020a0311010b040603060c200606010c14030703020a0515010f050405060f030d0f0f050f07120c0609121b020a06260f061203120105010f0c0803070206 75
    0x5000544c1e80300c20540d0b46488010410554007181580d81150140750842880b80c0142c0c001d40100302c00c1806580c4189031020000800c1115000f4403c1540c480c0c07151b9441040d41d4003011200700004d510200240c02c1900012110360041814142c1e0034002c0c44080318620503c681c05203190f011860590140c0d01800150007009410818084143c2c01e004014003e540342031f000c0c1b0b0000505000b114880c0e910366000400700d84922145000310340300102180c1407102130b10006800072a4446440e80060708090420a039903009030222281105030381041407511129031120f003040035403107001c0010030203403000c4100450a02c0c050214078500070358060603444580c20700275045180d403040705082d9284148111002da82d80d0b8480038203d44050904003a0403811564900d031440c0102c0020311843c51075400d01140c2003201c40320f240f0811068850703555000100400315503c1c0285031800703103810854130041c040ea501ca0101044074104504020400044650f2143c500760070484200005920160800103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 855581789 1250 855580539 855580543
    0x12061214030c0d260f0420130207030201060803040b0309100e0c09040c0915051002011401062601091e06150c1a090708061e01140a031b0503 62
    0x280a0306420000e41c60141c4400c1e80a8852000a040d1410f100a5010000003140310802044401c1c01c0c2140450b000d243c500341e00d80c816a800d540c15954007541032501000c0005518802d404810010700031815220080c600401030341c08001304500319500d9403000a080c080400c0644064030454081903103070314020030154904035031501070303004031400c142c071402e11143c001c6080f84104405803103a846035501c82c00e1070408e0440c1c80d488011183d10344500c419071180d0314071050041d580304035907a080302e048c1e90800301d00303039121303914074480b000541d00040145074003408403541000c1d5040c81ba80001200402680c000600036441084003545848400312880340e2200200070f58501520104617460501819484201068030340c681813088807a03002c8280444201c041c00e0f848000c1078040c03028a44110081e4407000d480c4580c070300c10b108070000f0403200da1504040c109a948860590080340c0c0c0380c0104641c00407401141c66030044200740f00400868080002e01825400280e03849089515240c1854 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 855583039 1250 855581789 855581813
    0x307020a0b150918011b0e0f0409030e0d0f170c010b15041a07050a0305040503120c03091e03060901050717040b0604050705040801020a090321080109020307120612 72
    0xb440d039660708000301243c1c0d81c0d001070a410100e215048403011009202d954010703d490141013081b0011842400792480d8400e0b030117290071201751080c00c2d034405100140b10646241190050102d0315040068149050003041e03030301420702031880007200003059204e1122800c101c01c007018007058006411244120309000380c2076035090640c6c0b466543d800540002d00d003801103015071510300090001c2505a0641c44081d1003002e80c001041d611b642801c2d18010b04140d0040c0314160090185003100d00018a040059441644480000d0b5240020007400c104105280d01c06004c0d0442004000300e4140d00c04102c03491003900d101c3c00024060401e42c20181010319a0500c0203081080b242c1040001503044002580103c400e03240817806454469044d98039010300c2d0814006507201142d04080190b000686d002180e026030503e415403105810031303800c410184038803035001c41d10180041184088030303802541d22520b140341c00c44007010021340300e03000e4074025484582c145030580400310078000809086 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 855584289 1250 855583039 855583051
    0x3040c03060c2d0c1e050606010504060203040e0601121404020f030a0302070e25080106180311130f020406050705010c0315030b04020a0e25030506330307020a0b 71
    0x1218030b051250a8040409900c60100c420f00c0112060307904100d40961120000164040241088051070700440901c0540e001ca05984604c07640000c00c0c0f095000b030086030b0a5626a80c055890305042103104004640b0150095040107041c11400b981000548208400c20a201c410081d00d8100390042042030302106020030b109070401c4114000107500021300e10110303031850303135564403541e00d0388500900c40003804000d4031154480b000d81c0c20700b550b001e00b4060690750151144403591000000609440308039000c01040689009005000303440c140d40007054401002c1d0780410406c0002201c84140e070002d500440c0414404120381701000400e0140e00030fa0050341c9020001c0404246c0d0f0700d06248807500c409402d14a210002c00c0640d114500c00e00050202a0300c0d61a40b800d003c0003440400e030481c0b8246442040d0750076902c1040d84240200d601559004140b100c0051500004000c10420b00d0440746140509000c00782840d031422020303501c15803003138000e05529074141c1450040d00344001c00b8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 855585539 1250 855584289 855584297
    0xd080601051218060c0403140a0b0c0d06080f010b1311030412020a0534141302040315060512121905090a080c120c03060a09050a0803040c03060c 64
    0x8010699074048140e580002641848142c5901d51421405150240c10041100d42c041e180804c94078546180040045070f200c2d000100102d2008035069403180c0c07448100a2100e1846400308103200250b60180c90310b502103540004607665a8560540740600c201315809099455070084009441c1c15042040c0303100d1960421700042e4442140b0000d0744c480108014020390b00448510204d91081146c0364080364020120703070030080c02590010790794007103080d003080e001c4100c0c410b103402d60044900e04040350b0021030b40040d0031003c8010080401080c0075200c5007160309002c00800b0803e00040b21b02c1c4143c0d490b80025180c1c0c101303028450f5200400030802101e91010003291142e00d400f20444110140340c0c05203811a050440d400c891510843c4207989c1c4c4801440008601100c0201d07080720494000c85ea140c20440011240c1612019880707141681a04403000082d010f2131103411130301442c1d20441c26541310388856038802001d50020340e403e442c205504002032080120520031103a011b550343c20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 855586789 1250 855585539 855585541
    0x120a030809010c081506161a0f07050c072702030f0f060a030503041202010516030306090516080c030601050c061807090902091503100f1e1e051005041803020d08 71
    0x400e05c2240e0151041c0d50003407000007020a04405000080c08205070b0158074441d000b040034440c80841d89082c0c80d0000e603210000086180140900704841c900689040034050a91a02d407619241c414400f8140c2d80407160038034103641200c550320055102c0c00085814441c0390074088816165580d00904990042a80400038404180004280c4044920304617404c9415441c5100480300c90042440101200b00030024400402d50103030000026903c03044800c01c45a51110840b4501400940100c000701d103180e0003280201104200a583c4a00181084d0b841c10000403581c0d803400d5011901d4441200421403102620b00c42802180b0042c641c0340002d100100c038940005200f02c07006080310b2940c1e001c0910403080384c1c405000c184604070150704100310b41151083c2d90000b400c040e044c035485080c0543e40102c0809081d01c10f005112802c03132440c81100f03401e94241c60080c58090110b070700c400f1503600e000074035940303038061f074038440d9011a0b01c1e4585040910300a460305071940f60b00c81c14094004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 855588039 1250 855586789 855586801
    0xf07080d09050d060b04111914210c070f12020c1f0807030b12010b040b06040e241e1e010806010c06090c17100204060e0d02120a030809010c08 63
    0x44010382080b071304150001620041080024000c3c4107854000480000c0440d1140100f000f400201000c01d8140d1200306451664066040c031030302c40d2605500381c01814072030720709000846030700e038035400950a40300e1032500c0b05588820917145441ca00c00c50f0081410711b10020102d034107000d40c21002c4015035100c2a50400111001c1c40c2d13906140b540c104003d1144c0c0000c40301032098005699050300500151240380c42034481c20701800c1855030050242d07044c04480c46050501c04200d40031541d0b0144e0502054841d0f588045c0b00320004e11024000da000c104540e501d581d116034929aa40c5c000241030107002c4c03200d07010702c051070851002c00701410341d20300b42a001c641d80001c445030388a6001d18106800000301d1034854000e003c40700c4040c0964607044804204841a00750a480203805901100d00c89a03285035403805030301c11401808002006041c00ca402d9017852840040c1c002d100400d01c50054580c0b030866840c1c400c0000c015070000b10b000703041c48600e407000c2c400e02d100b001c0249849819448c0034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 855589289 1250 855588039 855588049
    0x141c0c08040e04110a030510060f05060d050c0f120402010e0603070e060309120309030301050a23061e0307031b031a13110715050606250507080f07080d0905 69
    0x707446140382014100c400681000140482c5424090000f052100b110343c80381442039403410341550004846282000100d4403482c000001d4003114802805103140405154039440a85005844500300340014080c0c15000005000505402440380b09c445001e0301d07003400018031324161a24804e00039031080080c0107145a03c007400400c5540b040e501e2036501d841e982c000f64038000c0f4034201c2e548500404000c3c415000c1000c4001c0d81200c00403104603450507101c0707441015210282c80403030b0482850640c00c15140c2010300c082c2c201e0603006504070160b0190043c124401e030740100d1f690f4002a50710f43e56400b180d115828011100402da00e0b0800580718540242140800e5046a0900c2040301c200703e060064034603004200c0c40c80d041c442107a1251503e1030002c2000000d003d0045035107042030005011800d12009848080310913008544030032448040c080080302c2d00e41e10549042c0240303100414040d00810001c030031150800000c006032450b10011a003440c400c4800d45003000420841005203560b2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 855590539 1250 855589289 855589297
    0x50c03040605180114010e0907080706031109040603120801090c050702090a06030f033506011107050618041811060d06080a141b0a060c050a141c0c08 66
    0xc81a80040c1540f030707106600d01e501400090a0120f503003805449440c1c40100c0341e050b4103e909941042c0120b07100c40c5645a160045406800003640c812801084000d209810401d0740003081c600151411a81d400861b050b14000e8009950b2000010351407000326520142250060142d020208001c441500c4010300501c81c030311000e48603188a0300800d6400c4103030f6000500031603105018150400040c0b502420083c0940c95241c00350305815007401e40f09682e414601c5001741600d81c401141d035255001554a121400603240f464400c041c070224440c0c51364401804011031055020500700380c00e00c104029140d0841d0400490032040032501e0010745c1d10401c960903440c00310391190702c9810045004005000e036070720840191081c034080e001400070503110740481652402c1954148030820400082c0180f00d0320b14150000001c8900300071745845071000701180d0344200300342e4401c0a11502e50700d2690340d8410380f0b01d4107900994051020845030620b00356080748113003454020f40d01e9a450703041603801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 855591789 1250 855590539 855590543
    0x251b201918020a0905030708071502030406020a0308040f14010617030f0d05091f0b011b03200114040503041508190c1209060b010201271104020910050309060109050c0304 75
    0x9000314030344800c0c901880c811300c007500006d02100c0c056940c032540c450348da18032481060000390300d569008035418400300072101070f036050350002c0c152032541c1d56045807101d400030300560701842060662000103600d5044080018004000410350a00b40841d00880200323004254049038030402c40001c0c801607000584413140c07500c0800007003e1b0b843e0362115092061010059058100b80004040300c41c01c13560040702c000303800781da0340800c02c0c4210303007062583e0141d0140a00070840c20140200025410802c2c200c110035003000100d013512902c8400750050100b910100d03115000440c05000c03c00348840808d1001001d85401d054a04200c80c0030b0b1802021401407880c1c06803140c4520005500a1804007130030400b0340070030841342c0414240a0014100a03078018015400c0203445104100345c00c010386011442c401c00c14111030000d40d2003900c504030707109107140c20540a200c03000090b51100b9104541510035124150b1764a402d0310400d041c50341c160003a40a0910b003800b804807039110300065076403280d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 855593039 1250 855591789 855591791
    0x20102041d070e150304060612050c0d031b03020618030405101805060a0806091510030e160b070b06040908040b1309061706251b201918 60
    0x911074000841d0100c01101d01a508030804204c0d43d580780384104020b5110328012031003004400d0321220740c0c1104444458000d0010383c4551082e6000d0f20780b0441440d1042e209003404524544265100078000600c48410b40158001c4030401041010461484001c1c20005010f18580340c1070100003a021758001619070200705c045e50a94411480071507440700504070042419489124184000f0702c04002100c4150203078543c2004100c0c800b110524079400d00c0d00c01050078114441d452401c400416a03607610f506140b15800d00118180200b480007000b50041e11105590f400f5a810801c2c03400602a2107140503500e45411200481c2000c02170740c0980301c6800825507039a03006005d808556205800c0207120300c1c42c001001034031400f02c042c0d0500042c070800c159005650780038a011540342c18a203c0c030f01e074401c41c0440040e4251095021280b0381e118411906030340302e03280c0c55405240040f41c0010400320b00235601801586807007645d00b03484560707200e010310382a0705145004e05440602c0011000306 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 855594289 1250 855593039 855593041
    0x102041a070c1e050f01031b053004051b03031e1209010c030b030705090c03180a0609140c0d11060c122512080c070203030706060f06020102041d 64
    0x220801c8060000d18900398003d0100c0381c0b0001c040c1c2058003903c61648a101c860380e00b0040c40d4001d00503400f04400010406800b07040710541916103602280c40369100b20f4080301404c211481d00f074010300502010405250051401d03141c1149440500c0c0750400c0561011203114444e43d40000848244600d244e20810b00c10701c2203140a4041d0150300c4403806409009820080d08860552080c101d0440680c0d052018607554024140c6402e21401102c0c1c00180100001764801c1d2040011500040e4035429031154441e0214031078240030000408030b60301c1e901c5040c038134107210308165420030082d4084060403a4031075400000300085521b40c40180300c59801c5540100d140c0d00e0b2000d030745074840700e0010341c5d01010100000c010b16038000200380075002500c4030611a120360070030184507015404600c101861910880036100402e0082624001001c20003211006890500103042950701c180f4000c04e40c6810402120862002500502c04582c810710042183d51010700e03440407410000340090703101d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 855595539 1250 855594289 855594293
    0x10803030619030209150411041a07030e06070807020406060e01050304060b04060b071a0a0b012001021303060b01080f070e0d0c050d0c14010e0108270f0703020906030102041a07 78
    0x204500e01d500203940036149a081010f030040c110324000000c60112400c02c8020048d05c42c030880c1d801b490094a680c0f0304c40a010040305a80c1c6030041c182c01d4000d041c840c3c3d142d50404001205984908401c0fa040100481e01c2c90444c103050045201412150620150f200e4200000800c60302000b000504180c6e201c141c03000094840768005000351030700740c108a56034200c9040ca140c545441c104c030509101c400380f001512000381880781d900c2002050b50b8144055030541e00c41c0d4811721102202c2d62440d5400c00c0102010611a1010740085101d842d0210300ca82d041d400140601c00c0090200001498000c10020010d92102a6006900d412901d040306080142003006564070b080c0c120a42003070f00b144448040c8480050311808030fa1010341c030500d80002001c01140d031041d406035a139010410701d8001c10300d04400e500c4400c01c0e108510f00c1d40102d403980c072000a131034025001901d000c1c40e041218180700f5070500000e41c07613004905038025407500e49050348160029010031010a81140c1c08600842 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 855596789 1250 855595539 855595579
    0x10804060b0907111009020901050d0c0b18090a06140d060b151911030406050c010f09030806030111030405120a11101b0f021213090203010806040c08060108030306 72
    0x190101d40980440502c0c0360400d40900440c074901c80000083c03080355031100080450b0700401002541c0501640060392820061020b0032850080844003502c5140e00030801c25480400342c103c0395514141a094100d41e481801112100a07004080d2181495018000c9030009002c4611040e42074940c50307445041030800000502c098051642d008051b103240c5450a644071010305142800d0480c003e0315252800401c0d10f0141c000048820250001d010402c10302d4003400240200408441c00840c0c500b010301988403c03601d08000480214000105100ca030f03003024441c030007001c1c0051201510b54202a203c4a0380e070040c0a5a0a110080000d520020300b07206104a035146408601254801d840c1c059604016202c20164003143c2c2d840501d0210b0000d110704070a619050040d0094061440380c030030000e11561202c22216280b40e10200c0c00504564a0700c001c0d0b008143c004050304890500d868401e0040c1c01320f0b0b121f51110380c0854010f1081c3c02c404811240c2001d4101c850145000c01d002540b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 855598039 1250 855596789 855596801
    0xf07020a03151401120f0f140706090b130b03040305120103080a23031302031207080c2e0209040f0c0f0e0a0f030b0414010501290703080601080406 65
    0xd4220211880c000200080e41d40380c80c2225030035400a11208400724030002c80001e0900c02c2c0802c0c05294401d000204983d11140d12815008620752074107074540361115080c1d058115141ca041e90300a640402003540d000b115a40a0004407006920305450301c0a40c08000100e07001c0e6002d00440080030404250094040b40d8160204072151003241d030703490401e010903820002080c00810b40b0003c1e00c403035030007181b200d400400c510080c031542151107840c003100b5090301e4010100d03094410581041c000089460207002118032030364030540e541d0a201c0845040080d010001c5004030f4040609240c07462005c182d404079103042074030068550f500000010040c0c01e180703105a491b1407501c50620111680007c4010100682e40c0358028000111014040c0c1450306102c1d00a100540c0c11050002460001490703400c580203105840c031011200c0b00301405c6802c2a1311008101004500e4581d034010301c2c1c00c1c80014190080007003414a0781e42e4901408007400204101c0c10080488005420456280e0042d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 855599289 1250 855598039 855598043
    0x4090f0e01050907031a07080a09020111030c160b07230a0818030d111c030908031303020607050a0807032409020301140a030c050411210403030c0203031501050f07 72
    0x248010f04100300b005455a980f400103544080e10a07404801e0f06081250302030207482e480c1c1c1c401d03046a8456800e0380042184070341c102c0c1040101a003400c108030741040900250f4540d00d000d408148044001c2d24600d2203594000b0301c001c00248802d0002c528040102c00300000b201302c1c54030034159002070300c03410412803d00042003c0070108a2290f41c0c962003a201c100381c44250101c58514101607000c0c3c40400c010030541001e0b50000000c69400e0f42c42c0780300b050b4006000e00380410003036081d949005407904221000003048100e1590182416410444c05030814130720308000e490100c500000411884008044400b4180c032a100c2102440c0c0302d4402d940c1c00018000b96403030320317512566110065802031058a44a05050223280d50500d40280c281e02100d41c40044041240e16220501006d00040302c0b0703100103050244043d507800c945201c2481c0d013140094800c9022490140380203000c40b490300090704119481031081190000100c442201c00c040242003041d02d41d040500170009500c114000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 855600539 1250 855599289 855599291
    0x120d020c160806100e06130c1403150109121109100503030703030f050c0405011e111603050114010303080f0a020f0c0604050f0c03030a03380a060206010b04090f0e01 73
    0xc0022070034004201d0384d004000016400c031800b6513407400300711413a030161550340e80314146034451401e0f00200e6000824a40302e500304111503880310074000c1d0807900200c510b5406080c41200030855580d002130f5103000341803189400707480d00d40c081d1078120f94501d0188000d40900d107881d01040c1d000700070100d034030b0080400508603580c8002e90701d030040141c9580707070034689401d08010100701c0c851408000d460640b80c042c0e4810143d50509585405042401b4603400107124048030f040d04c41c01801c3c4110018a10a101c0418850b840c600d8014210b88002c0c990060050800d40140006548201d031241c018202d83c40d1000b080e140c0f000c40000078030030081b1403110b48000042d000c04500c80032514511803800f680a81c1c01d06039001d44c2040c0c0b00d102c007054640d41a0010400d80c0a030500a600020b80007582034480140b02240712240c83c0851b03081d540c524080d00c0304500c6403045140ca00c80c90030143c01184007500b03255241c0911045e050040740205a0039a4a4400c00003650045500010b000002c03800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 855601789 1250 855600539 855600583
    0x5040311040f020f07060b030d022a1005070302060a1109040e120a0309020108010e010812071a0703090b09150612010b1c02010824040e01090c03140708120d020c 71
    0xb0340b04060340884e02c100d071b8090800018008a14011401c000403e000d80c0242520b0900c09858500c2c0500d4012015281d1907000d03a400303000e071104ca0300160504006d8a070995a00041d0401030304d0244000e0941000c1c6051110030301e1101014001c0c4c8000f404161004503001005401050812a014480d070b0000100031403241d4035554160400d001c2e82e4000c0e00e40140a0741c80b21218581203600340255a1141c0c0181448120b4014400007031400d80d0007440b6580a100000a07440740062054030300400083d12403240405001000b000341703801c80c0100b030040c0705c056000070812000500042c140c0c0c6c403902d0120a40310044100317412040841c18010684115840102c40d07001603440c44140603030002e4840030025a551040d11082401c0c501000700e80c2d00307030030804000c00015144240c20075041d5520307000200c00085800d1144070107544681d02c40047c0300c8140200c0c600e4101594418603c0b503008103541c0c4061544001281c0e10000b0031000580e030381e203640c2c0c4868600030940c101105c0c0410303a84 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 855603039 1250 855601789 855601807
    0x20a0b0405070f050114041e1701020406080a021204170f070f0615030f2301021c0b0307230a0e0106020c270a150506040906030203011104030305040311040f02 70
    0x42407801c1903d1640e5001c424150700c0b240110380c03c03e40c07010b100c10341c1401040144848229400c920703040300c07030740840da814045c1c0f6080e2590151004442e03900b56a900030900b8001c2a40005640d58060703038001d0210705000b103108800e00440c8018102820f540c082040c0411101d403460200c52145280300b50b043da45980030301c1d01e0f6204910504c2c09a599618218598407110072005900742100d41000c8500700c4482c46807200b550b4020740f403510800c284426000c0c1010000c0a00180c048a4055180c01130480c48281d0004140d40481080ea40304c1d41084c1d009000d61501c4e03800f450003209902c8141540c0305800f00100303000c04500d401080760b00703242c030000069070344d80065a11005241668101034923004a2002007842c41e0914103004070003860f40000e04a221701c0c0d4000d00b0070300e00000d140596142c0e07813800b04400d40d202c1d0301301000351900d603541403066080034010004102034400300c00c0d26140c615100240280102d000c02010440441040161982c580d000046c510315800000c640e650840c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 855604289 1250 855603039 855603043
    0x2c0c0d0e06091005040506010b0307030207121d010f050a120b032d0102030c0a0e01030b120d02061501020a0f060e03042402010501060203030606130b0352020a0b0405 73
    0x100e0b030700b68062042c40340d02d18a00380c0c20f000b954002d541c000c00500c1613901f0f100a03880607800082881041540c240f04050100704400540d11820346d80b601d03105501e1302002e14000180880701c40c4581031001001c0031754003103540a000c440040616280144201d01c44074040b1000d84800d9032030990610a00783d0f20030030071030b094451403814a80a13072003025460724007407500d080c0d000840d00d0301c0b10400c0600100c8a803600504503000e0ba607405140001d80e60340c040b80003542510792a00c2c480c4180e4003034000d8840003501000416007140da01480c00c2000c1c0c0d40c050000f90360f0035513190000c06420901507900e04016090300140c40d118030020a070380d02c0b141c039039554108802101c01c40b1800c880e000b0011020b25801842040d051f200300368040d500c0c580d214400d00403150710000c2c0d070b0308010303094180005840aa07500a540144111400c402d6031880c1604a00f20801102d240300d401c0c00780ca60302c1000200c00c102100180f07418844202410800544400d9040c80322840300582003141010400080200c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 855605539 1250 855604289 855604291
    0x40c090c0c211e1106010f0308070b04080c0625050c120c210901270302040b0d08040e04061b0503160e1306080d020c130b03011b02070e012c0c0d0e06 66
    0x302102ca07560780c0d8044120380401f075488041c200d80c10030407104000c28102e5030f041e0b500a000781601032409106014980c90f0034000c40d00044207400c003142004000134000c289280307400c11450301c6407d01c00510503158030f0300700198481d101c8180c006180f812031141481320940d4203410713412070040188401a81c40007071744240c0309680010b0380e03514030424540000070b0350420032028288a030700d06400c42c0d00b88030050141c00f2105900103096001900001c0307003003000f803000d0404025500c00301e050034540101503403a6030030030702c0380c0e01d10803101c004a06600409503a17005503104504000c6050020701034494203030341c00f00550400c1d800310010310140341c40e41061040795050000c603a020740107010300302d0320703802a001e40590080c1c88200840c00200710f90000c14110000400005407008852080411541044103c0b800b40e007140d482040b022003101c003194010807201000100d1104d282d036000c80341c0c201410742580c5000c2d94101040c0c841c408001a81c07001d0000c0d04003000340041c102c40c080d9850700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 855606789 1250 855605539 855605567
    0x30d02070e011d06010f02010b0301060f030209010b040302100516020414040c090516110c03160e060904080901081b0a03060906080f030f03040812040c090c0c211e 72
    0xc06440001a110f80301c224a000c0312442050860b034135210400119501354540712103104664950740c180310700d66828452007000713000e43c2c5404952280703544180000ba41c0140d01140701e0341002c2c0410809604c1e920740c22034030311410f8035040350b4600c000c3c1d01c00703001d1303c5a45e00042d41151030201e5620408403030340b003128050703405155401d11032a070300d5180d0002d442045a50b203032391078010483c40d680b0b9401240c030001c802e294101910f070401c80c80c9000ca4504800c19480360124060780004204070710240c11040c0d00a1401c2c0c0700110781d072500f5100c19a035441054400c5040240440005e001d12081c980c500303003580101c0e00019076034024000001c010780f00ba8040e02942030310b840710000320100001030800502d04060040d50801111942d0340e42d55410050040d1422442001070345020210b241a0510462080e580d1551071402e0100340400c807200b480290050040451030718000c1190740070000d020210701c01c0f440c40f0150303044ea021103c801c04109a08108518140485030040e0440e06d095a02e017 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 855608039 1250 855606789 855606809
    0xf0f0706090305221a090d06020a0207030311160b070f021003230103021503090f01020a03021c15030809030c03030304080d0c0f1205270c0f0d050c10030b030d0207 72
    0x303500d50042c10b5010141d125086170040d044088400c00c900010103800b803c0d20040107a0b607901c1c07032521060103030b034050680c42c40103800a44043c010140c11a407030840b080e4800740103001030070803041c804046001c280214040c0f0301c00410804200a8400405182c4c41e17409480303800c0220b600c110141c0501481580101c030310341409103c5802d500501d04950407650000c08e00405071401117003103511a40094418500c46c000c4c1d142444958000740018109682d03161b400603545c04150204811025101000c00305082c1401d1100c1d03007080003000ba81040e40c0d0003054a503a6030b0b801e880040c0c6086840c8000ca6014000801044103100d5224042c100c01c3d6505a810702080ca0084800c40e052a18440c030400031640410742c880c2d03565540d07805150311820b00c0040025106003a00c3e01000500c0d2502e0100c216481450b40600c0c6060543e5000d42182003644c240e02d804206a80392074403030001c3e460315401800c0c4117440741c0100d4446e801012010b00b014007601e45110501100a464401c24010314041c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 855609289 1250 855608039 855608077
    0x1f09060c2409031d0312070203070510121103060f101803030314130515041b0b0a030f020306060901030504170f07031b0f060504020117070207081002040b0f0f0706090305 75
    0x44c0707581c620743c1502000100503003c0488002c2445007180c01c50781e416601403042d00e0001c11030780c03255a81c0104c0c03c3c41c80d498250509004035442010380701c11642d42c05060358240184080ea48803543d0503409041d040710070040e90321010008440b5130801081041c04038081a4000041c5601580400480b040141c038a5080b591030001c1c900c0d003884880b03401071040c0c0c40310144480d80115250b906411030720602e02080d40702c04404003071134000d4940c1c01c10491520300183d54119503800d44199002e08184142c15030451030500c000601d01c0c0a110708031814103440303400040420a20104840c0c80c044d05011951b102e00c075125810041d900702030700880c0030500c5070b01c417110342222480c200458980e1220004814405555440700030300380103032041b81801045c0e01c200e80c05545501c9164030440c01c60f0700805005240c442e0039880e06c00f007441d4907180c4a2041009202d0307054000121041e001507484c08550303500042c4000c090520850750301901d45c6152a000404041c0c0c840000c0481001c41140c43c01e02e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 855610539 1250 855609289 855609317
    0xf1a0301090b0c03040c0803030115020610060807050a1407110109090218040b01050c1203071403040503030106080c0d02120604050a020c0615220b1f09060c240903 72
    0x22601e00700005000032072500c00256160b1070f5030000b9503210f48220b1406034500e0b5a111440e01d15042038001c45075100000e40c50628031981080481e902041080d16003107182d161240107004290003520440401070002507450040d030007085110900c042c1e030158070740c0d141c1e400c1c2031425140160002403030000e010680c0000c0d15400c640241c0b03101c04280504a60000942020000203242c20041c4c2c40c1401810b202d003520f01001407020326958514544415035038500b05c1c80c01414040c8941c000707140b43c5828010b120102d50000192415501241010390043e150203031103040354040c803804115058000507042c0b913055a0b400c1c1441c09140c00780d600b4015a114004802d0580c000c40c6036990f001d9001000040240180359016401040f010700414416405082c00c00c41441420b00e82c8250f082d11425103040c2030a01040c0c4012200841203108a040c03240c81006102c00002e03c40c200c100490b8207000001c0c400d65106003001d00d1089180d41400c8101d450020003d030a8028069000c00c0300701c0e0380090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 855611789 1250 855610539 855610541
    0xa14042004120611030414072126030a06030507090501082e0e070f0501050304050307060b0a260607020c0303070209041e03110f0d0905220f1a0301 65
    0x41203240002840d041a082040c0358200200920064800544802c543c0e00390f11001e00c01503000d01e014000c0000420030f12403001c2e25041c0d6a9000001007000f003400440034800d500040c8510691203042411686035640e0144c901e8a140c14088081030000800c1c026006416417001044034400d200740c1d41030780d5665400d00101d4200b44540182074000d5480c10355040904540020707686000d5004010082c1c01000c4030b41101e07000007000380e07254010f0800340010b100800c0c001c0020078007481e100d49546001c0d45c4003600c0f80102e01000f001141c4858414060350b03501d0404001070b01c07011b008109484d50880003003102c0c030702102000f0014000c840c04110407d201203050680c0c0080940210700d03048295003800707440f001c024003d4601200981100c0351b2460041091003405002c1ea440c1410654074034105400d0913105142250b040d4810440d807800644c10000540032210225401c850f807203619a40640b84450044100e00c005141203100d2143c103599a001c074003034403a180c001000400d044000d241c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 855613039 1250 855611789 855611831
    0x2030711010509281a090a0c0504052a0c03120a0c0905301603020307061d040506010e090403020607020c060324030f030a020a0b0a0903170c090a1404 66
    0x142070000100c0c4a01c070460a401c40e4160040c442e112516001149040c0c82c0c605c02d82c140c0e07500049400004c2e8200510000c1c42800c0050803044a003040503081180f00d005880e1f0100596070124031140b00d0703404481040b2000d44440503400402c1d29518101c440220b0720261049403203401c3c103480c1007401d9001a21503407c040590704042d204403e680c10f400e6841e003030a100385080b850038090361036500311407600610840700390041c140030305004941544105420595590042410000500012580708401c9003182c200000c003a140002c840e100c000040301e240b142e03d2800f0b500500301c04184001c240d4000b551078460300039a425140c2c1c000d52101003054520003a2130400c0e01140e8082e040301c048240319040c04960b04014102d440d120700c18050907007142c01c005401000342c0c02c01c40440c401d102011103102c5c1c1c8491000000c004542465401902c0e49a005118401500035a40015016039800c004c6407034130341c001006400a655280e00c1c1d842c220001c0e10442d4020303800d20884442c400350030a102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 855614289 1250 855613039 855613063
    0x1020f130e090c061b1f1b05190516050c13181716060c030f0905030a030f021c0911010804020a0314011e05070906091805060402040902030711010509 66
    0x150002036081c0040094540080d003490745030017940003c600714180d00300006000c002051011030315000e01c0d03520b8842194124030801d00c01da61424030944080f603000040724024a034514a8088014075800d0440c0d65005003034812094402e500070301d800b405800215a00340c403c00b1548980c455491410700d4080d2a150030b002443c000c104460100068070810052130040122110a800c0952101c86200340c3c1250704400e5446c1c1d6a00d0f0ac411a03042d5050143d200c080c100448103000c507040b2035403130590301c1c4202c04401040682d12140641000c18640446114240384ac6180d00c17a5091603500c140200b1029a04881420241102c00019401459841e110359002041d0440c1c0ca840c2d40c6130741c51000041d1201001039541c1f0740c403a440ca0343c0160103400e1001e0b180880016107181031000030306030b4295074100000f406a00c0f401082110350240c24500c0d0710b445800e0200d031039150000410042c0c06550805c282107070000c001c020415500900c90301c04092104009d110030b4440b0031090341c640e101c924078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 855615539 1250 855614289 855614293
    0x4090c030e06071d0f03210318120403030e0409140d020105060a120b1b1314010216090c0c0204020706151e05010806030a050607050307030614090103110a0801020f130e09 75
    0x121940310300d41101c010014030800340c1691a80305054001d07004510100000c07820310307c408014080c0601c0035044052280c40800001d0055035214010408180920300c03005007082005008088907855641109a00d43e501110000c601d00420088a0b21a10b411540000641c42d107000074000d0314081c280b40013181c10907983c1a10404564403044400341c0d0003080b00242018203510480c54511b0040100440d5071000c610450407401c01885200740400c0b40601411540700f80074407441d181103003540d041210001000002c2d01d100440c019158030b0f401c120060b601600c0400d41e081400060f0f006414441448004100b03141d80f0340041c40341c1c13000000c0714140344080b000014456540500c41058100304000d003100c4584400d40d503454a4180b0844e410300000394048240542681c00d1300452000d040b00c1c400000b05100204d022605441c0d05100c0941418441a03a40d45203440c2c0342448000b4040001c020341d07544d545488a80511741c041c2c240c1900305440e185000a0071108080c071140540c0e02400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 855616789 1250 855615539 855615587
    0xb071119032f030729012303160608090f0d030504080d0c031a0406060c1205190804020a0b0c0c0f040f02040303020a060506041e02030c04090c030e0607 67
    0x1401c8581414502190303418003000d8034404810654280d041d00350403000001190f980205152100c02150039914403c0c84510401140c000c1510b141c0074103055600c45074101610707d4014101071001058030b540c0b5501401107880c0c1c171400c0c6030042003210586240fa10b038004d45403110140f15a8451628490148030f070400d40c5080820340c070a81003140c100d4006e40200d400c1440e01240380045581d921001c0c0d002c00e603a00a8902000b24442d09036106242c110b034108840d074904140640030444001c03000b0300d80420200c0d40e200241c0a0410350704201030710140c0320142c1c07054040280c6600d00c00d0703030140d101d132511000018030200300d41c0072210140e040318094842c0c1d07404141030208840c2c1d070420903540141c581001ca107134000b03039101400055000c6d0b80103040050309410401d00b21907001d02001d01480c20000300e98a845155108201941c140030001a501d90700c0e1104010b850040d13400080403241480c00f0461010340c15000b6020f0700086806403007032912032803400c0d80c1901e402c1c000344801200b821 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 855618039 1250 855616789 855616793
    0x507020c011e18060e010f0801140411070602072301230a060e09031b070b0a0c06020c070b0a170f01060309051221220b090f0a0b071119 60
    0x114610403030b1160420141c1149203046600c1c0451540e007003a0002144003030f60001940c0e1290300341103d030b482070a01d4021541452503030603ca0405082c0755000d40d07254105410000c042c0400c9860464014504549030046803074010320f044d440207014001520101007040c100701c01849003400e640041c807502280d01d140940e132002c1022009001c2c0c14440d50701c001c0000d940707120320754140c420683c078000b4654508035480301a00c0b601e00030b44201c2c04c90f4006003043c460707552560102c0c1c4013841c490410003914016850076002070b10030909991043c0c001d844000903800161800790141c8500341d1110300c02d40004141411040008451204014247c00010000c1c10300035406452020300a00644000f401c0840441050740d0200c0d0440009081c40403401c10215620721502d0780003404800000600403007d02201c0780c811107a040900070621490200708911710801001000e407140780c051760b01036612800d00c60010a41220810301040186400701483c41e0045140e450103214003080c054000030903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 855619289 1250 855618039 855618077
    0x81b0607170910110d06090614093705060d020a17071e0503070b0711090a0608012301050114030a0e1f090c0e070507060c020709140a0507020c01 64
    0x15201100d24055050325441c11107503130103120000d4140000ca13950300d41602650a04481c030b160300c80d040946c90f1000a101035818000d001514100c03c5a120794562130345950743c0110341c1d03641e98080400402400c00011914016060b4102914011040020b41c2c0d80d082448000d00003020000c0d40312520500510503605009070524180c440d080440340300588034240a5111440d03265401102401d4410800070392808204060280c4083c0c40e401303040413000d80d5840d44406440c12841c0c4960040c600082c0030070300c158428802403881d14002c0c052001100e940c484800007159000114258240010a003035010f0303821554440007100c01d10b4a0f554a0060a000821182010300c00ca8050040d03000d000c801d004480c00103102d130300340c00040ca8140e14034082581c40c0c1035511164016038104200300807181c01c0803d42d10000d8121102141501d020b403400c0b41020105d811010b001c0707150941180502c94034908a900c140c5080c5420001c0b0380310354500781d94444403ca45a400140e50703030a00803021082e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 855620539 1250 855619289 855619291
    0xf060504050c120f10230402060706092303040f18151d0108120f090a05030d0c060b04060812070309210b071e031a0d081b060717 57
    0xd2050b41c202c503401c1c2c0c0c000380790b9601c0c00803c11074a502c00079512040c1c80c8148410034132030303401d034500f04100713841d220f034080c0301c0c0c4240400e01481b216040002010f41d250b52003251006a03002c0c804000c000031a1a200c41420f035181c410122442c484040e42e400c48000100700e80c1902c0c1191400c2c0031780303441c00013940d5001d0030540c0e10030042038480300c28580851015820300050302504c8440c0c542d41810100103140c80d54140d1110740030b94000264880c40180a0307040f10301d205001b180e03c582d40d01c3d19001150000405a01142d05841940c00340c41c0507030751240821300d0581c802c070428008982c01d0002c0105551880c09042982e4002c001b9216000c1c500c500206109031090800c48850384e9240d030140044240540c0c43c40e00c400701c004604003042108040303c1c0c0c0c0420241451840074940301c182011a90303280302c61109155644181c000440e03403c801741d0f240080000c100710009156464606401e40180c1e003403500c4000102201a5044804901e180c4180041e560b410580c6404540c400901c100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 855621789 1250 855620539 855620543
    0x1c021c03060803030114130644030d0b0103051504230f15010c03020606120309041508060c030c091003090605130c0503030c07090c020c060406110c0105070f060504 72
    0x240d074620002e0034000030300c0910b0003460004001032212032000c0034010a124583c50781c840b19450100280400c40c40700600c8041107541840780b182c0b07914034001c0000403ca0f07224040441100d00503001030380800000040080c0704180e081449036009010054055440603102c4505022a00c15501c3c0c107400c0c036501654803520400f000c0008030320004411080d0110540b014103480d08031008010280c030741b07603101c00d800980030328204048a20f2910025101c20001d48018494900f500409103d5030b8108252002c50100800400c4001507200c0c1d0500076000c00d20504596008003030008101c000903206807480b4030925800d0926080c100c004000d0350301d110921405c10315a441c10703008041801403003030740e10801d41c6486082403841c460900f0503004241c5d42c40148254020450448484408a42c520455507214000324141c0b0300c5a400341e080144002d00c00342c0240c0003040005100381c0c000903100700564440705464420515000459852154100c090404240c911150303000403a6540070942c800c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 855623039 1250 855621789 855621791
    0x50409031719290405150a0b04052b12120507030b090a0209100c022b060501080a021f23041d04020a030210050c030307030203091c021c03 61
    0x81110307800508907540036030328944003002000311442809100d200b4098011944540700e900070712194a44820302d44000030860140e922030020802c0d400540e03411445440c0c0040000450a40328503050b4030a80191160500c5200c0a01500410321804032805103002100001e200d003201058880c605011020908601003003500c0c0e0540d602d4251034482c045c050142980c010070050780c1c8808100e040300c0058200704c45644100505141c503500d0321400003a8050300d0810448443d03190001500b4100e00c1c0001140b030001c040ba4441c0c0650054a498120781c3c0f150008000c181d880700f000c103030342d42d1413607800a401414043c140d50b003d00450f400581d2800f01c902c2d2501058594a4003510002c40c509000341e0394010216003072000c81d1001d80307102c20032200e03420016403500e442d40010322040014400a4021140b440c0c96040c00d0303104600301d601c1c00840078201da6407800e01c0d003002030082d4001c440d040098003644070314200c030b8042c0080308400ccc030115600501c44d20500c498001c000400040f0610b00341 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 855624289 1250 855623039 855623057
    0x101e06030f03140409060906140111030a1803020303030a0e15151509190821190c0819110604020306010b0a020106091b171014012d1b0b0105040903 65
    0x101805001c0c05040202c1000c08d50720318045862181842a00c100c6040c401004403601c550640002501d030440300c9490305202e10042014012014000b5810107034040c00008200f0244119030f03000a0400803100d030456400114034030f0100310083d0243c40c1c0f00d04114141c01415007903d0651001c0c148001800b800780d2903d080000041c070840302c1c405415205102c511030070808191309002d01e0f0046540c00603410004c4240344003000091246d40005c00400c5042c2c2c141c1c1810602c540b9a14003010b6101040541c4c60120000180c2d402d0003111074100041c4000c40b1007041c0300c0c00403c0c02c0e40100d0740a4000d003e242d0810318a40e07200d80040041604540d42c8000008003004140681d046007400201d2103030190358000c0004120a890300c400180c103c01440600400005140403502103641400c018081b400b0318500483c0c040d1900d22808501c0004002c8094040d19407400f905560400d40c1c40d84440c9201092481003090030444e8007600f1000c07194010413040c1840d401140110b886032508180c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 855625539 1250 855624289 855624299
    0x510050604140717160806122a090a0605060318010b03030706020d110702030307110d06060b311205070f0608011e1406090a0503101e06030f031404 65
    0xb00c0900300c4081000800010f00343e40c0d20948000981c0c2c001400031000345e0304580140300074250b4a0040c05690003500740b4075a4080c1030380203001c00014000e82d10030b2207030108002112458070b1110800d55074812030100000c9084090700344121811580013422040c259078030f100600d282c40b116004000125501c64401030902d035424401040c1d168841d510040e22010f80c1080e150841e0b03900d40c00c50b20f01a0301001445d000d40c0d00001501c10351035014225506800c08030020621203085800001d0040742001408501100440094032601c2ca00e0f40d4004d121995003000380c101301424511303000c4001410607013440f12803100b140c01c1000e00d0150045500382691901082d6140206511440c00a40c409006009500300140380310f9282c120404d100007542d0501034112541c5c100e4bd14103a100d000c001a03c240140c40d003101c2c1100400001341500c1d2018403211310314010344050548200618032444042d07804d1070307440c880c11003076a0b040b4850580403803450741d06541c0500343d846c4604600c40c0030300c40094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 855626789 1250 855625539 855625571
    0x6031606050d0b33160c0302090a090201080a0b030a05030706060f0e0106080c0922020d27030302210702010b090a0219050901030914010c110a0510050604 68
    0x2842903949059840d02c00300c00c89000c8a0700e07880c0c818802c0100042400c0750ba0700d1008108030355400100c9814103a241c040c4480428419035000812081c006000344c1c080c007050b034070000103e034000d450704130141d030301c9001e00006c0310b0700c1000007400b20b400c00c0c0115280388170b503034042400e041003d400c541d40c801460b1507061a40d04201412280c0e5074030340e00107001500b014900500103140c0301e442c012640d41000380217007910707100424000c0161404124000560350319440409240301d00042c04040c500120341c088060b5101e10b03070b038089003401c2515245c2c0001c5c0b20000200407045c0034030017102e0000a50b5086010703511481c2070200c64400038410401a0054980b0240a5281500001003611983c800e1002144005106e8146c2d18030510440040035203904407948084011302c1d1003950b914042005030002c04c2c1d0b85401601921004040800000c4150302c80700074010541c6826a002000d20426a500d5120110040180c1c00c0120035880b02d203000c0d00aa508080003c0010a440e08036660b008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 855628039 1250 855626789 855626833
    0xe2508060c0403060e030a0f261e0c0702010207030b0c0403150615050c0a1101020709092301020c300307021c181a070512030106110c180603 62
    0x2128000c8005401c00c1042007611030601a0f48096002c0d60800401540240044904a9214040c41103001344140b41602e00382750340080d810b1403c43c60800d814014a440c00c0211a180d5103101c1d01120000b01c2d14403107900040c0c07404954143e00501c241400e40d91210501c420240100c0030700300042c440800012071448a030712580c003c40e0400540e507460580c407a482c0e6200115240c0a22000b00003805520001003910411b642e00000c450f0000088240102e181002c1741d40900740c584d142408170010810104900204500415403048120b84148500ca08034401c1140c00701140e071000c40443e07a00c04403049149205841010f2000a624010703020b404254801c0340e000006803c4652586074901c51a20038515a48580c42c1100d501c0b4080034002c07580042ea40100320074140900c0d40e10030600200c404446400d641b0009580e8032405903160950103820030301400c400308030118001503c50700c0000351119802c00c020007a030f500754241403a461042d000942140e406008a202c8041f828400d85008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 855629289 1250 855628039 855628051
    0x31f1206110c0304030f030e0103050403050f030402130f020c01060e09031218070902040e1b040501050c120a0804120c08120c07050607021b0a050f090c07060903080109050a0e250806 80
    0x51b0b601e050351464018944c002c980501410705152200b80004a6401020f50300802c842c60380b4a640c0e62181d00001d0301e01d01d641510355095505003003142c500488285c0143c01c4040c519002803141c691600082071042c44111000d02c00350b4820720846841141000040e600040f804003812203403080a034540342402c0d08d682011718a40d400040820400041c3d6503000d40c0582c07050701d00e082080704404801040c0c42284585410010042014650750a0a10a2952901d0021082c5585100300400900502400c4030181d80460503070a000f40c004d0f0041c004440c1d0694028034140c40c1c0b031390a800310280e42e600641020782c1e4a80c2030244800041c2c013001681d00401d1150000c0c2075086607071942490480c2e407440464007031214030104103c0754480b04810140100300311682400d40e82c40c41d005000701e000d21200900180d04000306c131000e00d030b0001d83c2e103416100c4020050100b030350380791b01503400d6071000c6101e90101d511145080403240d02d2540c403103010f1904128551815952004400d04c1c00c00709070380c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 855630539 1250 855629289 855629303
    0x11100204030b0105041e0b030705040e010902040e1b01140d0c080f060303090d0b070c02190503060f070804021908151f050108130615060203031f1206110c030403 71
    0xc14414007800810742e40c010700e03084034203200810740d8204170448050310901001c01e1640307900140380d072641e05000d0f01d070180c5400760041203071040402c0010302902543e00c0682c026031511081c210038400202d6400180e80f003500c4030f50002000c3c00700445a04aa0030720b641c190310424003018054000a019004000d1b07195521541107042c0036600702e4454001400701442640304000e041055102c0104032005160485d159540b542d94100c0140c906502003040254040c010b1005081d4000e0298810000c1c5e07401601100c0080e2740c0e0031880c4c840790b24195064008030b44084002401480c00920131148800e011404c07a10081e50742074807030314181500b06c07541e1a0682a1007041456143c0225074000076620780c825200f168500340029215190190030085c0c00c0001f000d100c2e0a0101d550420341c0c8030343d9000c1883c501240e0780c41009440e40c0094442e440105000c444841c440d81e1468170103c1a03030480401c030f075150039581c0d55071001024209080c004800086c44010154002800a4802103004c2c1c0340e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 855631789 1250 855630539 855630547
    0x30305120c12070e12070501270b0424091404020c0a02030706111c2705060a0504031509080d020c070906060512010e2202121f06051c1101111002 64
    0x400c0107141034817041045144e5020030f004000c60380e4002c0e400692202e40b550745204030700c00544a950500907580000e20345102c001030006444a090312004854005a0f00d24070600c0301213802198412101c0c4941e46010541500c44602850207900900002c030064040741c914035034950200e070404da5207074070080c041000e002c1400c08030b44091005403146110b4002007421411810f00240180900300710507560110b0b2460f0b250384045110241c00040d00f00103002c10f8445080940040c2a0381c000cac00112307404180080c8003011685140609036407164070042c400d00b842e807040b45503402034000d01c070700a1445c4152440020115064490721000c3c001c644d841d0361355110322446141804070306034801407008040b0410031500901211100d8500e69841903d114410b4044c00013800f80500c0c0f0407021298055041d500305001010205115a00034070f070004d1001564840c00c205c2d4016010640e25044402c0b600900d000030000500300c0d880304c5050604042e091900038000340b80c0340c400b044020030254005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 855633039 1250 855631789 855631817
    0xf020909161101090507090b03190605060a09090b060103021614100b180c0a0c05010510050a09110f0304061104060305040501050604052203031116020f010801030305120c1207 77
    0x10080b0715510560900034040c3c0521596626900c010320310035050f400c1d035101009007040e9070a21810a589034540121801401d090501800030001074403240e12841121000261101150160103500b5070015101c80c10380d035860005401a5018948800e81e2030140e26202c0c0014101d0074555020350440300c000c02a034a9668811000c541700110401d205800c0c0441070701120000e800d0083d4410350807180743da00c034002842e00340c81d4a84201c030002c1655082004000c55600710040c0c0f03000300e91088405400b12a6500076800c21100865441081030808200c3c034107501c005500210b030458480c4070700003140498040b40c032045130815008071001030386032020305c4140039090246d650840713000c440c10401410001c103030311503924040042d89801c0b0074800145007858080c0e400001c1402003c0b040580c1c80c06001e401c0d60801103602c400721700c0382140c1c2111441c25441381e8042e606030380d455110603203007000700000b160100c040109a940055010003001e038180400e10038140c006e42c115103440c14614211 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 855634289 1250 855633039 855633047
    0x1b1225030b03100b0306071d1305040312020c030d2003090709114f062c0607050a02040623100e010f090f0605032205100f02090916 58
    0xb8001603883c20741450b07101da080e40d80c041000368001e001420140f4620501c011b114039800e040080d090703800043c01c0d004445020094011510842c401d54900c030741c8040c000c0c0040c08a01801034241120b070701c1440001903035403440d442642d84100c41191152241c9150306102c6203980100d8044566801031241040304010a0041310380141c0c10a894900744070750400b4030400c034542c410920200e018580b81e20703100c0f0159601d032480441c8069100c0c0002002d1f2560aa1480c5603c0c8509000503034805910100c0c007a80207108800c0010024035104070701d65000400c0403a82189006650a01401c81c01300016550b900c100c0c4c00502c0c1c410704002c07042c800400701440703805400904c5030143c0d07100404107410300d500180d0140400c009003410001c00072030300401c50303142c811b40e0442c440803542d9043c040740450704000594421845491040c40b8a91407000e201d80c025000c0c0c000604650003200c0b0000d0011440e0094402055800790040c200642000002c2c80c882c82511190740d8043c003034031013840750303688 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 855635539 1250 855634289 855634303
    0x10c0306080d0e010e01050307230a021b280801020d0c1e090302190e0f0f060307030302031207030b030318030709230402040e0307060c02061b1225030b03 68
    0x1400c010300303c1c0d001c100018240e5424803880c181001400400555800e00541140886e034049400900c0c0070a42c0c1190301846900c030300548805413143c2007900143d501d0080f0000d81c4814081e04111115800341d04454041d00800980140c50444c00404220840244090022240da000000c14242c0000c072000d001142680810440c0344241d40041072400d8000402508807941a00c0c0034070001c0307402c9452040314409400101d610380d00741d014032400c0041a00c0b414060050058240e04a8840c2010103541d1400b038031005000d80c000340800104801c40701482c5500c903100c4d00340071644040410020342103034084505040c0c4003a0882c40884203090401c65000503010828040000400700101c60344c0ca01c00f11941401d805c518000040d00715242c070341005180c0d074500000c43c2e480e00803500d05040130300500540100184900c40008441801c010611503242441c00565807a0007c41004480d80100085c1469007803074044211201c06032541d05c10032042c00480d03030001829041081014180703c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 855636789 1250 855635539 855635563
    0x90f020d121b03022a0a0306021b0c090106180e0106170a1e1109060708040e060103050411090a0b031e072301110a0602040e06100f1d12010c030608 65
    0x39101e40b400040d0300054040f41c580c4442c00b59450091109211910112880c00c1c41604105003040000400440b40c000d0312000a010440c1001c050008960960f28149002081d5005200f4001080024041d880c400d01d60100204281e0032262941d04c16050030100fa4450320000d803060503d05000b4290322410790b00221003090900c00c408101b0001e5292050707010070600300d00d03a140c42c4110319142074011500003100c0506080c1e15081d0600f40082d59801034403501c40c1540310300c400240c456102e8407a2502c90f0360f12100180144160000380f08042780e000b40210170360317a920701419609613000c000fa00758004140086e40314a1080500290070618181c2c000c0904001c1c04620041e07004000c0151401480d00303113082c4142da194500031038a0003991940290090703100160100d401c2c2100158039100e2641659040c0f140d80b00000e041b104007420b41c034683e0000d2484118841c41076406201450224802894030b00c2c00101c082d041401c492030300791820301080d40d4070010441d80c2c00030b00030586aa2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 855638039 1250 855636789 855636827
    0x50705090306090f21040305070602070f0e09030304061a0a1e12020a050103020f0d090f03030605180f0703020702060c0303180d1218080d0903141309090f020d12 71
    0x74070082070745540c031311070390000c41501844903011604e072508100039071b00190b0700a0100d03080c0350350b40c0001039151885805500c0e050a080701001c90103070303415688240544441c1d0f00451441e605c035261f5100030507061162040701d0744020321013540b954030302000340042c1428441d02c2e494280c602d40c2d0f078002503645a001c0032111800264800140c0d40b00d61740d0313000f210828240540c0d9400036501180c80c40c840c1500c507031005c07450021000203224a200200c03801610075101085000d88820820034040084088003648020388070024103c0c1d055010020340014985c20054244005940028002e401c241000c2809900c08803c000014540c4a4400001180302c0c1c06043d14000b4500000c0141e5040302510070301684440c600340040c0794200013910035035042940c2989510011926038040c140030300054000030034a0301c0c011104400d50003292102e401c4100307130b500c03400e15080c2440c004e86540340d0140c4d2403044081c0b030000543c854003135400700d0310303c41e101075031694840e228041d100c4c01d0a01491181c0e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 855639289 1250 855638039 855638053
    0x4062304061d0a0903030b120601050307090e0d030c02010204090c120615020303131e060f0b040b2b061b09060c020a030b09070315020a09140a062105070509030609 72
    0xe0b545400b0415080102c1001c003043e18402c40c1020340180c220304c040260812404140c2c604165404074000c1e0507030340e044080c0c4084a07562005034050b10002e14050009410905001082c5c60083d03124001c8041c95000160816a07075484070002c0310ba1011268021075070203c1e50b010421680d2080c60301606480000f00000c002d484002135517070100412070302152078071121503400d02c07140700b01035800c0c0003050410b9102c22000d458041302502c0d503104417880c100d0a0190340001850303c3c0c060075611250140440c84960641158805021075030142500c981d03008444520214049002c1d44802260750a180143c11030034102c008c042008175031000041010744941c0500507610b61025000b200e400c50b02004041e19884641410055283d000812248018281c120407090a4000d400c601c61903888060120b81d07668101801d418100015951180c0302503001e202c064003034650300d0b00300c0c541518810704030701003078003120103e0b5820744800002c688081102116403900308403440d07004108070050031803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 855640539 1250 855639289 855639329
    0xe0a050312151c06050601020c0609060d060513140901060620031620090402031507050720040b0105070209190207060203100602070f1d060406230406 66
    0x12401941d0a04210310703900c402044a9103841d44400c000078000070101e403042c1ca2115003c90204540800c04c440d100d00b404c0010754550f00204410410140190000d46081c000d402041455071152525071200d075075400b000300700303500ca8241602004c180c1e04800140e1009203a85c0c2c5284c0342d0b00a0051040340e041500a1028962001d540ea0440607040c00c245102d0450315a424118020003002403a011404a040350502c41c0d039808030100d00c0301c9030000684200c510814051030ba4000c07140030f90580c1c0417205902852500c00307880765006a0a1410a04110341c50b40c99500e40700910000d00140000c000d44003955150500c20107242c29802d0138454036003180c5a010410b805002483e5000d8402150565014280113804503800141d106004650307038681842c20140d180e0250140000502c01c03000e010600028004140d42560029032002010340e00c80007090f508204010b1080780c1103900d5000000c4d0103001040170301c0e1010414614120348145c0c0605000442e03a655011410343c1c041d001c020300c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 855641789 1250 855640539 855640543
    0x504200915040801022a0d211e0f050c0304240b151803060405030403141507110d09060e012f070317040e070807030e100c030e0a05 58
    0x380000d000d94009941c10452014954507014541c0b141c1655400004d4001c40390b64046072807820652038a0340c02000448180f10142c3e1400c5030321004001c0303080c2c0c1e440b1080c281030794100c0e51400c45d410000480d48140e070759030317400c22800b42c414064080d030340322062420481418012240d0048507200303104d041d03160a071501913080100522407d690402c800340710543c00030340e0b0081c802c50705024103d805680d01d038220007141d641c0b00104041401014040305d812510300801c0712802242c02000850034282107845055450700c245a8005462042055500200701030f40503040c407032801c075102d2030820602c00525900f00b0f44114134841c200509503409010007504140340071060982072800c1201140b01100e000c00b0960929048007425484881d5400414400194002541e2180c4480d50002410100180702809036006500b20112150005070346a4460841d40d07a11014914000c038801c0780d49030945041c11000485441c030691100d54800099405010718450900074000400140d5415141c42d9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 855643039 1250 855641789 855641797
    0x20d17010302121501060512060402121b0c161e06080106030f020c011a100503010e040602031e0f060f0604030803061002030c0d0f17060a060305070c1b050420 70
    0xd1283c60f0b40150540b65800c10840001d00c4440016540c1ca1961110806822504004000c4000c20100e000240e040c0c03c141c000e45203c3c0c5006030300301e144c03500c0d000c1d400c0781003031001070185d01d001d00b080c0301c02001002d04000c0c1ca00002c0d03002e82498881401c00c250790103100d030860303460790303400340400420071005500841c5c00741140c1851600084018a4030600c20181c0f080403005682036007001c0c1e200040c100401c0c4002d8042c1c0040f121031000c881e008006907001d010910940c00314005400004000c14241d4004540c02406205241c2d50b040303811410780001700c0b0941d0880c1c6140300080c1000003e05125003001c4e907000040ba1540c0c101441d40d80e890710315100088c140d502550b024104504240e0080040d10124000c200903900c0c08850400300030080710b0b007228810300060000b041c400010070038003880c601864000d03110102003410040c041d80a042d0103444181008050329a903004998440480350101d4290306010381c1c144d00d000100402d40e1031200c03006035001c050341144609450064216 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 855644289 1250 855643039 855643043
    0xf06010c0305181f030506010f0e0d021c0507090f110d181505070e010504060e0906120f0304032109060813080c0a0203010f0c0c03050d18050607020d170103 69
    0xa69214501404600103400310940300340c100ca00c0c00007420300504c000d11100b8500019036010010b07070762a000115000d803869006940421700584107000142401c4200c180c101d070025059141d0000c3c14045540ca180f80aa003d60301600044814003211005000e400e10900e125039043c40b00341c0000d03000e48414410000c031161184e40e211200005135075442c4078800e186400c007a04a01d2900c0c10703034003403000e010308481800c0081d50860703500107950b0250094030291200790b9904d54118180a060000701800a00131301c1e8040042900c50600701030810802c1c522141000203151103d03c0c0d80b900d21510021400004044010030261603e8035601c4452601210007034036240009490301400c80186e040c0c0c5c3c000c090107140000861440d20700002503800141442036001300003651405441b4021600c40c2042c220004080440f44000320f442403000d010f0074603042c2e20001b4a190b880c030a04503501e10b1150200c80d150405e208000d0704075010300c61310f80d000c082414403802e0310501d440140c524800c14000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 855645539 1250 855644289 855644297
    0xf0c1e1f032a02010f02180f0f0409030c06200d0f0605130c090b04050603040305031b03040f05061f17030d050f07140a0507030f0215010e0a060617160203120106030204030b0f06010c03 81
    0x10843c2d1b0307580d9270f4064440000c03004e0b004000f403c11604000b40514178502c825105c0c0782c20608154802d1b00d003805074002000d101c001036407c0101040d0024003030020148103130726540e1121030100d82c95a42100750000c81c4406140003c46c261404c9002d0401e481644c414900510309100812040e1169011a588140c0c54900b86589560300581003e100c00c0340000c20645400110400c010080c0040d08004203900410032142c031030386c2e0071103403c2000c0c1c0506203041c02180d52007010001403041d880d8000000c1451802c4d83d060460007000c1104840048641c4690340030041d00380304d0416003001c0303056041c1e44002c880d07038038000400034007030110320030070000034204401c03400540c130080e00c20700540504010709005510036503503404901c0ca44120581c0c2e80c0b0704162501000254450003190320040c0410b0248800345c99030340c2e50b00d000140280c03c1c81c411007980410080c20040c66601c4070143d02070940d070b40300143c866082d41001050440c3c01020312103418064424412140e03006403046028940c1450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 855646789 1250 855645539 855645559
    0x90c11070506361203090a060f0c0f121b08030c0702010e030607020706030e210a020f0f060a060603090203030d15080f0c1e1f032a02010f0218 63
    0x25040c8007500400c01c1c2942c98480345220710400b4840006100c0c1400f00321180c403101818151450380702d102c0c0d290303100c2d4840340c0c5400c2040032a00404079089413809900705080f6007042d0b40c540000844808208031340041003409034401035600004504890941469480158081655055490312024126402c0b001c0040b8815046a104400c40c2400c42405001e40d065801c1240d0040d68440c00d81c0901e0740440d04100264204840010b100300140107145000c030400f440346400c4071015400701211201f1801003064158161804010000c81410300030018903407480c00c038900004a4020340c0201c010142015000d2025950000565041002e01035000921004a50425404042030f80c010301c0c1c01c0c0075071000144001c0021a00001643d01a41e65a07104441c080306589004d4002c00392a41c44080a10100c090703580340c0e121042581890f0800090800400c41c0040c0340d0200d1000d54040750504902c0d60a03400d42c280164003580981280543c1003500c0d03030440801c2503006d610740358091a5001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 855648039 1250 855646789 855646807
    0x5060c1e1e0d050f0c0f070803061302040303020a0506060105042301090312020a03110c0612130c030807140f030f0d06180203060a1a070b071106010f090c11070506 72
    0x410030034844584010540d00c0400c0c400b2400601811164000350b44200c2c03000900e1604900102c039200442159107506e4001245d070740400e039070400307807045801072000d070b404201082ea5071005001950094005180a0110345401c0b41381000003088a4100b0000740800c0200010941e8040e070f08091250380200381d040b0f1200122200c0701c15500203041860600380d40c03240d0316000f1504022150296848401707110080705150341d250980c0301582e40120b4200281c01d00c05002804094201000d00c0800300002265200c92100002c0d80d0420344101c03000160300e5040000a4903040c0d108440000038040400610005a4482c0200c0311518030f0020006180c000c1e800b40340d4060380c040d14030320030252052000303400b080b0000e4000304e5003d8011a00f840021030710184100c82081700f1050984514940561552540410340025080000344102e140c10789841a4051201c64080d003091801a1809032801011000795440110301e20140450403030b102021b01e00c040b0740b01c0146e400c2510040d549804403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 855649289 1250 855648039 855648067
    0x301030f1406240307050901050120010207030e010e091303110102070516262a0603070c110d0503090603040804150309051018170d020a05040305060c1e 67
    0x2500c181c6040c02484100b03c0101400642401c00307441d000f000c0480c45002e50285a0348482c64050158002e030f6400042110358403c010300d82001c3c0b0340030049007122000d401c3e038500366007001e0012030208030b420000014030b5038440301c0360710b000f10100d900c44a070782400c14a10807441c0c071800e00902000580c01c80c400e28064250100c0c0d01140d4407004461041e910603088a510511501400321f440707081d0710400c2c014400d9498401459400c0f0806403213040f508206102d4404140500000d91150548035114190340340f40c0650322503d12600d42400421162411000704c00c89090040d1040c00100c40c0000403641c0081540c050120030344000d9600d45990801841a008a83c0070b07002050450300d203002a01d40c0354101c1c41c101c034030079812650f050a580f45804140e0751460011450029240c0000300410841c0031210000c040880501d85407072030905144c41661b20500510010810001d402c00401c041040001e0f8810540401c1c2802d10081002544181c420310104184103100422150145004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 855650539 1250 855649289 855649313
    0x40b0301060f2f160e0f010906060206010605031302040204030b1b0c1f0605030a1202060a050606030408090f032d071401261303080a060b09130b0a0e0f01080109080301030f 76
    0x81038006840711642d40301e00306500c00088030282106c9400c507000080d0710400c0d0164006482c1c140d00038040aa00f00102120b4540000b00041c1800040200a0001da25070348001c5c405076003d18080c0c4500e1806110b0f900e0130000f51181c1940641302004815400300e03000c200c00328502300b084003c0241890310300504e030140c401c5401030766141c0516500c0000b002101140034038042c020741c0070740d01d1ba565101e68502c00c44a0465840d5000341040000500042c103000080a050f00014081c9000d200c1180100c0e14080040c00542da80f41c0068581e1200281443c0164141000f248014080d1500303201d1198a1980d4070130100b4144565008c200900108902c0c1d0302060841111603040c440c41c00000b001130b001c0310304205901140e00304010400822103400fa80050301d1150044502e004404000e00c40d011300d0525400807450780d1005031440c282d0f00c5415150081c904103221050508001803016542d000603440050b00b030703141450352000188040180c03811207802c81c4052030031030f0076401e10344441c401c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 855651789 1250 855650539 855650563
    0x904020903060934030206070f061d190825050a0813050315062101050406020c0606100e150708031026060a05130503040b0301060f2f 59
    0x42c0003c001c1c0fa0302d40081e00408014000c901040740302c04036038150b04116180580002d00340c8280c00140090305094005240346403149031481c0c400151500c501c0c0c101c8468035040c40032284411035021a60604108003148000390420080e00034255a842240600c6852820141d4160356840c02d8002c10076001c11038001500f00e81510341081440c50a41210390182503403c109402096000c9075900300007911901d80c0320101000c00560311400100440c1031508001c4001c5501e000e504030a03850400e0003154016445450003580b07402c00b104aa50910000802c1240160a6114001c040c103034440030b1107440300825140d1840d0808801e03422804c13403255400140080c0400014000103400c40741820b0200c46070903054508a04035010100c9541402601c5d0f80d00a074400000701300b411140d42d0200e5040254025aa005660603136280750841e00254414105450084010044543c00902c4007114420031300d444440034045400d01120b101c1001311540c0030040380f5400450a4104011001c4014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 855653039 1250 855651789 855651793
    0x5040803030a052a0d14060105031b0d11040905010b030606030a0c03061d04020a06030204080d1b1403070b010920030411090a0f06170a0201110a0b151c1203020904020903 75
    0x1041d40c802c07849a41e4040040c00800506d03200038411101c00d1303054020b0140c981655506c0c9542c5071406030841881604102000054080013080500c506611444095103140c580042c2c480e45007009600072a04c050344451000c0e001081040306035a10380c002c80341e004a60701d60004520210304808c070000e101c1a00181100b009510b01d04c3c81c2c03000201c820f030348a0391080360070070512620b0341421400d80c001c500c0b0391002948030f50b1084c251180140b215122000d00310011414548064860300d8140d864107a4001141d04009400014441c60980060240002a40c1884803102a8040c4072594900c00c104e030010f0100440400c1c20440030207106020040020003004490038440301c1c1030010602401c401001500c0d11000040b084400524a8001501c0f000901541c0c03403c0c3c0c0040d202410f0700014000c542c001c2d0101d5100089645030b205005505402d20a903644a2200502a2858082d52072030400782151002c000001d0042e04008000358087c60096180c1201402080190207003080c81540340c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 855654289 1250 855653039 855653101
    0x61204120c12081f050913021801030602030907150c0f0317101d06210a060908090a140307091517010902010314190207080702041508060705040803030a05 68
    0x4141c0c810310640c003d0404c03a9403d00c00d2440c4c695001080d01a51180355080444500000d001d00008002c004007240050942d18100003902d007599800344090300101d0340242c2c00301c2405445001000000e01800040c0d011082c4040301400c0540390132418880144229601070002d410103104541c5000701c0342c0c00390300044190400c0d04ea0b020101e100ca0040031003450004003081000d001040e5a0750040d80040d050301b40710315005811070241d030800c02900e4240e10130900c41000150851141c1820b950091055913150300c500c0c400c2041316001d170313070001c00004400c9415885a80e00401c401080310b07005c060000340407503044510809010310398020103503a20030b8040008041410340106e00240e1007660204400746225070544006076042d509190909000c000c094001341c099802000c01a0150043c1c60500c65180e0000b03065582207140c04003009025407042103003a8042001c180c02c40818201141494180200140d0343e01006000598864540004c10442c4812801c03a08408002100f07400b00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 855655539 1250 855654289 855654323
    0x50405040903080708070f0504090e0304050a060e041b021504030e06130306062106110d2c031819050415060809010603020d02190b040f14061204120c 66
    0x209030803c031010701c0171540071000101c0081c421884124031302c1c100d444041c103013414100518020300c080a010b41c803610041002148981e41d10180000508150380c4804003081da110520040d54072a900450710304c2c0300611002d210705d40104040ca40f020034010035052a54031818206e98400044410680000000510030354603030310f54000701d096901a1406100e203036a2036050000c1b4481c400380d80c1c01060b072843c1030180000d2650300086005c40070090740a05200403c15450210740d02e034112542815000030861090500941c002401010744002941c102034120300c1e0001200b6013035400702e11130300024903114400f000c490411406040050310802c50801c0444640f13001d50403d000e060046110140007640d000b905020b42001e4a60250040c0702c80e503501d609004420010111002c56000f41c10741c04a0010b6a1078058002400d8000d11007800720310300100c4000034041b032003115005103810098580103603040c03121650032507400360104080f04445a0220303500c01c1103c40041c201000da9002e000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 855656789 1250 855655539 855655547
    0x1204170a080f0a03060f060c02060a0302120132090a020a1707020706021506030d0809010f0f02090f0a21020114070f0b0a151a160f111806040c050405040903 69
    0xf00c3e03000070b07102001000d440322807030010303030702284104400521015a141e0046c01e11030043d04030f440d010b042c05824008542c1e441c02c03610380240c000d004007000c4207660008500801d00c4803514200c4080505010128060100b500880000c2c412140f19800191004055208901c03040d80040c002c21404c400e03080108000351a4145442080d0040c440e4011003800100340c0000c031b5000b0358004004244260042d1820780307241d1402400400155650380309058102100d0180b5041c05012002c016a46c0c95004100102003450208090080503c100240507010011030705041c80c0240c5110885070040d1440102c405028001d454000305102041d0441009100b28205641c0e03446010201d200313690f905510411940080c0710841100700c0c501c010000400100700c042c0000b005c002000f03103001c012000e0032309900100007003110b0ba101c4150401c81407200b117040c130b035001d080115107071041400f00d1038019840c80c0002e002c007440303035940340c1c41d8044150240c02210000c02001d4000c0c0510718490070098 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 855658039 1250 855656789 855656797
    0x315030506041550040803090f1f0f06170109140a081608040b0c011e09110d081b0f010e03090109140a03060603050102030f06040612081309020c0d030605031204170a080f 75
    0x2801c3d219400041d094107402296000070070180100307160607203d8101d07564ac0505220700701c0c40c200e0390b030700c10b4045895240c5130850b00181e20740e0000030907645001d180040107005205196003e130340202d44030000180100b000c076055040114080700b0004140d0800c0c401c0352080c0e501003982d00b540010481100350f0306400c070218000240c00c48034581c000300d207a00c4050716446038004000080301003403c00305140c900443c544d02400391402504003661560f51031007901c4401c1800189030b00c07000b60604e6501090140f82d0078101501d0207503013011b04110018000d01030600074000e02850382c1e0600f0101c2d49480134000001c50f00040c1c1403210f15500d040aa0003903009079030016214038200c0000b40b06040c1030007140100ca0044519044d10209a12041d115030002c8400241c0d10b2171010000640023507d0000e086081f150308003034052503d4602c000fa003112140d610241c000d1704801c030b0028100700d60200f600c0c00c6032846070141040340c00022080f800d0440804005010810100b244140d0301d80da403002d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 855659289 1250 855658039 855658051
    0x14040e041401110a08160903053c0d05030702190305091804110f0103090515061f0905011b0c030606181b0315030506041550040803 58
    0x204158044605007000f2440f410030000046045000800e9a00c00801e024a10b00403181c40d00c2c901c0b098613591039504010340101c0d030404031aa802d000c145000c00003040ca1414145050078807001d00b100f402159100c04000c0b904c0c00500501000040200f8001d000215908400e00715104201b030075441c010740503800400c2082e0140015006118580e0310030681240910781007600100da41621404022400e500004018105600c610000c000107004000349041c05400e403541012a207001014451481d043c2003102d42d004c10500035143c0d04a0b040b503142010f03a0420310b44940f80c2d2480f15100002071300f108000900b12991100e000040c01800c4d40542c065804d2003808000032080700340c4160940d1980104110305000d42107249002e24000d0f40105030030300b59041c003012030035641e88865003070270300489054505c80030031011001c00d0865071084122000c4010940d004000c034640e5180c11641903200180c049400e50750800c1440d0300c500c3c1d03288407615004002000c440c545480e013070f803086e08141d0381 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 855660539 1250 855659289 855659291
    0x1e0f0b090a170315121612050c090f0a180b09100c030c210608030d06030b0601090617070327060b0d0203060a0b040906060314150903070314040e041401 67
    0x2c8035070045000c1003128003c582488260080051020030001d990070114480134592044a51080e0140760741040341e4028000c0780004c0d0031142043c2401d505110b11074179038600c104540340802158a007a400016041040001c0006030304203020914a281c00c151400940380d0a4420200550004001030201680055003070501441c4a81070317042e4291751b5180105400300c0ca01d1100f2120720302100740e0101801d1403d810104040d0750b034280717644c10340d8010040e20500549403e402c0c030138032140d420b0403a00103000386843c6c49560f00d07008005151101404100c8003540c090004500070314469004165000c14102407480c640d01121081d041c080c402107000ca42d810304102190500e40390086155901c03a8014020b00300c00d03540d620a110050219080b8a984180e5070006940416040e00c02c2c100a10b1140388100c2e0000b000f020045e141104500385140812403010401450042c0030040e5000190300d4100b241c820722804030441106d0113590060386c58184250200000d00440c2d540d0980f16200c2000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 855661789 1250 855660539 855660563
    0xe060d0c1211120c1009260a0602130602191205210117060105030114071b05010203010b180405040c210609210518010e0f0405190e0303041e0f0b090a 66
    0x17020384650030913111b44402d0703140c865090005100e550b407682852804080995801c81c02541e00c0d802245c1298262016111503038006104c0107404200100b10312802c4008280304000c1d42d0b40b07842a440c5c18000b01e00c00c002c4c2c0400e52020070301d0900b130610202a101c0400d44450341c4c450a54030615403440d07152510310301c41e95000103510305045c440c034051403015009403203803551410002c0e114001030000141d001d851310001c11001c600c00384040e501911040386400c0d61164101480c84c69803140761140d62180b03207400c0901000585083c4900f00f140c0190300900310040c0c9060099950400411014100070300b484014401c02c801c000c820000c21011a51029807010b820501715400d001c1c83c400c4404800d05a0305456141d03004080480c4100401090240c24a50302004503095407019209002c4040710b0028540440303503139001b030b22002d0300240021401e6240c241c540514035a03505500200001e00e40750300301c05010309001c44a4125410041c5a00c20307003008001295070340b1142c0815110004800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 855663039 1250 855661789 855661819
    0xd03020a121a101e14041e05040615020a0204050a02040f031211060106020a020904020a08011b0f0255020301180206030601270602070e060d0c1211120c 67
    0x1c080c04513440020710500d0040d5034200021303500e514031101031900790300c0d05000000300b050003000c00d690102034103502034030094a02814030090340c619800c0344401c03140c03038039000626030380c0000c1a00b0710640440d400324094543c0b00c4003e000b482690445104000c55260110038000c1c1007407452009480c5a64100c0700b2810804d069840320001e01990006801c084005030243c5007215a4640180c002024480c141d60307241c010900b1541c40c1000c480862400c0c0c40b6500c6000d4019110321116507084c0040e068180000000382005e14070807614010b150f2407050f11884806078000301c640e29a00c4000c211045c2200c2140701400c007207501e1801c902c82d40c20f01e002c0c104820142451070101581c05000c02d030840d1100401550b081c070340c80c0440026100100c0000b00281a80024140200f00b0b035009811800d0510b1030315051b40900419440c0a08204410080003503540d140303010441e402d01e048101492035a1428254482071a10b1656000c1841488100741001c00700e01d100b02c0c0d0700202d4050300050914 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 855664289 1250 855663039 855663047
    0x31b0307050a12061116050c1311040501050f0405040e1e0309311506030e03120105150c03130914010825030b0903030907060306080d03020a121a10 65
    0xa0702a81116000c540243c00015215802103041050700c006860308180c40c00760940d10341d8114078400d03140b0f40d1109080d9500c5003004220322501c0c5042c8401030004803440001906284a644130303032810000002580800307284401d042d02d000d480c2c010002d110180d52050004e81d6100038134044101c05600072003158401d140002240c6a0310809080340d40c1c00ca40a4100210320342d03403241d40c00b0a1801c60b00551400800ea4450285c0b19154410003140301404d00c80c3c01070885039540210383c82035200304809543e03000c03511036640c112036044480c80304004082b08030f036520f805a000c429520f884041050300d8452a007803074131003d40341000010400c3d004100e007601c0b0541000e100d4644540c000301031400364024103807080c0c6e01515102c00302c80300e181e0756a625491200d1084400c0710242d0004000d0014840c01805040700900f614941806401d09000c240c42d11244042d440006140e40090b403075003003078020001ca074021403c94400301305004404840005140500400c24420300011026040050103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 855665539 1250 855664289 855664309
    0x10e16020607050a1707020609011112040f05031c1a030a020901052808010c0f0906051207031e1505010504030f15060b13050301050f010305031c0b031b030705 70
    0x4550041c1082d440b80d00040d603956200103001010481c13600403560b1103038040e01c002d03400b580c1d41354001c1030141303017000c0c0050850303040480100900d40c080202303c020351203141d0402e81058000c20302d20100300c19440c0c41ba03e188180c4801c15450b10403500a012805159401038050110300d001040c0b00c2540c050405407514240d180095100134440018007040c20041a4100100c2008108451280080410354005107007940108000ea45500880c01030725848030030203030140d0745800c00d420034a0a02d48054898024032071400008418100054002d030701c690045880d80d846500d03030020314182c83c403042e009800c110b0010144842c2d0204005060751180c021a001c583d007010250102841a031b4400c0c5181002044d8840641d45520700854480e40c40d6004242d90040320b0011005036180a0616081d184014440c3c00e00084460041011420220490304480d41d08901d02410000002030782005001000089815209252051754140c0c010084844d40040440c116117030386540e40704115403104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 855666789 1250 855665539 855665581
    0xa020102060106141c0b0604290301060206010314070f0303170114010c060b06070203011d06252726160b16020d0b0142110a0506010e 59
    0xd030800925844402a60f001c0840392403120021600400550010b059900308c2e03004640705640780304010307521040e485e0358009a030b8038002d41142990b142130406505e4210510019061074881c1c0311003800088180f00c580042c1c590801c1600c0c0c09901c030b0400030440c04100500400924090b070000c80d148034102d00c04600008140e4034142500d100b550362101a2180c0500b0a4201d80c00788050700050350280220400341007020340699101612849040c50002c020380000d001d0006001080074005840300c0510307090200d03007440708011a0314400c49050104100510303005003040000801d120714079040c010a107400805165024410046043c4c1d2508501103443d02992505c040070004d640c807080103028001d5140812001929a540102d07034820200d0000f00d40d54604034005107c0242c010726400c154600354290f10400b9002c1d11a14401d10340d00c01e041013003d402880ca500c11241c85000c29603092442c1c601510f4041000b071410580d40e19083c0100ca5920990303400050064440340200354402e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 855668039 1250 855666789 855666827
    0x40f0f060b12011a06071a0106020f10020c03040b1c09060b03013e040801090305070c0e04021e06040b0c160e090d0e040902040c110d030207080d0b0418050a020102060106 75
    0x1801301000c00249502c40e4004032100c0b5682c151243d0139556001019000300a103030041c0040000c540c602d90700701040e28204080161048c040a190b402001054400b0f032f41070812500e81d04c02c1170192040c0718100039480541418145881c110820810380c008000c0050700341d00070b118403c0e604000d42204010210f12480d036821441d203200810507420070000e95407500541461400d911010080d003540c44001040d400b10f00001888000c11000342900802030131001b0444059050550008aa0081d91840d4101b42d01c440c80129400e03544460071a0014028403000b40e507070740c8120000715200c14000c0c0221406481549001940c18102804980b04c0d0500d8000b07003413030074541d400a0301d50205420001360403950300c050050050311103129140303000c3c42c5038440147c0d211204036814a01802070a0300030070180181700d018000f074480e40980303c1140125030b0100e00d514100022030014440d42140112041c508200d01c7c040c8000411242e407910b000ba402d40319140c1e2039660554800e41d016503801d44035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 855669289 1250 855668039 855668081
    0x109030801120222020412030203030405060a050c03071107050301061202040b01030c20210304060c02010c09092004030f12140d0b12030c010f0b0406060512040f0f060b1201 76
    0xe850040004ca00d15100316900509050b100c5d2414040305070078034411800f60744000103002c04e12070200031b4a07500c6013400d0024403042c40c0c82d80c50100c20b400702900110a11000891a0021070804e01400c03001e088060000c1044076681e002e4140030100b288402d0b070059240c007000030f45951080c010107481101c07540341c1e43e11642d104072884a03805007400e0405c0035400354120280b071074400415043e01c00c17521501c41648034142810120304403000b20014409680c90040d0145e4800e410400c160112508000001001d084075554a072004010f030801d82c070000300000e03000c4100005d045105a00c24018100300c03030b02e03030360892080d141010001002c120883d010b0200d2422801190040803100d540500142e03040c02041e0540c03031035a040080e80c0c901c5039440340302e01182c040e80f601c2240c01440040320f0174082e00386011405440c51040d0f01c07446002143c1c0600003820720044103940c0c455540d0082e00d800c00180941003080003090420702c03444c4a0001c2c8e580600942405014502141c200e40401a00c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 855670539 1250 855669289 855669319
    0xa0206010315020d050c0d0509150c0703090e090d1101050105060304080f0c060907080f0c0a140a18090210031a040f0e0304080a02090106050c0d050f0d090501090308011202 76
    0x2802007600714200350b19001c12000382541418025103004214031003c07180c407000c80c8121304d4181d5400400842d0300d43e209050700c0e85880081ca0600e0382000c1c4101c190fa507a07400606040b0381c8070712183c001040e0000030a041c04003080002450b0a9209115a2404149080f002c421402c2ea9800e04c15258060005c1c00840c0c0880d40c954024002c0208132200603103066030905440742000d004455035003458100340307000c02c801d55043c45803040030780d244005001c0d0300c0c0700c00000407401d2006010b07d6910864218100280340c032034a002078007902d1202c8801954040d46040756000c0c0c14410400c0303000701c50000344600e01c0d5000c0e010311301c1000d00b200c00b44140c04422806100040c08491392541180f515441142c0c908442071000340041c10411020b410301c0a10b600520082d0f0b40d0617401242040020081401c13010720202e14001e25074020b151046d65041c4c00d0200c10100d0058010804d6403500c1c29140e03008016055101c1d1030301d01d10a480c0c043c102d0781e88003943c6d9012200720a029400130741320303600400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 855671789 1250 855670539 855670553
    0x12140105160c081335150c0c0f061f06050c1009080f220b030906071d150901020c06090f010806041d030d11040528082a03030a02060103 60
    0x4140000804c01002003036503914022003d00d15503210f8804039101c03002010b141000c0000c46540e640500d4010310900c09507145201c441c4200806010344000c1c04654a00c01c0c500500c8190001354448040b01c0403030500039404514400d692482c00050796040700c0025070345001e4001e650302030310340d00040c09811b88816100d502404503040110b906082c00c2010340786a5103000041c2c0440c0500c0c1000030780000072003801e0b50021006400250b01c10505108001140d240001c003145d106040d450900e04160500442d01901071145480d180e000841100e05103001010401401c810b02c026030031038005010301814403856202e0000f40a8200c1034641c803643e007550091080c3c0350003860103000000d00b110814884612042d001650700ea583c1c20004204240c1c3c800c500450a4070124113144c50300d46413800c40001c4603280780210014400c403640204901d280200017000004160640541d03001c00c081080035210500d0480b036080035450910600300c46400c00005582c00381c400d940040000f88d00f19180d0b40c0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 855673039 1250 855671789 855671797
    0x1104020d0b060c010f0b0303090603061e0d0605060f0d0302072112080106080a061d06040b0414070906030e121c02070c060e031501030b070912140105160c08 69
    0x240500340c580112607140d84a00c801007004490300c3c2c00000f00c00c0c020a8240050316000c2c19032510a03401484101e030759541d504102ca420031000c6480b40b0780490148180c0c184c04144449590348840000700700f500f07228040d00700c01d1103040b08440d10355080078003404202e1418004040580141c0c002036040c0300c00c0001000c4a40c4010b050b040c0100031014640d1881c900026021400c0c0000386004010441540c00011060308014182e4007413089030705210407220f440907405075600d4006a18001b24996444580c07104000500151040c84074040004121101c1075044e580d21001400f443d00000f40e10384a485a986d030141840050300c016140c113100b01007550450b406403100d08410309105030700300e4101d100801c1d4041c440e1074200d284a244c050083d26455000404030300039080445540702030307140d03002000d066942c81001500b00e91034000084403a192503402c085882c010385007000b010710126281c910300c155060340c0248081d5842c110210312120035500d01201007040510a0300001d10800c02138 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 855674289 1250 855673039 855673057
    0x1303050a0905060d0c081003050c221a1017060d08090607110301050109021c2403060905011d1504060f060b0715060f0501080a180317070903110402 65
    0x141c01c801c1c0c4410000b05950300c01c01d803a480141d5221400032501d604804810341c083c81a07441f00606518644410713031180700c1e08200ca40305044084040300e182c60b82076030045509101200401005403280c6c0c0a03000700b150352049910411140315041c264510407140c0f22a0380c10002249551512000288100036600716012108094140518420387d298000a050218002c071300c0c81c00c1590604040c90308407136061700400407050040200c500100c2426695045200031104005904202d00460300801418242d2803d151a42100004113102d025004140a60b000d0002003003100350000e02003c01040c00b409a6103160000c5282102030350408403190741c030ad4092070004ca40320342c000390344400300c0d160f68100f00007410f000f04501c014815a01540d09003000086010000c2c0c5040c100030b003005140c1d0344161410020088000b8000000fa90001d00340800c0081a0900c0c1e540c1528029159034150711103405404007160015580501c184860030441350029040c1c0b6496001b50b040c040a54000406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 855675539 1250 855674289 855674297
    0x2a030a06050603040b0a05010506040509010308092e0201062408091c0f1b080f0d02040801020703021f06050108060d03021c050a1101290102160b0409050901051303050a 74
    0x8006400c2d00d40100961245114690018180c5482442e0308100e420681080d4010030301070005210940b110030038581501e4102984607110707e1101c00084002403217101c1a42c82213a2041240c944a0b04c8003400c0e04800c1080d002401540d489a04014041c03004202c41e4011001c132241c514441c502601400360000c5e06942541c6549180c0b8607025a254104143c00c000181c604844900d03456000c29060042d0584415890400c00341d612480c40c07502419042c1030104000066114901e10954110303001004484025520b0b0091410041d44910f0145141500000000011440c07030007103214803400c0d188140c41d25159501c41034103201c4080c812403003c6055108074420f01c8107644880c0c100d200c0140c00350303071115626415000c00400490386606e514280d681010b82c840c60301c0d80e01c15000b54018010103c610204181c0d000105d160001e40c000b0320103400184030001c1441d40650b0020b00039180700000600060701c41806d85422a04d04a5001800f140c07010203200000e8440c1c0020106844a481c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 855676789 1250 855675539 855675551
    0x90e01061413052d010f0e0709170c090f1515040303030209010507150e0d03140f040305040f0602010e0c01050c0604020d0203010f0c030203040c0f050d080a02150a0b01082a030a 78
    0x540c02c0e40c14000a06407041100c0d000740104080c9000b4090880540b00c80103602d07c0c0350400c8200502401581d010312800102c0200454420710410840a18160f000600c2401c05007815950700d141324800b580c914a000002041d100a142049603001102040340585180703018075645049000313403c68444c09040040400103840410003030b101c88507400c1d40c1d0711030004000e0070300e1210b1458101d170b600609061600740040300313406900c405503040e401190301203034000390741d1549012907a900c04d0390403011205001c08030124110382e05501440c4d660f000f5008407603013070035500010748550103620117960196005c1e80000d8010700f40170551500d13151000c1d0002c40d1201d49843d54005a60b940940304000031340c00300030441800150000b800c0100100144c0d0744c0c0b0036007803001103544007080f144054040d1400046103814070307100308442d07a4400c024010030301190802c820004050441c0b5588980018100408918800c1607562845000c40880b0503114060003401d500003846d8000a286101c155a100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 855678039 1250 855676789 855676831
    0x10020c010204180f2406050d0e030a020d091a090d0309090221062b08070606060f0f0306050a090c020307150e0f0d0507030806040b0a090e0106141305 66
    0x224040403c4030400b00f004c500d030000c04503c2402c0b01c2c06100001c412204055545c0f80d21041d0030041c0c0140d43d26442c08950303d50350740d4400c90240a0088204c1c01c00e100c00602c4a404540c085a0014442d20340c0d0b0700d001605e5070ba454400840d0b0020784485000e080c0410160f0000d02c0c0ca0240748181c5442418049801a65101c0c0c101c100e0f0085e0b050741c401c0c0540002c0f100b0f030b030040c40300510780d2140048903010f042d003840b022041c003d489042ca1794a07010200742040814041640c0c2603481051f401001484a142c603244024011040205040301044e551005110300c02d00901412054071070180501c0c046514041450000d000c2e0064000294001080045e012030810180704880300c1c95210003140d403003520481240b400281d11084105604080d59041e40968001e0440b90404e0f058075040b2040e0315001e0001d4010803581000c198496014140000e0b41c1c5100e07000010003404500003000060b5450002020750b07000c4c052060390005108903408c0c485d0f080756000c2d5400c20340748180030103032645903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 855679289 1250 855678039 855678059
    0x702160303090825090507111614090f0609060402040b1b12040f0302220e06060109080a110d030e090c0c010c0905210f0a0323090310020c010204 64
    0x90300154001400c0000500c8034010800940394428001c8400e0b41d98040040d90780d100c80b1419020362100151030343e0201c1d082d2489850150301c2c0110080554181524a100d2a1092000d40c40b50000030341480043c1c0d015840c00c01099403083c20f400c541140d00d80d4440742008000c3e00000e1400d0751080c2c1c04d000102d04011004082d241804c1241514004030210b40441d0307152405107a11018258404c00c400e10090200044040440e42e058a10b41a540880c84040f00d07041c0b56810342d81400c510708800e80da035405001034000c0c000c907401c0e21244007440d101d0343c2d90b40e1140702e801d0001c0c000c1e40d6001e03c03101090034040c6410ba4024000c0c0382500d02071050301c0c0016540c0d0400c1e62448507100001c62080c0c00b100f800e22503001d01c00da15042600c041442c000205096052030512584188842104000c0c5640c0c00d02c0445a00440881580c4400102d0715010b0000c0c4c1122048400603130f01610841f803a0b0b6103403c21503135240e20060040281e5071a281400000e035218960b0000255028800000c215501c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 855680539 1250 855679289 855679333
    0x90a2a0f05030c030601030c120c21030801050907021e0c04050c0309010e0105011401120f1811090411190f0e0106110a170903070308040308131502030d050702 70
    0x1940524006645070008043c030300006181550b111360815801003002403200c01c0c0c800100d0b0244001c12808140754100740601c140541d001360481856100840175035081e40f0312890710b03580300e91125520381c0d8070b0b48180306c071415007103800c2030240c0d01004c03401c0c04440d00d91800001300610b1400700c0d2400a99400480c05407007065420404091000c8103000d003c960a028649040071084020880c0e5272404001c030f411240000c50341c0f414408005040c2c0d262400c0341d0002c000314810b481062200c50800e00c0300340c005140b492020755402c240c2d060251181e140000031140581c3d0440c011642c070b0845d1070100217001c91303600070410b103040d4007580000e4003072000480b000003403128540d903400344d6140c0f000103400700f03008201c0010250001049800094030380c506d80d0340d02c00c66204145032900044008a803800d04141c0001c0d041c1c2601007070003c208072903031004104144912421320a0584c0d1190b011404040704528080135820078881000140c45507401140e105004e40b04840c8a0200940034250980d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 855681789 1250 855680539 855680549
    0x203010e031209012702030f0601080c0f150301170a0b0901090b220b0c1c061a0f030109050a14070c03020c060a080f182a0603090a2a 59
    0x4081664103560380c00c80b01250784050303408001c0c4007000440404910b110f80303504c01c1e1517404404c4002c00f425501d04000c0d00c40c0440c0200e04841d01c5584a0142c60b5403003105140140c41003001c0300c0350381300e45d050071802c801c192280c00c8aa07904507401c1000030403c5000c6580150000d10500408002044200300030368014160303980005015421402e040d00204030080014411810740c8440011403000c10800388500c640100214146459000c8000c0c04da200394507030310011000c0c81c3d603009c24102440c2c1c0480102c4040c0009440101c1e08800408418007480464550704d110501c0108050040c40d004254802001000001c900380308001e4060074070405d40d10200042c00d00f28403081055010860034038160f4084444504000101c0c00044c0454030082241c0c808806030700105449a041c0f079040e42880145400780c80d9160000e1004040128008400015000307030511003903800d050100860340101008809001c20700e0840c1ca41e02102ca50310350080070801c40190054001c0b0807011001d0015107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 855683039 1250 855681789 855681793
    0x1a0c0702040b0d0302100c030e01090809130b0622031505100608060d021e03032b0203070f0c0f02090a0b01020705060c1903090b03070f0210110a03090606030203010e 73
    0x12540103000448100050307280c0504070f000340c0c05000c00d800052032179a039000307420007084800344c0718801c6014003840e0031070712802e42c20000ca0300704004030b08010381451002510403410344402e8107050000e5516032864560000c20400c6000c1c800d150220155116116a844001c4020b41d01d80c3c0359141020300032388000d440d41d510024482c00800c0b20024000802c101c0c544200c8038209000001c2021540e040024850440d51003e80900004000c03400c000c440014280c1c0d854a001036034000000000c8005850004204059001c8884607482501e00441803961a0702d4042d41514058800740010315098070000311511030140181c2d140e018544c4100c00c0020003007894840b83c400039103400c12540000348100030a001182c0c040d200000c4070704503601010100b242d035100c6030500707664a0750b04d504450b0f00003a0000070030011a8104d03254500301ca51a0742150085484000c17000101c8008030300d003a6011380100300d6900414800d411815049000308400070b03440381d50380d0021342180c04c842c038407142507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 855684289 1250 855683039 855683047
    0xc061303020c031b040b1c0803090f0a0c170c03060106020c031203061e06070501020a0206180d12020c03040503010f090c050a030503040e0c07140705030c0307061205041a0c 76
    0x140d0602c421000040241d00800d083d60346034010a1800da071001072503000d070b07980d01a1a60140d55070880317000f0071510185840074004143c01c21188a90080760390491510403c0350780d40b05240001a204100341e00300402a0810342403c00301d09103068034603100011480f8607948245295000d208282c0201400d800030598200300e0024507090602c11110103500040500c10003250740c84182880ca102e08070455420081202c00e80040c0d618082c07040090000e43c4082503104459800042045c02403500b18030a060b40201c203c9211b94441c030701004030300000c2808401030400b40c2c164011b400d00d5200101503e081c9038451000c2070031641100d00300b0089030f454603211014880d500a40d100548400d80b002d000007421915100e944e841207114004295a8040018030860129820340d40200d50262814040c03080005106507154014051140b00340034008080d180303440c2c0000c0b036204031605a01c0300403412840103032000050500030003e603529030030784a950300800c8200c2c41c02c0703100321070811505441e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 855685539 1250 855684289 855684293
    0x30e010e07090c030b09010504110c0d050c120313120e0d050102030417031303050d110d020a020105061009030f0510050c120c040e040f061e09020127061101020c0613 73
    0x3c0d2a07080710103005142c5002100036154450184441c107462050f0340c0030a081c1c144042c1c207000d0707120b032141340016802694080103926a012008000100c00c0a003241c0c003d81c0080c40d0100d50317100036100d500c100031090550100103100150900341c0d44810b41045502840c0c014045003d5598004c0202c035140d5000007000100f00d002e5140c0128160a9101d080c25407901ca0b440d460080035200c0f002c4c01b805808200c025403901c0c1d0350030601c841013207066070540743c906e68044100a5081003100c40090b50070800007982c2d44c14451050407084119076180354095246072904101410259000d96a60259040280307802010f0b00446014004032000c4d0355452a0400103244841400381441200714000c01c0204415528825543c0d08503820284240c1102c0d041d150210080400c40d146ca056000124240c101c0000303254810f144840c000c5e03e84105085102840041501c0c050f202d04000700c815000500050f403180080520352035181c000107142c00640324407a440c09404440030b40c560802c041c44a01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 855686789 1250 855685539 855685541
    0x3051b011116050904080d090c14040b150901030908070b1608070210021606150801141009020f0d0615110a0308061009120605100f0f090c030e010e0709 67
    0x70240c0300407400303070414418000140d141400d05124044c40740820350301003400e00c1003040032641c0c041c003503100800000710180b51014982e180c3e4821820304c20050340c03c010280c202401406a9020000c14024080000e89070f40d1a41c3d800455083c0c0c10103580f002100005081140140a03203030140e0401901440e041c80c51750a0301a46012003010428807034280608a500010118003152542c580036840300d13808070240010082d00c1c030000e444181485440408892031401c0001a00d40d1030009002134510098000d08020042d0b615a625408246007000481c505074094000400400022460810f44d800e0b000e0503503440b508961216002d0b03950101005412101940c2c1c00c45c1510040d115204482d200945080750090840340242e19901c803440300705105100441c050326041c0d1444007480c3c01400c1800013000210307801c0c2c00303200400d0800300b050450000058120b075011050070006d142414650780203880200c0602c0d0925031580c0e46030b10005020b00890700700e0300c9000000c1031550300d00701d00c00b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 855688039 1250 855686789 855686807
    0xb0409050601091208390705010e0609060306060403020619022a040504021909020c0c06090d08070215070f0303110a140304052d0d030204060801140a03051b01 70
    0x9418402c111400b000044a4250320380c44154110044c0c40d262070a110f0351000e15000b00c200c86d03000100c1c6a40d4a40d01c02079280655034520000700c200d80d0720030b84940043d41d81041e2844d040754085010721a41c4060b01d80781000710b41c4400050030b6641415986e50105050390002450300c0c03200e050110400c50201e6040203581201a03441590031803540e03809aa90b0040100e8509041c0680d4481000509549a081c10000e80e0140d0300f05240b09503035240c4501c0003d4200c4140410b5500401c6280d42240c906a810780f01d4030b02d80182078203680e115503a110b8805601c0301c0c10881c1c1250120705e0302d600c0c7c4415030019060032401512008010b50087c5001400c950071072640424000302030003c2c041c0194803601c0600c4110301c0c0c80f0816901e845a041142c030b00180b034203402070807005601e1290000c0e02c484100d0084402060200c0310203941c0c4e0790301541a80130700d02940d400111010010004000140702c07001410202800410059891791941030404641d803101d9101c2d05135a4502d007040c0d5900100b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 855689289 1250 855688039 855688051
    0xa0210060b0304110d021e031b0a0b1b010c05120609090d0f270e070c050d0f110d030c140306090403033801030c02061501050c030906040b040905 64
    0xc220007800c0030708514050001030b1024040d1480c2d603052550030384403014a00b2006400a10180c112011004009603141c0d05012082c0240914100e4a1400000f080350f90408800142410f903424100f01c0400c0c50f90b004840c10300105100f03140350f200120402e22070040301c1926540c8807580c501000c40302c84141e003c041c141a0180180b0400c101d43c082d00403440b540d0b00740c3c1030300d03000e60680405d14040b07400ea046c0044000401070200b940b5640750314071005160403501802c510b1850355a41c0107007540c0700d83c4140c40140a41e0841441b101420784509009100c0d0f24040c10142d6006924803489803401c03641d0300700786012a54071010644100d8200e061141c802030b46106003451454000b0102e02140c40141009082c151140c4507480404418000300d221440810f01c0011307440c501411a081540b5450b5140380400d1500c0003030310f1f03114400708074944500d408517010802c1c2440c40c0011540c42d4007480712100301e40014011204190b031044001c000900081d10602d841e9400c003954481128005412 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 855690539 1250 855689289 855689291
    0x80f0d05011710020307120f050108060c071a041e05010b0415060504090c032403023c06041a0c1018060504050c040e010c0306080c1c110d080a0210 65
    0xe00382c001500082c200c6500f20031030805a203945911100f031b11584065400210000d0414441c20321104081e440b4074100e448210481d40551142c4402c0843c912506101900c1c070310360000484c3e41c0280d00d400c0650450b00c501d400e441c800e404030500c0a0719141c0d0b082d044400d651101d0054015107400c0c015564503001d45050481180c1c42c00501500c0e9104605c0b0302c00f00c05464403000d004460080e8444420500d08864420350582c04140764102c0b02d8031804101d1050030300d80403078072120240300500c10200c4140c40d07113503850b200b50311612003e1402d071611555002e4000c200106075a079010024000341c40381c0c000c5003911072034140c1125003484801191607001c6854020300580c8003101e00b003401140340c2c20210004070303034480d800c00c1810001d4130a0035581140c108243da40c8181c0e01503002ca419856540d408000d12900d81042549030b08040d140141e0010a00b28004d84240c1d5101e081c107641445015000d40715040000030035135010401005070f1f020320001c51018059178050084913180008140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 855691789 1250 855690539 855690569
    0x90705010e10140903070305070e0c0f0406050d1113030b060303120612150f0106030b0f060a0518040c05040614040806190f060308040f080309061602010c080f0d0501 73
    0x4281c04408204500b010440002018031032502d050301250407005000d0280d490780c03900c9041c010b50750702043c41901e421203485070001c0d48001822041d00c580000d054001850302c3d04d0607100705d030380d50010b5a00c17002003550b401d0800c0603421601c0040c41105a503003450030007140745080580d04031400910080c0aa0410402c5c0b0300c00104a00b00d065001d1021540c1c031841c1c590149900c0c0c0b500d0b1030b80c104402c1c03080303c0509111200c060700718180d048903000d50f414408008940140408050782111142d0003608c14029404160b0051000d4410b81c52100a808200400350001a09460302c2c079001e003011860003c0c1c1401071981c08144003c06181b0f5044492400f441e081e0b5003580e44000402c859184007004020710581031480d00030312a109081903080c040ba5407282000b00150b07000e8485e004000040460000d00048080140d42c0044801010241000d02a01e0304644401003002c041381008401080c840004000c10b0107440c01410800e50f083d111101c0f01000c0084440c1a002000700001420b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 855693039 1250 855691789 855691817
    0x1080105100b13031e0803190507020a21050f070807120f0212070f12120b010c050316020d0b0a0b090703050105130903120216061b050301031e060906020309070501 72
    0x3680880344c2c403d0121031000171007800d4070030a90401200070200d1400000384850307105c4001110010b10110001009140c0354901c1c240c0e51040407500007003146180700404030f0395240d001c084c0c0b6001085810b100e4506241c444e030f040b0700c1c3d0b80640401c0310100c8000c18901c0070702048004440c04100030f4107004200c0303181640e0103581c40c100954000e0075260002804001c1102219000f030b4080e91007002810070b552005005403c0c220040c4000c0f0640d441d10b10140469031194010354501074101020718a84401941000910007042c4800e13070b0030440c1c00040000007840402c245119842c801000200214032900700015003102601e84410581410014040e03507980e003026009529035610006414080c9140036076510341507190ba00c112910208883c0b0750104400700700c0040301d00c1075008110300c05100ea003c008422444004500064051006000040c01324035a10b030b00d244030b200c2020a0b001d007039898800f5102200c008460300c1d07070044140110762200b04004c00182609080c01c1200d441c074a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 855694289 1250 855693039 855693067
    0xc050f09010317070218040b0a1a060c0f070303020a030e0409110904021807051c0606020307080a050d11090306070908030d0c0e0a062102070c051002031201080105100b 74
    0x40c00b01920070380080355407014200115040340c407400d602421085d1410280561208248821107040d55106504800502000c0e414800c21010000807101550200a40741c14001c154004202082040c8a42c0c5a41c03100002c0801181000394030941c02400382d041680340003840741c00a001800c1c011810126600001068055400058101510081da240e656400014001515041c81c43c0e4140a0f1a05201c0290307031100043c405060b4070b982d00031888130400308103022207243d8030078800160828480080020202c0c00280340701842c0d490700606007448500f480045491048030f0190150b000140b140250600b0300000d40c0c04502030800b80503881c500504103032a4443c86143c08142562403c280c5000c5025049142c00d18001500e9035000715143c85010b0701d0f03a032540000300710062030703c04509542c07003442c001c03200001d070f220858084d680d00e00001d011421818440d000e080d4081805008440d5040304643c0d4000d1010307000115442c20031658040709000309400100350840108006000c06200b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 855695539 1250 855694289 855694291
    0x4050a050f0120030406200705010503040c030c0807140103020a020607051e0c0c01200706140f0712030c0507030516052505030d0516060b06090d0f0c050f09 69
    0x39190740c030700c811490300102c034080c1c15440035055102c50700343e411150440000150080e030f10503460304121a50200440003468000b81403000260784501002d10003135100704055904680710301410f207171450b01c0307950302c41c85a20300d81c0002020303a01442d4100040c1402e640c050b62060000e090441ca4146d8858000b034448400412200900c0800103007003c403090308204090b03038500c803512070644410b074800f000c980b99854a044a800100c144180b18404c00160b04a19010100da000801c802481e0400a80e10707001304440303c2c1241c150500c0b00040f032050950080c40305034880da0350303030029221000c07002d4101c40900d0150f00c1000000c0c0304040000740c101003151042030980c041d4043c01042460700500d40605500c80c0c2100d80030540b1131003a25090f120851342070b140101e05072842140013000440b82d0340901c4510b500101038001034403000c1121540181c0882c9030142a59150403d881c0100306030072030b60750382190340c916149040424010607000c0040681012244580e000380360070300141d45104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 855696789 1250 855695539 855695549
    0x20d0501180f1208071e0e060d0b041410060c05070e0702030915040812073306080604030f05160b011d132607060908030402100c080d18051509100204050a 68
    0x10f01c43c40421215000701843c00030501e00911840c0d52700c4155048501809036000b04601450801c8000b00f11035030310010040c801c041e000e20048000d032a00108403448040e580b800d94a6004000001c2140f010304d806141c8904ca458009603618142d100c00d11401800580d80409080028031091101c0400810156540034170380d10540e850701018141904501d08060383c030500c100c1040340c50b4111061605100c0c180d9110480d0820025540700200e13511b83e401214010300240710340c0400303203031b450049024207011511440d000168445541d5112841c0b00c1c03e030040b0318008800c040c1140c45811080441c0d0740b1521f28481c81410b03a0007591050050040300d01140d100101c0e08601030100c0080d101071fa01c4043e0041030600c0791b001d0130700302940304e43c0c0140c6080e400b940b03120a44200c1580106043c00307000ba84070f100d180c542030301c04030f045009000030341481514221201552000c90006c00ca44c19200005046290720345c03e00700c460a10b03012550300c1a84060340103100c00c01a035503071706400c4000c0b19 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 855698039 1250 855696789 855696827
    0x105180c101d030f0303070306031406040b070302160515160c0507050105031810020715020a08011a0d09060c030b030a0f03210216020a061407020d0501180f120807 72
    0x1100300c0c1c0001c0c1c144500301134050140d11010007041500c0d41d01d9088042101c0c00354003200c4103d448000c24541b500e00440e00038248074215000b0400c518030035030041c000310004a074a15603c0030341e41e40f02d509001d00c0b550792136030148041e42408014840c95852403010b04840c241180000c4403075940c036482d070005100d580e0501c032020002920302000b02c0c5903015800c0010003035034884d1821803003c000941010905403a54000304003503902004041c0b007280c00f003226545801480e40e1a108042140044141ca050480c22040c001e0340794441960213825405881120081411700d1252402000c0303030b800c100040e10960215280d0f1005c0303942c03298580003080d094940741041c1d640542915200c0a05078000d0b1903050720003d07501099a202c10b891300e60701403007100e06d40200b41d40c0390411116010100e120a510b0001040294014940002c10748a06271091002203100e8a0a010100101c06e90034415078084800601c050100060304800312203001207410154440d0074050310080c8105c8801d9440304120b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 855699289 1250 855698039 855698087
    0x3020906120a05060c0a02102a030b030a031e0507080a0305060103090b010303021501050907270f0f061227020307090c0e04320c0c0105180c10 63
    0x7103001400040c2225801c038085603a01c1c2010b600443d8240e0041607110010300912030700408420150140d000c00c5102c01e00707540821040d041e01820b00707404aa26504c24140e4600c0000c103240c03000d010a5140c42d010745c8074141c0d10400c0c2c1c50343c00422010b6403845400c0100401003040001c20b0081604c4440415141c00104d6540c0c41c070042e00100002c5034040d00c5014464000010903500183d0058413940e04403c01c0443d0340c0c0d40003403060003401910140081101d081804a00594184041c001051040c8c501a0703025640c964958144110380c000e007042012055007031000a42211038a00b000000c0e45042000c0b10340c00e40740c90000d145a120342e05103105400b8075401035590402c0910046c042c00320042111020750000500303801002c0a03006d01850401c16540c46e50490b004105d00744010700784024008501ca4001c840da9008014140c0102400c14040040300c0d101c00d1003414418040074082d28080200d01c807106240480c04003607613104011850000a83c607034010702d01036411800e00103096074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 855700539 1250 855699289 855699319
    0x402101d0901090b040c0804230102040e070215131a0403030f0c030510081516180e100909121202211b040b09150c0105040f110a03020906 61
    0x9031802003600c0c2644a11401d001046140013540864440402140c0c00c01003001c2d006001d4030b486404036409050720410480700d10440002029480064050800040c5803a40303e840f0341c0c0f81c2c03d40544406006034070280e03203080064009614690400c2c20442e0f560210107081d9540720100740c2000000c0d141906801c041810540650040004024010320500040d401d0020040c0140070407030702d41d810003081020008545101180c4040445c0194001c0241030381c0301141c080101c41840112010000d042ca204011100442d40c5400901070f01d0920100d43c0c00e00a00030710840e5080d810500c60185030903d0040000d00c000500340e108503440c1011000c059184210900034010340807402c2c4616410641d12034601600300c0766903c074141601c0040c11280304002c0700314079400380b8040c101c290101007000a000c3d150005c0018081c40c80301a10303c0c40e1a82c2600d250742561401c4d1002c071180041c910392a802c014031160310b84400384d01036071460350452454000404d10b040140081b4001c52450074680300d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 855701789 1250 855700539 855700577
    0x70201120203070e031b0f062101080f060c0f0a110c21012007171b010b03101512020a0302040c0504090f02040e070806120f03040f0905040210 63
    0x600c48030311000464a901d8012405130102c0c07070780da120034030a0040310240f00b4005001109110001030181c0001450413840702030014a510541c4441c80c0401106441860031680e41d5402e400380c41480080e003000d540d0b0b803401d90f02c0c1030009443c3e10202881130050540c8000c02c54161141140646003c581c0e084040340014142031140c1c49068100103580c0300c200e1510100b581c1421328000c008000c010780c181008500900070740d4450a840010401c12103c1c0119050700d078101c0d60443c250340030030b103480d0054802c040f42210700c03140078040d651109000f20f01483c09120500c2d80c1c1c00d49403818029540f1402c0f111010030918040c181d804040c01141c0c10a54681d1004000078640c060320400c0201101c03d0040c02c103400c0f03845800e0010f41081c50480480d9414000d8a044a00c0c0341400703075154031140350a89655400401103600720a44100780901054200001030b1800802ca000d550303a2400e00c40f51741151001900107841d01800c1205200040e16035130328182e030b10000d528003000c070611983c103466 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 855703039 1250 855701789 855701807
    0x21b1e0907030f020c0a0b06041119090b1201064505030a060209090a090b010506090607050d031a0625020102250e0610020714060c070b070215190302070201 69
    0xc145241301060300c04601400299101007107001e4000300d651a6907503010042a00d89080314801080010311840c104100996050300b04401d060502d040c00b9a15145440c0d80341e04249812081908684010000103812803c0c642516204101030444221041c0b8a0000d081203100200c14940b9100500144002d0324441c9401801004060711140b041d0b40c1010030180d084150400d103e40b103140c003c108508018480c1c8141c2581c05087c0701b16682c40c000030440340340c21003c2941d42102c030400000380007400500540548840d00e0321300007070144020412402984072900954040c000c01c00028aa0312020342c40c103100000c0020142c2040112840100c0c2814503407a01101003041e4a05001c2014002121060668140710680009a230300c01040195017005141c41d240544c210100501058800a0400d080304070058003045c60941411141490503000380c6c00f5880f409000318103002146040141900200c4c504c081e40d41c00c01d002240515010b92580d0103400925500240f00d004590044081e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 855704289 1250 855703039 855703061
    0xc1011120d060303020c030d0f0e040b12070f380903030309060108010c09030f0b07090f06080a0c0507020a140409230c03060705160f05060106021b1e090703 69
    0x10545850040710100094402808120b025000e021403007410790500207000d0060314040d07961580c903032022034020303200e04400c85541604552901500b607035a4880320107081003100c8030390003048101e25051008094070083d40040c0308005d040121124030565a25010f80500c4420310705024400c034503100744d52140f00b4280c04541500002c030400ca1805c00c01f01d00c0c14100c43d40f0000034848800c000200310f4100f00f003400000d1940c241120342c2d0020070400e10400364046a64101403e40e161140320a0107560841d50200c40002c00d0442003040450b110b0007442490513607400c005080612075030004424180314003030884110100b0f40c06400941d11600032401943d0001d8520141c6560190740c0308030b080a040b40100b0910580000c26460300b40003c09a00c1075a140e82c8180c10320111407500c0c900d0303881c030b22002c1d02d0105c10f0395010390100d0b409012880c001c1403075400500440080d40d241d5030b0341c4e810400141c0d129000d41070204640070703040212003101e50b80448018205684521054000340403003580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 855705539 1250 855704289 855704323
    0x4062001052719081806074b050c06030f06060a020c04090609110a030c1a040b0414120706050a081305070305070617060a12081c0501090c020c1011 65
    0x20503013030004090003001182c062142c6000e141d0000e0003441218070611100500b5a80749030102070180440c0020f100d48094020660071074940c1e80120b41940c1c01c7e214240d0920307400304158500402c80c3c01c04c04109118001d446081c2507152810001000b900010300c0301b4041e560015007411500c0c420300160000b864010710411a500860501d1303402080340190850300e01c0381c2002001250710300f22081c1821130794001142010075080070140b5805485501c00401424418400410100c1c003401c040c1000e03142107a00d400b41c2d4000c0704100025124010581885900709039020f001d00d585c0304045030008005403c203000c1030b84030018031040400a181e405003035400390302d00c0071040100208000045803100d0b51541411a110318038045c1484064410503403100e03411078200480b420080c9081c010601031840c030b40c1401a5181c540c01d001c2030620f101414103550340c0050085013154450000501c1d50707171000700056032046000ca84840001d081034014040211200c1d49020800c0050318000c104480c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 855706789 1250 855705539 855705583
    0x9090c06030403092310080f060f0102030c07031b051c021c0b0f0103030e01110715020f03030a0c180b07060b03011838010e0a02040b040620010527 65
    0x604685040c07101101248180200303000c80c003405100303d50140c0070b440040300e00c02e456101c0750f040ac42c0212000c00ba01c5e05602051154000d010400e00c02000154020345050042081c00390700004410b1a40d0413803440740c007600c00e41170180c1d0300c240340e02d020300c90b81610302c4407a003182403441030f402a64520008001d00142401c201c0070048070ba60b114126407094035034030140141d81c00151280b040d40485011603500024081180d140c0e001c00c4c41880844038016180e400c08a80703115402c43d48225594201d4545520300100310700d80c81440d0018650050b54240b420508000c5010001c0c4038500340a813030302e91130ba480311155503420351200010402040804000c281145000e080d9643d440b0301002c0b0f507042902d00c0e2201084491110703800040e04100003a101e0b800c2c61104828298040d00c401d4401d6800c2c4000300c0c0b5405010000c0020340015140c5000c08a0300b480c229219101050202f440c0da414071007404207098006200c4040d0501d426081c05201e01420411880e04038040c0d4a0f070360007040c10f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 855708039 1250 855706789 855706829
    0xd03200f0d05010b0f0915071b140103060609060503091c0921030c020d06020904050f2707060507060f142505070b061f020304060e09090c0603040309 66
    0x81400440c001c00501880c3ea0340e00c4144802d000c0c40d5507000c0c1c0e80c10f04104000851614640e00d1018042070158542445000c0e25a0004140300e40e8999105150032507090001401c20016000c03007030710900e424450107041c041c0c0101181050712a250a010300803010a2416005101c0d05091178950341c0c0c030034410543d140780242110b19610806000c190f04606030b000c001301030981043d2031901602c07588040c202a0b400c1c403020740104601030f47c030300b5401e010b1f02d001d550355030040b64010001c0d42001d0209041c00da41c2c00c010b144120034803107a0b01c032030b03075681d02e0a071007010a05004503a440e080481d02d032805070030900081d080c460b011100040c40c0503001c0180b103552074500c0b070084003910040308c000c00a0000d9038541101e002903000200b20700340301e103500040100c00d000c0c1d80500043e2502d82000c107680341080f100c486c454600340150b0400301303003400752680c0a5002c80651804607070000c0c0500b0401e40d0941c4610942e14618060070001001406050245c0c03040d600801c0140e01142e200280f030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 855709289 1250 855708039 855708067
    0x507020d0506180c0a120311010f06050906030105070e0105130b0c070303090806010e15061b150a060501080f07030e0d020a030801121e0201120c030b030c120d0320 72
    0x45412550b140b84121a00103500c800180a44c090440503050b490890708050403c0240c0b840d02c0002c404114414040200c205028007a01044c15405000800c0b25800c002c2082040a00102454081d80c036100804c04615071015009170000c10a0900781d0390f600e60314204400b0400350f80c00902101134001400c0d0b2160800003490421680a40c0c0c8400e8120303103d52516032a60000c1c81030b600e614040c1d01c0820301c40c030101030030480300f40d400403c200d20b8205c0b840076000e000a5002801899500f180c0e00c03980e180d000e00c0c2c050aa00404c1240100121400c02001034141c810190000c0ca0070641400001e01d202d020b68801d5440c0c44281040340c2084039aa0002580c070060040d08400040c48000005001c1c249840d032144041c1d0f000203582044048a90850704444811205904115a00b91304030b051400c180700340c21030560203a03000329642502e20203040c44c0007100c00800d40200e84414020650510101c1e140b80c0750000c9250125004007480584034458600ca41003000c0d250340095182002005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 855710539 1250 855709289 855709291
    0x40303021b0306010e010e0c070b13060f021c11070203191a1003061e0507090914060f1003090b0c03040b07020c030c010e040906060b1e091c02010507020d0506 70
    0x40d91075100c1c030304040103090507107a150a00c910b1016114020040c00300c8194036480c1c503030000e40390707048904162241d100d05008440594003a20500e10989c003200c140900390003a0b0b80c0d1840740301e0041d45051000c1c0500d103000d40c4414110100b07156200329000705500108222003440d500141201d18060004161042e02c905200341240c1d9402c10b140e03c1808005000c1240340b0401c80c1c9202c01d1001c51844d01d440000e0318800c014003411100750604031244d04c155114050045000e603030780403241410441c0c20003c8171b20f201c10074410460a1010040b40d5550245400041c200c1135502020340f110402c81a0302401d400c0e00002d010000d507130300300456295a0009940b0540c0603030407110140c0c84881099859104e1540c03516056005204500d5903940200800303141d011015200103a038803880d1711020112440394000b03420400c40020300240558914003400031121600303000d41d152015000004016180054948503c2080109400c05580c0910306440340035401800c07101440c0e1461800c039840d250 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 855711789 1250 855710539 855710563
    0x110f0a0507150b1912030e13060e060102010c0504080c12160618140306040803190203090c1906050904150e0906090d0c022107030f11042003040b061504030302 70
    0xe210045a003c0f03803106804000715442040030110170011038030111030704140118602c1c0c0220510050500354080c0e88189030060010041194a03424500c000a00352141203050004200003484103004410000c90b400c00d0800b03040320040c4441107000d0405040c034121681e166402c05104c40d00044207034102030200b4603c8000b04070588950745070b150b0384900e290b040b0240c40d095130041c000200008c410500850304004c448404801d88110306003180103a9104039035007040c68100041603d44e42c2042d420601c1ca5040f45004003207241c2c14440014424001c2501c103900c5180c442000e00100000c3d4545031014101e07a2800190307505d0801115903030750605440565481c42042d00c0354100b9441800a58529a8000d02412071026600100252540125503402d07084c0035a1000200103100e00148410a51003a16841c550001c240100821913a5415410702500c1e0f1420041d85441c080d5000c580e0303c154498091700031515640c002c240036000015081440c0c06001401109164001406a0b40340ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 855713039 1250 855711789 855711799
    0x110a05031201090507020d030b0f0d0c1a0f16080910180819030804290a0c020601030f0201050a0201140a0b0420070b0411060f090f04110f0a0507150b 66
    0x641c0c1c031140f1100300c403021605c0748016041501c40340d210703e110381c00c010000ca00c001c211844003211440021290030810701c0c11159000400410010703103103041941440d900040c140c140c00c10002450001d294444d41002031074050345172584d00c0c20400c02000780e41c91580003900030b8400405425014000702100000400110700f01440018920b000082d06c2032200d03c0034103040c0c03504145075001e80b286100a08201c03001004a039120030750f0b100c0d80d010b101402140c06d0318013016052100072141181c1804d012041103400600060012071122614440000d50a190003540c48620030001c0b8014000030040100e214803075400c0c402c00207400e801412090200b110100407240d0101e0084002c20f58040b10440c1e90074052201c000400d420003c002d42c042d0249048805140014000a4080d805008038280102022a1441c814189034503001c4e015801510100155207130081642c00c02c0c000c0000e1003181410000700750300340a10400549140700d80c4180c108803071100380008140a0a40181c5040c011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 855714289 1250 855713039 855713041
    0x8100203070314060102030d0b1f0513172a0301050907060201140609040210110102070804030c06020604050604080c0c04110c012405040f0e060703050603061b041401110a050312 78
    0x801401c0d20703c5402403c050300250314109400c04020058007a40c40444e40c400382d1f48401094210704006009c1a0705c04640d5615a28111a56000a010408d400000c99200d42917103011000800103448409d0b1203503441d03100145070440c4034110390004103454154140d420441480800c07800010020203a49440c0c0082c440341d800340395040049003040300c030954480710301c0c0c01007005406c0c089a10b154000c031500e08101e96403000b04880b426640310260840c0c41c0c000000342002071101d0880c401d070240542c1e00c044c000c0ca0a1a40341c15039074070006000030b04a2440000e880d001c2d1102007100600d10200500244030310100c034840924642c101658140d03d95003070004d104a000c1414a04460080984412041c02c5081c24140002041001282500c6a076a40fa07400401c8004210360380c4a00002c3e6004905481d00e0000d241c00c20501809580000811000034004885244150f8056070f4990040510b2500610300486489040d42d00510190007003c00620501c28040010091586105444811 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 855715539 1250 855714289 855714311
    0x18190318171005071d04020a020c09040c080d0809030a080604180807210909020c0106030f060506130b0609040b030316030203030f06010c0b160e0a0b0c0f060405060619081002030703 80
    0x90350010407100088402170000300d00591510b94080c0c503a0012501c1140e884149100100c0c1200c0c005440507200800c0d01041001540010030106401901a240006450405d4054180e40380101c540c0030702485804000140580c032a03500200c4031701025802c8054001c1c032070038081030039401400c050341e10314041c0010900c01b121001900b659801d50342d5483c003100f450181c5110081d0001e4180100c61754070348900002060600b01e60702070460285034005100e0800d00c00700100c010400c000300c6062410b02c1402400c596514050315031038070301601e010030402d54400000741148109904207100c0551506d40d8014181c0c000081d600c10054241c50b14200e07102c0d01c0065840460b000401032035012040c2c0050a50b070462410b00c0e1480c0203a0800c10084800c40c0f0000c1e10500b0300c0e40185c0e50707404000c100404042d200b00170021030001c0140191400703003860385501d40c80d5500101528040c004425004080082c0501a9401042204140c515414000028401940c404e03600f010009080403483c0d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 855716789 1250 855715539 855715547
    0x170a050103080912010b0402030103030f030e06070801150207030b0a05061c08030a0b130c031a0d1a1902030906010303140a09150309060e061819031817100507 70
    0x30581c1c2d0009503282c1002000d8003004400040e0121a4540f5520b6050501807500c0d01e002940c0607500c241c49858408406040040440e0540d000394a11580040706101401e41c01c10070a034103641c002034045505140c900c0040c2d04e031840030390000305030710107450811a149007294880c5000c0d520844200b54000c05164030400340000960003d04500e130700b000846c1c10044158001040140040c0c010314200c009030000c607003110340c01d841c40d40120341c40e0354107644107034600840c030003450108846064500c3e0558035064040f0303014600c0103102c075034200041045040085814a1403917000e00c003e44d0b69191403145030351228000e00c01107012603013103100b202180c1594401d0744e03240300305680c82c0c3d18224502100704008054220b40c800a141c3d0356030034040404c8041c05100c0624a0351001002141882c401d20259040343c82101540c540104900865a8081210640c0e840d41c140c0b801250010784008205242421540703c206602c461400c010b5014801003414096090445001c100650354a03405a17 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 855718039 1250 855716789 855716791
    0x171b0a080a0c0204110d0509060610051e0f03010b090a14030c040c05040b0f120c091014090a030b04060b0a290403050d020a0507090605130506030a080307170a05 71
    0x2003180e1028401003112520824400c405540024000305145000052401c3c0e2680446074100b4501d8441003005441082004080e8000c0000d0310707070b1500311101500091650080c491985c07411074207510002021401c14055039820302e10f14411666a507900c03034105200d41e00900c8503c0c02000218400130354143c0071031125010901c0a0041c01d0920012400c010043c50f642c05000b084c03003003d1101145c429041070107880d4024546000710764a91000010b910700a030020035002c0030b06810803501019446107103070b8034840e00799401d0101c010810313806040100e00403c2401504408030103000000d0044c0c421300d580c0154001c030010003107881500d051003100c2103180943d81c0f040c0200c0c0482c01c6c419808025500c107180030408102e040907180ea943e01c1c100560500000300680c481c0c0e0071001440824821000182411501040364502e040046921340380b10b000320502c0c0550395400940141c5060100e4000c00b41c1c4856120340d02e1030404030141c580d240813081d001a001c00c5900080d1240050311840b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 855719289 1250 855718039 855718043
    0xd0b041b0e06040b12091f0c02010605030d0c080a0e1503071b050607050c160f03140106141302130b0414040501080c0d0503130f031703060d0311030403171b0a 70
    0x4c0d450840f0000005a40c0c400250000c451481104103846100501171001a040304642c400031a603841c45c2c01e00282503c9035a040780703101e5040704170b091071a180c1241246403115030040c5655102c2c003070075401342c8a00d4440c83c813003074100c0e149004800740300811000961041e031041e00c1d0750000e812030010884840030303050745c010004da00c8540415151401827000c0c0c4060134124044902c451058139000c5100031650303120240304018818184204102a9417003040d83c131841c0d000f0002c141ca4400706940e0b10142000643c02101da460100101c06441d80444070464442083d02180c2c543d0343c6040b28140d0310a10500b01d980301e000150200f540380901400c0c0c121920080141805409a81000343e0407040744021225440100002000c181401c04500c0082c00440f103032081242c950309000314010700f074403003012441404008114031541c13407a0102c624141c1602d080c018910410081c5490f611554002404824002d494001d1040130707200207209050342c041150010f030311907400980c0d44180c00200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 855720539 1250 855719289 855719309
    0x8060703060b16020427050a1217070f050409051008160806042a0f05090f040b0f04031809060f0501090b0703052107030f14060a0b0d0b041b0e0604 65
    0x3c8009460326802c003aa45060405c0c020040210b0300081100f10a2280d5044030705801c1002118180610058118114501810090011680210041060000204450b090015031003694510511810a44000d0040f1000400050038503e0b240e520300c1440d0710648a141c401c51050b00c2540b030495403030300704494166008202503101c95075486000000715007101d1f2280940c0c2d036028401600b6000c01001000d55407410514175040c50240061038000501810002d40329400f840000385003800141e078407000442050040791200c0c602101c8006803490300c1d800601518001040b00304aa901400460b41c03c0740e2030641850340d0b030006440c1c4001c2407140f038058102c10300000e404207000340010401a00c00041d040303098400003104048a5006403103010009654001002c29001d083c499210080340c003000a800c01e1401d80001a407600c0385000310241110041816030b900802da130080c100629009009211800c0c4044600b0001c1c0e10841041c00041c004261618803802c007401218150303030b90044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 855721789 1250 855720539 855720577
    0x106140328060c050415140a0f0c0503032403010c0e10030204030f08093307050a060608150106030605010e010c02033a03060806040201030b03120408060703060b 71
    0x114010803080380d454840300034030030890000004400e4030035410704800f507840359500d55041144200c0c14015000c49442400300351074200310240080c0c1e003595552010b0380351070081400c11040c00c4807036a2503440b0044c002d101c04410301c0350900c070540d002d94581320303c40701900e0101d60b0441014203131407600b4203420114043d00149000d03414440c2104085800034203000d460507980e582c81e104620300201c0300303450100c00451080611302e0402902009485d800d902c0e0184960342c0322405805240e4002d9031817140800054007802c2241c1446074581aa0300b20314200302d0260341c0d508098071000c41d6207528500207031500000c10a5800b920800c01035075012b95900c0e81c0c210b00c0c0001500c059107810416680762086407107901e0710710301466101c102c4192001d00131080c1b40c4810500400e46281207080b6040c9800c00c141480403140c000340c01a4000d40919000c12070008020110382440680300c640184280d000501080314100000c1060003120070359001c0009564035040f2051a001c2c220f81184142c40c900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 855723039 1250 855721789 855721813
    0x280c0e15030a2702040c110d02030306090109090b060609040f09080702040b060a17181b041a13020d1401030f02030c10080a0e10091a0f070801090c05090d08070501061403 75
    0xa0f0103000401c1b81401d00d80d240c1a034440140349864014026940160f0001003080781c90304011401500602c1824024008442c0c076556451046000501c03440c0200008105000355070b8594200f501540000142041010503906100340c091f40070708001d07401a402c09584400f5803d18204a0302c0d0444181da440d41520101d0000004403000a04000e21f100c040078180c41803a01c0501428140303040910445404641100c01c0c041500d00f110000b1120941d809043e00702d03511900c50420103d01c0705203006039a0031844041400509100e80300040c004c42078000030040000207403400741442d000f1012610603004480801c81e809000402030000540c0c1040811800b05990304482109204003042d1202c0c0b50842090340304030341c0e079003c040c0d41c1883d903010901404d4120041e915045100a2000c0e0034519220b103018200074418410080425a2401404880d5110f00c0c2034880031000188494152141400c01e010300760040380d0145c6803946444c0c4000364150407943c80d0040c5000140150102c00c00705 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 855724289 1250 855723039 855723041
    0x3031e0c0403080a0e04022803060b0904050421090f050603010f0608040c0e130c0b0406021221010906030b0702150703150f120b280c0e15030a270204 66
    0x2030700d40d5105000d10070185840b1591180003602e003c0b1000d100e0b07042109014a2368141d16448858a502410302e040010b101a8144030308881c01414180c1d00403d50361141c4ca4090f0500c08604520280c1c03885441c2010301582d481003c100440325444400466070383c591040011600c400e00c02c01824a24000c03081040d42d00400090b54801d010341c8402d50415559002400d504004407158504032580955850030803200d2100314015000e0000308505140c104640a9134480001c10529510040450340d64071500e45802c0c00d02c0714200046c0b0004965956810200107050503000c100c13a91907501000503203c070710000e240c41d4200c2448108070754503101d421007a00280005544a1342101031503401150b01c1c5013003c0954028515024100350407101420704406008000c3c025418020240c0103145200b9030140b03030b1290000d1b180b540042c01001c1e0210a0310301e580c0b0f034a080340d04a64050400c80e030743d403004406107110341c001c00c809010803403848001142910030255110020b0700c1450b207d00241c20300d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 855725539 1250 855724289 855724297
    0x20f0307030c020f030a141b09010b0309030c011b090e06011d2704140a11131409010b130c1704050c060f09040c080105060a080702010b1203031e0c040308 68
    0x14182e107110101e13180c042420248054000c0d40c041c80c0c2a07000e030601d00c7c410130001114810031802c00d105924100f000449084042c414a80602d0000c00030501d016010710449541c406002c0003040b190703003480d80709004082c1d10300f1280046480c036000040c00c540d0104400f40308040c140e440e03100660700c01110030464250100c032607400c0300b000c8040341c403030100140040e11054400030200c00e542c5071070b2030300d50061a01d00000c000b886d000380707002c8000100780b052075540c0070000300c0318a452107144d28101001445800c2550703110784034050601c0b00068041d07201003000002502c0c00f01480ea6030002e00300a49003003040150000d040c3d00c10203501d1440c00d0340700c280c0051280064411071600f0030b001071403c0d001800750900300d101c0000c040c0700907d400d1240f00101c5487d4101803c49600d400002042c0c0c0c0180c0050506001004001401d180e100790711040262500034003400301d5000d0050540c1e80c03034004444041c00c01d400c4100302c1560842e81103026204010000c0c09925060643c1c1ea82d4400d03400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 855726789 1250 855725539 855725543
    0x1b1806050a022e061806150206040f030219030512090d09061101150605040806060114180a0f0f03050c04110412260d1b02060a0b010504030f060e0d020f0307030c 71
    0x1d030101c0c03080c07598901e0b024a9004100305c1d0004c400380203160a040707048034000e6100d258452150400d4920a58004c20702c00d44c17141c1c1180707040054131502d0600b0703402d281a03880840d4541121035401c01c03c141c2c1181c0074184500003140032020560f07580100d07030340d1110707400031600208040c000100304640c86044800a20501d00b4001301d502c0020183d1280c18010680200300400c0b00440c0600400608001c616805102460041c1d4622082d600d8080640f14000403101d580b02c8540760070105884000c5030707500501d14015400c0403155207042009a108407400100e86601480005440500d0300b8014024604244104549401c2c500001c000b611140030008481d07100c8141000229410040140744030600003400469580315170210fa4011240300d0400d080803015070441202400d82d00043e200d5000c80c0c203040005000d041580141c0303150084e60700040040c0040b445031010069941c005103180d14808003203c1400c1c41841c02a81c995030055568002a8800e12442011034070620090301164 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 855728039 1250 855726789 855726853
    0x31605010516080c0c0304031a0106120212060609031509010e0706020c0337050a02040c03090c030618051014221506050d05010606091a04050d061b1806050a02 70
    0x29660703544819035247c40303105c105412781903a0010005240c0081c61012140600f4500314a0202c00b40803c0d41003490250010780075040100710101d032034500f00301598042c0040040c1510038542252914003030450094071f60450701480ca030029000c5c0c0006000005458014003402d480d44c504c2111000c596201800c64200c0006144e0400c2511140c9444441031801040540101205030040c0010b458000180c05c0406140c04d1101001c20b103509a0b10301603d80c00800862400a25800341208404199019140b401110a11851200c465000c01d80b041d64240c0c3c0000355940e01e142c0051002c135410b41e030484503558500040b00081c402c030350180886495903c00218980c440002c01c5c0000710084d003c0341c00e030f9510001485400d400100740c4000303001b00c801019080c1d02d03880c002c0e06c0a024a00c02c4034010003081028104000d5550002000c140d070304560b580142c00600d00081000020158012030750a5280b000f180c0148104c080707850140c042e0300100086070480c022207101c2a002d40c0b20100e80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 855729289 1250 855728039 855728047
    0x30b040612440c031207260105060304020409020a0b0409050f0703090201050a080907031217100f060c020f0d0f1a0f160c02060a09080c0607021020031605010516080c0c03 75
    0x9081003070100d001e52240d80d00c801080c0c6401400c87c042d08108140c00301c0c1011a90300405c141d58800c03044a502c1613068070041480050341c404201c9440554200aa0a100114000c03885404540c442d501c03030241c0302c400c60503986032000306408481486e4400f034005013041044100d020300a180e101d410cc25080101c0d4101c1e9520b031038251606102c00c4803140092410100040c1a6400901c01a000202c114144085034070300705460012001620500051050f603040c18bc0655a407061028414a40a00380c40c0c8601703118903180031200b0740c142044400c1912102c414505c800c0340c2034240d102c0c91805034803012035142c247c0d902c4105100304118104021710f0608440060b11404040c211001503901c4801c02c141c00e2101c2c090410304000d5509000300024000107026940d8141410180c003203600389200d15a4107480e035900450100c6040400d144000500b64102c0c00c0222200c81c08580108000c1006890f900941302e4190b40043d14880003070004030220f4214150000140880b081800c2103c2c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 855730539 1250 855729289 855729307
    0x150e0c0c10020c060f160f050d020a050c060c090a031421310605090136061701090209120625020d0f030b040612440c03 53
    0x1c0c1241c100441000720381c0220b00c84410719020010355070171240350000c1307502d6841c10b00001e044010103441100c04001c0c0816040310940e0181c401c54113600610701c415980c6600f402005403e66006031410b0400e8410f8800080385034290800385d40c01001d0062041c0f03200c9285444228030504c0350034a07642980200d0088003050000e0032182490600d000620340d071643d0000003101c0451060001d00807a2501140c125203100075112801e07400d440785818500d854014610048074100d800302040030501e40308268941c1031a030311102007410607051200d207101c519141c01040740d021290005d50b9402c8442100103204c00340a50300504800031029150207200950801c0f072502e0141c0c1640d0300344094000880d83c20301c0d00b80007100362130f1310050740c0000c020340d5040c401c004080b8089a00c00504040e0703a0b0038180680da07980e07084803006007441841803a203858142800306040c0d045400d28440c4284d0048408800110720200031802d071412001130051100045140421394000510001d450008102d0221 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 855731789 1250 855730539 855730543
    0x30f0f0f12040f020405070f1e18180506040b060a030b010203130e2e1a0403060e030c0d090503030a0e0d05010903020708060703051012230a050c04150e0c0c 69
    0xc0b00b140203c0c1c00c0000401940140001c8070009071214080050700c0c501703084010303005013141088808041c581c11942d00b0001e0300300d580e032030f681c16014490b5403039010001e01248580d01e42104113101d540c080000d0340b0f82e203040004807000d030780013190845002e10031464198029808042101c00600560386041807400c0320b00202150307904003d40d00c019410905c007041d055090744990801d9200000e00c041c0003a503003010032101241c41703070a0b91f649a01c904c1b01443ca10907000e8800560f8030203024000b0141d61020709859810008102c4202e01c02d48007920107040c031500c440c4049403c003074051490200d07103600c1100c2c0000704515503504820300440004c0019024440c0c1841b0701d010340e015040c0b9500348000c1c0c5050650107400707501050b050074107024510100c200c000c011983c3c4207010540c0c1c0419850000856040c40c2d0050840d4507003802e00310740c2500f000c81d4090203544034101b03445003c22407800304811a00b0094031179041e0007640b0010f000c2410541f103010340201c1c8001180d4100302c65003200c14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 855733039 1250 855731789 855731791
    0x9100b0408010204030c08012d020d1805152403011805010b190b12150306090f0d03050907050f030718090b06030c030a080f070b18070602030f0f0f12 66
    0x1207030760f03500240030001e0040d000030340c1e80984010b00007445210242e00001e07403840440190700e002c00300106105222071030700c0c2d411503400c003030016024030581d0301584500503252280c0700180d074039000d00b419202c41c0b21101c606031807040c01e032207a6540c45941154028141910031090094141d942c440188100d041c403410401802c510440003c0340018001c0301b4013440044c2120742c0403001c081e1400c1404195600001d58149074207003580740e581a901e4070703517889140b0605541950140245024801c1108020038000d040c0d0111004a8a00c04c03403220b4124115801158107640329000854244958030b4501080c41907603400800300e4290f951240306500700d0307044400e2008123740d55900307030800700054410400e5002c1c80450140410448100100f2340b58601d118008044140005149216050500030348500f03503080a040c8915107072007511030b047c070701d001c2d1003a2030240316294000500c1c51001088401084600c1c0009080100c0c01e145d43c1030b03a411030300a11030603100501000c005110081c07101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 855734289 1250 855733039 855733049
    0x513050621190b010305070509040f03050a0905330c1c021c090f21060b04021308150c04120b310c05011d060c03160b091501050a030209100b04 63
    0xf0004139403651800a282082c107030b01c00c6015950f44000c002c0031500402401d540c09801d414180d0f5562411030044072500c000e5048280e0000c210301c0030aa009200030021180c2c10048011078a07003601411000c20b51b400354151103450b03a030100406c512402c28444802c500f9140c98012030328070301c0c00184480b51400700e015140000801d401000c01100e40c4c4103140e64000c2290f502c0b070a40c2075000040703003c0300401b40c0c10081c0406407124072040040d1943e904842c06010310607108031300700d915403400c00e0300ca0700d1404042180240794000b10b0881d403551001c850841c0d601e1040240401d01c03d54a00000500050a1100300c5c20726507580d59040e03244030507034103074810300d80010f42c1c00556501c0c2020700f090450300058100000c400c40114003520010840b08540011140d482d180c0c03152460350f40c55407081e15070003c0048aa034400300204010820841e02890f4240e0030340d0009071401c07240c4441c1c202c09105455010a1801041008d030525040164000714902102031840e9100d811503000e03580190302c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 855735539 1250 855734289 855734303
    0x91e040b100f030b01050703090e070e030708030d20270306040c05010f0807090506070203120f1c020f09090405011803121406060d0209010909090309051305062119 72
    0x8405203142e0b0504c5606038502090030103030b0801440f034400600500032400b840c0020b114820119860070300a01c0d444c6070310301d8000c0403030700c18684544107a40c898100820401d034103824401e0303009544c081c80503810404a8a40d42c3c107800c00c84030250118400444141b00c03030440004010416903a01e042c01200d2085000d6880c03014403600e0100014401c1042d81e1041b402c10080c0000d001706198003404e090100d85045902c0c40e142c5000d03000003401c0c15940b4045640030140007501c5040046c0c80030192440c0ca9012442c43c4a0a81c0c0c0700084099200c0c030540151200010044e20046240c40300345607030498002d800000341d840f02c1800030301c4035900091065003c600c42c2c3d102c10f102203e036409481c80c8211071048a1140341080e80c0841c00a001e02c546010340f0540200c0c105909921032122200103001104050200841c203040140c41442180200c90241c001c48031206d036405003a01070580a0f203c080c260001c00b14030200e00c0045801c0a01c08450140107940f880303002c2105007945c2115460041d01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 855736789 1250 855735539 855735557
    0x5010306091103010b090601211407030c0c0b010b0d020c0d0c0506060d02030601151103040609050319080306041a0a030605090706090f030b040c12031e020102091e040b10 75
    0x1000e8002c1018118414842d030f0500d80d00ca291a261181075030703000072003802d00324901c911402017144411a80c2100040b5213107041c41038903a0b0407410421501a5032161801c000c140580b0004a6514107442d10240084074007400411000020500409503044030032001800d01040c28141d84c00c161031525a03030000340a0410b40b0090080602105400190848080700005440d0707011030348a550500c5031294809034100c01c0240340b80680310407207084020000340e80c0d58039210500586011075900400340244503008221010005274680c0603215a0000ea00c3c0341180c0d681c42c2080041d20203100500c0620700300e200d4400c02c5032201d904640103184210408030341032030001c0d04507291001c2039214400b003007200704040082e00d40400c8440143ca0f00010203081706e80d03481c1045542e203210ba5000c0420b8540306615001450740c0450801000440c050051620900c1008224240d028103d030765039012006082946403010440101003d00002602c04a00041e4480000360f01441801c019408280600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 855738039 1250 855736789 855736793
    0xc0316080d060b0c1b2806091505090919020f250201170a020903120301230a050103232d0103080904020702010c02030d090f0501020316030c0c090501030609 69
    0x301546014211202495090880304000300d503039804141d043e030071405c20300d140703d40450700c0d1410300c46030060742c1d000d070b100c0e80708041c80341082d100c88240316031000588480f10100d15503001800c1c00000400d240d40311428000141704200064401400804011403100c2503842c5103074050000e03040090030105010303154441140445113000e4120b80d00c00100d5503a480490051b0707004000c084800e100e00003d070307040743d4501c0100f80091054507880b40e0306104152141601100300c0004505a030700b403055400e42404d88203030740c00c040b100116900c1d034080d16006003480300d54441c2d48915200c0481c0c42c032860010000303040034400700000390340b90f403955410300c501c84c0c00c20f464208250680191044e015071807503242d6101e014503400b030303880649d00c0b9640005041d000d5a1140f5204134144e5001000d03900307107415201c0c1c0502004003902c601e0341d1600c500440024558008003d407040300d801c442a04d0b60f981c032542d0b42146c800c5210b4500315149a80301c200410519840c0c800c0078080c62250a00107050303101c3d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 855739289 1250 855738039 855738041
    0xa0b0a0306080f0a08030c160501060302120303071e03110c03040303021908090918150612070305301c050112240230010806010302150c0316080d 64
    0x290800c40c820b03889420003103c240400243d83c2e00180c0c1118005882c2d031580740545e403061251080312000200e010b01c015060200641c46402102d20896110b1041180806c031903440e40401c48002010039282d00800815036404101c16081d0501361600094200506940ca9500e130042c1d50401f415620119040c810150104000d086a0340c01c00110140301da61556410701d580305800d81c0f01e00031718000022481c5c0158031a40181d1800030101034500c81d00701e1003100f0710b10700d0040782c01074400e11815030b0b031081c103210204401e03042e20b0300940901500317000b840f000308c0c4080e0b042c00760100b00d09601c0e4041500c0c00b919405010640c1c6101d002d420003180642c4d810050b2541a0010400c3c94484c9a0396400690b05c030061840c043c103413031046806d4210000c407100007400307400403003000d4125501c544001d800501041040c450580341701600ca998849a900c1e513034130001d0100035005841d52241c40b1801a815000d04440400d000072240f509004402d100c009040e05a01214038160104030448070840c0d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 855740539 1250 855739289 855739301
    0x10e06160525050c10170a0e0a060207382202120a0b07170f090a0209150a06120b190501230301140315040309030308070c020a0b0a03 59
    0x8149800c1d070070006034048040064001d800d1240000404180c6001045410b00601da00c11400030080300000941d0f100150501c4502404035083d0001000001c41c801c07100c0c840c003590707511080c0080c0515401076554000a500585055400341007a5000c0e60b00e1811a04050041c0d81c3c20020004942103e90304605580b1405030800000384442200d01240d140445005605150115154000520300c45c00071810003c0b05d0034080e10144045c0c00700b0400f1030f04800300032045605406c00c1c0c0c22990380c00c00200c0030707000d0954000626800003103116001d481c00e49020f64020302112104112076000c400003c1100e4416800389021a081070b8010001d15010310504400400c251119401d4640011410098850500074181800031304400030740940030061803e01503c800b400b05503641d507140c100240f202d1800000882c4a4410b00300c4114042d500c2e801100e001e294142c40301181d940c2076903020b41d4080d000900c84001c0050300315880015954080b4024004e0201c051004c0d80c4031243c80004040d590 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 855741789 1250 855740539 855740581
    0x2304060903260408070f05010606050a170903041202031207050a06060510080f070908060a14010b0406090e0a0b060a0e010e0d0b01180b0a0305011a0d120c050f010e06 73
    0xc0c40281440b072074007541520355019074030103100340d0741d0300302c510388000495040d90f00038000398641440851145d820400800080800d40c4039034021240462098910032422603229201e60400c0c04100400c0a5074081d90503218801401d030f6074000c002c0c0ca4040d981e078111100a0b0b80da940b0402c004400c1c0402449940301601080e180c250401c20000c8010b03015102c06000c2d200c50f00400000606194410080407000e803084da419138215080a420540142c02c554048440301403044000003546181c810480d01100c415071111603c491802c034503440366401c010703e403191b440e481c2d01480030540d135035600904054005440d14201c1080d194001000000d04a4050f80a0a902d900381008100c0c1c0000d400d0440b0f2242006d0a0b414484004800140c200e642c0c070141c011201c0c4102104104064100440755140d0300058405650300d40f0401c0b0f0100740a09028115066240081407010311070032184640a0042c0d08440f0400e600d09031007402c5480340a00e104031500000700740a90b4602c0c0501822000c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 855743039 1250 855741789 855741827
    0x10c140901020c0f1c0f0506010b09030a0f0606031a0a060b0301080c040504140a0339020603100b0d02130801110313030908010f020c0c03120d2304060903 68
    0x103200c0c140080e580e450032102c120711030450101d81d0b140070340e654689400c0d034019021810310713512160714010941c3d49080d0001c55440c000ca90000ca404250039068840181c1c00900801040b100c1b610758596090001038291030854481002002048428081010003070601d41615144d18203c44081c040b1800c503000f011040e017042004018508000420980c42d03242210005495121413410240101c0300c01c60b0070796140100c140c403a0034560030210302d84164490b00800b208803007208025001482c5a03103503d42062034854507090143c105a006143d12801c1c84844070b42954039141d6104494001d09841d81310301e900010302d03900b4503440e524840018198000280501030241c01c0640043c00003e1030503101410b0740502d8814580700b86803100c020041071000700559a6041c030440069401504a206140300e040d100106505000400810f451000904542481c0030003e0303402c06402e40202d0f2101d100705485203641e4207445082a2b80c0154403e01000407141100d18025040c00c80400140c5504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 855744289 1250 855743039 855743047
    0x30e07030803150f1f20060f041a041523040209040f1403070c0816090b010c0c14100c0f020f04020f03090726030414060903060702010c14 61
    0x40c1c0303030000380c0350803d01c020a0228650651404200b0703040d902e000081d03004002c101035280b40318000c928845854210380d02d10300401450071400da0030322041108040700703601000c00207511600814400341c1280c0300d842c0c4200c3c080d064005070b04403550706907802d8138524080c90030840c00d0820740c450130640c40703035100e100c2c59108040d60a1a108a02c020800390041554500203810803160140301492181d00c00000c400035104500102e82c1da4004200c1160001c809450202e034194002a201036200c490b2150100760b0350410502d00050414600540d0610040c96000300001b03501180c040b000d08440c0d12190500c0c0c00795400c0044035580711900b0381c184042c03001642c0110f2103921081d50810303010354054400b91050000b24000f031040a2417003001400100c18848000300c00308001041b03450006208501c02080c5004401c03809854002c22441e500c10082049041c2c0c00e140718043c003910040c030207400c2000b020042800d03d00100c61160060755141200c10070b45400c00d40e883c1e0001070702c031140c5084c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 855745539 1250 855744289 855744293
    0x71409010302040b06120f010f0b0705190c180e01050c03060d08030702280302070504020c0c012607120c0903020109120204150b12061f08040812010e0601030e0703 72
    0x4000810300000c0c0c042c80d00c400b200c0410340c42e8001114885400240718103200c2c0b80801c404103488100f8000e20780400a000b000180c0c00341c0b10030a4611035a000f201038014480700703042040500c414000c0843c2c019102c44000220040780300c06a03840114010030204110902102850071030f1801032045a00c41414005c0c0240c98940c40c0041c3c606a502c01801d036540d8070ac0400a03403511500c014013414040342c0c5040300c0d080006089030300304940d20039000c40300300740d8031072082100342e0044a1000c040395100c035032441d0144d071280104400e45140485040180f41c0400180a9504000c544003808906090f800c2c681100c0c5034070a1200c200365600c0c3c4410100d06603030008001d024280310300c540243c00700044006565a0f5808400c0308408a4542070380d080e5514a500c40a800401041c120720745142c1c0020100e0824a001d0900c0d000005103e4140640c0c0c0c1806a8801c0f40142c40cd4844000c18080c21007103503c3e201c0c00502800c82c09507044c0c07a0349468000141030329402c8507400c1d1250414402000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 855746789 1250 855745539 855745549
    0xf0c020d0519060b090f0714040f0b0406021632100203090a0f05090411130c0f031103041a0c0c160f0503011407110124030201080105030604030e0f01090806090f0714 73
    0x41c01614510304621501d408000454803400380d50081c04140c41030ae1000130364070841100600469880344c00b80e40d9590b034924184041c414543c800c0b8800a05010031060388181c01001810380c01500f00060a560010000813030050201e408242001d41d10001d10985589404000b1000409203410751400382401d20b8003140f01d500c07024000a1500b1a005104070556441c0c022610078100d004c0d404000c5800880d100420005180c1c0d40c9a012925021606055402c010704591043d90081480761003c940150001030714a0300030149403120000707100041c0707212014450030782480c40c280c9003c2c0c4040d04011449001030320f41d510182c030030382c03400000c0b0004c0041a40140d40c04021400e191044c0703000c00e06040e0240c401d0786070b0807075064030600140302c400706019034041c1924002c4c0e030f5842c0d06a0700c840a04d03544140c01d40e0701801050b50390100110902c0c1441000201071010300d000c0f80403ea4507a040c07450b0800646c0e03400d03416006910202c0c2000740030001c07000101191101d00100403004404a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 855748039 1250 855746789 855746791
    0x6101d040f0f021512010f052d0109050a030f05060f07020c04110c0709060819020604091a1201020304030e0618060d060b0a0c0c060f0f0c020d0519060b090f 69
    0x2094040c1140c100002c3d0741d110100300d400f83c1405041141d0310100702c0442c40319280c0074042d081c60705180030b0001c9958142980005220200c03196203132201c1494410941c500c0611310480c604010030740c54041215110000d02000640c42400c01503101e03002403800d00d0521000802031040021001c1c10400c0440d4001110010444107882c005840ba00040555006100300e40e0f40300041c0c0b040800000b018031003944560308590440c0b0641c1e00341c0d0385028003400960031040000e584208284801e01a012907a448135034054008030131000101510004615a9107010940e00c0311a503000c4100001d01d50000c407604900d203004c696481c40c3c940d44c0a10524034510a007051800341c40c0c04608055140219400b46018060b610080f917198030f09007030020085141c40308119140b25100300005211400f0313050b079207490882626a0607941e40c602c0c2e000c41d805400120240d91206000d12444042981030151021102c6448903241100c07581c0d082040c151070344018018040d8004004100d90019004001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 855749289 1250 855748039 855748043
    0x120310081c0e0303130b0912011b08100b040e1306090b0105010e012a17040305010903090e0f070c060b090f060f030a0503071704081b130b0f101106101d040f 69
    0x3441d07d401c107400101300702c090062440d4a0b103604e00b0044402c446901e03280010014141c2da50b248051751a8507641e9244010f03440365503c0c1b100d0038001400700f054506d80c84c0e40d10070011509021542c0c003540b07440098441c40e820030340d25944480018031640d41d02c001e54241c094801c0c02d0891f28500788204041c00b440040381d401001456050106003081004045e0035805407041100a0705d0f10307228100700d0f0080c8040f400c1100032400c8003e0000c0d10840c2640385621031080044103035059a949501a00c582285120444119640b58021012950f645031401d0080040c421590803903d084801d00c0401a01c030510b0364441e5011014140000d44001704036040198818440200c0c8c80105d84100c9031409150801c1d100c90140c6000f0081c2c0083c0d20441c00ca400404581303024026980900e80c000319501e0485260b040700740a28001c2c081e0805002130406a449441c081c01208100c03014a400d1101c1582c5070100c04994006c1004140f9840c07101a404443c2030744002c1e150308059880105c030f50300d04c1d180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 855750539 1250 855749289 855749309
    0x220b0115210b03070512011a09072309030a1103011104030f1209031202030d0b0603040f0f0206040906090b0f032404150507020c120d02120310081c0e030313 69
    0x70340c01c6520701380511401028060010460a002d41ca003a41c0640705440340001c2c80c42c3c1c4012000462318020b00308c6401000b0a4a5240035040b020150740540c40c00070004a0504004009111190300c1c10070040f05a47d010b079000c10b01c09001c807010942175650320f802044d10400140000d101240001c0082240c0e6a802000740e15080341c020400e440403c9540e001414410b42d4031140c5508136004001440c1d103c00b040420041c8400e180d040028a0000381d402410280c00300609030001104041e1455103180010401814550b0b41da05d40c0701591500e41100d01560b0315420040d00c80d0500c12944100403904402a00003c010340fa25421500c103410741c800080f49500c0d02043c20320100300101210000f124000344001d1600207006503980b9490022580140f5903107400320b01c02c010100300102c4204044d40540401469882e045405400c0900442c5510410210018040300108400003034208401d014080030100d964000d8000c2c1c000152032802600100300444022020f0300043c0d06440074450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 855751789 1250 855750539 855750551
    0x6060b18010e1f0810050a0f36051305100b12030304080a050307180308030429150102100c0207060f0203090f040f091a0a060501050702030c0108220b011521 69
    0x8514051079480c0d4481c03a0082c12001000c00c5108040440c072054841015102441c030307140c0c0350200e004502700c0401c001080e8122840c2064428681c00160304110004801c00506486465281c1024034805e940101540e0310704903002c4505103000c00700700403400903001d1801c41c6404e8541240360b1141c46c01080c1004000000a6522805682c4c0500b0340c2502007041c030100c54076450601c44030b03401070b10305456084550700c8040c08802901803a41506000d030602d600140c41e41d48580f00d110100740200d906601030b40c43e007034100030400d1080c1d0f00d4420b401d9000701030301450040f028007842118015042150402c100003030381780d00c40f0b4078005071100c8103640010707404500055070380c000c0444180080501c0300202070b110090035540e203102d004102c81d80d003c00800356103030010b5566100d0b0a0009400d0f8000860302600340d800f071071382c05600840320038034802c4402c884032091581e80224001120300b0850760b8014001000280f02c41e0000c3c002d18200441040501a142d1081c060b604041c0300a90b92640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 855753039 1250 855751789 855751801
    0x5040c0803130e150109062105090d03050609040507140414070915180905040819020f06070e130e01020c100e0c030d0c0f06060b18010e1f08 62
    0x2014002010300318152900c80320000c1050050441d94425407030030500503c081070399029041da010b80102d030305031207045c07030289005425100c4240912110f10b0105941354440740140150040318440d41150002e040c03000c12110020b011a00040e03c0315002d200c0100030480000c400107084000d0720900041544081e10002c001409030a8181120038000748200c14002403640004038881603805455444450101c0342404a031441c3d000c10b60042d9040b0750794401c20020b031155009981190188500074582005040d0340d00d4040040c03010a00103904c900c3c01d0180070201800702680001440c40d040039084041c3c00000c000039454040d10207840d9480d10819566802507040303c5c0c1c80304045080d610490180c08a1800030f1050b14100d211038043d03000c03101e100f4070700401d18800d00ca81e40d4075032002c41ca900341c4500e001c9140c4840225900c43e0340f4000418001c0402001c0d06181c200c030014481341143d80000100a000e060000500400c00a501009041520b00c1d442c0c500c152103140101c0743d46d46203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 855754289 1250 855753039 855753053
    0x1b0702030a300e0901060201051009051308040602061009060b031503100c051c0209010203040b0d0e0703080c0f0604030e040b0117090a1202030405130e031b030d0c0503040b0a0504 79
    0x201042c030388001018010600190819030320805003400301d40c910566a03a5034170036404d860f030071a40d1300c0d9002c401e00002c0c0240c1d0126131240703402181c8400303243d43c0c1e12801d0b615050b05030b001d07821000140c0d22400800100b5540070180c4405425215820b1040616100c20300703c0c13600009e400344a4018108010b007010340c07010070201018142802044c8000c5090040191031544840d400d0504505442408201081d81c0d0003100c180c1c840681c000c42c64180fa11440038215003029072940c1d0b101e9101c1110800204042080c0320166000350005075a5010f541c0c002c4e4074240403504200a1034004100f000042600840c0210b003a58040d01c1c0454004266001221b01282d07000790f0020018902c424000c84c03900000722005210311481880d0b000100c8100241d03900d00070752182c540d00c001d03c82c00c442450032080d0402c4240324035000c1140d00303000840c0c40100c82010030b901e00181039070002c215503c0d14034007030103090035100050404030b145007410f84034000e41600041804a655464001040810003c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 855755395 1106 855754289 855754343
    0x60e0f040c080105031614091803030708070906020d0c080f0f03010e06040e070f0b070c080a14011104030b1506160503070201020615031f02040512061b0702030a 71
    0x7281081031401d402420b482740c0c080d60050300c9059a6040000d035000d060143c851000c20301d0412030080c2014031950040f4210b5100c08044514203802490f60020942c210074051766480d0a0b90000b0001e204a603004404541d0010000801c0a80382d070006002c3d1104031030034801c00e25000300c01a55040386001e07200320090021000c220300c088000003848254411248101c5a40c1c4c9c4010b00c60502d003850302e0595100310b1140031010031040c20702c01e506c220000009418181411900c85132401c100041103400d0308105421451402d540c0c07102a501c010310055549184921207150060310780d080600202c0c054417812010410f41c0600718003099041344081c0042035419059488406502c10b01250320310100d5080002103902e0b11034850003810030007483c00404031410440c100c00102500c101107102e214001740300f810016038001c1040190703c1d03040301c1001e1250003640100000400 = true := by decide +kernel

theorem cover : BRFrame.Cov 855575539 855755395 := by
  have h0 := BRFrame.cov_init 855575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 855575539 ≤ n) (h2 : n < 855755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
