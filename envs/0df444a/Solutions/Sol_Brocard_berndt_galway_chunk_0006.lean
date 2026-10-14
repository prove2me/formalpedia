-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:19:10.533432+00:00
-- url     : https://prove2.me/submissions/2bd25b8d-86c6-432c-8676-d0552eb78f84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 899288 ≤ n < 1079144 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900538 1250 899288 899291
    0x501060e0a050a0911061809010b0703020c030604080f090402040302090906010e0c0906030a05100b07050105090601090c08060904020f04090303050615032503060e0702030a09080607210609 83
    0x400650410405004102491062000c1d9568809003c101c1e0481d000140501c1410140c280403070804c2c0300104a0000e0095151650070260b9000c01c1000000780e02a11070b144000406a0a0517414000603100a004602821807810103444641d002d0086840ea415200c20008440340613568903130481d00216400741c4001120319142125a8a0700003d120700841d2103640f4002801490907242240c070706480c0140751a0454450710684001420028880000d40450311750110300301d0315a0018203840c40c4500000b05017894804800c90801c08180d002d0f4045031b0402000c49400360300b165013540e1007001501d403015240c0c0c881c0000b4002c0c94035000c0c2e00d50003d1800607058181a81500018891401aa20300b403409075500c6a1000c0c52004a81e4445a1112240d00403400502c02c1072409044035030707160105450b61110005070801c1c50035500325001d42d000003060300700140c101082e42c2c01000200040c0c41540382c0b00901a005040000094100c0820145004117000c6150302040c00b40800d56030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901788 1250 900538 900551
    0xa0b040c030f05010b040b040b070f0b0c0a09060206010509070302030601020a02100e030c0f030a020111010207050303010e040b0702070602190201050c01060b0301061803150207030c0501050403090906080106050d08070201020304030501 103
    0x80034009000e00c01d012a8283d0410001007130450010040f10116081100d5040c0751501d8076170740040d07940090f40b084448144511007c0040360a41c070449026600038100b45980740d007140d20107403000d034056100c48255007000004015658038500503503441107082c2805030340d1b0b07610100100c0c00c00c0c0401800a600c000481000030300c1d942d01802031103042d0f40a8007140e18191302101002002c001140c000f0358154040d001c414010b51040880808a806034400982841c05556038030741141c0003600030000c40c0111601304803c0c003080747c809a821440c5400a00055414107500030346440e00c402c0540c0d0380d03410101c201ca0842e4440c0e4100c0703101c040e581000b00422604c885006040e94003e105000008000c0e07108482805c0c1c1d0b80684100b20780e0b200f1000d0310b003504081101c1020303402c40d0b941a01030045141d88400030582c00e01030184940d11039524228603900708904002112856084408a42c0c94444203110580764200c10b00e6003550030510f210f0700c40f815840104d28620541c0c000130b0065003040c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903038 1250 901788 901811
    0x908060411030c031204060f03020304050a0f0f0c0b03070906030203040f021005040503070e0601030605031507030903030b060c0606100302070b0402090901110d05061302090f0111030405060406020a050d03060501080f0a0b04 98
    0x401500507180c980d41c60501c9010444021070503404280ccd000307481342d00300700e11085c002058607a40b65080d5204c0e6003001c0840c103080d251448002c101e1351200812910001c1000203256000a03900f000c2e103180d040443c1907040c0b07600e0b041d00d40b280c61017000380185010a81c0000240c010020380b0000d01e030050031606c071031340c0710b825034490b050b070995046001c00d0520001084e2481c1c081041d218220010341e8000b1540d40f41c00089019182c2d403001a0185941c91041c504e050316110014800521100014500c0d8103080e001c0c0581110b04044c00c10405106100420010b0986840150000d070121025a203548070400386500420301c4207501940303402c1c00160209401c6164000902c184401c50b010f900e400a40420f0509038490104d07625444440454000500d40c00b51111044803c4d54104881c1001d88902c0441c03050b0307016030060005030f0b001014940030420100803c41c9a10580d180500015180a00203842410b000d40100003500c0482d0000304890341540c08141d507110001d0040c000c680918 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 904288 1250 903038 903073
    0xf04021b0304030b1501050304060c050d0207030203070201090b041406090f030708060f070c0b0a020315040507020c040e03130308030711070b0301030b070206010b04060507061506030e06070908060411030c03 91
    0x240b100f29a076400d12400140c8002071100c14541c5e441c1c060712003034515591075507400010a40801c0c0340c018004148079402e0480310910203000c01c03030321a800450340c030012303400050081c007440e80c049000044104401c0c00480149008066000c809032880b030340301c15580c80051080300009a400d038141c0300752000000c0e03c150000d440d03030280030314062a5041da10740c00710840381c2074100c80c0040d100c11f0f0400e001c1a84842241c1c01594468480d804036542e61b10b84c10300040a65000341ca4410051380280200c20342441e1500c503c01012440394000c51131b042020321010741751001da10015014000200004200c40e0081080c049104130030300030f03502101d44030040304003075410a0000f0703a60703c0d50000c00150580e0001554606a802280c80c89041502e0140c04580d10340c00703004102c1d20552903081040e0303030080210014014058985000c1074a4042a059600d04207000b051101082300780e010403c4440b6010030b559030040d4011090303110004410f8046481e003a0003460558052045070031000c10310400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905538 1250 904288 904297
    0x904020906030f1605030708040212101104050f01030b0a0b070201050409020307020307060c02060603150601051b01060602010b030303070c06050402040204050d03030c0206010602010903020304090c02070e040302010605030c09150f04021b03 105
    0x4c100b00f20744003032072030750100c0391804201c40500c08100002c0215025140101207260a41a08801c40b54a00d2740042010165140d1210025031010b0101e020700191600018004c0000c00a1a0400420301d100380060b03900c01b42480380d20918080007502e9419a4405c50459000d00510b4606654a040801c0d000750349611024064030107500d0050801c500c0303071001c950f00c2d010301d000038020700540d40d0b402d004100194010f46083d0601c207040080c0ea2280c0c1a01140100c1162403400015180b468034802a082d113501005052080d00704008000b003c43e0041c1c0d5004c101d0b03811a5000a0300d503114404100280f24507004180e0181c4511f441c4020075500d5000a504082c05500340c88060366204416402d0716046000100540c00c2840280204900b41c1d010044101c000d00c11034411b150b5a210024400702d09880a0b0f005075101d00091003281010400301d40752030800e843c40e0340c0b90f140254008542c20380004405228000301e2070600104c1d41d55405035502a1402d01c84550b004000f000314950741c1e0b01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 906788 1250 905538 905551
    0xa060b040803040807060503010b0703030506030c040c02060610080108030a050304060f020309060403030b03060106020a020d020d0209040305041706010609170703050102041202040e0304061b0507080a080301140306040302030904020904020906030f 108
    0xfa031400030505602c910148c81c102c2e00805d442c50b003001d291340e80a40c090300c8000c00300c0f5010302c00c15240d4000c036610780c020203e403807010380c01410381801c02d40180108011040001e1003800340030001080020781c008211100358107546860794a036155444c1c01c030040c1c00301101c2c0800307090000c01032140c45c90380810041e0003207202c5e0b1000c121247c0c1030418161030b01c009110740009600480355030300c003604201e012107246038030041c800b0103140c0707590380090840b1000740c4d41036000400c017040500c248000780760400000703100c000c011f05080d8076081009003020302e68007a4038400700c90044002858801045904051a4840c00070740d1140d0300c502c0c40d29040030190806900ca00d00b0302020144407a40803007201c0544040d55210000c0c2807080c0c141803060541d410040707a4074880c0f07000000d581d800c00c2c00729401c3d80744580c0c50310359603500d45000f18a111410a03900d620030b400c46400c0c4000203800000f140ea0894083c4d40140c3c4a00300c00000500038050030300e6180c2c0140d000800c20800701d03a5409140d205d40b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 908038 1250 906788 906793
    0x8060a050702061302010e01050f0702090a0b03060901020711010c0302030705010c020303071803080306120307060501060507030e0102010b010210050a020906040b0403030201060807030b01030b060d05100501170c0306010306050a060b0408030408 107
    0x103840704c503420000c0205580280c08030700d15600111842d441440180500d043e5448c0c05440d0847c50703404600c116004a0300b90f00c10300c0e40d03600080110720b011b11107580c001c50045c0095042070000e0f21410001171b0f00b0601c881c1800744510300ca004250090042c3c03009203070420002c00c400c0d0070444000c1c1d100d0b80202c03600800100003d070f40d01105d41c0c1c17442c5040141e035000130005007959540f605011640c4a41512091148014000c2500241d01405454042d2030b1940c0c2d108d4466440d45400b6040054404c030315415a41009111903141e6400100710b56040881d0300003003215250304810b44020700c40e9038011a00860001804200d0322682c04c020000c4071710a900030418541d40b00e800e5a00c0703814600009210070034050040012603c001003843d000741d00140701744a80301c143c0e980c20f482c081486480005568840c1e0040220185044590781100401130141c5400d2581d01c1c0007035101e0701c0501001702100c0e80c400103e0b00c0b842e06a44058090301c6403d000aa4031511403803200da40f40c10034031511400e032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909288 1250 908038 908041
    0x8010501030e0303010b070f0b09070303080109050702030304020d11030d080108060108010203010e010303050d0605040504061401080d020307030305040c030203030304050601090605040b01120207020310020f130806040807020d080408060a05070206 108
    0x6520a2203808402c0c0d03560310207142142d0078541d6040155006400c203031002e1849020700d60100c3c01580685010754400c0c001004a2450f6150241105e80140c2c40b810b44540361204100c5007d80101c100c0e64070179812100031035880f080d440c06610540c0160112a094400c00707420034401a08100403e044e66000d1080780c4482e81c2c0c03a803442d401d170700c42400ac460200041c1001000007900581c007414a01c0007943c008555242c031503021078202c0f10202c40648266440e104081d150040002c100da024040880260a500c3e4506c88041d580e8400d014000b82010f683d440080d013446003051000010b0b541c02410b43e5520304207810160707a035550a000c0c034541140742500000303541c50244181428284180c440c11018420b22440034004d4000c1403059816004101c0301d50300303c05161009003040b100d000c034400d0712003c1405403410b03081c0d0983c0041403240c0c0306105100c08120b0f0141910900c0354100d4464488250b0fa2411460314011940f21030890702c208024410580001d0300124850441c6a00300c8103103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910538 1250 909288 909299
    0x20301080a0308130218070201020d1a041b0e011805030303010b030f01060306030201020c090a0e0d02011b03020301050607020d020a0306020703030903031103040215030901060b0f0301050414090303070e040902040e01050105010801 101
    0xc0c130540c2d00000d41c82440800e0224507213484070303029580808507000040c00c24001c10400c10996688012458504581040c00c0701c01d8509846242c0c02d4808417458007141d4031000c04081c160180790486a41403022019100c18a141d507400e20f5001b42001600752502c1c6c3d603450342488540e400075506951b007403a0340c41c00424020311074803642007100d40580c000c01007a0340000c1070280551001e880c10030789544590070003100d208108092802840d16600001e24043c040941c808000300741d01804040600410040019955070016075110a4044801d0307440199103200185500c0b8056200821352400880e22340140b6170560320003010280070351814006803004003103001d035500c01114003e5020140c100e010140d02c44220256a01064040c00080c850f5101c0d103808155130048015017180410010042c0400d04040c000c01510b488144140b0301c1e581015040303a9201d0100520382010404d2051440203140d8276170308807644039034001e48200408004055070318068082402500e001c146c1540001a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 911788 1250 910538 910561
    0x60103061203020c060702060903010504030c060c02160b0a02160308090315040201080703050405010b0a08010204090b030102030106090905060105070c030506040b0c090f0d0f021005040603050a021201090f0906020301080a0308 99
    0x4140e40d2643c050200c1c4c40c24241002050340014100380c3c0c00180c24440094030391002d11486000e20300989446904565034544001030b074402200c014215001741100100a11003c034040c3c00380e40741031402c55266954441c04134608081078a1241c9103440c00040002408035410081410040550540c0d0314415204208884083d099030b0080c00100f91000041005110b50300c400e07001071091001185100800700041d02601c402d0f000f280302c50f540000c0403c0000001d104601040e14190000d40c2190b14040001d40445908d201c2c4804031520364001402c10303032041040b10074140e8491019a1201d4070b03030400d60750307401c0e0880d404c0351040300c1c3c0303000b283c4501040070030740e001190000c100300342c1000500300f0b00041d5013031500c0445000d00b18041d100d0069071003e42c0c1e02000c008503995107031210301e4544010251040900501d40c8548100070790074000100820f05415601d41ca003020803081d4400b54030b50010401d845c0080e004901c044000703c0c40c207401044102c45035000fa5201c0c8200d4403920740d07880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 913038 1250 911788 911819
    0xa060f11030d061212020c0105070b060301060306060914010503010605030705010c0512270108190b0a0305010507030203060102060112020303030c09030319090906060503090307032007030b040201080c13050103020f0702030703060506010306 105
    0x14003207801401034100180e40c4be5034282c0c1c06080030f400400c2e220360701d07507610041c5c510981082541c55100e0340582590100340200500400d4110000e00c58144ac280200c1c0c1c039141d190040038108606000f80d0024011300b00280c80117aa2501a865a00c0e0727201d0140440219615020400c020440d0940440315845054202c1c042c030245480e040e05001c8103600c3d40c0080a00c1d1201603005405074100001080003881001e2040600c0d49015a0301d00d4624002030034004140c000181403002c0c00304030000358030000250390b03110760030f501120ba561020000080c03a40c051a10426881c10317114611150580c0e00000034006c0796480300342071100f5a12100c050340c10b03000441c0d2421a43c2c0c0103004c6900400e00c1910041800c60412030ba440d240d94002104a00f8030030150803da8551240d2070a010455900040c4a580100d031008858140486400c48040c401c4803031203482d04240c1c000c240c603800545c40808072800325074001d0807a660703da030701e01d0010042d00c4102e4841d40400d2503d040040c078550f03011200e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914288 1250 913038 913063
    0x30606030e070506090109030b010e0f07230307030b091305060709080a15060e090708070b1801180503011d0d020d05030406020a0c12030203060f0a060f11030d06121202 74
    0x300b841500385814800035410402c0000e0400c49880000004200d00c01e8440740a0519001c0c00c1205d071500b00c2849d20003141c081d040380c2c104501c41803d46000c0009114100b5051004070042c0e0b920389812108401809a1000300b1b98020400018040340d00d02e40c0825441d103a100303000740c03513142d5903900d400c2c1e50270030103845015425004132024000080150319401d180403040303500000c1842e00c0d0800503020603801c6441400980c865407042c0040743c02004540020050803448174a0030725003440806c6403002c140e2800e8107002d418942180003001680e050b8000e000003138001c0042095241040a02da02c0340240c203041809050708800c1040d1020941c050080115103a49195403626941e600c025480f850100c4208580d03820b0000004022100340c180b00d6020396409a02c9003803907401c004d07900b200b601e01c45204070b400c004200715141d0840680749011403541000200c9882189102d07085210f5168101e02c0e951800780c001c20b0090401201140300c3c1c0c011210404240800701060360369501002c0076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 915538 1250 914288 914293
    0x6010f0504030314040e07170606071505090c0301020c0109020103050c07020d15020702040606050d050a0516030207030302070804030605010303140304050616050909010603050105040e0601030b0705030603071d01030201030606030e 101
    0x40c000300c0d0149001e048010600c005a5160590700d400291b4055025914000000c924603091115040d90b00035003500a6003c0780c015140c803c01c1d991f0b1480044280414822a81d101d40016010320000e02200b4a400b4003d0300035035407482d601c64218000d001c444000c90100c6e142c5404645035101243c15a8502e42d800303480e0521419140c0c99001040746104e45450303042d41c0030411200103840e24050381009200d01e45900d91115036892448041e0f5500424495255207400d082025481c0a40e5003030b030004221b810700581c0c40800c0e0030110003078400d0f2140a05a407100160003c100a16640054100c078000c1d51101c07458558405007901c1440240c40180c4035a000c0300200305803845010385461082103a003841c3e4600040b407400700d0564a001da0101c80826541e6004200d141400d0089400154106000d40b059606503520010003800240100c3e08101c0d01100003900340d1420004c42c8090b0003034001c150744103145200100300c055024003080380068107110b400200355009024800700004121f02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916788 1250 915538 915547
    0x406090203160305130f0c0e010806040f06050c0d02030c0301030303050c030c0a030b01090e0906011401020c010203040e0601030603020d060204080114090606010e01030f060906140f03030a03020c03070c09050405010506010f05 99
    0x700f14080d250151580d0754020480c0b840400003141804803d000e1440b941d1180c0440f0314044080d001585d05a20020007034005504010000d81802840c145880d07110b00300054940390301d0784030b130010700455102c1d501e400e10010900038440302460155048921968051216982d0000009100c1c002174844115014050100745801c902070780280d42c1301001031401104042e6a161101207a078820b6490708940d42244005000583c04235410044d420ba081c002444000601e0740004c0d581d101c2d0317110f40e02c000041d02c008a05103a103e90040030056400810000e02c0d01c0c05400d00000941c80b52003003007119031811205080c1c00c100d40c4800c41c80343c0b8030380024003410340c0c4000040d00d0306984401780904055880040c00d119180300c3c4201070141400b040005185400d08140300159140c1810940c410b280e00c1007001c1c0c2a0354000100d50040201d85009600c900c11400220310b0350140300c40081a00d0300040000c1201c0304c5a600c02440746024800902040d1103140066414083c07680c04034000520410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918038 1250 916788 916831
    0x40b030705060d0b04090b0a0c020f03090a030303020903070305010204030804080c010905090402060309010908040f030510050108120d09050a03050d050f0402010504050f03070306090302060402030f01050112020d060b030109030e0406090203 105
    0x1400603c0d513080280c40400e08462030360b02c084c82d922041f13601c902105e42e128460401c3c66030401244805510900096180c040d06400080c1d0400311444020100360300022000d2842d10180032540045911100030f6440e00e480703281803001da8000e40100000c911518881d15990340c80b078070b02c1a0841d800030b4426000c6d41c84503024891160301c000c001c2c4c4c82541d00c0b0800040082c005100806c010310155074120481801c501d412424041048410b50340c035070800005001c80701000c1441510010800034041d921041100954082c0401440140903400703440d440c44203241e001001098020b8945c03108000544d10801000c01e561001c3d200680018001d000c284046c0c144521585102000101110780b4140d499840d00180d0300e800d241200144c21960900086050400500d045402040001c1c000e80d03040c203440d800c201408440c045d200f410000308000030700940c5c1d4458900b88001070024042c0da81d460501500300c985503108207000c3c030b2921100103132482503407094030b000c1d480f080700d820002c801070b1303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919288 1250 918038 918041
    0xf010609030611070209010311030708030909010e07020f010501030c09060501020f0705060a0905030f030406020607021902010c03030e0d0201090c051008060d02030111040905040303060509090a0201110705030a0602040302040b030705060d 104
    0x41d0080c0f40b820100000e038050ba0340c41c0c0c811802148140c0382c0850441ca2181414208042540410030710b40c418005141c0e9640c40c551030a0640d0000ca00304900c1c0d50302c2200032072514494120703482c031079440c041c00401449018201e600550b55800001e21800c0c0e40e4500480c2c1d907150460100d0503580080500b40300714075003c001404100003030329041a5480d120782c00039042070401c1800e5209640009400c2007026010b101c032550100c03240c000350205040c0701c60454078044005400a0400481e00c1449d01014080d50003020610310304012100d0301e001c0b0300c001034001d04001605660410305400e0001d02c40c60700c604400891202640c864500e92100717800d001a070001020120ba02d5500c0e007500c1545060040050401804c040e00c0104140c1090305010b000c1303c640b504100c1c0110700c60001c001420400280c0b04038013582c2840c1c8880d04480c3c40c80a2818031885800240d81030041d80b1009050000c1c039005441524000ca808102c50540f440406984540610866030400818024094042c0d0203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 920538 1250 919288 919301
    0x7050c010510180b0a05060a02030c010b040204030803070c051005010303020f07050301020f09010507081b0709051005090105010507050109060612030306090605010e0d0501061805040b0a060e0604200a0201020408060f0106090306 100
    0x5031102c041151a46c3c006074441e001859501d006a1000c81c0000c9480c000b40aa40c0e80c00c0c500f0345d0214645420750706d501c0b20600c8010f1584040c050f10101c86810008104256070102c10400c000f08801e503102c3c60020f40b030b100440c0c44584c107446155404291440c041c421101c1c003a050003030301442e0059407c010350301a040b46505692240c414807042d604c01c000c59482d01461040880a000390301e05041458003203a8029054444800311340070180001d4896000f0a030550300d00b42042a2a4041c5281041c0913242d003c40c010055420018000307030b48101c556031904118441d8400b03000858541d41102c0031648981f2501d80002c0c140c40030b101942c1441c40448521900030f17030020a2143d01c8a01c07814030580741c9412086416030301c40c1048280010358038140d8112400d2802448118948011408d54074006070036188111765071105421f40072000000140d804a044600d00e4564640714000790007500140705622940c0aa074001034142860b10700c09a060710a01c0d120640b0080c119290003008008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921788 1250 920538 920561
    0x80f010911040905010303020f0d050a020304090506040914030901030c020318010e030a0b13030e010804050a0201030b06040305060f06031501080303010e040303020d0f0b030708030a0801030b040501060b0307050c01051018 97
    0x50401c0b001c140c207402406400c1c081c5009800900d110302c000481c9620b0308101210200400c10240448502554044115000c0b5000079101107446e0700c2c1c8000041c0200740074103004000031038108201040c040088054014540309880c1000b480402c0d4400b40c3c0c491046006032005c2c5074143e86941c0c415030080308440004400036048607450465940c0d0404c0c00c0c0c206a4050001140e0704c0022010550f10001c000c900c13120a290502c05800c040c0d940c0341ea01d01103464000d0501d03440e50907000c0e1507182c200c151001140c00c00116001400c12103010a50820261907d9009014220005284000d2070f0034580c12244108015480c50303281c6841d444200c440908218101034082202c00712840e01801414519000700d8400592102c40d40100342c44c1c20426403043e0706541062040b51221600180d065044a400074500b0042d96070354078240780100b4407600210300200010041c000304661101c094140011a20300800007a154441144e2550741c40d032282600c4621001d41141154010307070443c820200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923038 1250 921788 921821
    0x3081b01020903030c0a150c05120414030d14010506090901060c020103020403061406090702010605010c03030e100c050309010506030601030b070507030315170c060301030201050702010503100f0e060301050601080f0109 96
    0x408141c00241551301a9800d8441c66100c10b1b500000c3c0290445c04007001400300b00b08011131007110401800c5801000b00c420b1855000100140070310412200c644680a88003041c0c0355200c60204040c401088200140400700c09032a0012a10781452001c4428054004152448036842d0075421280c4a8010300100e0405809120020018031580900d2000c00444007010b08585800c1c1c041c0703c0803030802050709045a0600f2030401c02c60f604140000255038041ca404a90410804c440310f01d04140c0c83d04402e0610314140703030040b03070962040c043d60140c41004000c0c09651104420140c4d110030a01015240408200205203660b014000a01c5014031034103000c20420801c0c8440030301000250311418101050b424501c289030020f0045007018201107031054215411900028401d015403a4004d0501800001141c50302002c524400010840f014080c011240ca6040c4003d502d00d0603034a26003e0340c00d00f03002c1202c40d0b008020480c07044c603c0782c55281c4107a02c1c0450f000064503030304640b0715084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 924288 1250 923038 923047
    0x10b070c0801060e1603090b060f040207050708010203040210020303040203030405060711040501080c0a080f0c0405040311060c070204050106030504020d02040f02070204020d02040608010b03040b011e0503030c01090201030c03020403081b0102 106
    0x56003030107440c0040c061000800b0302c0b8549809140c00d4144080e240305d0030545031124400001d41840140c64002d142525000405841503010800038801c401c0c01901e82c0c07181c460001085c000540003180b040340f0a0b102032640501002c410f81e603d00007910003c0d0326801c01e110500150900c0d0002d0a59540118114003c2003101c4011030300300c41081c2c202030f441e038021089004043c140b03080341500030955280104108089050304545a8a440c01064446d9031241b0106007454442c0d00901d000030b81100a0302c0b95410190b8103c0403551005800724020b90900000203542c80c001d1007514807894002d080f07036034001007039800c0100038502c488407045840e07424003200015890320f20141048079074480f00181d0351401c05c80080c3c80450b0507400444a5a03041082000040c072961172141159414161800400c0c5006003004003202c2b02d40200740c2600c00441d1802031180150401e0801754001e8800708001c0442c40412000d038461404003911910b0100b1000d414038007880d13022510616000c0006080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925538 1250 924288 924299
    0x90109120302060106090b0c0705040207020a0510080603010f020a0c0204090203030d02040303050301030506060303040b0f03100b0d02030f0601080108070302060304060204030206070b0108010c0816030b01020a02030f0d030501080102070b010b070c 108
    0x492100340c00035001a40042e0043c03190b290000104005440c02c0e14005040005000c02241d580146000d19406690042071007411503d4a00038500070b018001e1000e00741000c01c0c0e400038840c3c0b6007250854860342c202415052001e100f8800c170750071000c0f43d60300e280205185400340b00152207284401c81c0c05202c1000b510501a05901c0540081c600c2035645969079403660034440d140040150450380700390402c0000304648940301040321043d12107c00c0480d10ba640740845075070301a0752a0300c5030a003641d0010304400c104400f94003c5120f003861020b075545644030f42c0d004442000090145000c3c5900c103007002e00140c80d0030009035070b010f44258000b6288c141c80e98045a00d43d00040310850b00702e086240103010f0101d003070103050034083c8189024009440d0240d07004032410b075001d41c000d05042d55008040c460b84d1080c01310700305c1e45070041e08403420391442182941d69076000e4140000001e00d80800815204418000c0719642034101060416a9080ad40003c1341c03540a06811201c00c02c803a40001031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 926788 1250 925538 925559
    0x40c08030a050a03110306090105010c05030f030703020a020d02070b030c07060605060a02010c09080a0b06060c0a020405040b010801060501051603050a050409060303080406051503060411031504060c090503070608010605090109 99
    0x81259403070355003a444442d421005411784003860130800c4503100900402009403a24a95141102c00c2440c0142502c000e80c1000b07821813107180340c18a840103001080011080d01034000b490011800c1d400c80703145d00d552441c01c82c0c03201c0841c003d84044401c10004540009910300140c00c01034040c00000402965500c000b682c90346c00b0081140141c1d44407550766074a00d80001e0002c004000030f4000d8110356100b0b543d0f405068100600c0203108200114000010711400c0101041d050341c041c00c20072083c200b45c10400d0b03141c0070034414030b0f000e503017019404100740d4443e4007a15060240b81c0400341502034a81d0342903d850300000810030410000344400505080c0d2030044900541c041d882c0c05440b403c09081610a070340740140f060001d10807400a40243e85c40c0054025403058000c6005030f030180c00800002c0c02c00600d240c007007410900007823702080c032085602000642d1282e03140c80084d01d03510014103494121901c90400440c1503c0c0042101c40d00620080080110514041c51200c0e00c8241020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928038 1250 926788 926797
    0x9080604150e03032e03050303040609060605030a08090d03030902030601150906080402060a031a040e030c0613030206070e0d0213020a030606140403030e12030309030304031209020a0608040c0803 86
    0x11250404014881c011020307038851800203045080181d40b0303615140c000e00d012050800341e4500c60808501c0c00c801c03502d011440070005140e003c002e03241d032820b080c10400054a80040c06a49151816000150525001901580300b80c0d0100c0d4480c1400103680030002071141544058090540ba407151000603601400710074060800010210b160303101215004000080316003052041c802e0b0340d4280700140c1d8650007910030742405072038003081262050765007007180c0c41d50002664006041413103080c2c04800100192200c0c2d0301203422600c191303880e4a403403080b6030707611140900540c020201040c0c05c0340c86135002051850b40601040ca440ea0990b0206400d00220885184a968082100c03400c00750706010303500040841e483c5c40801d042c09082001075611442c440201440310611402240da100c00c400c1650030481c1c40e09481d00d034603100703021a072654001c45048000805c00c0c130b0b6218035001d1901c581c0240c80e030090400b450039801d0040a40f0442805007095804038090313440012450810070080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 929288 1250 928038 928043
    0x2041805060405060a05060f01050d05040606080d020304030201030b030601030c170307050a0606050f0102070303080121020a0905010303080106051201061115010303020c01020705180703090309080102070b04170702010206010e060109080604 105
    0x13800c3e00d00d41810307a007003204c1c405440300780718910800300214142c0e07114064a0621403010070014140d1200e01e400c100802095204410303a01640c80c0420145402202500c100d034000e0301c0c1400380002500030513403500c0003404001c24081000000340030348282203e0301c4000a410b86e045a180030030f0307030325018600312071144100c80c003641310032003070105060210b140d00340c00900f0300003072010a065941c058003441050103400c50080540c0881b000240c1442d07000304141e1340150040cad454503112100c00b07020f40000d000c250040b6001e1000014568483d07021602054549100c220050742410001c407030150a0454070704003840b40c180200d00441880b2855802580b2030340080800c03c003440700290030520290704c103a101e84204110841042036000100d44c0c08032207490000760900d00e0349020b0740d02d0074503904a44429032010400340100600d4062050007036000b00c442a040c10300903040319285200c5c0d983c0080c01a00130800412000030003120050300f00c030050404c0c00e8940c0d19405814508035048405 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930538 1250 929288 929293
    0x60109021305040506010f0e0a0515070b060102030414090601030204030813030606050102010e100e030705061603050604090f020108070e0301020a0c0b0c0301050102070b03040602040b0a0302070c0e0601090302041805060405 98
    0x36007040c0300d01c00c540040200720946040c003ea2401d0000a40005201510320041c40403450904403550b807035402c0d88015000007800505a5490800162042c2e04058005c0300c00b0003e020100d103166000000b510200c841322102e5245c0d0000360824450803a002500380740c10b140c1c00384800700000f5201d8014200c041d44905e43c0b103075032914605103801942d040364411415039160003182c1d95150b802088920940060042c049008081d0008042c6180304115016115014000a1000380310b403981076002c055115a60502654540780c04001c00c441e68074100804001a007041d1b8030041d40a0010954011a9400e01c01c2024036584042400da0340080803d400090524008404021050f1200341c7c0100224900c07600315814400003035540d02ca0b43c007d05a0070034000c0000303010001c2c2601110013420752500e5403030b2100c141140240107500144030495400ca04c4000100c0c3c1e01c80ba584580d84075840585d034074a0a545140c00b032000a14440c0c221280404512500d01e001c03031000c2203014012482a1700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 931788 1250 930538 930547
    0xd0b03010c030204050109091109090c0a02010e030406090621020f0c0610030203070b0d020c0703060603050c01020d050a1b0506010602150a0b0d020603070513030507060906090b070809010c0506010902 88
    0x20142180e28108400050600c10f10042c04181d80c4500740c0700640e4504000020184505014842580a51107003507511804207000c000303d20141c3d4001c1d19291845800074800030202e030000a8890050780202800110201010884648035903008040c03d41d41c56800000e11900c000300c103081c2d902480c000d82002a00050b580301c2c45030200080c507403013075441c10301c400b11908583c00280c46485500c01d107107011801140724031451505ea0304030390400d900202100c0000d0703503034039080d40608103600c4141e840b4020080800303000d500100e180c4450a07000c1d6950380c90818594010b5030404107020201a1782c2d08402c04ca04002003042154501811039500204914034032180c6462400200070b062038076103810a11071514580320320620391403046d41214607903140e0741c2d4041c0841c1c8034040d4608040902091344000420711901160719400e03074074556106418152186001d40e0301004520561500c3c0100704002004580a04081d09010314149801c084103031741503c0c0c5602e042c1c0283c1081d0043c650008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 933038 1250 931788 931811
    0x80327030301060e09010807030602030702030f04080c0a080109020906210102070602130602030406020304060804080705010c03050601021c0206040807170d02030105010207060c02090601080a0f060909020907090305060403030903020705060d 105
    0x2000c1042d02d002180d0407605507041c410b003d9110020749c80001c1c245038001c0042034074503000303006481c54044074904141e2200d40c1c07100c11555036212242814015803440c0c20100c1c082c01c047c01201c032000c0e0003410103d07a5445680520054554010300440758405810742502c0c0c01800f80024440c1502901002d40c555081200480c6d018000ea4020015507004000802545402100303403001c40c0c2c1d26040c40419659603041c240c01c0ea100340640100207502e448a01d0080381e4040c0e2265000e00c800380c0c21078081c0c68900000c140600d001c62400000369000344006030002d00e407040207080c024421220710aa81d00852118180c80d00100c4d04840000d4000c40103101e1540d0422049008221601d42609105103507000704d5001c040c081d00d003c0c100614940058407080e83c9801c4103180c40a56141000074581d54000c0000810603880124800c50420f0007045542e842008081c0650b40c010020344260b0b00c031079500741d00070002d0700070850540c019030314001030f2581d584020308400c1c4030150003c9032200710203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934288 1250 933038 933047
    0xd020303160c0905070903050703120e040c03020310050105030105030c040b030307020306040f050f0102040b03010605030a0b10020d030b030f03031305010e0d09080f0607020304140a050306040c0302090a0204050d08032703030106 100
    0x4045d81c040003155681003012850000b541f00c210798100703900421100b0351241c01c5802c40c4c956800076400c5401d2481600366942d040d80258415a15000300d00740040d200d000440302488284106641030380031690b822441e20785540314080001000b4102d900d04685580402e0a10908580c1a14502c13100310420041c048180141c0da80015488002c40c9800d0400316410a180018062501008001700c00221445066444a07135011001490308410450f0314000941d80c00700242c01038002420b0014600807030400003184209540341a02442c2103030303a40e842c0103946400181c0107885564031070304400c41c401d800b848132900d41082d80c0c0d0b03044051410101c240f0f05d007600110146000354403005c100583c4a41c08025202078a043d1200710602464550000d074401c1d05076000319615028020500c410000309032000012a4825a403011007680ca8010f160103e016621503039030480000c807a40d600099003a0020340d484003a90326407030740801c600d6540402c2d104000a0520381c80d80b00000610140c1c1c2c21 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 935538 1250 934288 934291
    0x501020316030903090e07020a0507030602090307121502070f060204030809011103070b04021201090b01090504020a0501050301030b0408030a06030b04050a05010e0a020f0d03020309060307020307030905010306030b060d020303160c0905 103
    0x8508041c040f05140d503500030603014681c031a031101c0b11480b50128a600d4800c0c4080c40086d0b42140850340c2e040d4682c1400c2d4003e600c03c07540c0320301c6031003010300c0051b00401c0d191145005a402034215001c51240403504000782d072112808a031001010128000050394074406400513600600e40c0395102c03444000054038100900c5000c8105074001e0080c88006040c95000d141e00ca9410307981600c83c170400e2008039000d4104010b0042026060701b00205088030038ac0e11043c8500d008a540d00e01a6550300010744242c4402e020181c0f407900036100003004075203444011a0032501000000038901da50ba104c0101c12030041e60100d5850304809110340c24844240501c60a040341e050280c443c030501940000d014140d2213006502490502c41020185802803040c0c1d00c41c01c402034580342d564680008000c1d141d520821044000ca58041404203495103e4880c46040d690700c0100c0d06419118034042041703101c1000012a418070082044c01c44060a464400345880e12581100304036500700004078041d61070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936788 1250 935538 935581
    0x90a1508070903020f010309020609030304060e0a06050a090603050603030909070c03030506091005040e010b030a03020a03080109050c040308160c0b040e22021309020604030b070305150105040501050c0106090905010203 96
    0x140b882840980d80c0c040300c0c034002c50b409007400580045248042400c0303018070701910f42e06000118000070141d4000110030a42042101c0c50101c441d00c5a0040d00c1c14040c040084001070a42541404464041d038005a00170400408a13810150030800250402100301d400c1030000e03001000c02405c144d0140583d54000800305c54800807817808410240c0c18ae61240302e51482203841d2a20005c96040030740c0454034400024040c5e0b103c00c0c0403400d010b59102a003840031800110030000000d406103440c03003524002d0ba4558200c510703240c0b45440da030315150001c1019449182c00d000000f40000c2e01884820300505503034054585440c40c05019016001000f0f10186c0f0711000555260100a10560340c910300b030b07904880300f00d16100b4407810070000304010000250041e01c0001d0100038886011034a40c8140302503607051146984a200c1181580c04109003203010032800c0c0703c1030009600170f10160041030000000001c0f06581d81c081c1c4001d444503001c0030f171400d95001003445078460001e91032044692 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 938038 1250 936788 936797
    0x10201090302030d0b0a03080408010504030f030902030606060d020d060806010602010b010203070b010603110d050a0207020f0415030b070327050105010b0a080a020a031b0908010b01021207060209010302090a150807 94
    0xd40c40181d10391040d10701c03004140b50b454001c2045543c54030b883c2d10240d070b04548070680b641d03104c05299000340f03404d4400783c002c620720410a0540a00c00e00810b1115a4050068a829192103040c005250801c208403280b0680078040b0705039040701c0744075110040000070000c120310b52401a01070308448007030908a04542080080c40d0204041403203136411504c0503d000616010b00544850190144020391143c031424042409030b026103503005040390038001c0381d111048858240801007119440c0f00703c40600903101e401000881d01c12109658414450304001c5144da5081103800303402204141c1102c41c14400c0310100d42449024440c1c2805400032510071441d03c54011006080180018200c414076600003440005d07840c481e030080d40d035070442840c000105020f001c0700a40f081ca03540c050b44002d58a0101116203a41c4001406824100d601d14110b140041c1500c500000c0e40c0003640a905042c1c0803c420b1820703880e1841e0100c02402d01140c148508045260000c24008002d0071403010070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939288 1250 938038 938051
    0xf09030314090d050601060512010509010e150402090301060305030409140105060706020a0215071110020915030a0902030d020d08100303051603090504020309070807080303040507060c1b06050405030606010201 92
    0x2a04450154891045410503a80300d90b501c80006190350b022510090030340c0030748400096000e4014016003805120102d014050343c1c1c0300e1080c02100d020034072071800d541e00d8000104640b0b4220800c1003c0d12800500050701d0406030401090075a14107500854031544005410822404188159940070b1041c440203030f00365240c01c0c0003c000d801891000380c030b05940001c0d550011030007000f1002400540c615405014505480040d00c10020340c0b9014a2500a030300d8112042c030080d01c01c8820600d001040c0184682d50407032980d2540c0c20041c400c2130082e41c2c030070001000d0b903410080e007042c20889600034180c2c000c80020003000320201816050004800c40028400690004142c0d011020110304201c0219001e00b0211402801d83e4480c5401038800801d00280000c0407550034103a83c185d104984101d55a415100e80c0c9200440380604039420561080c005940715040710b40110303004542204200441100054180d8401d44c0420f010500000d000c111b075003014441c040d4440b0090000b040700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 940538 1250 939288 939293
    0xf06110a0201020601030b0903041809020f0405010b040902090406050406030b060307060f0f050703120608010204080114040b0a05090304080f010902010905010c030f08060d050106090f140c0909040204090b0702060105010f0903 99
    0x5039075041c0001011016500005007230400c04205480041a41d012001034085040782c00100070071b9800010b90040c450403807514000e003001d0049a0484030610180d030300d058030300f403c400004d4100702980b9a01640b582e4000407250307114000d84010703501900d5151480c3c1411700c20146070900c00e6001c4018448800c55020b0110b40149560301500384c98105a50395848620f802c03034440258404a4003e10703e004804a500c0c2415030191090307a40d40d42c003c2107405202e41d0b00c5010120100da00410603c0907000181c1c4200c80e1f41c10464122480004403810141c43e0b542141c28041521441100e60795284401c0c0155a030028154005000070300b00741086150980703004155400294519085c4090100030aa00c0e0b11200da40a6855400c007008100c501d444078804006448640b845804032400d12107031080d01c0c00621011401b03003010212292510251009203d001c401c000c2099034856036442418011454081e030052040b44250f000e44810340c1894005800856200740c45000c12030300103800d100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941788 1250 940538 940543
    0x90b0d0b0a09030302070b0906010305060c0405030a06020a090302030601090203040204060b0c0c040b030705100206010e0601030b0604030b04020109031a0702060108060c0409050405070504090c0602060702010b0a03030309060b0a0f06110a020102 107
    0x30015544500411840c100f0b05095010744250b0000801016102c0304000f001c00d00482c80034140c0e0f10440030b841d840c1d111615150f40c01e0245004959058020204032000560f01d64010b1030b08201c07500300102059504d4001a09008013640400c1240d500041088110b00d028031a18000c1c01c5404841070503d964100f045544021854001d409695210100613240da010000c80000304402003405807030a81000e00292266020312a0384d20880801022034800d41c0603010301d008146014100c2070030036155484d203505401020b0700c181d06100c4540400300c04992041000407031322980080c400400d003001c1c0d00091418005a0100b603c940002e4288400320228000f150203c0b40d1424011540e900c41d42045801e03c1b016900c156801441d1142e0300080104000c0c0b4007049402680a40303071907645508003030f4281c940d0003a82d0395101c0e0190800744002402540120f4505005480024401e11083c2c00f01d81c4480041e0040c0c04101020302040050304d17446865140105081c0001c1c250910703041e80042d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943038 1250 941788 941791
    0x501030807060902030a02120d0801050307050102030a080c0408070b0405090f0103080f070503040e0703060f0f050102100f020d0c0201051006050c0309060901020a0f0605060906030102030702070504050c070209040c090b0d0b 98
    0x918054481210400713660b42004462855034000f0500c100c528100354515a684044290341c0000c5a060000000c141c54040b13520340440d00e068024500d00040703183d0449030050700a00515010406000c040741c90b200801418010740a8241600c1e40d0b40d051004100203ca002410400a146058010300000d07824009880d2036101c246041911580d403442e05500710302031a000b00050180c44401c1140b0154960451000c8424100507054501e842d00740700310002002d802868056170107030795204e010605980c042c01c00203540200050030042c40c0c0f80d5a80030b5611140014005070b46800601c860b180080440030003e25117070403d6403401c101a44595180e02466003640d10036900801c10590503402440b142c030820394482c2081110070b00324a40b00005002c140d5000d8010341c0303100001881d03801c0510841b4050b10b4190000e054a03454041000040c1c40f00411714540510306000200041e11f8182d001d40c01070780303d21501946981061090300840b0400c00c8000c0c8100e2174103581c3d0340818000218a0f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 944288 1250 943038 943043
    0x9140a061101020903150609060102030717031005060712080a090203100b0301020909010801020403030305060f03150711010609020c010f060b03150406030807030203070b0702010606020c09060307080d0207060f030501030807 98
    0xa69040c501074003a034020300641c0003942c0c06000b218030442e00362514080341e900c10042140c03d00715680700d40004a81e6801452001006105650310300b0004681d01e102459000c0144400c450780c858640c00412480e400c6103c003103485019810062400603008040c841d40304400300c0042014450a400207a516203114428199141d0345100900c850b032401e40465090300000380526105580d5084007900030761251100740d0000c0e151a0102d0700c149841c000200c02140d00600501c0c40d444c0401c2214241c6202401c02c009000031417a01c0140a8420b0150600a0a50180c0161100d81030311240d403d45040415144145241000a02c18805400240c07034100c40010301045500300304002042c010324035070300b015041140100e140020164004010a1a54071031202e46a0b1612901d0050342600c42030b00407131001d42c0100707100c0c00e071030300782a000e0a900007402001c8448103951100140e0804d020384075130f140140c10054080c40416041265103440852900d0100081d40c03554882e12502e00811100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945538 1250 944288 944297
    0x601050f0d14010305030d0b06030106050405040513021c0308010f0e0414070f0b03160903050c0f01020307080c06090d02150106030506010509040f06090608010504050303010b030903070b01060903020109140a06 92
    0x99800040d0b485841c104900c0501080d40e540c503401e055982c0d4202d03040c001c3d4294286404c9880f0303401d040e401d49048070b9036920b45a0800d0305200800c000313000001c003800d2840c0100d0383c0c8000583d407030009440b041f0050031a080c801100c5030900504001c2c058200040700d40c400a010000c103829413a840b0341c85a003000d140300084801c004054204103159204402ea0301ca102030100b500c0c1e03004001540907001a040038452400900c3c0b0648040502c1d110280683c2c000300141103090a0401051540040500c140d0b45420381715501c03540e03543c000b010100c0c0b907030b48024200014a4070070070040709010060300042041400040c007800b91340d00140214020035846202041d56a40079405446a03460002c0c42401004210a0020000c000c140b141d03800792400c2c01000600841d061184a008a4100e00910300d941c3c02c20021145607400078225902c244802c2085101040e8051040343c060b00c001d42d1082d04051640c0001008951a5002031541b0b01011102900c03a03912404c0c00001c03200706081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946788 1250 945538 945547
    0x30f0209090708060403050a08060102011b0e030c1201020901090503120307030b0112020a08090c0d080708070f05060108010501150305090a0b06030102040b040602010f0e03030105060a0e03010f0c02010c08010e0601050f 96
    0x50203400c00c00c855103c0e201c0351084805000406401602510524035980e03071751801503840c0d50049090380c840c4c40300d4052001080d040048603034492000c03014036880107011520340e481450f010034400301c401110b0b0180382e5400b090680040da484022540100b0b4214000c00f1886410800e1410512003d4805014944e40f226000d1259002d803e040c0070400060600710348421a0b803030090b10b03205003111100b095020384e00381e0858600e4440701c07036109690004550380c2800110b03074075a0000d52007020300b035601103035200011000a40402506000c1e0100c4070022942d540340c1080c2110381d001c0400780401380740c200400c01010b000c0000e0f281c1c3e0711542055403a00e840d100d0802284c0244119044040000300004e800704d010742c1c0540040744c0004111004003c8895004c20141c0c580c002030241540c400b1007041145c034500d106096211445000a00018a914078200740078104d800020038480940d4440d00144071140d0880f0050340180300100e54200c041ca482c47c0020003d100e02c062000b513a55000c039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948038 1250 946788 946801
    0x402040605060a0c02100503090a0602030907080a050a03020106050402180402030703090c090b0f0409110904030201020903010204060305070e120c120307061104051219030f0203090406030606090c020601030f0209 93
    0x200244000c01d4003030141d50380c0701040c00340100b880f0070032803050703008049075030340300082d9031007001240d101e81415800f44c551180e4903a540c0b0065031000d003540e44d451044050200360044203000005609100381c00a00c0341c2c804524020782500c3c0030b80d00c40341c0314510600c065a140d000e005503c1034848401c940050f41d903501c1c403401740c0040a0040700038048030b00c103040c04038050205a0000c41c406808507260801300d113210f002c110607914254002880c500c0b103140b81b405a410300990094101d446030001505040c50803005c203003242c0107903000780c1c0025124000c0c032619940040c503143c00d40d0420303070720561040740300d0440a5803000f640700382c140901042d100240e5610390034801d454685a02c10b80c01d0000300c0d2401c6403d0700b150058043c8034401ca05002600d006d03494005036804085004845961130342189407030940c1c00c603030843c04090a50004200c1d0b4841d070b40e00c520614015500c41d0b4000240a4180700b020f10071500300c0c012010a5600c520014804a45450b03940300316954101e0341d8551a41c1c411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 949288 1250 948038 948041
    0x2032502150405010e01140603030904051e0403020601090608010c02070b0307050c030414010f090e0403120621060c030207080f0906040302060a020105070e09070c03030905031e07020901050315010b03040204 91
    0x1d440c54076107803160740c144800c115041d00060b0000107088028407000d4003004520300000015260203900d58800c0200440c030703040c01c0c0c00440d4040403000400c4d24141c9042031400e00104225012001600000c00501c004201840794202030000140200800c1e099008003a6490000f40110000b109000c0f001031025071241d021984a001203805036501e4a48d81c0784400101448c60041e1408610700c01c407401e0046114803032807401c4500c0006085d050b40c0ba01d481c02c0c1c48001e00d01c07241c2e1001d943c40303c502085450f0024030040f4058507200c0c2103c10550642042400c480703011040c07008040c0108010000700e901001a18484101d081d0000e540d21080030000d040741c801c942c0025002100801c24030200e503010340c8050b10400035034072650303603900780e9004000d440c00040382c039900424400311403440800e2095005003241e500c2103049a1034201e2a412559803010031008440e032204d00003c0361001c50401c0400540103200641c0201090750560852249100d414055151172500c003000081c01d55859 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950538 1250 949288 949303
    0x315060d02040603020702030601060c0b040f030507021806090603010203070e010806130608060f0105030706050403030302030601030e06011202130b0603060d110402070308010305010506010903081603021203090105010602070902032502 103
    0x100c5045554550310980036000c0c0d082904241d11a015010001076802e01407030032401a0307a4406030034001a9141d03030341d140c0031500521041e01005030a108910045c1c40b030b210904040c0040001c0180030b4640401002501c0c000100341c1d40c0664018801c0c407001e160058400c800132882420040c00a03694500450015105681060780d014101007000806000106007640905600c0400422507a03c8030141995041c2c00d21a50300080c10402040002c248607501954110f901454049540c048142c040da250500a8200d080e111000500078001c519000c25180d40c8002c05400074021601600c1c00181180001891103014014000c240d004015807941c201078a0500207104648503401818028400c0740d0034001103c240d0700c0e200c04a01c0c150b00805180044030350210215142105560f070f20351807840048400c505510031085444c501c2d01c0700c02c010718822110300c0c0001409600d032090007468180d441e404142c1e412b2040060108100c081011000403d054154848007031401d00000c0b841c1094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 951788 1250 950538 950557
    0xe040b0d060203101a040f05010302071103010507021c0306050a06050703090803030901051008010209130e10050a0b01030501050901030309030209041103030703031505010e0109030209040f0503070309030204050c040308031506 99
    0x400010007002009000c1c1110a50f006800701007050103118030505c107613201d54040c040501d584480300300100c1d0320039002080c070a40305000843c1481204d2010909441081d10f0b5840560070000a80d500c4920031180b0440701e81e51403030103201c0c0b03618050214a4010031801070f03000300800010500d0925000b0f8942000401c0f52400302c0ea642d19084031154003d102c01d1741c410440690403d000140e0005c14000c2e282081c0d001404a4030403040e812003a4002c00c540310f180065070040c082000b04038a5a44602441241e24001c0801d0301e8007035074001003c40d141600000c3c42210030704010300109a1102480d420740f68161048002c5840f00d06020840000c0c20440c1d540c180300008000d0101030781900b101c20150000c3c2c448103403d90700c5200640b2440701c40d00b41e1038006094160104054a00b030030f0540d400500460030119034500546030309040d5403190b28250085410f650040045007081e1113110b0344200001112070400c6e0441d03542180300d01c0f000e04048400136001e0024440d6585240031100902c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 953038 1250 951788 951791
    0xa0906020c0601080d0801060507030203031303020708070305010b090906010f090203060105040f0b07050706030e030a031505030d0801080712080306010c0309050604080703060506030303070507080a0e04020f0408010f09030e040b0d06 102
    0x1030f03480b82c1c1c1c10f1707568880d508598000342c1004000030701c05000f007003a03588603503040d000fa6056036114020030440705100c00301036003184920036001503121400d20078000030318003660000c5044441501408070340f00c0040c003070000c141e0100d001000703c01c150700044c2080d00d44504000d40d070b9807506801210305000c0c1d5000201c103410304901c006240141e04005104061155054843e642e90303803002601240c02003081b13200103400c1000f022080394481e81c403490380c40c0c1c0c03c0503411001540b03802c00f1030f00d08801c48070510003003000c2000500c4207000c2001240000c01c0c00c1c540054056285580e14481400301901c0c0d241404000082a0200750090070030f28003900001d00115204d070750310502184e44c0c1a03d0710060300d4152130000840c055080100c2103a10030017031030315807518000184e83ca000ca5984401031030002c002d010780030504513030b4540c0001d0040d0b9803042c461320744590030122400d01311288140ba080d091840e0804000029800c40300c00c101404044400141c0100b00d000440e03200196580010300e00d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954288 1250 953038 953041
    0x2060a0504030201020c0406030b07050903010e030f0c100203070203040e060303120406050a1401080d080c0409050a0204090e0d080402090702010207050f0303101a0304060c0c060903080f06040b090a0906020c06 92
    0x80d48003000e40101d9000b6030889200f40d80030300c141700407509a0302001d0700c4c03003d0300400200541d02a00c000e040d010302c09000001c41100301d901160840d045035081081c030a000107100003070a241000260300d180b041c40f04c00c51550410440107580c070b206602c15206c0e00c0c98040000303007459509200f1f0391216030754880c000d0180d00d01460308070006c1001321a010302d420300d0000d4205502e160781a8103070503241d09500421a0b841104400d4510303c8000b800000810000c000100f080d0300356005460040100040c0561078500b011006001c1da0072442049a15030f120303d81003408598000d2030b07690800d8058a01000b140c0b18810100e0182c41001c1d0b000c5c026220741880d03550940ca0010096100740882413800d10307215102c0c2c55066140034a05d20301c1744801800e2022401142203a480424040306500302200c003400195500015680010000e4010841280800c80e20b09000840694172040844040198050160000300650005404081c43c156900ca4980070028154125143c0390041c000f1121203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955538 1250 954288 954307
    0x41203031e0f0509010204060801031506080d02070302010f030203090a030309050f0304060c05010e010506011706010201150303031401060201020901200307080403080a030b0409020a0e100b0406030b0405090c09060105160206 98
    0x1400700100b101508625210004039503a5041c0b0980d019a03041e0750700c004450740303961540032100d924140c1e24800507aa501d00001c0224042007800d8100c060398001e0814603241d400050417141d089003550381071600401c200040e1210100d11443c01075494140000c403c1007504040b840d28007080da6619080c400080c01180c1e4a400c1255007803968410b0b8001d000031202d0181c01801d072281030b55004e02149043d4489600ea02400b0581644000103100016048500301030b0800508016802030303022a6542003a40741c0c107000352001c2c501600050000758a80418480020002c492074040c0d5404681203110f044902241841180c0c0d0403504500320035111070306d0b810841c0f80340d84541045004a85003500280311401c050088100130f9030020403030a42c80c1d00e099200300c0110782c000c6c80c90345510800c40022504c20a114007034006003009940004000410a060100703d032030241401d03100741d0146840b010070351b0360f1106050b4414001e20740140c80300200c1c044503d1038060440029400032010410fa001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 956788 1250 955538 955541
    0x603060f060f050d0507051c080f091804050d180e01030302030a02060f040b0402040c031b0f020c03030c0d03180501020a020303060109090504020d060b03030706020414010801060212041203031e 85
    0x1500d160381d0701d01952070f64400400030640081003009069030061482040b00b850034445e00c2c0080b54040c0d0030000d20340390a0340c607040d140d88603030f07614141d00700049150b070b0107410141007040d81c0c01031050015285042540302e1560710211072411400708141e102450080c001c0c100510802010401d00744006544c591070b002c3e490f034000344a450014070680c0b00045058034a4542c1c14003964020a110b20b15445540902024140320207400040c1a250070042c0f01e280c401402c04544900380d682d4004041400500003801d100240507443d00c80e500a0283c0c03c03504e0f0780401c4c080c002030154100020b005841001450340f0754448400035069520108043d09000e4011004520641d406d0303aa400380c0c01e440d8000da5003203841c2aa8069088141819110001100f44c0e210001c0c9040041c110390078081143e403064280d90003600040d0480040d1111841c2c03035600820500c4c050172050021f85082c181c1c0d9420b40b01d543c040c911800b941c1c1e05003003032a4020b0601a5100c9140041c4160000d850308035a81074400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 958038 1250 956788 956801
    0x301030209070807090302060a0e06030a0e01051302090a050603011508010f0501060c030203090f21010603020315060603070e0d08030a05090606040b0307050105030a0608010203100303110105060a030b0a0603060f 93
    0x240107408101c00180564412600180f04840e552603220040b400d58083c80b5040e04462041c506020603251070f41a265600400313140305841d901c0c004a0740301401132043c0d007503075405009280e000042080340d10050382d504a00c0c1e503200481000025503075a0340c4001a014104440c0700c1800d600c041d58000c514403e040d0810081e08001d888280626661500e0449201c81c2680f0301070011b070130605c0071110301c1c64440032120145100034203501041042291540c08500e80c1c4845c1c4032180e550b0203003042103007070078008082604442d0b4442c0d00c0c1c3d0320345070011541600c00140034600f080400b040150080d81d41103042038030703d500f0110b11a121725008540c2402404162084d03c4188610400542c8600d854000c22121a00c0600604105c2c0c3c034003001941c0035000584950086d546510000c11480c0f000d04c080c5108441e6000300c00549851810003030032003110710000b05c2c40350341081c0800090361102c402c03030011260b21040880b241c0d514941080010040360f00014440da0406105141f008140d41220 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959288 1250 958038 958043
    0x303040306060305160501020d050405010c050705030610030525120302030c01050a020703030b030705060a0513051203040302010f0509100c020102010902090106030b0a080f0606010302030402030304030c0e01170a050a020909011d03030103 104
    0x45c05a181d1005a030390b51903c20a07000024000c101c01c2c03010f54032405c94480c4030740c03294084800294407031002a0401c1c00858200d602d1100c03204d0100240030040001c818950f911080b0010b54000c0112031101134045070080568092900c0200350405200700219203400411000800840c04c01107e5032020354800314042d0002410180b0441c2c0d58079004c500041101c00c02001c07145000d032041016910b41d000360f09101c000000c9060002016260480b448000d03068510113940d0713450462002520513106420b03194100841403200f0f0303d207515203450300c0560411a082200e050401440100e02400410000a4200d211480001152030305034100c0d506104048030f4160a00341c0b00d0b10300e296140308400c4207203006d45c00034004c60500d50003a0b0080d600640050240c0340b4254aa407244031458906900c5141c0c060305080042000703220715414110130f80f0601000d440e007104107841e09030f9103001e0904068420101e85000c40c40c404000d6110061000ea00f09100c0c0c05105059602c0b9201d03042440107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 960538 1250 959288 959323
    0x303061502010b01020d180f03050a0605010f0311040b060904090b060103050115090302090601180803030703050c0403020102100b040b03070b07020f0402091005070309090e16050102010203061e0303040306060305 93
    0x80c05454010b005514020b4410390050011020400c001c40340c0155030103081169000404d008145040c0458000c0080c501490050020003070914040b011180c0582c841d66062000c0d410600000301c00c090401981e0008980c0481c000110b00c001581c140324007801180e000d0f21b00ba441104100d020b200f090f00c90402600d081105c0d0303a9455561130041145100000050007500c0d083c80113113001c50343c02d50090b00c180340ca41c0c00540b010120b480212116007003204d60354808010004642e500d400380b141d10209a6180c40c2c1020700d103034000703951018481031034201d03070b0b80314581c840d02c54440f54000c50280100030112000581e4500c62045990310004d0140c6c000c103501c180819050070305000701c03038840ca00a4444440503009030b02c00c0fa0b83d42c201c1c8070b0407403c000d07004100060030180d13400340c58041c030540c1015000c65000d164640e00080a035030321040c1564014410801280e44414111402c2c101c80420080d4110104c00081d00314880e0390001809070340b41c00404030500000140c1c440740c003c03d0380c80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961788 1250 960538 960569
    0x2010b03030406050403020d06020408010207030203040306110901080109020a0e0301020a0e01021b0a030f03020f01140601020c010305010305030405010302070201020f060906010303080a0203150d0f020a03050f0d0e03060705090102031204030306 107
    0x24541c03644640d00031140400d404210410040c00c04035040c41e030070350142d2001800c0c641c54540031400e980c024400ad4005920114081c82405913502c41c020850829140503031808040e100042e010344814881c040d0810f5001c03c00c0d44120307009410070108401d004000315540c034130038040907000a186800c030700e0045c400c4020090303621303031024002c1504d02401000c61016030305c1c50b51030300000145100110110f0103981041c14404500b4000c0d14009001b00422500d6032604000091810504486560405003048010008150f01004940c142d441c00c1c603000d41e031008035000503480c026039500041c0582c85200304100600c2c0307010804038183d91003565808290745401c131410085e40070542d4100c442c14240103030907407149032029039081d15030322508600181466a8001401400a5510986540e00401d004141e912380c01d000000752592182403400c1c7d03403d80400031030768509004043e0010701600140074203082e8020420380d100c145c40100195120301c0c180c6002405000c0520480003501e640c000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963038 1250 961788 961811
    0xb0903190206060d0b0402130501031101030b010f080103021002031b01020301080d0203040308090409030e03030a0305010603050702190b10031205070302120a080f060a0b070605040b0108010504080703051804050403030c0201 98
    0x602c1c94025940184149102c0400d9114030024000c00350081703070704c051151002d424146940c06110300950281c00007031681800c4200240c140c0d00e840000c1810090040404031480c0e80040b034450541e41c040e0f85002c0180407000040e03140d8481c80f07003442038241c1320703905468082c0070540042d81a11060780c00d464046d02403d03010307a030728040d078040284a03003c01d105810441c00e0560200c1e0026003c1d00d0039207411100100400d0555100b02c9013100003d07154001400b21940600519401c04d40c148001c1041401000c1c4035904d900c0f140f9002042000d120000c2280880442d6200000e1904820b01103018280d9a0000d0301540c404a8210050300400410111106468060700c1c0e00c1c8a4039220100c10341d44030703001440341c035900174400c1d644003c0071100450b0100c14034025100d998420940011a401c060501000c03011050740045216230504003003000158004045e0342030a80e141c1000c0361034500d190f20582c0290f00038281c0e9a0004e25120400c001e265058000c220b00e0b000350340013080002a003c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964288 1250 963038 963043
    0x5030306030c03030403080301031101020304170109120810050603060f030f0f06010b03040803010b030603070801050a0605010305010b040305070b030a0b1e0103050a11040b09060903010504060501080f06010602060a020304050a0b09031902 104
    0x241b00151909000b8001000800c001d0405402d40c8441441583d1915031100d0030f034400014910400009a99681d0342a01001001c0e401c2e0280c080c4241000350091400c0245d4070b076070107118002d560103110040b001c44c080761600500d0b84245000181a0741218000c0540599156425490000584100c90002601c0080ca83c1164011504103004902c0c682c03c0042030b551070f1388040c0400303806100311a4000b81c2c6203070a109140c0034003201040451007518040004041c3d95041c1c000500e106401c000400c005000003a00400f1034162039001610390ba190300342030000748160070a146d0417900040400d07004140c000c9031301601c48000d0b01c0800164a03449081c1040f81c0700070303c2c80074000c001080b05020545ca202c0180c42061402401189040f01d001e0100b400d40d8804e840031110103441c2c00041c0000301040c00b50b8480c4400400c01060740350724145000b0350342c25000d0b04021050780e00001003030a00005100603506a03070007030140b80352400c09010881d5a90b01c4590380c21000c01c4281108804180301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 965538 1250 964288 964297
    0x120809070608040807050703060203010f060e0607060c0908030d02030105010305070807020606010e060c150402010e03030708040302040510030f03020d021009030207090c0e0a030303060e0601050301120f05031605030306030c0303 100
    0x2500144032880c103101c402d5550076006481540d49100034040b4800040c401c00100003e540b24400c0983c8951410760040d01015090300407109100c04c0d850010116101d14040d1740210f50458804032b0b0140e020f00098651b0f0403107070400d5039507003c0000d04061041c0150000e504840080c1d804001c1035503001822552400140d84090041c0c1220b030215030998807568220340d898800500440c5850300c60003265241c02110031161040d00800000c01c82950b070001d40d2200c99047c00d5001d1407929040ea603c0c1c2c0c140b8807a6000007442140d82c0c2004c112034a00441c07a40c07026643c00340ca5817100001c14107004e5079803c03032100003c005201d103440a800590031401103811565054008010103403c2018510141c04803c0e0900100b040c40301c02100346580b03400400c80214002e40380019030034141240080c020070014961810700004000400282c100c5442c090209900005510404040f0386030241c20351240001c84151604003510107000e100300400103501841c021002c540003405000145502e0713004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966788 1250 965538 965551
    0x506010317070b0f0c190801030b0601020f0d050a0306050405090c04060504060501020a030507020303070b0708040303050106031104050d02220608010b030703050d11120304150506010207051311090604080105041208 94
    0x941404241140c420881064000640f0481c2d42d01b0b008140b0108848a480c041011001800d024010001d0000c24a22207030029028406050582c101e4081c4568914003134a90700b042010015003030401e548650b101c140600f10040050016051070102079648003506203c943c407e9150040006280c506440b8040446030180c014261990241d06d0544154001c000281d8040c0003c009440005880c6800144079809580300c24482d401d150600038100d0341c05030070030700906180c0281041d0718403090f000d44007100c0c0102c85120200c051440030581080e040700942000010108640b070380f050f100c2e008141035911041c0201310220207402055640c0c080d500c0050804c1d0003495104000502c540e4102000e0040401265507140c0010081c0342039500407201071360042d46450f1441c0400c0c0590043c0307600a40244000c00c24103051100040c0000d041c3c200707c1880741c0e80e66486110490040b000e482808900400b51a15569a8840f0602030314003150304840b1448030071704c0b110a03907006a940500542 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968038 1250 966788 966803
    0x60d0b07030207020a0905070306080d02070602060402100309050106090605030d02120a0c081309020304060b040506010f030e0106080303010b040e010f0e0f10050919060f0803030a050c0702030307050601031707 92
    0x31110300c010341c02580200c5099801085240d004980260180600c900a0015540010f2168034210b146410900803202910454100d0302041003002e80c0015890741103038044400b0b584e0701c11401c000364028403007001c00070b00c0395080003400900551a40d01c5402220340941c160340320700590000498803080c0300d9801401c002028003030b0b483e40c540305142940c5070f00d1080c2480c6280c2911100d440b0010461540003484043d0000708010411807640100c4c0950b81007660300380300c0d508108002a01c081d43e010a500105692140220100b01d000d4005034014408101035179629610390404039000d84c028060103c0420700d000002503114281301c44403007107480480c140d030b4103600c80e070b4410000700300040c107180c00000d10b848001c1403542c1d0b14035074a402200210003d40502004072a1b6030103940107030380071150b21000980204201000170046a512074500f020010b5a69640c03000c03113071103028401c4007039018400810701404120307002800c54140c034000d04030a1458040c0f88100b003001c0c0f064041c000c03d44e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 969288 1250 968038 968041
    0x60201140f06010207031a01060e0409020607060b04020d1404020a0b030106090b0d02040504140f010807050d020603180a03050a080108010b06040b0304020f04020c0a02040506040903020606010c080c070603020a020105060d0b 98
    0x541e0002030305500440148103645100380d803521403c000b042ca9040f100020481368004000d29a00a2552640214241c07400d21498074503400007082070064190207480030340c4894000606607101e60440d6050400d82c04200501401c030015641019003c550403400707070022840110300c0c4526034041d41c0c100d4038560358024129060032824803281d0000d1000811803502440042440d03615801502040c1c000c01d005840d2903d02811542008030341a0f10184550b040b00100303000d540c41e42007044140d9a0103491395a82ca4507016440344843c0e008c2010481c0700d00071000c0000805074440000c2020002d02d40d901110340e40c031003640b01d003251200102280e01c40d100700410040c1c416150003079548140010326a0103c1210900403c0603648403d00030b07106908440d214008600d860700c601604008151010081c092a1b5a006503581101620380c034144005000d4410030801041c3c200d410203003e000c25a80728030b0750b9400150280d0060300c611405542400e0000311503082c00c040c0b05c58103582001810480c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970538 1250 969288 969301
    0x7050f0a050606061606060605030405010f1413050309060301060503060102061b070b0a02090301050406021306180302040209060403060f0606030c0203070b0103110103020d0213030c050d0c0303080703020705010507020d0906020114 101
    0x6030b02c29004201c000c4c0c1005860404180684240720041a48d078403120381d02d01c1c2510b40fa80c215100070004d450342d1454044400341e1a103507000141d5000320038440c029a2000181069859070040c4210190300140010012985540c0580958000c0c1420707000c07655191a001a07243c180e01e100c0c22107004211092141001190300300c07403c140c020000719030052600304010042400d564007200d00fa0b1340940c002030710942403200351000e00003e103942d26102268503411f8040391140d255074800070744079940204844071641d8070681107a004591260341040448413030540f2401500c120710031580800c0c5400450341310710307001004981441d5440700d51285d0a13800c41e82c801c44a05003c40c0711504041c1d00740b0000c0c9401e0580d200500c020015403031000b40c66031035072908141d480b0700d41d000342c0d0240c3e4804070840001142030400d507013030705d40c1400e000c0c05c00e60b20318504030020300413694050002e41c01c1c8024400440e4001c07808445000341981d0300000e031360300c40200307a09840030f4030601d51840800703500003141c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 971788 1250 970538 970549
    0x3030906130804030f050703050f0106180b0301060e04060504020310060509060103050702070f090501030506070f050a03090203010f060308070501060501030b010509010309020609030a030503010609060207030201050f0d0b060a0507050f0a050606 107
    0x7003442c41000001d04280d101d440304042021a107100b01e405601c10101403041c00800c024031040101048003c0c072000b0300700301c1494100000d07841c1d42043c01c0d4494110191030703542908424040e040078203107040f0b46e240030700304038020700401d45059003e80103040744004210307101d018120076540e014240901c1ca4641400440c014003000302201e0440c041c4401c08a021351365013070b868004040d5400040382a50550600c541800d134081d0a520901000c1c00d00035645980001c107450340a5030702c1c01c0c001140d0740580046405400f018100d508220b140040100c1000303c014003420f900f0380910001c0001c039848500660840b50700c094401e000c41da00740054001c941c4607421429200d4409001203080c801c1000110f407503c11b0510040300410310210041c000c265004498500414981c80101400c40c030b1500040c0c0780c0d226802e003010300c4031400100d0300e070002c80350340001480f10805003030656504014080101607800209007111a40211918080c08041c00507030302c6400e0b50484040c03c03664546204104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973038 1250 971788 971821
    0x50309010e010507050c01140106090b0703020c0303210a09020906060705010609020a0c140604020d06020901020f0a030203040503120304020f01030b0111010c02010501030b06040c0801060806040209040603060207021203030906 99
    0x9180d03407100c0c026414400c00780115030160742d041e19203640f40c00441c40702034252a01001c18205001000004112655114000c40200c1d00f440349030745e40d518100e007000ca0a1801c01c0c04501d400d440b0000355200355500070001d9030345481ca0b02da0203001741d0300ea401c000d00c25a0998200a5441003102c4045102458408010061a417180d800080c681d55920901420390700070901150128002c0c41c80d202c10300c07051440e0b0140510548018003a80e00e015030005920403901003002e007145602281108490b4001c1045907481445601140d00841141c03500a41c0c84c0d00034052540607004803400b207440114080c1c02d0301e0050b58001d05420728400d5000c0110000c02c0071090541c10811100341642120408cc801d41c60a400f50303a001250355030441c00c04000d07a05010300b039940a6850005501d4105920098850548400e0b14090000c0e80310080060064042c18500d164080c4ca440310010401c085503008203800c41c404d9030329090680c03c1841c200d8490004071168521a0007000c0083d2002d840c00000d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 974288 1250 973038 973051
    0xc0f060c0703020406120c05010503010602030708090d0506040c03171309020313080705060601030b010f120506060d11030f07050403120e0a09050106050703110105100302010c140d0504090b0f090402010503 90
    0x21a0070700d5590300090f0955607030740d2080d01d65002c907843c414180300074054008050002030804514551414800955a21891501418503030000c07031507005652b1808108072005400030107d5441e4185402c040d0001942c0d032004840b81100300c00b5035541210780c1010380e050b03d03a01c6848800494540340c1071101030340c401404065081515202d0f600080e000304003404100b8001d034002d00203450150009811101c40c01d1145040c4040c15001c881c085074040414103240860701000b24413925500082203003400b600481045031810902040c1d1080f0070500558412101079080c0e00081e10341100a51700c0d4841c42c00b0240802d01c0500340d0642c00e600134004404100f5000c0c00c0000300365551810300040712820380114000410000c0c4000505900c50b42030390000172400300810070ba090150b55041ca01216220007414800c050b0000360a102c202d0000c0f841c40d02c03806080d02d00340306100c41e000304180e0181c05064400b40c0b5188444580f4205a184020140030160070303c0519151074005581d2038000030001e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975538 1250 974288 974293
    0x7050a090e010e010606020f0c030303100302060c0a050d030207020114090303030c03091603060902100306050303030105010f021002040303020106060801080f060601050c01021902011a04050903030601030903050408070803030601030507020c0f060c 108
    0x40104102441040d00401b210340c083c0040c2807140180f18140b41301c1143e0031b48079610500511091411036007144080b00d904440b20355540c0d40980301e00c0d05004d100380001c0c00074051032100f0307007a0941540090203118403d0340c601001504908001c1d00078021800010303050352041c000500c05280c902d0041d50000f85450480706030303810b0b01c00c03200c062039240d406c00c49107144c0300c40c0e0400860405640852a81d526030606104d103904060110fa524001445024101b0003849004408a4000d10170000e030492107540c01d560380c5440b414041c0c081c00c124441d00000601d14400054282c1012034071a91181c04080503061944510004403401e41040110a04030f550801030030200d90002c00c28114490032a0b000814500c1e601c503c0e00c5d0403034800010640c011030500081280825000c0100c84c2c2c400c1d401d00f40060010418181110180120381005c50140700e40c01020500c200000007842c0b0518003640c0c28016955106800c036111042140d0b2140c1040c036a440f903180515280c5d014201c0d50800d4403c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 976788 1250 975538 975551
    0xd03090b190306050f0d02010807030f050103080c0606030303070203040e041109150102010b04090b0a0903050f0a05040305011a030a020907050c01110301080706050a020604031b02040f050a05060307050a090e01 92
    0x20442a80804101030880c01140c04030790308142c142c0185001000c0450f021600d0060f0f44010031071010b11188000c0c104141003000440d401d00a50040c100b0078000003003004503685a14200046600a000c40d0100d4810000000d1035880d0000c1201c0c0324407420790141d41403500d0218071850707008024008075045d8110100c0d1105989030318070320620403540400c446002c2106800060b086440103e070441c0250308200391000450365040c1455000380c20305d240040c002c0f00f103060450303060144611f4223038403040003c0e100c40b60301e9100000d0019280610700030801001d4820a01c0c1c4494940564a50560012050075016150480c0e08075844619801c18501e00140b09403500d0848035200c80c11007138854040b00500070031604210000250030b80b410064038005600034045e581d080f00410040c10442501c40d54131444082d0201d20b034940b540a001400035002c88003204000d4002210450a080e15210019580381340c00110001210300252545a05ca42031950040141c0313580600300c10199220b24 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 978038 1250 976788 976799
    0x1020702040203070302030f16020d080a0609060305060f070c020d060515090108010c0e0904031e050c010213030201030e0c0f060702030c030604080901140a0906050c010f11030907050d0f020d0309 86
    0x30f61041d240c40c1d800603036030710f001ca060302c0d80303800050f00505c070030076041c4070f8800f4041d000505941c1000990500120a588504c910b01c050b0095030842c01899050810020400c0000104140074096514120a559543c860700300c42d001c0f65160041d51000201f00b4810200e00c0561205030405030110500034040e641901003001c1004c283d11240c201d0f95a904071403403040c2d00501c8102800021107402000e414503803001000c900c0c0b0b40301c500c1d0303038410308225080040b4080c00c1242e111806010080d500c0b030310488403220040200d131209038007083c20b1113001003080002049880141c20300034004500242c0180602c091a04940e80032038061046100c804240d540402960740304038462001180c0d00c0f8104000140389966112004c0c41c0e55909000110005402c040420107444961030701d41d44845007100860301400e40d0b084100c8141d454406442000c1d0686c10045105000490403220a55514030620800180028000d4491400000d4800c01403508250a00c1d40500a24100b1180e23903c80c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979288 1250 978038 978041
    0x20409030203070b04050610050402030606030402150403050f010c030b04020c0d0807050c0604050106090b010c0c03080708040312020c0103060f0e0a050a06030503040b0705070f0501020307120203040f03050304030b010b0301120b0601020102070204 108
    0x1910203039405d607c16401c20103d04001c103042000b030201036a055056052000120b4110300000d40004c0c03088142d0801a0300c014881030540300110380210480d0301d8170100205071402050343c04201000a030030044c1c207407031505141c000ca804051120009100082241d082120f141d0405080d541c01c21800b04845840316201700b0503e030003680290000550185000c0c4820211030800381c880d41484030340366804020400c280485030449400a444541d40ca00915140b01c40f41300c0ca805c014000d4031588020b01042e41c0c006903d400a6034283c8040050644031031102040d640c1c1407140750280e4445070f0000390040b06c5608501e421500d541004150b1645030354415003144c0050308210852000803650002740401000344c0d900070b028211002000302d05100000391203114441014003407210400010380310602c20400c48004103c103e501c14a416180d250154482d40a84004d0f0303440e030040e80010030010050700440f4126451a980080c1c100d182c4c1ea1041c039956001414141036540c288507803800340e181e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 980538 1250 979288 979291
    0xb030102040b041706010906050904030804080712030b0310060f0b09030705060307050d05010b0a14090a0e01060903051506060a0f050f0409142a07020301060513050709080a0c03020409030203070b 86
    0x41c0304004020075400d854030b8980b000580c000c0c7c02c04c1d41403560410550326181d500710f4020780c0514092807595102d00388810188582c0c20020b21001c42c0b556000c1d0313016415842220000d0b07044050300c0d0701c03900b50008401501d000b400342c400751401b42c0104000c0345400300300408030450b010302075541c03255440c00000d256400499914010600001300040200c069216035405031406c43c54807420f104810100900c3e20b1410301080b0496100010610707c40c1e0341306003042d001001c1c0c8016420540d030315110000c004a4003480115194807a05264400724004003030740740d210301005040507080c034525500844030343c004c070751145080c4002004803141841e02c40006102130502c0da400800c6046031140d41103e0610000c00d0042000c20018016000b150742c0c00780001c2400503001c10b191500e1960000a00500b00d660101e60702118040c0126202241604580e12030122516003d40f5244e0703622425481d2001c0703600060555080d104148018076182d8410408140a44102c2e41404881c5c1e17269a44002c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981788 1250 980538 980549
    0x20030301060e130903020303040f08070b010605041502030c06040308040201090b0307021b040506010206040b0a060506070b0601021507020303060607030306120312050105010203120a020c010e15010501030b0105120a0b030102040b04 101
    0x500004507285818280a075943d0204180c000f008096615103000b501c902005e0401890a20110707c2401884402019a044660081d02c00c002a581d66000900b581e4420f100f0314004034411062502c000740040241d410860300400074080c0d941e16640d046448100041013281409031324034001c44d102000c1005103104060640041c09003061044c906d0310b01283c4203074404d2149051038104025a40c1c00700c0e08940180d03100d001c160542d00d850003248003070400c58006c50b400c100701045800c00e010305030a07118000d4030280c0035504030054048000d208a030044410a015a10410108001c2c0c01e1100003040518024540020300a4464125010641d8920703001d40000b0601103101a010105109150040009000461400b403075010b00700c800141c000c103a0604503a0103d2103a10102d02034024494541026040c0d541624001030000600702080c003039580003c1c980000c2e801c0c5075000707508990003007450001d0304501d80d0300c00d54540b001d419426811038141d5000d200000c1d0390920340014002030017 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 983038 1250 981788 981797
    0x50402030f07032904030e040b0310020a020106050906030304050913030203160506040507060201062102121905060906040201080a0e01140702010c02060a020708070201050a020102121302090601030b030c012003030106 95
    0x28251000c4410060341c0c03e401841a513440c400f444002a002100c00054800560b40401c42603000e8001a00b454001d000154940e80002084070308142d040d400081582e90840c1c502031181c403501c0034150380b80501d0041da40c01084100c0464001c0d560f4054003088144a48100e901d0a104608280c01a503410f00046030198030804c14017007044024000c11f00944071a10082100d98900b52424405060000d51403900c0d51300204c0100035500c9004400d0f05a440c881d0481c0d4540d2400e12030070700740101071345003035440b80038540c00324480b0380022a856015a03016500c4041646074070701d00c10024500f180000b10259a1103800760015660340f94a0340c4602c038642c000242e80c0101c00400303401d00030014022128117104004550001d00c401d400d6458064080c41c086860f1501184140d00920400c102020300643c504108008405041b11103407440e4030a507080000c5482d030000641c1a902c0000c80e4640c11b41001c0181c6840307501c80c2510307008030040b28042110440d8400d07040e42c210f40c002e8200c000000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984288 1250 983038 983063
    0x402040308030117060f0610090b03010e040c06050a050703120b03060f0901060f030203060103030311120114150a08010b0c010204030b0f0601020105010b0f0304080901050910030902030c060405030a0204050402030f0703 96
    0x214400b03100c03000d452240300c0940304514000b10b05c0c5814440040c80300780701c8d0000e8021071424510070060f14003c3c114803000955a961603410710150000304403002c1340d414005600c0851814450010381d0140d1669482e138031709115039650162079080403140600505035590034280c0d842d5270204400c1780542e84450f100281400d0900d80c05094840365003119012a010840400060f24006920703811240c1500d00060440f55644800c50144141030034056403034218400410580320340d010705102d40100b103828000b000f00401411845009112081d408112080010032404003035030000d0a4030088000010f14150f12980c91540c40001074444180c80301419041081b40d50302442120701414039006a5410810341c50360b146041e00c002040207200c0c520105040900784d020300207892a20100501c81c4905200440c0d008004200000003a031081c82402011001814040700b00c80c182c80016004d020004580c1d0203000107080c4c0640100c5e058420040e40100c000030901c2010080e40c8241216801c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 985538 1250 984288 984299
    0x20d0c0801050a03030206040602070807020a0e06040c030506010c110310020d0b0406060908030f070302160608040302010f020903030f1c0204080d0201060b19030903020a0b011503050a020a050304030503040804030204020403080301 101
    0x100c0030140c114900880002c0740c207102180d000941c056005901c100050b035204614602182503015840c3c0c020b401c000d002d0710215200c04201c441e18401c2c14241c400304014011445e0407820388805848a9012441082c80389000c41c4c5070341c91292208101070112080903400340941c0040ba400414002c02c8036a0f107180e040d03400c0c80c040c00f034a0010501c07840c2c02c9801a04221400e900c070701c02c051441041090009040e02014000d010000080035245807601c0b0142e40c40b4006000180111001c40065280450b00c041400720b602c20740b46201ccd40600154104009a10301d0500b9038000381211039100f01040074000311800ca40010300140044001400c0d809c5204040039003136803a281c112a82d01c000901040a40c01c540c4140c10032411114a80070402541c00d0900340d0400c20390b0341000e0b005c0d0004500101c0e078454030281181a00126a40030052a42c4100e001e400301c0c05000030b01800101c003080400c0110703100d48040d46d00a8060080180ba15580790300007402c0382d0142c1c2c4110340440c0301000401c00e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986788 1250 985538 985547
    0x1060903060b06040506040501050711090408090102060601020a05070501050a03110406031509060317030705090d03050301060e0102030309060f09030c0d020105010302090708090d030218060408010b09060307030c060509040906020d0c 102
    0x102c5809451603810541814000390860245010baa810040c0c0410054140941c0c640c4807040210050030740c1000d070800d414041e945074000c0c1500760261090001140d502c0d44002540d02e44150450060881d0a052100441d01903021008180806886000340c402c1d00300f00200a000410032034400040b40c1c8014070401c100b40d1000d03031040c6138a0b4a810000c0022443e036400000c0c0e0440d03c1e034a140c0c0d8a42e00c040080d1b03050702510080580240c000711907503080540200045040e144e984d01c4076a1030811080c01243d4912003120b035aa415000720002c21208184954400d803c010454141c0c0c0c244910b0200d801d181c00110300040340141e449400420a5081001205e40c215000340360090270303490032986007582c810b1180d112400f010790024010060fa84115202d00e86004001c01440d591b9a4400d501c40c064a03035040d50510030400e00f00825194034000078400100c0740e10655180d00146803d030150b6064002000d015000b540b50090b403400101148000c100c007145c0103400040328000024001c1c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988038 1250 986788 986801
    0x5090901080c01030509060705030402040f06080115090f060303021b0d08130e0c0403030e09040507090905030c15040b04140703150c080105030118080d02040302060304050703050c03010902090402010c17030106090306 95
    0x1000e50401003c8c024400d60180c01c8980c82078041e600420007199514006000703200c2d030740c0040b40c1c039440c0618800030704501000103000c03161100410b000150b02c0e403c04108994192100401583c44440342041c0c8162040101c624104014068080c484a170380b01c42140768455403c42604003000003050100c40e0f004a5426000100901d0060902d800c55030003a00103a117400646104400d0400043c041041c204050b43c0600103c3e402445600300c00c0c079080c0d81d2a004120402070b41e02078001501c01e500100c284044c855504041c81d030629881d10344446d0b03003040240310b4a1505004080380400498404001c9202c01d000c82d5400094801051000510418068020520990408004041e40d12500e10190030541d00304c441c495441040d01f405070028443c56000075041040030007004140580421702c0300490b4060301c1039451b08615441050700b00c4081c060300941c0003100d88045800f55206050410b00c0034031561032182c103c0c0d812a8000c6a0ba00260300203000a0720064003801085010302424 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 989288 1250 988038 988051
    0x702010608070e0105041d0118020a0905060f09100806070e040c080105060414030a020d030809060a0501031208040201030b040f0506030c03070b041505070b01030809040e0303060102071505090901080c010305 91
    0x40a01909210000f0004501803280030300c50b545840000491031850800c50a0039014040200140e2402920400c105040d0050070380c0f20351540000044d800340e1500031180300e9540104040c0d8131410140400134041801382c509001c500c01504041005202040701500568150321140800f07940c1c0c10402050700c110320b01002c20001d4503401002240c0b03070f10096230181c4181010041c0000d40b100e000c00d02e081104200654402d5005881806040d0042e14140c0030340050f50655110341e41e03001803c81070358405c3c4402072032014544035008505204641541e0002e105140c0464000706040029040c0c51805400c0ca0300555210180112490704100314204c2d41419400f406050749031810444180c09188140034522040c3c01845044521400448421a911400301041542c4034185100b05c3d8000c0e040040c0207034584080140303444c20000035244100f03030580c006d000050802c4148051019400d00c0701061080500c1007013560794503001114080e10300b4a000b003840140e550001025034101400a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990538 1250 989288 989293
    0xf060903060403050903210403030305010509010305030702010302090a0e0f01050306072a050307050601090203060406050402040b07020f0103020c030703080402030c10080408030603150109020c0d0e01050d0902040f020c03030702010608 103
    0x4048251000706400e50b016406081075500c40810038080780c1801102020400180e4903201e909920140380c00280059030702a80c0d082003140e8854041c00500320003070001034003d41c01807044000641c883d4000700000400900124582c9175503002c4d11800101c240c43d0b0b03260318130600006010030304082003042c1c1e2144841c03409a04034004c0601f86052540881e401003d40c0502c042c0040504c42e00300201e4811507070040803034902d903941d0292840290015140c4074440ca0900b0000541c900e49030090300d00780d60000b00510301c0d04201d83d081140c01502e00d00750506140d02800700c20300402050014000c214029102c10f1a42e02d0240f0403d070428032183c1c040c0e44106610b240700034285a115111b158400c2e0f01a401540e2034491100003460310107004007000f5846400d0b000403031800303816000fa1a8000c000303011111071450700002a81d03000312009405001039014021458414030540104140c41c1c00a04000341491103c0c070060180e0f84900402e610507400003041c060340d1035091103580020040d8101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991788 1250 990538 990547
    0x1021903110d0504050307050f060405060106020c060a03050a0603050f030901090b030c0708071406100303080703050c090112060302030307030302090a080303040f030c0201030f051005010f030e0706110f03031003020f06 96
    0x11044041c09518002c0034050380d02c0d0005020000c0030402c80700041c0d00201120341e1801419100741d80c0e61412102210240a0000002002e80c00010781c103800c42001003600b401c040030060210001d00300104000402c80e12602c00201144c0203007c000c1404028001545d61480018005000260264402e071403076002042002481075040302958841940710111a40d1040d00e410002041c9149a4074103441d0300039203050000016080310342c24100e0b846500c500f4150350710110250b084030803c8178000802001008102e40541c422012802520814100000c1050710b90300403d156401c07506045011a5001880b4485494206074460080a20000461031362425903584080d00c543b0040080600403444404000c582c040e4009030115000740000304207515001e40c2440401c0b549201c1c050200300e5202001c42818820b0086283e500007110052041901c0d042c2e04499181803000103600a00401c4525511114188010343c003400b080082a0200303400c0d40100300c80c840c030704c42005200b00c10410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993038 1250 991788 991811
    0x100807020c0d02060d05090a0803090307060c020102070c05040c14070803060f0d050703060f060509041a06040204060c0b04020114040e06010207090612020d060608010c120e01050606030103060203040602090406030501021903 98
    0x4445410b10031100c041043c2d07d8840d0042d207080c01d06000280421f20100c2003048240c000005010400d0090a0500c511006a50164200d10480303402400b508803444043c4800d08094116400b00b401c84e152440307140c041c10851000030303004107400f115080e40000620815107010700c00c50121000859201c02c240141b952882c0d541c602c0751200400b920303207603c1107404100d07184d03001d40000c00c0054000c0c02c8a01e0245052006c012810004004148005000c90071030704007803094034180e03902d5499060035142c1e41d8952010030300340200200d040000d403140703042000321800050320041001c1a07104505091120000e400c005d103030b4104003850707441d000342042191840d4920081190701510104c81081440c10a9805132501d90080e600660800c1150101740b9071101c8403680e240c8109008110a0b0045d6007200d00380d907400da80036603010a06100600c007040b0a64002d58003c0d204900c0180340080140105040c0c3d00a47c0c01135950341d5001c980b460071505a9000701d03039030000a20703040015090320f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 994288 1250 993038 993049
    0xc010801050102030d0b010302040f030501090b18030702010806060708070308090c030307030909050702010e0601081e070302100f030b100807110601060807030c03020f0d09021002070803030408030402010e100807020c0d02 97
    0x81034108005506c60302040141c1e4001e038115400b400303411000e1003103a602ca00f01280a080906000c80710041d001c00020b1a40e10900c030f004c20012040c0002d14038150301d6800444008401520a17648070b581000654009202d68008019035440b80d00c0e00340c803501d0502e58042c201207416a480c1c2c003e07041080200c001a6000b010385059400c0c3c61000500394a681004a006061000301601c441c0308040010820340800079104600c1d6106c40920003080083c007020540303850007171200a40000c072204083d590107000d0140c54002d02c50a02d00015041010800079aa6000d611800c2002c03e580e001400340240d0b10400300d1170300e8500707400100050351415030002c202c5c0100800c1e4100701503035031607440e12071880b0381c04540030b00b00545006610303410200c0c80c8030000c20820200320f00c540e07100c3c200b43c501c0900106a030300031201244c0180d805c541d038503124080c00c2c1c0c1c4001c0c0101d0400c40400c00540395a42c8042c0c4000409185680d0b8803110725244031b000c1c0c5051140c903041031080030394015080041c0d850 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995538 1250 994288 994297
    0x7030801050409150507020610060302040308030105010c0f0f03050417030a0e01120e010e0706030e0708030703030b0402070803070201090c090e03030105040c020312090a02040501051806090702030f0c010b030c01080105010203 99
    0x15280020694054140685801e921388100100c06040005000960b94002032160107a0704160403101c0e9075070343d02011f4080b4070036484000c0159606000400036580290074003000ca03402085c440480f00d200d66200054054080e10031400710f200820141f004000c5890324032808403241005502d066070081014011022080002d4100140b07030490b4607500720603130000082d4151034002440003030308010b0407617280c81c6140103120000346401e1018112900001e05e210886403a42c000d0751400c1d80a440c100c01800c000c0003403681058081200c1c40001d03001e8401503205030a181d0000810120701d14000d200048940d00c0040c0c0b0500700b8200810001000c01160b0441d041281d0028585040803016070460007034005035240c4440041c1040b902da080496a007422500c00c6800300302c0e5a803100704000d811180d00b11181032300e200070b100181107814050a071035042400c07401280c0c00c0c400d4500084da0180d001d0000004144d446080e01f085c1420100040b83d46000242428100c0e90305020000355240074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 996788 1250 995538 995549
    0x105060105030f040b090c120714010503010608010e04060605090c0d0f0b0102120310030605040b040302150106050702010302070c050312090f04050601020c010807090308031810050412050903070b04030605090609010207030801 99
    0x172090082555084100803843c00f00102911520b0012005400c2d1519140c66120704461031201d240341e07108540c440c0303084072b041e25103544034480e00e6402c00301402d8004000800880e00c155903104003050903501e4030407092003485621403040c1e60b00c1d4605d180c10140c1d0480c20030700300e1442c00d1000303401c05c5030b801180d075141ca814080446034490340d5040196400110980c4003810040c500414401032007980790a0354441e501903000c41d094a1002d8410801c072080c24814080019010702c0388000640c07080d00107001a50040007080599a01ea000280c103244d02055200e54200340003a411201d03051140c03840b58030080842d03040003036280c00d40000c0d454140203030340c0314108800320001985450140d042e880c06160064062900d07860440c040ca10122460245e860540c0304402070f000e000340140c01050303c40ca03805401c9151240c0100802c1d9010782102150940c5402000000b00c3c0501030000500001d50141401007031904000d44c146080030780c081c0006c2c81da43d004102c00c00103c3e030060340b01c504552 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 998038 1250 996788 996803
    0xe030301140105040909050106081203010501200102070507090501060e0306090601060509060403050a03030f1805070303120605060705030405010e030304060e0603130501020309010501030201030506060703080103060b0303071b06020105060105030f04 109
    0x2056500100c506100b139030482c45980e40b603c00c40074240241544080d059070004002c6511072561480c9a103080d020900c100c600055440414400c0e0000b0070741d034032050f280307098005400d240040d51503900708007080d0040480d0654501c01005014ae000c02500c800301c8040e8083d2406060001038652144814011b9000380200040c0090143d100c200460b00295001015155140b45918005003c0e051000c41d04e0142810320b1101021500da001c1380c1a002a071040041055610b15078041c3d480c054080301119032543d81d030340c1c00185505d49400400c01d89120b0760203107540c0c42c1420009420a03408100702802540148014000141c01003650b92400c4c1c4111001e540380d81c2c50044448281c0c40484004101d540003205001c198001504030328140c0f4402d80307045c8204d0382c0d81804e12244e40901800600045d0301d540c010030116500ea40039881d002c1c1c0240c1aa0310380202c0341c6480326141c1c100b107032200c000c002c2c041301041625420310816400c40c4007440c01c5440c5040021320310707040440c003400c05010389 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999288 1250 998038 998069
    0x10b0a090f0306020909060a08100504080903070308090307060302030705040612020702040603110a0503030a0e01030e01090203031c0506010507080d0e070302040609020c0c090c03040f03090306020f03070f030e030301 95
    0x1a40540c800e10000d200039286003900544034039050f8040d4000b035518a02138074034a00480c6e154034011500f1415208008001e040312245420408040c103c003400a03604941d04010803170131610240115070140d4061400c2c26500c3c4524020300d0300e000002d600407030400d8414414031003026840b50132241114071900e00007250742c01403215035000f481140300003540189044400020080d200386940d0b46402c00315410f9010740d6958051540740c0c441c0401060000b80c0b01c1000f444c0c90340c001c0d80a6200904e1050001845800503030109140d07511507118100b0303200a0044000d01201d40340203d035403003103003840c00030700b031001942d20611036004082c0d131035008584480e079480412404002035401540c0080007071010030381c3c4441c500000d41c00044a19228003980c1244441070421032486c0e4004c50024583e28a07540d65034070b80c2ca62611064904408104441c00d002000c2440d0380060010f0b500f003284004c0ea40e0500c0749029010b00f014900c50301c00d05040c40d03010307880c8002c00b00c2a20304442c008003101041c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 1000538 1250 999288 999307
    0x50a05010f03020f19020c0102070303020607050c0a050601080a020909010603030206060409060209091501020f0a020901030b07050c0a0516120203070b03130602070b0405010612050606040b0414070201150603060e010b 95
    0x2a001d12030b1400d0440c80045190709017940b100c0c40b412103075040754003500c51800d031040c0120785031403d6000c003034050ba100d000803804e018401d80061070302049880503036001c40195640d480c1896400c2c1d2003440194010041c54040d450300c0000030ba0801c0c020350081101c180345980280d1550b1004040c680306559130a200428002c0b10307012500040c000a000c03003c0d038602198444072614103600c002d4014860f4001e2850b08c103200007180d08502d600103018070702980c6107a40f42140303010020480e05c10081c0c140984130f0390304020445010220300c03507400380140061348010308840d4001e80c0e0280e4041840030020f4000b584020802009940500307400d150f0740d80d9002048480040300041c000c1c160362001540c00d05000c101c1200340d018500c140024820f0a91710098011030400303440000d05140c2004006c2091031400342e20880000902510108200c0e0301401c040c0b40941c01151000c001d40d44584116002d078003a49041800781000e81000c21043c2d081600403521064140200c45500100003241000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 1001788 1250 1000538 1000541
    0xb2404050601030207140a050d0207050a05040e030903060109020d050c0406080a050601030608030a020105040606060f090b03070207030f0807020103060e070203070209040213050106090e0105010912080714010c0306050108060901050a05010f03 106
    0x201031b40c2042d500c540164002c5011503488984000941c1c06010349000e0040b2280301207500707012101c005019102e070504160810005101c0300004a1591004200d610625242404414000c02d2000710068840d4045448101559002000c2c40c1d980340701000305200c0300760043d4104d50050040d80001a40f40c0c5c03074100680080620342c12000c0948400318000101c25415041280b103107110706000e0003c90303562607050f103000c0602190500411200131003413000b180c030b002c0a598051201d2048404a03a80c030707203c021041721071000580318004005450800d558050044000030110341c1800101031403c280700940364010980c00038400c16480001c1825550340c1128610381c00f1062004019650f550b1001a100c612548107100d50030061000010307156000f0641501107480000700c7c60540101e0303036140640c0c3c0e40071040450305208a494225407445c0244900c441c8004c10b5140010120300344000904447c0e001040207120303d1003540140887d465614510302126130a003000c2d803520000582c140d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 1003038 1250 1001788 1001797
    0x3030213050a08010b031501060207030308040302010f020406050702010806090103020f0d030c02120304080d0203030405030307050309030c0d08010501020115050d020105030712090b01030b0604050403020606100e0301020c0303040b24040506010302 108
    0x82d844424040b01041d41d200650002078103c00490440e203122406050548010909204e000c0258000840c1000880e00801e0354982c0a4460700c00001d5040b8450f49060403078015401600015002207010313011940c229113020f80000c0121200e101662455000644600300902080c0c00b071820641c0d80000c041c00341c90325004842d40109105050404418850350f281c106224004c00b40c460070300c46503811070000c0201d0740125003180140d85140c1e80c0b94010380d5650720240c014110351004000f0445044018401800d50b0512070382c1b401915494400028251442189a142c2d05408000c0c100000e503030301403a585400d603081c05d080780c8a42c1c61070b005441118030f1018204810742000c061408200c1700054003810b8a1250303076089101c1d143c8005000884800725802000360f40080b000c1070003864800b508001d030781990300c0c080070030f000c00d0300110f070a9070440160112941d101009210400060500d1280e1001810b5985016001c80303c0c450500000c5042e9458042d40c0e5500100b042030340311b030301203a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 1004288 1250 1003038 1003049
    0x70503040314060615030a0209010e060703020a0320030706090201050405130b010f08040302030304020909071802030105040614030d0513030f08030708060102010501060f08060307091401031a040b010303030213 92
    0x1603845036500d0400985001e0080c01601d80c0c2d0181e080010300e50318040c2c580c1414840540e0500303066603602d200c22002540000c510a040c4174100c00313901811390701c101c018511240301e580645070130701031071801400c4081d2610302000c03400c2c00404230b40c10001d40001950f0720305800040224505181d0f00040e0b41a11807500600d40001e14986032036244004c98207e105c13001401e0381c030304101000001c002c0b5413544059500500603002000070a0252034103440e0b25400c896814281d80b0f0780c40d0303681c196550801c100c4d40c881900d03c2d0084010803041ca42845050000c00c06140c0030b0700000740741e0300003d407152402030b440c0f8180180400c00c1e0180c11802c402c541c025590003d206407000b4081c2c1000070842c4c00885140000032881d43c0000c4a17540b041c01a81d048038015210610072480074101130b03802c14001450b82d60141f140e018000b614440d81d014100004280c139460f2080781d410340c280540340c0710103141c1c2e01055420b80b000340000200c10003501411a50940350041e01c419610b55600242d88555000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 1005538 1250 1004288 1004293
    0xe0105070c05060705090105070209090106050907020a03090e010503030403080d0905010c030b03010b04060503030a0302071703040f2609090601020307120503010501031a10030507050d090308040204060e0f0414030705 95
    0x104148290040740e004603050040003222401d98841100f15042d00c121601c00380040c2c014000c150040c10101160b44e08101c1043c0042640e03a150404600c4421040310b01c2c0c03005078018a6507005160b007081c00040640301003401c2405641c14038010940d0381c40341e40f0000b0000c0030006855448068503601607650103911000030b00c42020046030081c05010480c0880b407182d441c0c02c0d43e845030b034906807040c2d00c104d070f0000e0003950030900f00c0e1b002a002504001010707600d032030f0a60303030307041c80c03505100015441030f8424583d01e00b100b40a41070849001d000c40c5c2203480b4101c40000c00014284010040d2134030401c0c1201e90800b070b580c642d03004034254001d0001c01410008039085000c21582c100d005107041e41c07000c0c0d03002c026100e1448404142002c01e200e4141d00058082d9001184502c0303030300b2159028265090171880c1c880c1c1031042200310744c03a104e03080d070000d030300c1d5030620003146458000c903c01003007081d5500c2458106002c2428112001501c01090791080f006800000c1d44180150796026070044103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 1006788 1250 1005538 1005541
    0x40318080106090609051e07020a020a030c0602060903070b01030b0414010c0305060102010b0102010b06070204020306010c0206030103050102070510020c0d0807020709060b0309010e1903031e0515040b010807020309010c060e0105 100
    0x2140a4402d50140070700706802c1040200c0c1d101580d2142034820b030400c040c41c48510700b14040f6110791303a20181c02e610450203045140e001503241c0d09400c900562240c22120138280c6041c070001c4c01e0000241202849030810055070000c030364210b030072605580d0000058160f0fa1514a032108643c20b5000144800e5424981c058001e10b815620051158030284c0007401800c2d1701400490880d1407250038560702c80f03c140101009401c00d58003a40e130120041c100328015101d1034000440a030000d9204881ca42e400040e1a010003000b071103950000c0240103004d505142d01850b60701e8503a8101d084402c2002005000507100c14803c2000c0c10081c0b01c2c0c0042001590748075185207400340d008441440480d030804000356504200007460f400752042401050030a00907540d421005050b15101043d01fa01d524200e42c02d014001e8070803036018101c41205400b04a0580c0240300586101d8072030281401016010441620703004070860f058002c0c2441c0000c4100583e15001c0c1c000c20900c070300c3c03074030544c600170 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 1008038 1250 1006788 1006799
    0xc0d0f1d0102030702060c0306010903060f020706020f040303030609020403020901030204050405010f0213050114040b040b0708040906060807030b03070b0405011803060e0c03060c0405010905040b060c010f0204050a0602120304020108040318 105
    0x1070043d400b88105a00ba5a070303981c6c803404240c0e400c0c4801d407201800503841e280100046542035014803404503000601610304102511074000340d8201500585c84500d0000301002003541521400c001003081c84825414580380d41c0006030701c0c001c14400640140e84070800601002020340c85914201c038101811500c43c40f06450080703103040c40d405036078040703860040348240da1058441558104c0347c0e004840c0b8903060070034889001c2074120075012101c040e014800030442101034040c0030007800d185d5840c0604ea01d08071200800355158a02c52b103009810000b42800078000b00f908950980b0300a003041808155038018111400c0a1580094103491412100004090010804600120003207040302c42c50340350300004030141e114905c50517020540e0900704020501340f0360401c18000340028401402e000b4000151800d480400d01d8484032150700040900040c6001000200a040180700030020000c10b444019554032000c0d00281c1400f21410020b0101441603006040c0190b15080d804d00e110350340d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 1009288 1250 1008038 1008041
    0x80105010f0602030f030103020d02010207090c1206060f080103021005070501050f04020102010b0604080601030f0c0915150201020901080408030c0702030d08070206010501030b030a030804031b03050403020307050303030c0d0f1d01 101
    0x1e0040d4807001d00546400500a0310020546400b188494142442d5900e940d0030444410f9030b184080781940542180002d00c1785c0640301d000a1401d10380c641c0d4001103213840003d4221104c81c0c000303905004078140c0001078140c1c0b1a4225055903410345a084003650310341c0342500e85000b1914000c3c005d60a08041200e0300401c2003071180500e100ba0000d1040428003002c1000500a41c080c0300f00603808000104003003801c510f00300d48890700801640c140c03241c4503174845098031000d103a5100d80b0031822008108d8441d94815200e05a0325503c02141040c20060000780f503407101600c05800390740b000c00402c0100400004940d141c650040480700d001c2042507018080d084111003400c0503025840c0009501d5000b4043d544807031400601909160300650780940e140780c00034005408001002d0000c070f440b00fa800001403806400b035154240c59525520415281c219985c0103c0c2c041d030014824000149495000c3c1d40d104140010b004c201d1308288100074006142d0380d884444580c2c03000e080f000005106 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 1010538 1250 1009288 1009291
    0x1602031306090f0504050903030f040204020d0c020c10030e0d11010b060c0601170106120f0302010e06070509040e07080309060a031103071d09010303050306040e070b030c030106020d090308090607020402070b01080105 95
    0x1403c14100c469541c030707010041106c808486030a5107170810000269145c2c5030f041c0041d030040c80100b0050800503139003003100403980c0c1c801e40760015a209428885091401200c41041102189400e0003070b1031050904988460b01c00c01c0100c24003c4e46001410307590429084041c4401010b0b12482c0c440e0902171503181e4900080c0314214441058000d017442c03087d010702883e016140c201070003948a0320310780c0d0b50082c4441c041c030040c0c085550300c41d42d040a070101400080d0240000c3c1d601c5a0300d44e441c81c400c200072141c4d8000c2d080c140c1d901156041003034401c00305c140c0307049040c12245e09442c0c40710000d040d4058520740710001c2c001000002000501030300506450b540340b18102c00d03000700307042d2101808610072080c0005404500144002b03101403800da040b440e00da501607000d44c1d070038035038907500e0701141e80056038004a900800300c0103119190b41045981c415140f1840c00035030703a91039502c130f44c8464031400c40820300840002804030190b44403901114940c55108801a000e581d4820403140200710 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 1011788 1250 1010538 1010549
    0x509010908070602070b0a03020904050f010501020c03070f21060c05030703060503061504020310030204020d0c020c010f08060103020f0408060405010c0e06070201080a09050c0603040602040302010e010f0206160203130609 97
    0x4010040340d20301c1c0000e4400155511500100070860509030450541e80141c100780041540030044103800f500e41d030144901540b084e4140c0b00c184e504000000e0308080c01109054007076840200304000d4030083d610380c0c1d800c0311116203503e440900ca0b88038401d0417400c8254080d00890070842200403466010000b540b00d41c0380c0f5a030170014503842e202099200c50b81562a0003181412401c11140b500d0300ba801182c00c1902c010140300701654a9005c40c059130071405072a101207a07219000c0d0061501448208406c034400d10380405c0d90020440041c04100006d044503040560100350040d80f0400f040c120f0b806012050b0841d80a4a4940b502c54060050007030000c0c0041c4600c1e004560600307044017a00d0402c0d5051311130b0000d0345d5940c2c20480007400841000c3d5030b20722640d11450000d8031440000d40c0258040d0002594aa00f50300024141c030740128145810006605ca20000040d4085811070f00301ca40980c602d03c00d0410004100e00c0d50046415000d88000744120004103a50454421400c07030301d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 1013038 1250 1011788 1011797
    0x1605280506060a0303020607120608150f01090b090103060906020702040608030a020106090203090705010c0203030904090305040305010506010903021807090506030109060602060603060606070f030203040f03060b010e03060702030a0c021f050901 107
    0xd4607907003400f4610502d440018050380c40791000c110307840c2c015401a0b00c941e01c03800700050207990f1440c000e03140007410002120000310341c07428011125544803499024040c3c8003030520070550008003250b2600741c14030010b4070803070307590718504208841d42c6c0490304025001441409070b0780d15042c10a8070f0340e0084003002d000d9849c20900151401c400d00a4034881c0203403401900043d82340c1001503400c00c0480c0301c201d03070601041001c504030790745e144203480805010750784441d1180d0031490124211107018240c03a040c02010031080005944523098070b05d42c14040c1c20840e02d10748405000b902d070800300d0340020f94000e01c08800490032441d554020011588540e0071100365880f070f20181a00c4030030654800c0c2c0c01080c00c212070001300342d000c908100c0691092049916182ea43e040403a2684502d8104490f01d0381c41d240a00c6407580d1203194441280c0f0128080c0c0403604080388041d42c0c1c4e11983d80c4002c28481091555010356940c0700d141035081d102000404c003021050311008103154440c003517460115 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 1014288 1250 1013038 1013041
    0x1090203060108070c02010e0f01020a06020406030203040c0e0c040b071e05010b0301060e0402030304030b09030d06060201060603050f060109030b06030f01020c010c0314010e010b18040f060602070501050c031605280506 96
    0x220720404581700d0345e9406031034a8400407142002e01040001100d4614190704c205030158002031000d01c001c000800d007035a0700607100c2c141842c0400c2c1d00e134150350001c904c41031400140040da29800341190202c0b01c5000070359a036455186004401c0300c81d071703200074290a400c80c44604248241900800101502140204580e6480c0c4102208421041e00c0194040d48144010300001e40c800350810740000e050011242444220702d082d8042c0c031201c0c0c01901c0140d4403040104070580e01406999000750b409400c0200a03e0540c0c00200002d16510001d010080060081281614280111540b60410390020741d514480c45440b075020f000b0758444800004c0c905200280c062040c08081816108401c000c220103034680300f00c2c040541c10001c1441b0140d01002c004070840e035105d21840000e0303034800a011034401d1070858042e040c10000d500440c140501044040e40650000c0200c1351503c1c5c15100c00b41d180001820f00610b0702d90740210004a0746c0e401d2032042001a064141142b01620070344c1103a006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 1015538 1250 1014288 1014301
    0xf050105040903050301090504020301090507031101020106141023040e04020a06020d0206040303020304020f0a080a061109010504030f06020f040807030605010b0a0e0405070c0b070504090e030906031b04090501090203060108 98
    0x11180042e002a000490610040c8113411a0b07030459a001400140040354110040d15110305080d560703071040360341083d01200340400b5602801980d00a1012603d40c0000249000c0881e201d65280e490043c02c001e46202d0030300180300500c0050000c10300e8010030308d071210345810a0046015040d20b083c2d00c185640540011036510006091500c0007003980a410307940c80310b5600707501940029100701d030b2085903c41d0b01009a151003030018002c0c00200001c040e03500d81c41c200902160020300c00c1048016080155801c643d070490100e50841c3d030300c43c0188801d2110380c1040c40c001c0c0a0b80007401e0354442d00090006840c040010142c059030302402080107541d9803205100c0051240f03c1003680420203044002080e0b242c194092540003110f0300b0014043c044954036410300d00d00c221140804100042818040c0042c24880d1052800141009515008942c03000030400c4c04000c1c448030100e0303a429440b488400307106040c2c4d80200040c2c81d02b8003003175855929107006500112592400550309a00003400e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 1016788 1250 1015538 1015541
    0xf0302190303020c06031504090b0a05060108040201140f041206090209010e0601080112140d03020309010e0703050307060b0307080109030206010905071803030503070309050703051608030406020706030f110c010f05010504 97
    0x2202c0d03168000708009850442481050b402c010104442c0c949002d1100d0030f41e4845001d1074246038030071111a0410b00d01014001c08803080602501d04018802d410880180d8102ea41c04103290700b4804079030f0b1544070600c0e2400d26446540c012044601e512f000901c100420b580040e03410602c200c41c04000c983e2169284a0700c0a021030b0300d203001420710401004074011107501e20b40914002e084071105140e2036a00649085080400301d00003c5d4000308201c0114002c4c03049900700c0f40390a001d048800c0c80d41d22540c1d07a9006e90b00024000c5590303200184125078040042d03c0060103088000e02140c40f10b82406904c0760006d101e610127407818000002c0e03402d880f401111020a20a8219843c40c1d81540c804407201c0c3c100601c03c105245e912800200416001c008280c021841880204050b011280401c1003a0449920070304041d402400242704994000c24601c065403641c0c6400910080740c4643d400282c06066140d07201c108000400c1c41000300190840021101d07201004d001503680c4000b40b10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 1018038 1250 1016788 1016839
    0x1b070603111201060513030f11040b0103020a05090603100e0103050a050c010c030203180301061d01030c050117040303050403090302040203010308190905030703080904060b0a080901050a0212060603060103060905010f0302 97
    0x1c82c03403240703500140400780c040c101601c4510100221100c500d03440c0ea551103100c404d144000d440003d0090800041c80c07600e0701656000940a04c0c05600f02090301074050130714003c40360400c0c0b1902020000512690030001100e0040c440500303031900035692414050b40310f00385040c0a5409009503400c0141a50080700380101d455410360081d464034200ca1f088100040600e00840c0c9d043d500c600001030021824402040076000305020b14040d9495494000710003580390348424140071400440721030b030341010640262b000c0c2c1c06003400319080e038451900320785154494000035806840800040140420940a4100520711452069800001c00c0c01035500d64840d21420340d1617407100c0d8081c40001c58a001810340c160014001041aa0300c51a41055035081405034100044800302005040c00b02406455040b80380c00504614006078581c000b1050361004104034000d1000201040680e48070303900810050504080400183d619460742d21100c034960b100c140e00ca0804c241540000028241541c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 1019288 1250 1018038 1018057
    0x60510080403030203070e060a0216050d080301050d050c03030307050406030c020705030715020102090604030f020901060903020901030b040f0c080f0c06030c040504051b0a0c0204050a09030c0305030c1b07060311 93
    0x501141e88507501180a503000803c51402c11446107245142d80d1100300203010103841c41d8003c0c00c0546c10015440192110560100c0c1c4150300e200030b140c02081561041307905442090700d006011082e10b0070079511740210307a00c0c1c1c40d404d84400010040c0c4146d01c60040d00070754980d03541c140002020070b042286e80e034030240249a4190000d41d020050400e640d000c40e4100c4a080c000981082d88ca00005070715900503500540311140d01402c0c150440c1742c404121400340ca001d09040c0005815500403540e55a01400001c00d100040310100d810302c01d5425100079800d902040307a081c3d0940b00c070f1803c0d8860302500000051b6114000308114a86009410b4070310480d04900c90500b0320303150004100c003500d0f01a20b01890032800c200c03010155039500c0004c02e031280c00ca40743c82c031107034440f07105003c05c460780101081e00c2c2910706910b080c0025800114100016014a00152a40c840380307580c081a1203040052410014240c0282c4000500410500229503035900c0c07c1001c42402c046031002407003030a20f103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 1020538 1250 1019288 1019297
    0xa05030d0806060d11030a060303030605090408040e040c050607051e0307030c02040b010905030307050102030f160c020d0602040506040909060c030501030302060103030c0305040b1b070602010b030c04020702030a0501060b0a0201060510 103
    0x2440c6800c00340060400c14158400110b101c00045c16031440d90350080d6615821252500414030030f02d50180a43c4000f0f141c00c1d245d68080349810786520641c3d018070300900e841c1c5015003001c9024052042805006410000d15180c0d8861441c64143d590791042006010404895902c1002e100b0010041e611800d07019294020076400940c2080700402c1d41c0d91030300d4103012070030001091a490810203400c480340700d00001aa030b420080001c5d88402030040c003030b1954108510780994000d0b80014640300555060342d600e07800c08883e1400c00080d0085e5008190466408240025500b40d0f6403c00e00040b4046c16003040b00c007050540031020b441d001d01002c3d0150b40f1003030041000a126668110720140640740c143d00741526003072a0340b050b502521800f00c1c020081459480c2c000003d00c180d60003400640000c005d58040800441d48454015a50b0b601c80c40d404110a415500c05100d8030001030f5100000700607007a02c0703405400882c3c005030b940000641c80c1c5400840c2c1d605100600c1c4008091a0310f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 1021788 1250 1020538 1020541
    0x606030c04030809030312070c0501050c031603050a1b020a030806060708030402011101020c010203010306050103050d09080c010e01020f01020304030c0c090203010501020303010e090307060e0303010602010c090b0304110109030812060a05030d08 107
    0x5580d4166809144c03882d80601c0200319415804040fa8043c90082c031903513652440d40c08907800c0c8a800d5400c06480b41b454001d0800502190164006502160031030078180840d150303541c2c0c98200e000b40340001000c2ca40c2410860640382f4564041544405c16100740c60f000aa034980d401030141c50b0080d00c5000f0500c50040012601642c004c0c0c4240c01004041c0d4009440c0444010800f400ea070000c0c0d01c211003940e00e030001070003001024402080c08041c60300c1d000c44000d02d07003088903035910020210035040c00020038804e1400e074800c3c040c02701d81041c076200035580d03410a0710700107080d04007180d000d075401c991842c3c0c04100ea903401e00032a0b040b514140c0c0198110390901c542a2440103000e0b06400092000304250000941c882c0a03100c41c10521001458580d0700d0032001a00b07581d0384940000410161042c2404694403100a89401a41020380d441c2c070810104010380340119543c00c050b10a26000c9600b1154241c00c2040c3c51003000e050752910359841c2d84109060381ca18150161001080c007000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 1023038 1250 1021788 1021793
    0x30902060a0302091302070f0209060405060a0303080c0c061005090603030c070302090a0915060302010201050c0903071401020102121306140103030e04050402060d020403050f0606030a080313050115060509090606030c0403 97
    0x1000344c05200002440b20040031808810300c02260711040081724604042d1001d10107524000f000c09a12020a44040c0079501d0103070009441c0700d016000040520030208045965200d8041c00e031200e04443e101203034010706040401c902080383c54850b55102d503000c80d0004e50541004019100e440750707280001e01c040b9055500308800d4410090944010990707410b501001305541e61522001b011019100064650543c00024250303540240003100400c0104610b010540b800900035044961200b80b1003c49d4444400407406481115002c40507a20741c1d20602c24018076241d03102001ca480f5107070402184810b66000c2e41d81140c00d200280101d03030b141310840e9641c00c00e90000c5500ca440104070915000000c0e40540c102d030030980042d1203552001a408140305006c100d62030b0008011001045404115521013002c3d110080039a201c0f054825410410050250000c0000310f040b04030348140310b030719401c00034126086014040c1c4264031800c0442c03401e040c40c20403a40604400c6d00c3ca94035141c2182c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 1024288 1250 1023038 1023041
    0x105030103030f0e1509030606041802040207060f050f07020c0102012307030603061a09090105010b1605150c030703050a0b060a0315030209010b03040c060201050105060702010e010309020d03020f0d030902060a03 93
    0x180180b03001e1050754040d26202e55200e00d194481245017280103500c1e140320710103141c80c2100041009004c8c614140d5158600510115112030069044802694840a0703281620141100e80e006200342c0781020280480103070701110680c421040f6500700c40c9040340e4203004a0a8542080c4d52290380d6421a0306090000700c2c101ea01640051903007008a566a902c0c3e880608880f200354202c500da01c840c414840c141e1400103501908014200002d03c900e50500d00c0c10101c07442010300020540030070941d400100305040c8a405108909000407000b00d00d84003240142641c4100c4402000a00d45000104600e100380315940d0124000780420381440440d000039002072003440798440c0f140403040702c00401030741c411709428007916038045055120305061801800390840d90304140156410440140403580312002502e85080c0c09180001154402400503402440380c654041d400540c03000b42c4200f4190000b84980c02c0c400c10350b0031540800c40c03091301201100d500c10402544190b08000c16042c15109 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 1025538 1250 1024288 1024307
    0x10090504030c02030a0309080c0102030705100207030c0b010303030209040b03031204020105090301060306110405040606050c0303040204050604090609050a0c080d0e04050403020c030f0c0901050109060c060f02160303050604060b09010503010303 107
    0x20b0708040c0b1401120b40c0000340f174501104c808a0004003894002d115500c014400111400c03401c1c0000d5090400d1035076503d0700c83c19104a640c0328a60301040e881d06051040840400c07643d0460f141d80302c01d5850382802000380d071101d80c2c0d4900403428a00030844606000084a02184d2003c21503506501d580d0300448042d40032021055240d074a42e0303c003101040f510f224019a40381e06807040c650740c0d45007a0603c810707111164800c7e818000c09201d90659410007004490b88550704403000540f6945160000e0000d00c1050000b81a041c07409199104204d0700080b001e0323174140541c140340c41603540c4004250b5038402c400540d02c0000d5403804002e80e1810140c005503046803180c01510010481e12010a280501c50151880c55600915000d8031a0401078200c40c054002840c205922906090340600f20004100c001080325654103110008800c0e90360666100401c400341c061003136662400c004002d0705003924030070b200b28178045001440c200c00700c048030780848040e1181030440c1c0ca5034400f0740d0703030181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 1026788 1250 1025538 1025543
    0x7020906040f020c0c0f01020303220302010207080d14010b040506070303050406060e0907031202010b010509010f0c020604090e06090102030124090506030106030207110a0602070b09010311070c05030609010510090504 95
    0x111202c4840680300c86001400c01a00940010000042d0160822400c00584a881415500f04006208800e010b04445041143e140b03030004440c101d092404900902c60583c02030203255001c2a0603250480c55008001c100c2070814105102d45d80b514001d110910880c424a80d12010400444000074007d0b005641c0c081c0c040c5900141c0295a0813510ba00000200d80c41701ea00d4010040920070040c00c0c00b024141c94000d44000c203c0f40000c800003900341d124521045052105a81c62040401d1084801c0305c040c80c0d01402c203588843d607400861010308400b5000c22024000c6400140e441141482a01d040b03400443c00f07880c004160040080c0702c10f102c2c00c141420071480c09000325191301c84030003d6008050583c1e0069031190a410319440b94608103500f103100e0741e41c16100300286580010b5580c2500c9007074050f59503600d480c40041c1d0080c508c100d105085004045001420b00c40c20140c0d4004a80c0d0540c15a02c240e519650803a00b01c503c12244100c1840300c1407418803000a860303001950092 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 1028038 1250 1026788 1026791
    0x90602090303030408091314040f06150602030901020106060507050304120f08030c09010e0d02010206061003020409110d05010f06080a09060204050409050705010f0f080a020c0106051002010c020106060e03030702090604 96
    0xc4000881e0440d401100c05480200b00000d1103e203906000020011000c0480030400031100d0b000c0c0f0700c8a00890191016005211002d492410300c030242e03200c0e840c0300b41d06107032204c6056521354020f0b441e60040c4a101e400743d441c0601c0012114010030440d0a46580b0001862a003420700100240d040c2490700d013a9600c4040140d140c00040f02d0038011750040600304852501d038410180014420703c200300210307000e90f403106c1c03a820051740c0010b5482d4000204440b0f80040082e0404101c000740100d60007080b00c0743c02d00b044203480744141c3e0001c25280c0c0c0710007c10b10a580c0c031100c40444d000780910a9500140c102000502001c0d199030142026a219410262800d6135420000e41900c0c000312042d1029003280b10204105e6170000700034140c0c5185804c0c06a200004c00c540502000300080c0341503501b40d000910b1050094080d400b507400341c20000c7c401c0c00c58540c40303440240240802d40450002d503183c600003060316409030909102c0d0315070040c01140b4164056090200fa82d901600c2944c105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 1029288 1250 1028038 1028047
    0x1050402030408090607060213050406060503060d0203210705060109060602060112050a0f030e030d02060601051b010603080f0a0801050402180f0301110d09021c02010504030f050a0605040303050114040606020303010504090602 99
    0x40da81c42c001801c1d001e02511015842700000c4180c101c121310207501c81d0b40b0803440c10b2410020030703030000c1c10740e03900c400e04071a81066020903001081c20314110b803098a01172400c03410510540d2031200040c1542c58001c504448036681c9403080201120080c0c091000980d000b900100500c5180d01c0e02400060b11500688600f620141d07966165580c2d003183c11030103d044842021a50308003003100c034510404600c0240840d04040001904501c00d42c0c00c040303c840c4101d1003c00800318250003040c01550b0002525640708004404000c0d9500000c0050000070818000081c08d4a064020f684500640d0410094141004400c1010105070540065010754a03a000444e1a0f080c0c08043c1c07064144002d404164001c10340704005800d2030002c10703250b11400140003100540d034000151010340380d010100201030b01003401c0903880e18104c0388004100b10f0401c0200401c01d82d140d0444c50403252150610810b051107003007000300351072450265800581c02030004020034501904120917841c029031005250 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 1030538 1250 1029288 1029307
    0x2010912060e030409091505010506031504020415050316030b03060a0c0210050a0b0103060503010203010f0308070503040b0c010b090106020a1205030a11041203020d08040503040308070303020906030403110c01020a0b01050402030408 102
    0x1580c00550011402a65421b80102402080083c0340300d41c00800070100129030404000070418000500450719240c0c4544c1c05001e00d46407541114082c000e8000340c28104c0701a83c100415552046400001c0785051006030745019009014542d01064024007400159880c20950001405072081c1f540c00c5114022a82c80e40340060701c02c080c050724030750102180203841880090140c2e0308551289000ea0700c1000100007501d900b04036030080e00e910103111603480f5100e080c0b4924502071504009803070500001c50030000c5205520030419082c1c00d5451180c6681d984200366121180c5240141c10300840c92610b9004520420003180e104c40c1d0000c0c006440c1c02c0030401c011050300306800c8200000c071400c8881c410306404112094085010340781410703141ca0255940b507101d020b0340c4001019100081030040c1054021340607908190009080c0544900c0e245c103005203614850350340f042036805084241c42d070952022030110b250a40002400c40d01fa4a8003041c00020340c0028400c0e0740720b03001403011011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 1031788 1250 1030538 1030543
    0x6151003090218010306050106050f041202030708100608010507090302010807080405010615050c07050405010612150e0a020901120c02031605030f030108070f08030a080403030504030c02040501080a0b1302010912060e 95
    0x41d8043c1184240c625819490f110303048840c1a0003542c1844401d008034400d03242c03000103c8041c2c8620201d0100d1500803840464640b0616030049800f40c0180c0480c0c640f6030017550b02c66421296080000e10083c1c407112019a04c084080c040680041e180600107004240581d0a03581c215124400000e0659560b542d03840300c100f10010350340700080000035680c1c076240d0100700140150404440800565140c800090004d070030803980c43c400152211244024003800242e5080100800c0c000c401091821018000c025030003501010b001c81c0c00c0b030b407034106a26200e2140402030f41150b0003c41c5400780c0c00d540d984002d641e5600440e1248010080c1c1c003200508800070b14000c0c001c1c40c0c003c1c034216041100d0022a60500c0e044000b60f940144650324181ea071041c045500a80c1504000800e611542800c86526560010294020342070400000702034000065000e24107000b10400b21640d19192a0610581c244400190008031003850034031006288107103a4920034440c40c000100d4000214130382c0d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 1033038 1250 1031788 1031809
    0x1020a02030a03140105031507030e01020301030f02030f0606060306040207020f030d02030309060f07080106030c02030c0706050307020c010306050604060e0d06050901140a0c120209011404091d061510030902 91
    0x80040e000071522242c659014040c1c0500841c41600071403a07903040c2004a0764400b00e90884000d1855401e010941041c080d92100740c1c3c540100000b0b541e6903859041c030000702c0300030071b604900070300c100c04005444a50118415000d00e40043c4000d140d904c40303400708806904000c80a23607002d0841e400c61803c0303940030040c1d880c0b0f1403101d40240d40c03240382c40540c040c1010401010a080800e181003000700090f07000d04501d056802e5400c00003403010b01028128610b01a901800045104040700460f81d81d03040005580702e591160b003144c00c02c0381c0741d10044050346ca15204040e0008000e010510456028140e20500d1541c00703400081003001c0e036100d0006407507007691483d0707090b5507072941e60400440c00a00e69900c804103003402e009608003240010010070588400804040d80407400c10780381da104807001c450903140c18440c01c5c1c503140c440303001e000240ba002080c00340750150080b64a488603800700700b1612410f0120100c1140141400520a07070400703403010101010740d5002c0030b4005a80b1034002c40c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 1034288 1250 1033038 1033057
    0x803040e0f0105010206010605070303020a0c02090f011401090308120c1e0c01060b03040203030904051803040602010f0e01110409020a050403020a030303050702010e03030603070302010c0203030408011811040510060e0a05030102 100
    0x800321400c100c044440d040106070007103411500041d0052060540003400c0b901e4241c0d15141c0140d5401865000f1901542107010007584141144180150003040190050507a802881008140540f103030041d6844c1c08180701c01400b9000920000a2400300d201e251a80510384000c11490f054003a05080601d61090b98400e2140d0b0f400301d041c4104040c24070030b65028102c4000c5192540c00c2a4001035503901440d007202d84541d031100e000441090403006550f41d030060300411240c079075032503050285c060046c2c3c0e903014541610300a045468840140100c440042041902505d0b081c14001d805004e03601960801c01440401c010000050303c48416042c000c6001e07980c00202801c05040c02801d441c0c031000e80100c0f0360b05c140140000350ba404030b09142201d909081c8509044402c0c400300303042d805280d001d41080d51031302c1003e00e510002c58a40c1c0051301d01c030301d11151140380810100011a441a6112031258030394000500c5418003903401ea101c0120000e1542c466141d54900183c26039000c0a43da = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 1035538 1250 1034288 1034309
    0x3040905040807030e0a03020108010b0702030a020909010905060c070305030f0703020c100c0f08090c060702030c030105130c0602010204060203090904060212010b180301060b09010305070912050601050108090c10030b010207080304 101
    0xa0501d43e01c550000c81701c12040f5040780c80c0515580002740607440600448003034410000ba500210741e81000a030780d0050f030252982459141c803d0580d4000d280ea1038080c1c8881c000d190000f240c00c1c001104540038282d160319001d08685a07001c8040c410700e4014900c0f011701da0708102511a6240130400d044c5190443c0b040410401010300000b000101c01120b204284000c04092000b00038020610452001040c0c6019460700c84d0b500000c4d141141e000030031900741d46080d0a00c0007010018001c012124003c4818041c043d50f6105d04078200d1082d0b00c90640160000c3c4170700c0f091071901496894010740204005400c0ca0500c1800d913080e20006c3e405070400c010300041401c021102d1044e610300b1704404400030004c030361604101c0303491841b820707034884c3c101595540000c2c1224001c9a05a01034000400500c44000e0507251050b0f030782c50f0a000d502d004c103201c200001c240b490009079003004604090301e54801c907451880240d001d00203140301d15055001d10540813880c40030400c0503000402c1070042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 1036788 1250 1035538 1035547
    0xf0303090501030209180601030609060311090c030907030b06180a0b01020601050402040605030a02030402010903050f0a050c040204080a02010e060c010c02070302100c0c141305090109050d180504020309030409050408 95
    0x9015000c0d1600d5030140d818140184000c0070207a54541c12030000e001c00c660840041d544100040740101416009201d0300c41c87d0580c08000d2151070600518145003c2d14030303161503140c0c1b1550a08501080311107001d103902078403050001464250f54a07401020140c0301d04200a0100411000344808407000f00180340d845520b04107540e810040780780140720985085141ca4101a0010030901c40245803401b1550000089000c59101d011280e00070f542180c2039400c80c08005503800d403904020001540e00e842407160321400c5160920031a01190006401040d001c4d5150303005469000003002c01c03942c0b2600a01203100002c00a005100090443d580034040150561040048c0070101c2148641041100200d40b400940030040f001c041d02d2038280f250181c4107284000550029080d015405203d00b40303014010501415003107180401e20540640b0080c00c2c11503805c452000450041014030032008504100c1400d141e40110341003100f04080c0c900e002c4d1600e00b0141618419242141c8600f00041c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 1038038 1250 1036788 1036793
    0x20d020106050108090a0308060607050703080d0609050c040303031d01020a020d08090d02030a11030405040c03020d051b040501050703020a0606080a230304031101030b03061801060b03040b040f03020a0b010f03 92
    0x1c260740280c00c00342003858007820b11100c05992407400358002014800000003040460303650000351034405501904940c103041d2245402080fa1b00f11142e040780e41030038002d001c00c8103101b0b4001e441c41455110000ca00741491610101c0161003a61105940031903100e0802d40303501000e000400c1e600b4003070b800501c281c0c3c4a558000308201001407030340f4540e411400040c5029980401101c80c00310007481c01d1034903541d000c08520f0071403207180e00030740d40a071418002d41041d94054010341761108186800300081e039100000d041d0988e841441030b0045400811043c0525030140c40035049450080c412903e0f100200d681c0c000c221140c5030499080c55000c0007518007000006600010f11005801c6021074140c5454012a42c034011804006d02c00000c1a00120059129922141c200907000b0120ba0b00c900f40041c441403400b100c82840c404550910401082c660071220469015592020060b510f9030380f20f40b680500c01d04407210840031070003000f0380000071600c0310110358007a22111105d00303051451071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 1039288 1250 1038038 1038041
    0x31112010308030709050f0a150908070608010e06010c0201020607031806020c10180302060403140d0203070801090e03040302010801050d0c05030a03050c070e060904170405040213030203010c08010302060f07080415020d0201 98
    0x303030b00c084d205514010310148540c54548c49002259940501e80c0761100f11100169807503541c0d40c224140a210740500003410030303130141d4150304031a842c8050310429142d140045502080c80302020b4050b03400300003c1150a4840c3d8040d01d100d901d02001d0740701e042400d40d80c0707600740d07480f00c145080b03144d01c40c02d850114103080b8403c03985200e10f00d50940070805000c2c0c0e400394039003100030b00150601810101580d00700b40c0050440700d02c504c2c909400c40d545d280405014054010a000d0ba04d0b040d840c12909240028000040b2415250142c45d844001c1e03103000c1c10014030540104040300c1102c4010000540394504000b008a502c0c0b003174440648840b141e0800314a42083c5900524501c0d90020520410384c4030542d080c3d4003c0d400c61aa518511090b80c40c100e190f01c61380d44816000f510008245103507142d9103401d00141c0341300300e0082c0000c4138000c10848410780280000385d8843d1040040c00388850b004801018298402c01c040c609140e5511400000140120000c00150f0440c2c280c043c0700e168203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 1040538 1250 1039288 1039307
    0x80108100509070311010e04020a0305090706082a040806010308030103060b0306040209010501030b040b0a0f0306050a02031b070309050a030f1a0705030a0c021905030a021002040311010311120103080307 89
    0x1030300400c003070b107442c4a419948005912000d415071006001c0710034540d210f0b0920802148018100f956034840d0301c07000070010001120031003424047c010300072889c6445100325500400c107200c0b030301d000c44040311041342511507d004d01d8050003204004c000348800c41842154001e6000301d1a4540329859410700c101510049900c0a219800c5a4104001a80e5038508181501d50030701c1e00085a084010100300101580c2c0078603a80060441e40004102905210302025244110710a02142c3c84160b84a0107038003007518082012a403052008401d60700c644003410285001e40b621101d2255104003041e04040c0a800035100c01c54900301f00001d002e80c022080c1541d840250030980c02d40340c100002012800090807541280d5106c00700d900500d4800c00c03000c0d140207010b080740441c030012031922603a070f94070662481c8013500407008240442e500d20b209803000ca03500030322400c0c001080040110b000700503604040d0300300c04042c4485d09150081e40c81c00360285100712005a40d03414210340c0608010403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 1041788 1250 1040538 1040563
    0x303020606030f03040b0a030f0e0109050c011103030402030c0603071205010b03180c03070603020903010608060108010911010206010605030105090403121a040b040204050f04050406020c030304030203070201030b010807170601030b10080108 105
    0x10417003040520000c0085806004440c50000340c5400e481213058007404452070085d5656090500d18800e000001c52190f220700c1c0c09032592000d40302c0340f030100c648a000440d0301a41c1900200b446090900f0200000c540c8000c0e1803a01e800c012900c0618030003104c0d0281c020100010011007003056040c40380350074404584004004140c04211309000a688100310b0241c01d003003540110316081700d07403800d41010014000306015544150703158500b9078000c0110707c406940984d070003c0250802e500100784681640e149540380ca01d580c0c00c01040c014100c0000d8404c40400c4006020115500341a1140d0054041c211440004500c1c10750700f08025070704607000b442d204910420003000103607100800030f0111038080d2130104840c0d41e5410580002e0048460f424890b010000c108030805501000030304c8243d00c04d0303c00300001d04996004681c0c045044a8102c0421000d004011481c000d103260190310180525000c94111041030100d61183da61013070f80c001254040005012318401804030114000c0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 1043038 1250 1041788 1041793
    0x10b03120c06071206090e010212060604050a090b0d0c0305030318010605010507030315030210090906060e090402060c010b1201020408010f090302150405010603020402031302090a05040b060f0607020a0303020606030f 95
    0x8000c540c90342d8680c8006050700e0180448292580c14090a0303812910007007418020030418090f03401c644034041c1d403101000908403034581d1f00141651824009035402d50300081d1608080608080780c200007080402600c81c0c0c0144209071001c0011450000d4602452042c0301658981c1000005170208109200350200c4590403da000c0c803480cad038004195441160145004180440c90003002c5c6079140198001941100d0340101d200b28031500662000100c450041d001c010503540c0c0c1c0011034110b040006400d511800b010701060240c0b8180014100c0300424400008001101400003080b0070000d45407000e031a5004201002894002c0c800d400101b40c2c4070300203205050807550001d4480d815220140c0c41040003d021500740402544501c020711381c098001c5540e1705261040141600301b429003240304221010000320725141134001d060050f9400350020002e1f403509004c02c00c60700b0016402503048202400b11501503a40c0c45c80f800003c5002c2c3d00684901d06142c400d060130104e100740e0110003903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 1044288 1250 1043038 1043047
    0x2160501020607050a05040803030106030605031203060d0609021306090b03010b010c020604030201031d0303010303020a0b090a03090b09010201020f0706050406060506071a0c04090e06060301061d0402040504030203120702010b0312 101
    0x80c0d8012030b2066010b01c141ca0700540d0b4400000c802d45032400395400040032888003000100300b09405034040c10588000701c0488840401c003903c0900036210172141680c0004084807500d00040841d00201c1c909440100000201404003251000f1204640c0c8030503940da03254648c0c07200c45d04084c442c0002c03c3c1000e1034442610145600483c0491081d0308c402410541c0d1030000c8a201d0300c48144421400800c801920ba5951352401c0095031135001490954030052100003103007400f800020752051141e410745480460f01e182141e050300c1900104102410365400300407107800500c4080c0105816486000b00141c9824581004401c6407502e8020600802d01000a1404510824030380202d000903111900d202e9070f2503041182e018000c561006040300d007808801001d240e00890040c1c0705400503002003250075910f00c01199070418820101c984450804041000f40c10580c10161788180a1300440e0320f462030101c0c0c1000103c00489069005035920302c01d517652440c0601492124061025005040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 1045538 1250 1044288 1044299
    0x106050102070308070309150206010602010c090e06010f02100204030c03050d02010b0303030f09010908030405030d0f0513020609040204030b010e0106030501050102030f04120c05030d0207050f06040f0b0304030e060304060207030216 102
    0x1902d107140400703040101c01244090403d0311807103290b0042c00030241c15450750003080c00c0207035445100303018450165081c0404c04804078409d5401000300d5034083c0007101b040c0c4916005640c102c0642c5600c50441c010440b6150301008540014001035204030b2440000b10b1035420441d04018480028104590415140c0302641ea8000b06a0f504060100100503164542d400e0310707801030030300716001030400398007108000600c6400b2004d004180c509507018405405445007907003c5a20032104c50080e4840e00c04140d01506101c0003524107401c000d44014a41501d0752201000010242d0011021450100060040e00d52601a0034010714082c0011400e089215240000d24080c80c000d01d03522680841d18002031019200f0f082c0001c02014090b01c5103a90b019000940301c01e0b0501035140609805012030803141071600440341151102c154000d0800e0421200c5640c5910140c0154100b1102d421100e0b02a61014015401284110030040c0e80c2c1c0428a4003904014241c0e440e0b440c060b0070031004004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 1046788 1250 1045538 1045543
    0xf020708030a0503062205070302090108070e0105040b0f040b130501110703020901090209210309010f02060103021e0310020408010209100503091c02160906050901120c05011206080604050607110106050102 90
    0x1c000e08121014030b64081a00b000201c1100d18403400c030003403420202405652380c1c06500516030a0780a9848504036640d0341000c1d920408403441c41e500048080104021341075000d030140005401074011246819500d501081850b08801c1201c0c03030b0b140c54260304114568224076000041540b280241c0015440d5070005017081c101440b602c1811a00011001c0360b075501c0c043c5840c1990400d00903444801c0c5010000e43d580e0700411141408500705205501c0d0740c0d4000580181201e13030042c84105200601d0741003690300703078603003210035094450b80380314402600a83c009000542040000140c84030041c500300900300070345900030000d2180810510130000c0340822050401c9207450341d600400c4203c210104c2c5088461081c41d40d0300d41d01e07550041019030b400d411110850b0000c6a5541051346c85032612200c1010561004046144908042110354020780c100942c2650342d9000140f86642c60403424100003040300e04941c603402c0041046212900310441e0101c140b0790a000b00441c0303040c840042e6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 1048038 1250 1046788 1046791
    0x21e0601030807020105040504050a06031202010b090406150305060708040501050109020702011d010e0406030b0604060501180e0603030d0903020102090301050c04050f010c0809030102040605040608090105100308090409080a0f020708030a0503 106
    0x10508038001810700700b5a4010380891f0018400640704110605d45001c14030001c00c01400200c85c4054544488400140705020359407040100030300cac009135903c03556200002051116207490f4140b00020000000c59030070303c10f01d481440b094696100314074052400500f1034074142c0201407454814032811025036440004480d642020b003001000000d6080c0042e80c0350034160041c07a038400d080c100040204410340360700c2805410305a50500405494000640b80d42140d00701d000900c40810300304024540c0c0011050b5040180501039034030300f44451080b0402d4860b00001500940c0d0005003034481c60409100b043d5100840140050030a07040a0000b505582c00b0781009040000da14040301c103000400e002c85020480041c001c42d9644c0e9942006440c40d0410b21070400440e403840001140c441c41070240503c240d41442051086a0450750f507100346801003030001d43c10998815041002170700000c0107188014242e1914981102c80040017031030401303d074012404035007060008a09041d04081a203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 1049288 1250 1048038 1048043
    0x80d18031208090c060409090302010e0102030106080402060703030608060a0e160506030106050a05040b0403050c130204030b0a0e0307020406030501060510051e070510020a030207110909061501020a02190501021e060103 96
    0x18001074943ca03500602c1c0c91505002c1c198440701c009000903622020380c0c07149a8151117070b0020300800644214403403c0380000d21840c0301044510700050300500c1c1040c000c1005601c60708000855948a00395145442ca04075641c0300c003642d039440c00080a0004010412070400303a07801030016141054042040c501062282200348503000c134007100c0c224000c01c01c0d200500030344000307151155581d003001a0f130f908143c03030315070700504182c29046c602c3c100303e000721015290070100380701c01600c0d96800100106082100381c4902d000038808040140c1d00d40c000c40c0e00031405003002180c1c5500700010001d1110044007044180b000800443c4201144243d142205025000100b0707150340d41428920705200b0b05909005403548001115445160594054a99103004002010504900034148074503140261003130200c540c0311000107100d041c0e05850700001080d041c815207520107601d0380425004a44c03070070458001c052480c418825568100f000d00503001c0c0c190b40d141c580070024950f0685404060001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 1050538 1250 1049288 1049297
    0x290a090f1407030f0803010603050f0c0906030403050d0e0601030210030b0108061c020d06050901060b0705061501030e01020403030203030609090d0f050a020102070c080604020f0a06020304050607020301060b04080d180312 97
    0x80c0d4401c1c0d041441a0b41c025900a684020b1a81043c508026990f2007401000301091901001c0741d140c61451090610665203c180d440c0740c000381b00f08205898100a0003141006410410758810859502420b0a502e42e98002458154110301c10441000d84103030744001014a000c41e9010030b40c0c1d2188d07a950700881c00342d07030548010f00103207090b88210507070b43c90217900080c1ca840c6102c100b000942c0881e02c5208100005c03c0f21544450038201e4038480d0030005051780e440800414441541140d91816a0f201410700040c10401050030030b0982c0c00960060340507800100c01c01c115410004c80c4e19603c5030800d0054090f030958180040d00581c65131288408010021610410990007581261070381a0071140c42d40ca10b6a440d5003540ea200030485049004102c1d00da00c040c41828031000c040151101313a0061424203007040c0511219811a500690b031642d2101030001e0500c00510080000d042e00c40080c000d0b2408409000c0d181072241c038850515003d0343c0c5410070101344103464508410095150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 1051788 1250 1050538 1050563
    0x40b040902060f04061107030209010603050a06030203120409050105120304060c140703060504030f21020a020102041d0105090c04050102030a080612060106110111030f04020d0201020307290a090f 86
    0x20a00408515600a40002000075102440c80e115409402182d4940e9500d0410174640d442294841d507480c07000a4000300d2007001804002d00940040d0340c0405001e81c0068041e0307598000a00d084000d0821502c0703410002000d00101c1580e0083c079014013400c0e03e803801c40800a69500c0d40d0f84c45240309038020411028460b1080204010b550f90309803c030103084030185503d0b410040d0003000161030841c00b00d03500452135803240e40101c003480c003074058524030803212002d081e030200060b5104800f081c046540c20000456020185d102c07408210000322030100043d8100001d11088110140041e00160350a00040200340c3c1d00004a421601071032800d402641c1b128404075109440214266115000784000450780551004000b0700300307a5040002e0101e00c170f47c03414402d003070f11007070751040c1c12900d10b00d000601605180300c98900d03013032041c4102ca14000083d19280c50780c2c8511058444c120f01a82170709103150a101c403882d604060503581c2080b511090fa80c0d12050800145801810620070f0749 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 1053038 1250 1051788 1051811
    0x3040302040203100b0706051014010206040b10030501020f0a02060606070f110a1203020105070201150503070b030702280201030605060301051003050903091302090406080a0b01061202040902040b070507050f01090504 95
    0x144da0600902c0c5050045456819510708a03000c0c00080340c00a0000318000f030b00080c41038242003400308907501a00a003140b91103503200c41d5100b010041ca04c14585020000c0000054424801005107082c280c01d01070302d410301da190090415401501d50342c8103041c240700c502c011031000c0390001c9209a005100305800035034100440c11850440d400500c1c00c45104088506054044d0892407203805680d00800811030300faa44e03404400c0250141941541c0038120074081503403440002c507040031040c012982c20720340f28810107507540a109a0000c04004440c010811940c0500401c00076080450740035055604002c089a051002440032004140c0c4810120310390500900446500c5103003c0d0807024203600014032000a940842031183c0190f01d081c0d400a01c410000c660720041c40c0d40310001c0c080c16407a001040781d072032003040d00100c03009500f0400060620424030040005024040d03810382c50719070a041a500303041680e8001400342911012182043c0e90082d030000640c1c4007241d000491f02c0201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 1054288 1250 1053038 1053061
    0xd030203060301110406020c03060105040501121509060603050a03020601090204032d1203020414060405010507030503250c020301050703060509010603020a03060e0703090b070e09040b0402010c120305012603040302040203 97
    0x720020b2502903800200850541e44c08600000203101c149d0444d5020790380c500600c0103c440074424021204045607124001030400015803488800c803881c0410065200e4039a4030480e242540201e070f140e8840180e00c420150144035490040031170410860402e407460f1190681c045240380c07007910b4141850524010645889a4031840c9500480c0001401d130312100050029802801860048007044504100c28030341002210282c450680d43d06090002e0b50740c05980b0764001901088440c1c1c41d42004241401075020001629209980e070100c0d41d5600e40181421228042c00e40c00c10141040020322168841180003811071303509140050b911020040d00710000e20294003c903a8811803001802215585500000b56182c090b1f841600140c5807420159a4000c2d103403022034202c010100003601184107288659440750041c1880c40307600400c0d6891903003405407c25603601080e6500010320802013409941c3c0441e8000c0241030580848000155a89004512000b445035800100045508509 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 1055538 1250 1054288 1054301
    0x303030c0c060e01060911040305030406080402060d0911010305090114010b0c01020c0f030703090b0c12030a0209031905060603161205010213030309050906010507030e09040311030a080105030f060402030d030203060301 96
    0x4100a60f8001e120440d01900c182d100312a2030f60305081010480b03c0030081100d08480c1d11000462500d858401c2c1901e80c2c820040c0140c0e03000e0014040a003407101107010b2800324030710984800f021000000f002404541029011107420380c94003018040c0d103540138000505560788c40b640141c072040e4460300305004e44103100140240d40900d40480310707070800001c003901d204c9200c3c1d15514a003a86903410300000c0d004105080c403a84d4443c0100800d01c403505c0d0300654110a1288000d8502400000801d1238640102580c40361311000c8a011005e0020500c41c81d60018011030280030706e001044d4403101020360f94001d041500002690030f20420001b5411a45071030000188070545c55520300340039008807894800c40b802003282c980040e401d503208808031090b403039264036401c5040107190140020701c04000d20440901c02d08411a00c5495000c001030702c0f522801d60b880c0002c56041c0b42c1854101350300441408440d500110a010041e503000c0360041c0201c00038600161030b5604c2d880000e024100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 1056788 1250 1055538 1055543
    0x40f02030f07031109010614040909030207050604030b0a0608060105030a150b03010504030c03030c0305010b030c070c0302040612020a0801050402010e060d060506040308030702060702060606090409060f0203090c091e010303030c0c 101
    0x1440b80c0c0007040203001c100000c030744c1804580000c03042c0c0e6074a900b030756aa10001e5046220060400090040d08116400f40c0d62241c080d10495102c10f071a0004a00c5c20780c00394000382c0300d4020100070044224000e000c0c0310054a015006442c080d4986070100707540e01e0f40c00700002e009400318018081740e11580d80c0108801079004000b400b440c10309050107040d9203000502640040d0419142c005468001d028250403641000c40b164a96940c4160446e501d40000000302c4031419803010002c0965140d004100280042004510500c0d02c1ca00c1040b1004500346e0103c0f2059040c0810003002d42e81059160704885015a066a50343d55090801801030002b0b4002c580d115070b011034003006010a10029600c540d03500c1d004c44140e51076090b0181c2c1e80b10004c6401030383c400e600300071040c5181865045815002d00c107100109100c01010020010ba030011645034006602c031003e40303c800d2425822045d0840d85000c4104c80890786481c013042d00c40014080075040c1500c2c1d000c041e010070721600400c00b1068 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 1058038 1250 1056788 1056793
    0x708090907030501080609030310060507020d0b0c0d0e060112020909030705010903020c01080a05130201051c050901020a031b0806040b060702120109030e060c031207020703051006050a0603090b040f02030f 90
    0x41d007400d0107401820203000c0c2e0620341c40b600c1c0c005002a80000200c0e03004102602c0c5800081d8038041c012104d56002c1007080f03070031520110202c0005101c82181500a0009a0180b901c50b45013101c10411180300c1d402a02003940035400400071442d1506004080319010340341010150740d041c1d0071602c2d5100b60000200316620f440441c41c10703d03074040342030b00c402c03002607030342202035241d5441540c207490080d03550900e01e000580381c490040d0f00840082014901c62804000e2040c0c548443c00200d40044607884d0040c2d40001e46240d0080c0d04d071064802682c0c1e005856085030001e42e600a00070344c0000c0a003800345a640c62004034980d203c105586485900801c4005030400d01800340303001e058040c5044003c20840c8500078014a00441614000c1c0101401182040c3c203c0300d102d4034072040500b4507006e500a5040200c0800c1c7c0c18000352102e00400000859403a18000030301000800580c048401c01d482c140e107203000a030820640c1078109412600005074110140006410515045801c40f180c5c0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 1059288 1250 1058038 1058041
    0x507030b040201030f0204060806040c0306080d020303010f0605030108100f0f0f0b09060102060603030702010804060905030304030207060f02010c09031202070509090a020f0301020c0601050d080c03040b03090c04090201020d0507080909 103
    0x60400c10207101e28402c0ea42407000c00c000c1c3d4900400d034025405140007140000c0e000440301d04017980305448000341490045034040c1c1d02c01c20a4244500e860143c401a040000148a0061300195200c01010707240790080c0346600d000038003a100d116545043e50a0b54403440c0110300ca00c01c2e5000140302480240003080400d8081280000030220326100758003513040100003408075030000c80c0181c0325036006005185001e03e141e00454000300d004004884d110741e1410384002040c02040510f100d14840c0c0c0081c5100c909103840503092690305c24911003107a05001c540c00d991a40a00140c049903440b00301c0641104030314005906040e0140c10494010a0460404c15103e100140d00f98030b8500030f569440541032500180f5081c1e10030170050700482d501c048010406810403c0c5041c5125005020050030443d5400e1a0707402c59100b07030701c8000e00b14408410302a5440c0107106151148000f00c2c0d0400100c1c0341d03580083e40b20403500d13401c01e06000c030100303051f014048070104407681d0701001440c40005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 1060538 1250 1059288 1059293
    0x80111071a0c040801021305030d03060305060703090501060306020301030b0405100902060403080307050d09050d030f050402090105220203040f0209070507051209060403050a05010207060c050c070e07050f03040c060e0102070320030a050703 105
    0x47c2e4552140358440e110300d00c40c03020b01c00e002c0e11a074001d490300680540700301d03034031041c06401400c0081c008880350341d40c5040000200f040d5101660282d84106846a0342e418542061860000c1541e036160b403c51402403c400165501c05c01c94088981c00242107440e984c80c0142610140580e01e00f61110340c0c203022184041007070100e07106008401d0380e1400c100030140b10b8104002c07101d04172402504400c1c10b82c0148043d2030303d81107000189100c4082e08141c07003000c030b906070300340e82064030216100c4140c8907102c01140340c02011194020f66a1034058102841503c03640d07914400c004000121110010310b0f1441d5032118003c540166401104072560580c0a103881c50003540110401e603503140c41e0103810b1110511503011a000c0501c40030040911178204122106401e0024080c1018030004016206802005002079840784d401b82d8665503603d41b41040180459441076900b0313045410075034007400002e010800d8003400f0207010118903c0c103040030002c286030840c049005403540c8100c6100204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 1061788 1250 1060538 1060567
    0x109090c0c020301060b0406050405060d020903030406030902041107020d0f060e03070807050f03030705040306050c13090b0301060605030709060c1401050907061b08032802040b04080111071a0c04080102 89
    0x20654802d4000708103403903803503a07281520f007e40e00030207000a07001c010800440c60500044c04d03c0d107180c100700620f4400c07034000081c40c0da809a40a800032079140c101e0501507151912401102842d440c48061620810360700040c20306109000003044c1c544802c1441d030500220b81c0c044500d1009a00849a95070524108401d498100901c111818460020405000c4c40c02000366805446c00361030380350400341140e03142409050020a003544003581881004003a2185261200051209182c00122804d4400c14075080d20901c0e003018007801010000d2203480c03584002d65404880350340c03a2200701c200d05894044880416051407044c158280313800d0150b08100800c12400711852902c84204207244001003648030106004041c00101c814000a803091a0703400c51034482220742d46610700e02d8041a0380280403038010303410040411740046002c0c0203010091241c0c4242000641c48c1500381401c3e6500c402510b0031200c01210070310301150100c0c8481484a098a000d403110400075034941d03196008801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 1063038 1250 1061788 1061807
    0x60c02030705040605010e01080901020d0203010b0a0f020601180c03020705010e15011203050d05070e0d0809010e0603060310090f050118030e180711150906040c05150301030308060109090c 83
    0x80c03180c01101c10016052410307209141c01c072941070b11100da00032103800054840c600004c1201c002035400708481c2680c181c861000b1030103459241580d50b1189482e40d4014159008071401307000750350021005100603800c00c124100b0f5880c02c070601050f07094410300c04038041d005031070b0000d0071903007010a20a030f261004103020030064800030f40c905c0a80c1e40d0b011540306000f0b90b128007a0100d08200981c40481019801c4280d01514034242942c4401c0c0d21404a2000d0020b440180e80102011031001099a440300c0c80e01c0382c2d1041118001d0450400600003a100d5120464600e10540e440014030200b0220002000c01c040e003040007000080f078006036240450031400011400194840c100040c4c43c40d001d0645094045860403025555031101d0b420360751041d10a40500d424440c01101002e0380140e09000f034880e90314013000d0522403c20313140040b91140280c110512461200749540710b080f6200003528112501460160002e456420040e142c80e41160810b0945c5820460039040840e000103444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 1064288 1250 1063038 1063043
    0x901030602030f06030307150203060109030b070f09050f06090607020102011103010305030309010b010503040510050705040504060810060605040302061204030306030b0903030403020607090501090e10080f0f010b03060402060901030e070b04060c 107
    0x21400313545550801d0344030310812030010041041c070701a0044600c0c1a40c083e44d8420300c1818014007181c1c0b03d455034401034500300d41b42000504d1a03604036070600d42c03003078101c4002e000a941200c95404890300056180c00745600c410301a800110783c60f000d43e0f10075044001000f20071310080b503507541c403410455126070040700c20fa074440d030a00d00c010f0015403040707086a11550f0400040c2425054011300e2002404000d0602c0c002c102c424040400e080d904c0c0c3c0f141d400105504c00c02804920b81e800e9980050b079240350f12050a026052000708090f0f141e5500311035001444040d5540070f030b96185801c0c2c0062045030030240c0108a100104128030030000000e600644c0a6001c440455555980031a0a102603014050001e00c40e26001c01101107c4004550840d5616080351510b5448a008500e0520200d040c940349512170700e02c042d160710307082c804e00700c0d49081030f4090481403401e60085400c2d4881d988502c0c0c10948d51750315040c01c107001440507102502d540c1070242d41e615900c80004010004501c810b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 1065538 1250 1064288 1064311
    0xe040c060e010206040c05120c091602060603030c0304031704121202010b09010807060302090102010b060a0201050103030813031b060906090503031005040501080c120313080601060f020102120a020c0309090103060203 95
    0x60307803000d42c00010300f1032042d40d1048800181500b060113100c82e05201e0302025200d445003820011903a030720100070724855003030550110480c4040444c0240780c44005494140240c208109000d41c840000c4110360603260081000752210480c02e42602c414810f90b40304403500310170445c00b8010000c85141c00c04a03a07205030300902c42c000b020000c119074418207103e0351880d41e01030360082000e58040d4015096210050000140c00340d0240c0110f076141e0311039184100140d40d10001402055000700c0210340003060100c10034a9662180e5001d03091441c0302c801980b40d2031000401408101c103541100c41120360107031050141c000c42c0c0c5000e0742e880d002030742c0e001502d01841c4008600790802c2c0c890385040f643c1c55402800d42030054800d014041c8111207141006000402041c1449003591034110010100c507001004c0a40c0352500081981d80907085030011139004000805503c0040100e680d00505041b07001070b0b440c6003041c040c1e807031b51041c1d0702c0c02a04000c1402c000405d01c000d07a40554400d4050002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 1066788 1250 1065538 1065557
    0x30b060a020c040e030909040b01150503040b0403032007050601050a060c020303040308070206070803071d010801030b160207090f0b030c04021201030312020405040204090207050f0c06040303050c070e040c06 91
    0x8108040c0224480800140d00c251803184403450b003508140140704d00341c000c0d2441c211385000440c09204040303d0030740d51038a01034010401c0d6480520b024480c2c1c5000e140040c103600301035603103071780136000075001804043e201d07003081c0e1032103030419203c181c04205540a1903032008a441c0840d00c40c2c0b0b0900c102481410311240c00900d01e8083e07445480406c1d0700402840c42d1504540d24071109400400c01a030b00624140508800a0482401580110041e854241220300140e010340c1c02c20940101490400c03081c0300040002502c1c0d400e4494201c0340c904c09003810645055012442c02e42140d11103150981000752a079014030056201241c000400d038262685c02e00c5007010300c400d0340304126000c0500aa04801080032071702c1100001c90125240354054941030791000014240c4c0c0060f004940d04d02d500040400410004000012000c038801018002c00c074036020000c0c502d800740e440003500340f02c00001c42c41e51100b010300284c0003418204407540d40c103007000e04200795180c00301e008050102d8003900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 1068038 1250 1066788 1066811
    0x201090b0c090a06120609060305070e01060311040605030601030f020307090807090507020c010503070e060301090204090f0c02060604020901110f0c0907020c060406051b0703030509030705060301031509020a030804060f03 97
    0x1c00b00d03022104040d000c54000781c40c1c010f003110300c0c910758501242e140340c0e02c1c00301044800c2107003d2580114000c0c4010f010050500403120349200301a8044401d0604e0481c0542c41d0a040c1d005640803a410ba040107501d90344c07200d00590180c5264000882480d200004000303180e900141104141d680700310843c3c10070398485c0d00b85003c80c4e10580e040030260b0310000c00b4540540c820402154006030758034055080a06c03100205500e900281c00a1403019004241845050845d10809404003500e2405001100482070041c4d112807000c2c10700740c01a80c001a60050a9025a020600c405080401c03529206075a064554481565a03c181d108051840124141a100061540340420f00400b4245006d140010540d4540e11110b00d90187c102e41c08680c031007111052001da80118002d4442c6562a07869804041c2401019040503104550a00050000c00e1740700c901c1c09107100180200103016200382c0001414003580f58002021a8400500403070b0b10390340524044180802510140310000664 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 1069288 1250 1068038 1068061
    0x150807150206090316020105040305060f06010e06120402040c0306180c020606010503071403040c0902030f0103020102010c170105040b0609150901030506040b010e010c0303020c070306021206010201020304080706150909030201090b 101
    0x1950380c41d03a00d034002d00503030720b440500c0c05c00d8145280c414109203192941e0b0340d807098140201210750441001c100810001e40d96000550458548811a02c0d18030307103001071101010541010300081e000301e82d81e500d0240c242d40642d00c004083c1c210090351303040070104148100068101e4082200041c0039800c041000365020304240c034001e0049894400f5550744400d20050706801c0100107444140c1c9004001800080300e00c0110300130b100b101101d4040790f042d400061309442d181040c80080000c0880e0380c15030324158a200c14103651084070042400780f06840098994041d1800043d404903003c50b4080e5555003110040022100c00e8801b8030440e0340701c50800c004c40c1c0b101134206010030102e040000c1558401c0380802c918a11a007001802d017500d4107019850090543c00484240341c1c00510650400b034425603a07076102209200039072031890b0640e01c0140601520600604550300d584074807107007515052510000c1c6c0400c6108012915007410700038041c00203103209884406014000c154001200d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 1070538 1250 1069288 1069291
    0x5010302070503070602030a090b010303030b0a0605030108030409020f040305010507020304090b09130303090c030605010b04030b0108010203011a070f0204020f0d05070f02030a0e040b03030304030201050403020d05030112020405060103150807150206 109
    0x30b001d94200349541d250540a5400240f815600f50f59648020000600c02c0e0981ca000c2c6000303550011340402580280310b981c0e6045e40201e010300c5020b00041000b003400100703d60a035404204050f8541c000720000115501031604020415401d140401542980c00805001107902582d414400d014a01c41840031000d400c3e1584030041c6041111500440c0c02504440c4060748a06031002c8101d64030740741c0f501140c400380c200f00f0100c4030005040040c44461480e080c09000007000031403440d49440040e01da48091252582407195010030040240007040300b01182039034000d00259510040c0b421003c846074000004a40700c1c51905c03012545403441003140c0c9014181d035400840c5000641a0182c0e003a081000d41194003540b61904043c0944040c409180a03601c00d0300041101d00f02403401909020025210714100201440100719611281c041c251103150150f600080076103600d0f00480c00782201224001e90401035010004107254006038407421984219458070b03020b04072101c100d031540d10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 1071788 1250 1070538 1070543
    0x2070807060902120a060501080114060901030b040215040b0304020a06030b0102070504020c010e070806040201020d02060c03010504051b0304030c1203110403060b0d020904080c070608042003010b13150501030207 93
    0x814040c6a0000c0d81c140e2020036a50300090004550309403000703d0300c0c07401c06405000c50705561110010440c02c0000d01030514107035441c0c400c00c0d12914004003c0342045c01c0511010340f0144208001c2010f41d1280c085861003280c5018000b0b69482e00c8002880c1161300070340d070890288045103000541d1510a100d0404280740580c05040c810349041e042002a400050180c0c14a550301d01030b6410791001000050008d160203c0900789507c0d15000190400081845400564200b83c0422101c02000c070212070542c0c2044400040b41d40303c001e01900514054a1103200704400001400140b503001340b00b81501c0e070701c0340141c4400300e003d00d0021020f5810140c444440b02c00240400d0001900319000802d50f201f0190481142c40607d40004050079010344050b40c48240c00a841d0290301404d000c0e84018154508080c0c0c0300381042da850003070101c00510480c03403c0c00c80142e8034075903aa081d0862204e202c4018001c1c0740c5814802042e40043c0703604139610080044000c00003566500a0003a1000310741c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 1073038 1250 1071788 1071803
    0x207050604081b01030b040207030201060911040503030301030605040f0f0b1b0a02030723030a170601050403021005030403020c060d2301050307060c030507020d200f0906011103090402040e07080a0207 88
    0x703c2c496032503881d40d00d003802c906040d11181028000d48a92001d001060302940c00411690701c2d010b081001c403a03003481c15811000d0100400d0145880000032641182d034403980004241d62603081a000300110300c04000d1508483c644041c05102c5600081e9010f20150810741141401c50044100148a82941c000240e0000e01021000c903a441c01001a007091601c410403114902035401d40c15031744144080d001040742051003a00003d05603072403c0d80f0a00038204540760905540000d810910314410703500410100000041c10540300b84120f070150400900a04d0b01d0302003030f40080014015a03144c9030400e40c0032080c2c0d8911103182d566054100d5030b025019008450904404484c2070303c04081c241c0901200300b1969005840c1d81a00c0b1559a010790060040d032000c107110344007000e001030921403088105103d000c01b5a134540c0555900854242401c040c28064600d6042c194000d03800340a40c05031020400146881c4920891403054020707507180020fa9546942550490060140142491 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 1074288 1250 1073038 1073053
    0x70f0501050903010e1c11060402010c020402030a090b090f010f05010e0105060a0908060108160602010c12020a0c02030307050d080601080f07030f060305010e010f050709080a0209040204090f0302010507020705060408 95
    0x6500500040a041e07401034008140c0c8841070151790b1074500f550070078407104215040c203030010b1036100400420a80603c2d01408150405800003821020032000203480b55500102040c004003007540540440c9038080308283d040e00d000130800e074459100c4440341486508241202181c02803a200c0e40c1d058910031100840e081c0d00b0003041c0503558012031185d00502940c03880225103004200710f07a900030105200244050700c003180f11a01c09204c00c2d40544256070420903d000e0407600a941101d40104801d801a103400c880351080340c00040310038020350903000000c0c2100c01d1001c0445c0000d8500166102c081c00c50300e520303004684000c0102c941d000302e0108440400d0f09540300760007405244402c2c4030b01141040d102d172546821904105090149a17558500140506105000e07281c2e201c17010341000e91201d403030184030f10f85800400308006d108041103800a011583d941d841006c1450f080000c134142500d00b40b801900800e802d9031444050b03ca0741900040c949045000c0b603083d03a04180240210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 1075538 1250 1074288 1074299
    0x90c080c0306060403020a03050604020a0603110306011107050a0902030f0705030103020603040f05010603021503040308010602010b0a03020105030603030d02040323010510030201030504050c03010c050d0b0d0506010e04060e03130501030509070f 107
    0x316003000e8111070303201d42c0030000040541e462564100145001e07201800407820070b03104003c1164810780c4000149070400c42c3e10009500840c058a510030f01c00e080118101d20400c010a00300344254201c140e004d0394a180109405c81c0c1030f4046c51003125000c10306025601c0d04d002c1900d090100340300003544000c007040040c1c0060b40c0d01e88240582d52040e80082000e40d01ca600003074481d0361442c0e07214040d000120402c41419400403c09006050500003040343e42c01d0000410103010050101a050101c001b02048039500c00304202d40902040300800c42d00c440d105e143c81c1c0c0c980c85642ca00d82a402c031046030510f40d006c006200b601d0041d00210600020186035600541c045e01005006481e10302920440b05003584003800307021142c9003580c0d94650b480300001000c03c2114107100400b4001c0180309180d00010310300080e55415a0380070380200c10299035034a40700d0041c206080404000740804a000705400d03400b60b070800241d44090301c06000b180d40c1d404003156200018800c418101c24900c004000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 1076788 1250 1075538 1075561
    0x7050409080304140102070b0705120703060b030c0c0313030302010c0206070207060801090b030c030a0b01080d0c05060a020c0304030501020f0403030306050603040f081806130305120a080105010e010c020301050403020601030b01090c08 103
    0x4a58130503030001d410100180c42d034810101d03085840d807001c107a001808110044016800503072029440c01e0400c039482c204120a60b20303000080c441101c0941c0040c0380d034544601001900c2c8800c00a40c0c03d51f4080340c40c4e1500034080c1885c030304890058820100440c03080c0d8004074405082d00c50980e2041e80d942e06c0c010b90480900003440c0c0b46078050081003514441501c045c0850206075000350301d88c60075075141c45219460109050b15001c2000220107250001800c0401d0b45500810000307800350b2a0078950010500314442c65000600e00d40c4001060ba82880416024204803030003034404000035a0f0714420711485210480e001400f00390000500300000c2c1d4503901401201035032001104055103043c000c1207856002540511000e60103880810411a0030020714107a481004040350910810b02d10242c010241030190034144642d5146071529a40324801c2c240303060750001c000303200f5420a402c019440d52401e001c140c8264110b08004a000030950107100380300c140c95928005c940e520b00c600d001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 1078038 1250 1076788 1076813
    0x10c08010e130602040504020a030e0d0201090f02090702010b030f0105040506010605030702101104120b0103110f06040e04080d0903050d0501051c03030906060909080d0b0a060c03120e1002070507050409080304 92
    0x320b12130760a02011580341c0300d81c8040c05580a07281c400194541130502114607220f44009840c0c210380c1008940e1000a1490340e0b21806035505884c0c40040d919030780d0b81a4094503c12040d0354041c41024407041c2c0c14541500828080c40c003031002d503103542e6240c0307100721442d01c401c95208004d07920171010030840d603e0a0340045200c0c0d2031009228101500e0ba160385000400c41c0009645005030480144103108412540da10310b15811280440d02c03540b584041001c80c0a18410001c030148040c0000381800a550201c0c1c0c1c0e881c415000800100e510f519004c1c005800c00b10117801c506180800101d0f16080ca1601e00786070031020200c081401c5007596084020300040382044036101e0f00ea4600040d50000c5005982000c2e00c80c26500344c90340c031424282c0302217400368041c0a04c644888042088100e4000140000d030640508d0f1000c0704192454250014296400591400e8800c40e00f41d03d6070020b041d03000c2e2040f1072254043c0d41e020f03955a0104000e580065101a06c0944100b01040001d005e44c099003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1079144 1106 1078038 1078043
    0x70c080a030c0803040303020405030a060501080607080403050414030a02040c020309010f090308030604050408071b0f0b0f09091b030103050307020111012a030b0a0807030203010c08010e13 83
    0x1011801142d1002d0100140000414103161294040b00c01410000c1d00b00e500c0f0407120315100313000b80401d00c10030038940a400c1c0803a001602c00c1c281d0341d00030794140d0b89050504e400d20340c0e1a40300542c0e03840d02941c1031041070504001a1141c1c020b500d4800001e8002e55210100d00c0c0000d001b186000c0c0200c810082503060030710003d81c1c174006894000c030702507030300045996451502c800c131807244120107000c001002d60034485103680341000d902030314103036891485001d64501002140303009100709440c4030001440b00c0102414014402907100c1c03104181e120440c841c2c240300348240d500c20f0300140d07002e030400241c50080d56003107241d40d820742c04214002c1004080f42c1c01901400b0340600310200c0c0c0c40c0991285040703098801c0c2c00200340c4003801031242803083c1c3c0d101ca00650310242d51004a00a508040e2480d614600880c2018101c0f0250307501144e4035550201c07040d03800415510f08 = true := by decide +kernel

theorem cover : BRFrame.Cov 899288 1079144 := by
  have h0 := BRFrame.cov_init 899288
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899288 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 899288 ≤ n) (h2 : n < 1079144) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
