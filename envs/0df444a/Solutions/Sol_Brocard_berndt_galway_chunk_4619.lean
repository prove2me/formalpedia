-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4619
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:12:05.198321+00:00
-- url     : https://prove2.me/submissions/645d2a1b-431b-4dc3-a8b7-df4cb1b1fca8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 830575539 ≤ n < 830755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 830576789 1250 830575539 830575567
    0x1090c14040b071103030a111501080d0c030c1a01090f1b050714011b081f0512070e0405010e0601061b0803041a0901060302040e030a091401020102090d080702010f14 73
    0x1103201e0283ea044c4a0f03d40e2608002810360780601e0a403004100c0140302c400e070740703501000900402a41213040040c01d504001c2a40d07901c0764206c0701d0b401005800144401050700c102240901a644000205074840c100c541c199060b1400f405101d00b19841c0156040b4555414055114074a884041c6030003c1090700208540551050300b054403210100341d48034840e06024800c0a40140c0c40201000341c8044401004208050151030b5421180c00e05840b103481c000140c80d6442291812100c0d0400c5c6c48203501541e041250036070000d102103170b56600b080148001034002a80103403402e803c1d20b069a03201c00c016608010760003440c203403c404003001e01d00040c0180c0020f5801500410f032184140740c007421124100d8004036403010150b51241401c00460400340902624440404099410700180d04401844a07440b44a290451000c01d08603880c2a4000c1d411103100c008090200d550480032030034003441035404074000701c0c0020540c00050030701902c41c240c00c4d9200e2051000103031514604200c81c4c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 830578039 1250 830576789 830576797
    0x601020708060a0b09060909100c180315110a09150e100e030c0103061a310f050f100e0a05060408011e0902010801150e04020307030501090c14040b 65
    0x5056104968010858071000c0205a1103036001681c00305040c0d410318207100031400b019213018050f40c07102052100416021400b000109401440020682c01070001140c1943c0700a404d200c103041e503580c1c04802e220070700f101885400c030140b0f4280440c50701c281c0902c1892096074107510018110500c24052014124030320711110107946008192002c0a03800508a450084042008180100f00c512101d0409202c150540341003405c0c01c000781403030070a00441407480e08400d1110780200080c4904e0320865510709907045841031054501e0303d8942c803040740711036185005842807082498800140c0b40380a01c00083c0705070015281802c0441c41c103009590300700c10300014507030001e0861800310380360b1030b450040c00003060302c1c0c8008100c01042c00380392131500e003043c888001700a042c03005e0540583d8004007000c2c11a8020040040004d0030b08074212000400101c21030341c007a00000c113100b84941d240c1c0203036050b50352540e001c202d4100040000d64025050500d00e0350400d900344000c002480051003d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 830579289 1250 830578039 830578051
    0x105060a0504030515060f010809030306011107120302030306090a0501080a0206030a1806060f06051e1b100b0f030a030f030e0a0606080102071101080f04022b0309061e050f03 77
    0x7034101500e076580e05060107550a00c001040102c00e0400990340340415601505503802c2c20881c00c0d03418181212900c9100040410741171052600340300b4683c000800502d0020040d01440c150009103078030b0300a450742d00640f1000c1c46009800042001c50708180314840c100c5411100134012143e0650a00c41690001880da81c1d40c0c5545841005044800c046482903191064000252060030001c001d60f40020b40c0d00315030100300040c0f118007201148204024000424001e806840d0794640403a00e840343c07001c1311205110b0061ba40300d00c0c00c007842508559201e250032900f40c3c0d020182c6c1809c1c1542c999000700090009503101c90f01d000308038065401000300c17002400503641c081207103884000030364030150701400c01c50303500240d08030510a1599180920b0b6034246841c1d590750410903008940f4100140c4040d02c079410310814540d80038102c403034400d000c0d058000c034400d400c032903401e000e004850b180c810840441d00368482c400030340701c0e64011840c0c54841904d540b800e15a4800e845405a0002006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 830580539 1250 830579289 830579297
    0xf030b10091b0207080c130f090c032f060d090219170d11211e090906031f0e03211f03030903200603151e090105060a 52
    0x81819980e034011200b210180c0d040b0350608000c032407402860900e1507480311082c1e03001000c0074a9180c3e1071000f0f02c0c10b0030802c0d260201d4440300400d000802170a250600a0a80f0740c0304030004200115900b065007800018441e108041c410a400a0342c0074241418040d8081420401c074205461680d1241c49040e00180072103100345c0b4030f2035040503209007940046580442051452404800401c29400207454519081c140504030801660b034405494204004180e8030341c000c00700030b1038884191200015040c82920343c031101c04030701c048140e110704001030103140004002400c0e4100040c103920b50301440c189a1521138481a5a54000e00882d4101000d90004000c6a90312810442e010081500444143c910600701103a804160f00130000c046070300091400c10030000b00380c0120f000411a50400c2c0c15810072122900a1480f05d00c40c03412181c1e00090120501c0500a00900121901e1070f0030f0310205041c40801c0078060a8001c15001c4a038003045036401400241088400340074080d0003424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 830581789 1250 830580539 830580571
    0x1050910030506011721120403030b0406091b0801030224090405040602041e0b0301090203090c040e0f010f02030417071b0806270d0e0d290c040f030b 66
    0x1c0c0b99410070b0703400c1e809140401c1c0c0b2500c1c500f00300720080c89406101401c0301682281010140348031195401b80546190b01d6100c0d40c80000c00741402a000078054183c001d10420800da1101c07003000c014905e213421408031100003000b980406003c2c61502e416030380c005040841140d0000304140003100c0300d03034030386582250610424005484600655018a1185002607112410808070f00f00525100c0070b020100e50744498204011031050085a043d81d07408500940d80b85d6941c2c07110307407409000c107183d2500710340303001c1140286901c04075400034030035840c50003030050b0b6031145046002d90005440180140c10380090f140a84181c1100a080740380c42040340c03e04151144404090222150780810819040711082011200c0400d040280c0c128940b02c1c2c00310448444440c0903a6403c650107600c0074015281001400d5944003d448030200c3c0e400041c190b40554102e080410440d910381d00492051489408600da0f229048192000e075004040c006241070310315255001c8021010f404101c8640d0f8060f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 830583039 1250 830581789 830581793
    0x30a020402040b0405030c06030412050a0e060a02150a02040f0504020c2407120504050d14130902040906120f0b0a0204031e0201020f010e19151805010606050405090105091003 77
    0x7002800050040c10000c2e600d81c4c3c90300c824103041080c3c40d41c02600c1030104100b0000025400581d902280c421071500322342307654041d134058440821a102040e40b00318049009060345074002901c1c102d0300c00c450002d1034581c41d80310901d0241e01403030113002c2d00064400414016404c5c95130142810001c00350032207502c41c0d00d02c004034102207a00088902009884001c2040c0035400861072128140081020801440d00c2d840c0d4136240d0302d00c4540b0004000885d0007140741c075264642520312041003030481e0144243e844d0040c500a500511812090030f090140005540194052540000d41c0203018912417800b00e07650310415140080c135000c4120380c00d11000c000702e00c402c2000e010b0700c07900850070298003109000192030a9800c22688021340c0c108201840c80c04004645400b000000c6025200340c10403520780f6011000c048414212020b2500081003890030030340c0102484203002d00b000f000001d031105400c44040c45140681078100c007401004004504003111101c3c1d2140c03c04603580003862300c0f9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 830584289 1250 830583039 830583041
    0x5120d031e0606110601060203090901050d02010314130b100b1b120f0c16180b060903030703030615030908091201090f0606091503020f06030910140a2f09030a0204 72
    0x15810440016802c41311003d00c2d50340801080340501410300080d401c1003046400500d800405005850050401c00703900750859029801c100d880c81e0f41c0176081140792825041742d03d41c10150640c03d884100090010031256800005c03c181542c051003c420300c0d00102d80041908840c2c07400302d44201d4440c0c00c0300481010035640207400c1c27284e0440c0e270f000d07607485c07207100c00f1803901c002e0140942c4e0100745a01c0401000c09803207541448614410000302d041440000010514040c3c81d041039014000000d4071410140c1c140d0002050b43d0030300e42d600c980d00301281070840444060820043c903682081240400d540741c080c0c95200241d40795000800c0740600c80d036801c1059601c6039001c8420540b540b60030b100c41801c07402003c1e021118411420030562840d000120111445c4840b0b501a02c40040881d994203018004c1103240b020000040c0103900302c6a9080c10034080486502c00490310b48044441c0ca00c6030718000f1484404000d1054000c20194820301c9075950141007442d41c14814185410016155 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 830585539 1250 830584289 830584301
    0xa0803070303021810020d0305060310020d0b100c0b13020a0b0a030c08010503030f09130b1e01030b0f01020c150d0e160602030405010512060301110301030b04060605120d031e 77
    0x120b6a0056226041030f5040001100625001d9100340c080307140d00c00d9040d9000614030550100d9250104007504c0d880c0c0070a00b0103406018146909000040700000760382c941d003005031565015a44d09212400b0351a0403542444204002000d032800c5c4004900c1d283d0983c0343d00c2d441603000074460076407190b032014120f186a000c484040042902c0303040c2c0c0d40441d5001801d5900520064020b1807a080d0b800010782c5680c400c03030b180240f14800030602d40d5070602595002c007510b02c030007030590320b00030344030b001d041001d4030903200354900090612001048a040c101000705146a0680042c010f110150f02004a41d100d80b820314004800c041c03040c480419400e000705058000381c0030181c4414418203101c005400c1294111505560080000b017085036440b2084070928107088405c22015141c1900107405000c00d0300184c0b041017000b1002005000c541c08441c0d0103940300d030204112250780c1303806111107203036641c4c84242d280c1c2145820700710650290700081e80100c10842d200c1c4800004000c0301080300d407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 830586789 1250 830585539 830585543
    0xc090a0506033d02071a1923090a060f09051e0606010c03050d0603030f20060a02161a04020a0902090306010b090d0f0311190f0b060a080307 62
    0xd212010300605080c280f000703c0c01e091010041c40301c070b44401604403540302068041042d070742603610070003461125250b05680410fa40040c0c40e0220f901512009012004250f410b4141140309044203400f2070401d01c02c1600038a00021000e4110b0301c181150410328400500302c00050142e5080580000c1c0d452007803040d0300c0900710000820500a0500a02e000a0f5442e51442a9182122080407a0000a1480d4030100920b040c641c103504030710302110980240b9150400450521801204040d04207900900100e201e41e6013031301c4254510a010756200b00500e41c42e2181c2c0001e030218482c07030303902e40040101c4c01905e00b42801254003a82e60b80c02401402c00c51170101c0341c40b202400114903241c00900d00404201c00207500701000300f000039807294010710800040c407078006481c5005403501100800110b03003110b1480c0c1264624100a000c5082c2d122950786035002e2100a107110f00b921040c400c2205c0c1d0081702d081d60f00c00d280e81e115800c84101070030140e44040380d072100003000b010400060160034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 830588039 1250 830586789 830586791
    0x70f0b10080a020f04091407060302040e070e2d0d08090405070203180112110c0c010e0109080714040227010f031806150f090e0c010807090b07050c090a 67
    0x45026958100540001c0e00441c031a41c022007960070141c0d07140010724840c080c048400154503a00307840d00540340d00301d9240e22019406050030002e80d0507010340c00b40c130444271140c030860707029134401504498165403022101d500010741845c0200780e001c40404044505103210407810103400d00000104000d00040b002c0354000c4000601900b541068014203401c900c03140011801c0402d925400c6861a00c1130541e1410091a00594000c40219070004000240c075520701135515170b00103940507190b80b82c4244041c0418090003403071089501c0703140b401c400c441662025183c0703581007a6195100801102649511a400344041900f0304c030041d02c03086160078012007211036450030704009003140c0004100382e001d0500c3d1083d4400c800c0c40805031003011983c04440014000c040c1c0c100d0b0821000c15420040d5204d40101d000f01d2a10f0f4554041d01c1d00c108100101c0c0c000c0d845000c011105028112445030009107403c00400000c21104060240544214280c5411000a20101c0d465100c03c4507500ea81c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 830589289 1250 830588039 830588041
    0x3070813050109051503090a020a0e040c05062b1407020d031410050d2d06061505040b0f04030f08180103110a0f1b081b0316031103070f0b 61
    0x1445244000d00300410081c20048903441c64100010001c0c101002e9805191400000050b014075052000000e42503004008004a9803a07101c1040c40e64001c035411600d8034402d130320204803441e1007401d995401c3d00c0424211401c1c07040c03600072070841c0c0041c1c01c12644252145414405070801400244c8119078650003021b98140001008040e030340f0421020031007404040c144111a210102c102c0c0a41d1029a410a607a032606c4c41c047c400d602c0c16407001216080071030301c8200c5540c1c0e4450480800b80c019042444030300c2c0c450718000d541d00140d0382000046a410031040000301039800181c100045884070a50400755691100e90051041c19021202401d0009102141c01c0c46c40312441100d04c82031030200324880c0031004003502c0b8800e0403101011b01c451850080c040d54070400380046070400e0103620f8840b18019141840154100002202c40031030000d01400b0500c20000c01e844021188079580c3c0c2100f01c0700c0d02c064510329100031140c9403600007003007003d01040d084d00c64001810701c1500c4842c41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 830590539 1250 830589289 830589307
    0x6111203070806132304020117160e0105041d0c0d060f03020a08030a0e1c0501020c0102071e030c020108220f05060603011a040f1b05041505190809030c030708 70
    0x1040480e00d00c4e02034580e14142c0e4042c4410f007a0102030725411501040068640c58600060790b00351468944660445003041c100080701c103413041440000a096150b040f0400701003001500d6a000302d000706070802c8a00042182e1201e460707024150440340c0c0d0641c9502c0c000b00a9295810390b0707495080042403a944560400031814840c0340c0c480240b084030081c2d410100c0b5004001c0c00000c600d007040303204802c40141198400746000384500030f240e211000315650006205000d0103034000c1c120a484400460142201c50038624032a26407580d81035844640340652a0b006495002c00641307288503426580c4001d801c5161420703965600c07540540609101a0040d152061400000914060090b41414204d0f1080119800d11640300c1404880210300f00440200c401300501100c800d03034013011900360201044c0f5401c500184151104102e10a444401a02045d1035030721800300500c20001140400c040c1d00713481a5405d039040503199040d20702e0300614864240c9907810911054030980300000d00d0200c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 830591789 1250 830590539 830590549
    0x10906030603120c020f122505030d051612020a0c060201020c0d120b04111804060509060105030406060b030901140105030d020a0f06060e270f0706111203070806 71
    0x1412140380c1440001d003155039080005414a140e00103125132048044110340c3e610072143d10071400508284c1034004c0303128040359a680e50300728000b0301d0018120b0700a614041d9100355800d5503406030041014544058040322076501443d101180c003a800b00d8920002412038020448484882d4002e0a000c035660900e81c4005001e54800411f5a20410411588a03008a0303941059101e41c103155034290b00c48012100500720359200164403c2c6000341085800e03444c407020300075031909100100451044c200c240302c121005401055070105584002444940c4990700851784244218004134082c0e60750030300208039400903102e001040c0d440e6000001400052818240100307002c90050011440500c0045d403104d6982c030000e0081d00311001c0003070034801c0640100004001d412203105c2c007481c10108840c000d0700c994402a400214850b0300095103140000c00c01d0002c024400504050382c5000c0040c3c510001c4040803488901841c50003888025a20000e5032250000d5110f62840c2d00e80201080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 830593039 1250 830591789 830591807
    0xe0103030c06230c0d0204080106060c0510090b0f0c12250c0b0105010818030301080102040608011508190b030a060e0705010212070b100909030c02030c060c060c0711090702070501 79
    0x2600c3c020034900300f600c01480c00751030680c000012079000c41d80c6001c4044140d0113131145800103003466080c0b91000030926030080520b40c0c20380c00364040d03480310104c9a40c910161000600050400340d41070340428005c1030005111a0030021088040b4a400504929003290f0b11040301c186504203160301c0140406c400501c800c0440354034900d012103d0090643d076090140301c06010300ca0400000000040401c1100c0448828210a09040725120b40c1d4450b100c501035800f90103003000095114000040b01c3d00c21030240000c3d0842a1604460b0f82e981c1943d00d000c218214007a140044d4540c10f00b110305480c2808000c910a0148101196011496100601d48001c980c001411540090320080a4140320000e48182caa400701100100f074803203803603003d82c0d0301c02900b1084946241c0b00d441e100f019002603000f9182e6100b81c042c2c0d03010405032402c0100138051049a0079164014200003407200d101315008140141c81b440711551031904003008100b81e10380445035a005039100d00802d10503982c00020745 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 830594289 1250 830593039 830593061
    0x12020610050d03050f0c0f06010b07150204060e040b032401050f0a18020a02150c0307030f0539070c08060604090c03060e100c050a110307020102190c0e0103030c06 72
    0x9005042c0203941c0103080c0d21580c800004600710100728541109001c5c820814202103800441d05c80356120f0b500701090b0b03844014106d0b020300380040c4c400c2001483d0300a407021905281c442c18011040728042c8405000c0202041c0c0e414011591002445a0445480c1c0c90504494011414031340c180000d000790282801c8070140302d0500c00000300140410044030f84152140c843c00540c4078801c80170107a140420003a481110001004c0030400704240e00e00256124465554084c00030781c6500304400c0c120f55040d0b501400c1060520700903003102c13901400f10203820324004030300241d00e140000f142c400c2d40c100380b00c00c031031920b041e81c0c042210900802000d42c1004085804110b4000140d9500c0080111488004e0540e078843c1c8170800c5c0d80e1800c0c4070035069180400000e000c10703248004010419408900b405000c1200c0780205204408000240d0701000e606070000e00c0f076481030b58400000364000900c03c82d14806840c40100f14089028482c5000f184a41c4606426426a18010040e510a0690 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 830595539 1250 830594289 830594299
    0x80304180212191506080702060a06030b06010f021501090209010914010c020f0d06051f063912080a0605011b020f030a020603041a0610050406050a0306031202061005 73
    0x58004a2200680141e4008034a100d410002061107403540001c0c1003e4013400302d21048540000078010f80084840744100c826600b5520140d60f081d840504aa03401d0201078072600c01800003500650203284000700009090042382e240a980c2c1503034071000311098000c9a180c98000c02c03426050358000f07841c600601101c1045000b64105000020300c000e0301d010700607101c3c14003422100240c0e100c000000c240250010780a106a1400c010b401991110000000c038400d2140c070340000d50280700d41c61000c0340300c5401c003401031000302c0325801c01818640d404203c2c0c25003050403040740c00102c0404021840205c6500c500800b4540b030b0002c281140c02e035601c041c1c144898590240e2208940d52400100154101c8a9446280258001c240b410706031a00094100c40004144014050310854545624060500d00380c0140d40b07810503c484040115010408070b281840288070007801a006081540020b20b40001d170640c0d292160180b401200001c0e00160700540305000380c4a03003442c0454047c00056034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 830596789 1250 830595539 830595547
    0xf054602030f0322020405040606170102091305100f0306060321021005191a090c120103060504020607080a030507180f0b0315030a03170703090c031e05070803041802 73
    0x1800b03001c43e120081603808910aa02584440e0314000c55824005a40180c0b04202a00e020b150940040079180118030b50240396212091036900b05008942907400054050002301c03241500f00c038090070024080e090038400000e400301d070100c010030034280118041d0001040031403642c201080490f4070022148004800400325048954001030901082c1c807507200006a5503a44030310003102c40c985180d214200c18101986520010184804542c01403030850b03003007040d0380b41c5942c0340d6030038420244080c4840951600400210710141d02443d80640041c0c0030601d0040c0390303a1890526440408110041faa68806200e01c20380d0000d594407140009803240f00d078141c2881016020820940305407501c40340000005042c4003240d003c40310954401404981c202c860914014041c0f00d0b003445000000303110080001c5240d0300c64003400b49601d4101d49152001d504507141c04105101c00c1928407000d140201c010070000b4402c2004d54010505c0501a6032994103006424550a401d00070b00340f0204c2c0140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 830598039 1250 830596789 830596807
    0x603090a110a0b0f0307111c17060a05060705070b1c0b0f0102030f090102010f09111009240c020d200d120c24020d1b0f05460203 57
    0x41c080720030521036031340869101d03503030b002c0c0403201b091000e0f0a10606006000c01c0040e01c080505104161601c243c90b404001e8204050314080714004640301a8003000c40f03c410001410a60700620110b4000c0081c1d400d440d44400c446920780d8003684040c0e05403409944607a100e001c0074454464410f02c120340c0c05900700da0610000350360740140d20101e420071350001400e0089078000d60040301041c8a040b014000c524150a00340c540600980c2e0980c00b45e1001c5492050003403041440d44103554001801100d01c00360501b001640c0700d10486008140038090840303c1c0540c1d9079078403075403400b8416001000107242d07850040c90035402081e050350259100b007401c040010120100440c810700c01e4034191b030749a9440d081418109402981c01c04104905075030798540303034025400601e1b07aa01d0150341407018070801c281021401442c4000e00000408104807000ca0303620540042003011038103900792011022183c12040d90584c1080091540014002d041842524109001c1081001da001031402c1c07000394 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 830599289 1250 830598039 830598059
    0xa050f040602132d2715120b0415020708090d0503070b0a1418030a0e130e1b0d1e05101d07050901050607021507020603090a110a 57
    0x640020000e54000c0f03403c2c1d0301d0081c441503480042c001c221104900100a2580f544101c550700382058844050f440003003650183ca94041352012840c14040e48942e03e01c405034001131030a0b66400400041e01000041d010344c54501d50300784107014084281240c2040c0c038011a5594158254890580c0103000c40f0002c12080816614003c4042d5130310356040000f40340081c20b5100c3e031100100b20510341414442c840322682d00184080306004041c62254403104081c0102041ca1131200e805c0e0740c001c1044210f01d92240070100c0c1d0301c0c80e0180039210f44002201c400d40946d05041003648240c0c1c00340e4800c851207110322081e462100000d80e40201209140d484821112456600051004464020150410604100e91400c0045c002e008000c0c4400c0b603c1458411521008035854501c1494030210b00352804291250403074200130040c07413134202c840c0c0c20301481314600b40c410780401209111141c05611440d000b14400c000e80e1020703008602c114900b66445c403804040d482e0040c00000d0041c020760100d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 830600539 1250 830599289 830599291
    0x206010b07080313021504080c0609060a030f0f0606030903020111041401080c1c09020f0a06050405010c021c260703020607030b0301020d060312120e030306011107080d170a050f 78
    0x201c15a80d01e5030348284c100d822007524440250010850641140702d05240000340c01683c010390156081006c540d8100000d9010310007800e540700030200910f11600340281d0010184000d4801c0120702d140c44951a1070440d00a0f0344240f010a80310402c4908240c5d082c0b007940d12000203c0c40c0703281024180020101400c0000c14540c0c10b20143c0804107820100e00825500e44020001c21551000c0c0c4028400d0b0181000c20300c200e010b9414049803009030300d444800d4800760b900307943c0c0d03182c105440c1000444444524060617070b00001182000204e5805c0c5508010120b40140e50010040d045055803041c88000741c1c201580d500310178841680000d902044068020889240110341c000c1080c00107070091040c9800c0c1c01c1c1c03052608900204012010300802121580da8981580268000341c0b004180e54940b08070f5103aa82040000800541c014148800813080c003034202c0740718a44800a1520700b035900c503032000200304a00944880f0885001050740e1003210400140814107020048010900b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 830601789 1250 830600539 830600543
    0x108070501181202060f0c0d0807020d080f101d070813030206060603040611030a0603062f0703111e0111090306150f420406120b04020d020c0601060206010b07 70
    0x24905800200f5560303924146c0b00300080100c4111f9861004071041a03031540300051030300101c2d105000080443e40086546a04da17a0b42e600c2c1c414091341d9506c1c94000340b0b6402000240c0c8101c460101158100281c2043d545564500805030011300306820081e00c1054020078594406468401c40c0300000e074041103064120328190b42c0c080d100c1c0c6a40c0f40c0380000c2c1801045042290782c02000700400070701603030080000c407030160f0400c2210340e034002c25810078007400440710350290707004031701001506803102c009142070b42c041d2518210300080c241c100d0b03080c20044030b40c8002d080001d1003c0c80a040c0e080c840d494000011150907442c0800e01400b107905c614005041110303218080c80f0000c165161069150007400d401454140307001444144000b0851600d810707511b2602482144408801010101581c140c5445014908040c41c01c03400700d42c00c1140403c1d075400307183c5aa5179416075403101c0c00070f042a100111405a1a810700c404a60302c1c2510507840030f02150300190041000c046004c1c112101c243e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 830603039 1250 830601789 830601809
    0x405040509061e10090c08161107030807060e03220503070311010305150301021c0f0605090414190b0a14070905040906090b0f1b04140d1406070305010807050118 71
    0x5555030740010701314040ca82c400c0c0802401c0c150308110090348909503900c10010290b25000500401c10200c4021031002d4580c032030340d8003d0740d0620200704550054440c6621070000400c5030440800690308542091840d80d07225285940302813561250324003000090f01060f802064020b195407030700b99585c1c0328aa030550603d983d40d0049003043c4502d40d01071143e0500600251368518901510482c00c1c0310200003460440d140050025403000980501130450790010302c0c004994031103441d244800d02142a09203270501c180800d0a1120786414104032605005524441d440c0c07400302500000d4400c0c04d01c049111891000800609035001800502620070540d80080c0c0030f8540d14040c4e00801d6200b4001c2c0a00c0140d07000c0010082c06125a035100d929400660070410310b03502190b02c103500807802500715418102c4e11412007030030810792414a0314066034541404000612009003040815241da0000a84a01c0144800c1100b0040c41b0010402071a114901006c84114200b0613040c60081e0a402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 830604289 1250 830603039 830603041
    0xf060e2a0a0501140c0106060f02010b0a0312030c1209030e09060d050703030e062802010e15060411120a0902010e01020705010c0807170307020309090a0b0603180f01020a0201020405040509061e 85
    0x500003001900d0341c10305e44a00800c426905e511018146c0320200c000d0100560a0401d50036141c00d008088002302d941c4080c0904201d400d2820170b901800e4203014031001c1090400240580c0f0203140101801103010761140b40d03001704804144021000c0082419000380f8800c606080050030001e507d5045941515000220b99081e000040c5240315562244e04803640c003e420071040d400c201c1c12103004982580081040c0b002c0c270000d50307440304101d4400c81600740d1040d0014a581c2010b41004000601503080246004c1c0410032401d40c240701590070031040c5544085920442d60001040c42025909000a204082ca0000000c141c100403081c010803001010489100b0000e01e80c207440002120f03001003640341d28000d80000d5a80d0490700c0f240e8855524000400c025410a01c01c2c501c0c4010090b2441d0315540d181c00c810301510340b50904891403403107051000c1c2c0390f20500b84003506000540d6800076a07110b192404001c103481025004000d00d4010704c06109034210428480066065800d00281e42 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 830605539 1250 830604289 830604317
    0x40f0b0903060a0f0e0d0905120a05100b1302160c1413090c050a08210a0903020f030f010f20030c09010c061418011b020c0d0f060e2a0a0501 62
    0x1404070f0306241417079171268444004800d9045921b810a8a00684640e8035403031141d88819500c9150060203002034000084200495621340c100f03400070b103409001484140c404014900403603109400b0b100d00141c480a541c1c2c01c10460b0041d00340100000100e00070414030700c00c0000e004403484226081040c2d83e0f00c02c200c04008070074000d08000c0c40300400405140340d803140b141e522103101d4001400340d000000c0c6015030b02c06d5060181c801d400c600e6542d008040303041d50b092010601001c48070076498400da070b403c130724001c200340540904120700500101d07503500f115408100758031961000081910051082001c00721542c401e60344011000d10381000001024140040141016601410110303640760030000ca00c03085003089015118140005c112040451b03501050002c00c0004400040e0409030400085140c982010401140900e00d94600c0e042d4687e44e85040b40d1407000c0800c80e64124504c880306d0384108100c18a0b010100d8040c004290004000148004c181e41c0101c6050110500102d80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 830606789 1250 830605539 830605541
    0x3506181906030c03050f12040f0e1806011403011a0306040b1003080406020d1706100f02070801151d1b0313081201030204050c0906040315021e040f0b0903060a0f 71
    0xb5030304030105000d910740383d0401d141c40702500424000c15114501e088001341001401302c2c1c08556030810804119820803c004003c51005000340c0e01009281401d0f0141003c00e201c0700380200b400118413800c01001300140350a44002c441d0f491a15610030044150781e4070003044240d4060b80c48012a034050381c80b0001aa0581c05030b4001030074030000400c0c0414082c0d00014082d008004a44070280e10544204a00c508240c04441c034a8011400b0b180c441c859601034070309190325601e0780c01074031072094840351220300b114060821000502180301c801c00c64880031b01c00040c4030111014903c43c00d49003030b4503284071300c0c0112902d145420000100050a0240802226040550001c0e041765641d08a480a02c0600e4003070006070301c039910349004262008140c0007103c0b022140501024101841d5417600742401c1d01410381801d11756006c005003c02540308003038502c012481c1560b442c3e141c5040c611074918110313035a0403030307210180204080e80144d0b80008200d50310008800000c2076200005103804 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 830608039 1250 830606789 830606801
    0x1090f0918050312071d01120509073b09030301060c080d06030b24011205091c0c06050702160506090a0e1302011b0f030f35061819 58
    0xd4030394003001c1500001045803103c2580501480e59981621108646c180718a04405010309400b00e50110220505445a500121781c04136041b000c1e81c004941e640e80341c012421101c80b211001d606110200305c884103008a41078510310036042c48000e10310780030410b15035a1006000c1c000900401e40b42c1c1904205a000450304403d01c040303414021195245458020314000b0f0303800b1400d901c1411551000c04000341000450100c0507500ca80201c104a190000240000303002c1070090302030010094440002d123914076209007241d0f55100040340312400c0120032070750054481c0d0219045015003080c0303c61508484010303140121030381c56584485000181100515502c00845415240100f0072100f4400c010114414000c0e2101115540420740e454607030038182c1d40003040c2c8070468081802180c402c1c51081c60451300c6080070788503c000e0142031a08843c0038212880d5594110041d900c0301404100050f820a030f068403c035a0450303025150200c0160001d10300d0368030500e00301020f240c0e1314180e0444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 830609289 1250 830608039 830608043
    0x918010305210c0706030e010c0c032a17070213090213022104030315080105060612041e060501030611070b0f060604120f02101805060702130f0902030c01090f0918 72
    0x46801c540d5405c4050081c004490340c40005500e07100b0f030584694000e002891284d0b50590b10300d042c000500d03a40d030003000c004801f1380c65000c02c41c84001d0006025032400d6424650051002c5844203401c3c810080c004455944130440c9608003100d460040c1c5034600b03c0c0d84051328409003da121071803045c8804186030318440c4246011610414401415059801851150200300510310141d88138441142600c5041e15410f4000404020020b24201002c1a01e60000c0c840c44407100001c2c034550618240205043c01a00c0c04c990314001002001924416544070500031103400d4248070403034a420807500340003408107107a50311610000e200c035a10401150094803807640c041c034401441f8144002c2d5507490304000c900030130341099500304260040c0480d00341c41407291002c20081d420f00c4244280b5400114040380c20003141e404003581012180a000f20784056102c00140007100303401010b00d0118041101e0b418800b184000344512413a0000f0081524000780022580d198440244401200c2d44100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 830610539 1250 830609289 830609293
    0x50a03111309120e090714030415201210030807030e01180306050912251707210302030c0427140708011508160e04020c030918010305210c 61
    0x1c1540f5a94001c0580b0780002802e961828030b1741d54591003600c058150262645500805000050006d41e16030f4020000b422200b00108108411300060107812148141c0b1004800300414004440e40341e00100703a40c01800c20a414001d0340c0707161915085441110805002c010840700000d003541d005003502c007209000d1441c0d50883c199207050680040c40e0550f50b40999004040044101c90801c0040c3c0d88409501e4004107010301c6e03082c2d1108803500348007004a0301400001b0001e961220b10038058000340380990741030354602034026125880301c102c5e11106001e051040c003c1c040c2441d03840d02a58161400b01c096049540310700035907055440a0302c0561440d5a080403002c0d1484010040c80754020b07866a1149502c613620303228540e1700d030020001003400164088000030a0020a41c442000402c441e0820150442c0c0b408007180c2079074000b08511449178000540960b09041c910400400940d141d4052079040d4113507900c8581703908240560509529660052840390342e415800ca079060808101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 830611789 1250 830610539 830610563
    0xc070510020c031504021c052a010813030912050109021005091908120306010507050d020106080c0909060a20030109060e0901020a020c0108131401090c050a03111309 73
    0x2580c0300d1071410b00a001e401141c1c0008102c00d00e0050700360099030300821007020f080307040c480b07600c060341212402d9503a44905940030803141c0c1d1041c5803c500481c03042014410201010014203404006032000410502d1101d0101c0071a038000c5220060719100303440141101c249080c42400b5180011010750b00403000f5650300003a94000d0024102c114050b20300401c88180c00d01d200000e41030b14440c10603d50400b01a8281c040790641c01154480d0050421906092a40e01c4141c9000110043c1d0030160f035441c4c0301809040c8040003c40700c0081e08407600c00041c9000f10005486644c040c000000880e1075403416280c0303100505400b25000104c1c0c506944a45e50703040140d0140085100301a4420004004a041e1440c18000c480d50840c0640050145071910401141d8a0390020600d40c4103000103541d485c00208014607011246c0200c200104650041d81004c0c100354001d540210710480e0264410000100c41c40fa00c46a451001c450000100f94100030b644094021440c000f042d8148080b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 830613039 1250 830611789 830611819
    0x6050f311b09050f0702030702011818050106020f010c0c060b040603020d0606062a0201081b0d02130503070e010e070c0209040b0f0a02090a030f0c080616110a020607080c0705 77
    0x1e68044121561800280243d80301c0c0740d0800042e01044e1031072801070f0401c1246c000035501a41c5003d042a0a9107801e800c5190341d03d2800305441590300402e26850380343c1c8010484c069040146400f00b11084000700041c040310003008c0c00b0a100564001d04254a5401307031405903039030758007080085401600f900180a824070748800101154010720000c2040d2000d172001c07042038050710700c204680d0035881c00c907404c1041e001500c8550005040910503000010304010111148000d03084110b500100580c440643e04c614903c0f203891a0071081c06548040420054461184802030443c1c0c0100201085070f140d480044031003440e02c01001c6e410140701801e202c100414401d0182c4550203520305002d090b2103841602c070580c490341c0500b07a07002c800c80e0401c0c40850003a14003100d0861080200103101c075a500c400324100034007100c1c0e00c004600c42400582140341c00020140340b60980c60041c06a40c050f0f5030005400340507501e809800d1203000301d60282e81d00c0c02040b1403409400c0081c16865070003004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 830614289 1250 830613039 830613083
    0x60806012607050f060306030109120302211003121b0c0e1308090f0409120e010f020f060f0606070c180605060c0601090c0207030f030c06050f31 64
    0x5481c1120310484007100440ca40100410080e0580314018100c004a0382c841c1e00b00300c0031390400740425a25540c0c9000c540001030701000c840f19014625207025031034040300c4045141e01c1000c5410f481201e40316070104400010148009c20a0b0b07584400c2800040c40148411101070020444040050700c0c0407040c8014401d45441c2d040440701e11080361740b007503500da110008100b007840e10000c06007041484188032510700681f000c1c40c1d45902500001e10f40b00551604000355050150040125251700c82c45003495030b100d115403c0c400703201d00042104021040e006079031400300130002e000302c5c0a0030006c90525a94402103030710315604284120002600d610342c0d078560100010a0780b5245d4501200090a070030301205407400d80c1005400341c0078aa1070410100c0240030040141000c60140140c0440080d01c44809a00b132180265038282181c902440c0c4402111001740c400c0d040d68102d403040019501c01c1103849031072034058000e02002c90104840703032482d410070010002c04201e00880a40009212 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 830615539 1250 830614289 830614319
    0x61621030912021b01030e01020f040e010504061e05090c0f0c0105070e03190231060501030c08040f0222110315010e0102030414030709020d0c0e0109050f040f06080601 74
    0x40c180036110701407082c41c240c1c2c1c1d40da032404e803c01ea02603181489a6441d8020b502090810720300100151601d60510403101a40d807007504190091094040144001d04007849100041c3c005d1a1000c40b51600198284d000d8085601ca04c1e4400e01d03e0400045400720030b07400340d403174115a23000300d641c481e450030481c1406820304480c00340000b52121700035441da01d0b00041c0300c021281c40c0c01c0a80d20f94001602070044807645d82c1d11881c00b0121080610340f039a804d1201001c5c0d541c1100d5000604141032030001020b582050210100b080a814140b001081d5201c0031920500e50448240411040c143d80b6500c0400061800c801420310317100c7c2502c8500c4548000754400c210600608075240b242c2c00055892400f000c481d01c0c01603005110a2042a03651021f00d04860002412070f41c5141e90f400801c801da9102d0b00311404074584503123204007041c4c0c02c4164041c0d43c000900340204142d0a010210b40c01d15080d40070a8800c40d1603008000002d20141e000c100544081000e64403a5070b1241080707480300923 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 830616789 1250 830615539 830615543
    0x1206021608070212120703030b0f0307080a0c1a19030b12010c08011d0106080c04050409030f080a141906091a13020a08070e1206010906081b0616210309 67
    0x4c2290001d000c202007004651142560400e0b8185601a01d089000b0022402420341040000c13840c2e4905e51b0702041000c0c02482100c0040000340b07140c0c98400c0312084c1c0ca07032040d1103500e081c111040391140428283c0d500c1c0d1744000d0300d0542e5100e04041c120058030200220640028140350750207c4414190800300d90303900d05840d034180c1641d075249541140100380c1c140e106600324400c01400018422002d258000c000001000d0030f1588820000e4201ca04101c4200d000c11182444c0705030054100104035409282d0842c10010200d4210440211200041c4842170080c80100100c140100550103080600240f1404200441c07210464084407101c000c0c0f0f95201c1c2d6000c0840300c014104600072210940020381d0f500040c4d44030a0b50680d40c4001030000d040e480405000c0030400d6030010401c8a00805181901160807071611050034200840d401c01040b6500f821042c28a80f9200c04080310303980181003020468514a9050111700c05641c84100e0f10620020f04c260944107505030043c20050b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 830618039 1250 830616789 830616799
    0x2220e0f07061409090615031e06100e1306030c03081809040317042102012c06010e04051c081005012d142b021312060216080702 57
    0x1640781c41d002d4621040302c000d00714040c841081341850741d04004031450740000010b040c1d0501c800181c904022070307410480303040100c1003904036107580032100400c42d1904200b080c0c4071a144562030752001030000031070304034032400340c412101000103a4126900100040d0b0300906485034081d2a071030451050b6100070411188402501c003107403d83e01d40006190b00803036040e182d2240000a0300020100c01c40c00a00035100b14602c108859000342d403001c54480403040342c0d0f00000780c05c0c1d4140000e014030700742401071480564240815120309800040e4040c10749184285170b02c002e40e92843c02c14a001504041c50b004120518182d0b4602130b00302041600403110a035107a6041ca0310b50004403001c002c072802403514058000159150055007440c103541c0982d0328502504181c0c18284100300030740c050079190f0488a0030004640007a281d0008002c901150340da810752519419225001e1038400500a0302d40650380030340b1b004100403440c0d040f1000b890203440e03c0c3c210f500c50350030b106030f0f50703044060168040e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 830619289 1250 830618039 830618053
    0x30705010902150316080c0706020313120906120e01021b151e0103140c100507020307080c011e18060e030d02010507020d030b030a02030f0303160c0c0302220e0f 71
    0xd01c43c428140c038426003c101c088198002c03030a000f12a080784c06412000144030401c00300d030105540e8001503220300700100403400101128070349145039041e030444036001c100310f884003800003691100d8000e40f001d4642d00007066180501101d40d0080c0b150001054181040c100d801606410100b20404510042180019140d45000c1000241001084a0451b003003248005000140c1601c030075241c00121001107a80521424000c140c0b003440c2c481d20940072902c08a1002c1c00c47c501000079802178107600000d003101a081c140080e204503a04840c0701d00d403100c204030502640d48941d03003403a414071284025000c0b09a840d03001030840c1c400110518001d0159990403c9054014081c05000d440c55038024071403c15040300803801013030076055141d4140107540700c800150b50f00f00207541c07940b6004406155603007460003100340c0104200d00240c0620405030203040100300407540701e8080325010340c0c2e800c0c811001203015040c010000017040c0c85142c41c2c00c80c880352a05000030303a01414202c1404236452 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 830620539 1250 830619289 830619319
    0x1506090c0f0207150c0807051203060f0a031208040201020a05010609050402041b091802130b28230c03342d0203030c0c010305150d061a03030705010902 67
    0x50719030a000d0a10640c02c401c4504c00b43e103100b03002041c2d40a0242c00d1140c1044031076580c881c10001d40340f640c0e151941c808020320035140740c14415022070394412200d90503031601d0741d40c8607040c40302070081d694107000b1003000050030b690081c400c9201310b50b03105000304070464440c610403005000503141640034914221403858502d03020b0340d42d2610601903407510304406281200fa003030b0040c20200062001d5400b07104e13500300740c0c0c80d29006102804805500e580c540c0e248076040f000c6903006d800f0131058900e02c0404180d40980104074082c100d50b540c0c4d60620460520340340c003100c82c411040299440d220000c0c3c0f0348030110007248035008042070200e0300c2109105d074418070980b1041e40320300030f0315201c0d9180c20000d440c0842c0248a940f0500c640c0c214000300c1c02900000e0654120350312a0300241c010910407440c66030300d4401c080c0d1114a0300900190107131000007041c82c000ca558801000544e4440c40040418a01d003902c45003481c00500700c03651005245070650103801c030400228000d0081c003040da98 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 830621789 1250 830620539 830620543
    0xa06060617011d0406020d09050705120c060304080a1e050a02060a05070e13150b070507240318140f070801061a0703141605150f01050d1506090c0f02 66
    0x7040340c40e0351009042d58155040f400e0401c110180084401941c07c0103805c65010345030240400030360056018000e0f4030314080600541c44500340da207138182c3e04481c9021585540310820360f604583c000385c107561034200764031058030400b424540c0d125404107012010314106074000010328900c80b207642a5500d644492024100782c3d2000d407508800301d4030800c40c1c04811b060174034542c25070124040b000300d148143c540301540307522240e802080203840006090740502408100382c000810f041d6040f001d5601c81042040076141e400c0c040f110030161110400e242480069018640c0c040d0441403c1110480000d0120740d0382780d2080303000e0b04c1ca026031100001d4600d03042c480c000032141c9001e0b411000440d140e003080b8542d40080811400d00045070049625894590090449103040c0e0044010a4445050042c43c00d43d40c480030321403040d0100300300300c902401560464119401910038117030f240c140c0d00c0e001052142071500d1030059450240300066003006500a50301e400c00b280c030707007014404616000b2a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 830623039 1250 830621789 830621791
    0x2060d0b0f100219050127032a0b0a14010b030916180c050c010f060501140a140a03020d05100608060a06080f0a0209060a020a0203010f021c020313050a06060617 71
    0x140544c102ca03000d002d20409035200a5a0980b190b000020380448441c294103564041c40d14407d007007110502c1d50400c0541040e03a081c0340c6507105005010941c80200403410b600c0c01d0540042c240003640002c1602001550803144a220034100c01c00342c150384549103085c20b40c001b110149281d1050308a00d220705071a201c9110199000194a680032501100070315000c0c0000c1500e54042120030808071098440c20f10801c0c0f2902c101d8500412000e01d0180010500c1800e25083c1ca2800000c0100c8000c194000784564048207001111507110f000d4840194024003800c14501203017800c0030200320180c8039a407000e6041c0c4040d40c5030801107468410600160f09490300401002c182404041101c848011240c140d0018140c00054a13002068010070f0040c1c12810100000d41e01c0845c00306c00718070f801c0c043d041400a00160850400f00000e01c43c06003c0f0003001100841507000010440354402c044504080c240c104046694070129494440b000701694818500003a045031102c2911240e951101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 830624289 1250 830623039 830623069
    0x60f0108030307210e151e06101107030b04051b0906040c0302090a0b090901060804030206040b0405070f0b0a120507020307030c020d1b14030307120833090604060803030f1302060d0b0f 81
    0xb640c403d640d1101030140349034540e49c00c901402100595001c41080800034140a1032040c40c6032f00c0309007464a012468410052554140c41480016043c020b07141c48081070780c0641c0484003c160880f00fa00140c000b4881c2e403031441d81000d010100480d202850000a2170f80f10b90913118068540ea980c5801c88403000181e0700100141c0002c404500030800d04840d00ea04240140203840190303940e50101ca010207101c0e07100317071a02c560220700c40210315040102001090b003406001d00243c50100802500c0c1e100d102401400c1c000c00030310755401d40d1184400351501c2c56010114004114401102100f0310074035102d0550514901e000480e03040c24080103039030358181d1104034480401d840000985503030b10010f00042d0260f6000c211803507802092440d6074035a4400420022160680809000c00c1c0c003001440540102e0421404000203000082113a52021603051000c3e070380e445444900c4858500d15078041d5000e14049030b030a0801542c0d500411f486802100da03182e07010001c00c14040980d04416030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 830625539 1250 830624289 830624341
    0x612030c0318030d1b0516091d1b040207150908041e0302011403062e1b0506041101091206141e0703110d0617060f0108030307210e15 59
    0x11808120310305010031000c0342c0c8208152003181040b0700b580d03130400c074956000c0c9206640328240040074074084050740500c89002c1c002b9045001000750000e80d42410170910a0240d5030000740c000c2070291900c1c00035506200500c040c0002c00d000c0c24500459003042c0100a45858038407032160320440c40d02d0020707084a90603158580801451411090980c100520158101100891100c0c0c0300400c00104007030400040c0b44010350602c41d4800400030429240940c105140b01c402d080b01040d00000c1040e031055004155494042c0340c0350049450f0b00607907000d03090000303d4501d0b84040084031780141c120304c0c941080781d81855441e04443d23640a080f40100c4214146800007003190b480c800c0e04859024203118070050700c0c140391140c454085034165440403e446204501c41c4001401c1805055001032540d100c0c3c050b81d50400e031382c2a407a0b00c400b501310010303c07042407440300040e0b000c16451900840b060400708050305080c0c6c1c10b16201c8070200a182c14186400380082c1d004d0611346145810103400c02c1c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 830626789 1250 830625539 830625557
    0x201080121020d08161505010b0a170615040602060a0b06210403020705210c03060c040924080c040b0a060e06160605040323031b030612030c0318030d 66
    0xd0100d0920382c00d90513118040c0401482440c00320150300f804149100d0007000300108101c2014004951040e0407120b8215810069051074960001c5064a121b80c1004000e030140ca81c0300000c1c86217847d40d030027084801c83c0400c000a0340d580120300c41c1d05c2201001c00038088507030044104113191180350740c0aa0342d054418180c1c40c0450310005501d502621030300448a00c0d5031900c2c000398101004142c0c8070021031340840c04801590f01401580110321054004040e2b6080c000121081c0e030085010f0750781110740d5449076011104006440a47e50030140d001c01240d103449007072464803100341c03691301409241003019950880c280801c50508540c003135603034801215520001c22441c0d5002c0c941c4144020400350400021030828883c2c41c1c0550300c2510380c915165000ca00460480c82d000e03d050320051000e00800c4141d00071201c0405528620300480e541c2c0750740d507078001303104150000400055807201040001c00b00800200800d2880354241b6405164640385013003540d158038030f1102c8000900d03084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 830628039 1250 830626789 830626793
    0x9080324100507031404080a1505060d0f060f05070f030e0705090a0e1e061f050612090a150c0908030705030409110c010f2315100215130201080121 65
    0x202c0900186403203450180007140541450329030715009078118105641219000c48208a040c45801d8003c0409071014800c170702e008000520000d55071140545440c2c2a1080e40b030400145a00c0070b051001c1900007000349050003440140000c0c00c80d980d5401080c507050111400c40c0000079442c040301e030010715a4101e544e4694003603001e006006000940b91080030066406191244000605050042c005002c4c40c50003100400341148800d50094480002ea03205202c6600c8136011607800828420b0038403410b4495501d83c900d0190085005080419110303580f407a41c0c901a000f0382c406040e41c2da03c01100035102c958240e00c901c20348000508560041204000c4500c568109603c020422100075092003500003201e800e644d03503a0030758170241c2d95a1240603141d040105401c4074541211002000d2450034003080b01070440d0350403402d840303500c000007010340481c03081140d02c403000c207144a6a03440b4240101400c03200030420310101d000c40d00f040d0000c614142504003c0070805001403102031091095 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 830629289 1250 830628039 830628047
    0x90b0402010e01260a0507231602040f200a0912021801060206010f090b031b190801090b150d03110312190c030605030d03020d02040305010908032410 66
    0xc951500c0c10f2020401e507880c01391155904920071086107510103040ca184c007629003000c07a44001c02c1402800955003000000350301d8500440070450003101220703521000c1c00000000704103c1c90000b58864109400000d80207200e4000c61046c0a9580078918148109500000300d801a503481c0d50001d44141000c00009514038040d6200a0010b04139644110800c2111b03d43c0d4002608840b02507030080340100040da0341c0c0f00905004110100e0108038507158400042e03100e1b040341303010a514845145170789907103940303054815240d00804486513401e10341d40c011b03c901900030f8542c2a03c0021307507000003644c2000e641a01c1d01c4071520080c0702030507075852350b03406035000e46501e108401d40d444140030b803070716105003100980e0140300c20100a0507500341c1951044161801c100b0b85404141c105801000f0903200015070303a1003841241000b503200c14006032000700901540e480540360f5801c100c8000f041c000c184c001180291092108014410b048101c80200d20312810491600118101902000e041c41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 830630539 1250 830629289 830629307
    0x50306130f06031b03050d02060f010e070e031906050f01081e1204030c0821030c0d091707020117010308090f040f11090102010e07050d020f060f0a051c090b040201 72
    0x6000c0e000500c1da4a0341c44d100307040c08000300100e0206400110500512204004010008a0300d10040596103804001041308071010f102e00c800d522200404582c1950040320361241072074015003203480500f420760300e441102c84041000e440142c5005c5c0400e8042d2840580c030340c180c0e0b203003000404000c00007000c088d0703143d142c5a41641542c09044044503440341c0c040010001107025098004c4014106840c00741441d41a0800d54088951442c078160b40074200001c0e06d42c00000804000d464041803020701000d8040000014074134450400f4003803200510001402585001f0b07691a1200a482c28404114490038000a001c0007002c0c003007030302140307050307844902d004a02504c0400c503403901c411240c083d10003074600092950380100b9603003d5943d0910031000d4111810300149083e92505020500342c1c0d508040c064000ca400c4103030664907449039170440f100000442441641c0b000484001070154101882c3d40042c10070406a4010306c28080c000c0303035201d5070440081c00c625141c40d801075a207403178 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 830631789 1250 830630539 830630561
    0x50a060c050a0609050309011209050604030e0d0b040515060d03020a0204020a0c02060310030201020d0c020a0b0c01060b0c03031e011d2a07120c030f12060b030c070506010605030613 80
    0xc60700142d00c1c00030342680134190002e440b80004549900386140094510600001c0c22030099241030200385c0421400078505400ca078050620703507010f40e0800041903040200210180a0310895000d00c01004000904901d840c82c0415090300b1275141e00781044800e05041102600592015442902518255000703102c0e2041030300b0034210340c072180d6021421680045406000d1048070010800075541c05101900c507110180c41c015415035984e50016013410b0050003240c1c410480491600400c032425400301c0090a4441d145d0364581042d02d02c1540d4075481181c280300c082401036a03010341030b010703845214140c41000004440850045289038a060001440d800740a00c000407034031000002002030805440c25110749603600c0305941440000011175542e90b030200f124800800c40400e500c041c0740480c038162840e112001020111444001e052981c10107008003400000b80003c545000004001c503502c00ca09880300d60381d03107580c1640c090104a40003904102c841c400360040c07d5841d88400b14180d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 830633039 1250 830631789 830631793
    0x10605090d0c06030f060f0b1b0f150702120f0409020711100c060e0a260706060b07061505130c020a050a03050310091109060304050a050d1d0a050a060c05 68
    0x2801c6500c031000708140c6a480640426521120804086914040c0c800903001c00b070124090103140000000080c8550028481c5113800800c10041091060291590340e0030450101e803c000d1004007003440004061b04c00802511a8020b000030500402c000c0e25240d400701c41ca101e05040c0303004c0000011390710030a021241c8400c034008018166031608900d08000c50b42d6526140140103d18144044500c102c603600a5907000458030300014020407030403c4000300c0c00100e542006181c040d001018092001c00421182c1007041c00b160122500d0060b04070b41f400303103205004180c015150982406054000c40d90080140015480c0c0c0c01400d400404007000c16104851180007691102404e1410b00034040b000281c0c0001406044021450321001500d1110303020043c01860a0142c1e0307480c410030704803502174000440064203108040c0f2100a1241d0094190344a91003007100044c031a0b4fc1041c104d40d0109090904c06040e42401b42c8582c096800150010400074102041918400b2206008407414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 830634289 1250 830633039 830633059
    0xc060e010509030f01020a090503030c0a0303153303020309072903090a1b150c0609050318040501061407060218030a060f0605220b0301020c120d0608031201060509 72
    0x43d2420820003180c500600c00040e15030800184c000e094240540c4420721903030051144015281d0081002803e6548c117040000e41c3c00310649401003190f02c5640050005040328003441201541b408281c481c0700728440c51100840e40795030090342240416920754403250700c0100d09010301180c404040840807020030160110b40414681c00000342d100321071a040580200031030f1410011646410000036000414000c0c070ba074140403001225503156040c0d6420000e252850505010085e03004c41a41c907001015030740c4d1800f010200b050385007a000b000c01c1c003a504e4000006101c0d8480c440420f0b0121704c011640f490700c00c0d2904c884001c1d4200004812a0302d140e4819030100750340801c07100078924440c8902180c05100340c590101181c1541d4000e60003111210b00c0d10380d01604001b107402054207138902c00965a052070022078024080d46c1c81340f550500c9030b00f4080c0e82e01c0d4240405449400c24001c400c2c0400c980700c82c903140e10b074050030f060104590000f0380140700c8640501c0103006030040c050400724039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 830635539 1250 830634289 830634307
    0xf03051b01090c060c0b130305040510031d0c032a120a0501151a0a09030c09020405040e0a12121404080d0e070302011e020a08030a060501080703090c060e0105 70
    0x400c15210060003041e07550704848400c100f28060340c64001d04090a100b115540706844000c0602402030052640031f000c400c9141c200341c0110140c4001d0800941b070128120f440403c0503004103400300c031800d08a034010b0201d25507400006200010140080c01821016204000c6a100c10f6080c18141449071202105954507880307806445c851255481e00815a442e02820014216581c0c249055114010781000f405402c40c04100e41c0ca507111104c404d10b41d42c440910044030140c90a400c020300000c3c82e141e0005080310300c0e0b00500103881080741c08000310780040c417102d655110880c1000b0500450034038101c01803402022080c401608d50703170001c00c8000e2412000031420200f15811945c0d0700700803c180c0e10f02c09041c4180d84c0900322441c02440c0d290300750340010344038100d4208511448250404510300681c420700490640b194803000c4a41c59041c0728030710b070000d480a801102e0010342540e001840e0385110380180c485880d00102144446ca061120443d05039090941181c140700e010446512 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 830636789 1250 830635539 830635567
    0x209120a0302012c0a03080601031517070807030c0501030209060c070e07030609141b1303081803060c0403150912030501060e010c0206030f0a090f05070305070608040f0f0305 77
    0x4641c407a5000080c6041842e544680000c50000c03100c400003a5062075041801000503010401c41d0141002034541d038460004a000d802003005074030242081c3c41000800800d944020801d522208050315244e6860340c00450755021944005003801102030b101b040b00354000c0e0f008110038030000e40070601e0940c5164205c1c3c60410f095002e00c075859139030300c02c20031301540c14416080030b0540700278140540152100e1020b2440400790a924144082c0c1d0a50701138180c0200848001d031400d00001d2804940d01c1c20210b05981000c0c034240922594148040d40515021075014895841340200750300f801c0c01c50300c500c5919907070484402c2249607910304160100d0858074400c0c20780b0f80c0302c0d070740840c496041120050540c66281e0a06044c0f1001e001e60748010f07038606042d29405065540b9040340c3d0707614440384002070004030002401074000c0000313178020311001054403000d42c0e02510454861036601c840844004070100c4000d0700341680c0c201c10400007686040021900350103071070030138141f09075901211 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 830638039 1250 830636789 830636803
    0x81f02130509040f06060f080d0f110111030109050c0910142a0d020613020d1b030503040e0c0a1710051f11010902030d1119140c03011e020912 63
    0xa1341d800400980c49040080b02d02480000d06030a42ca5007506920780f281c848d035100d80f14940d040034010791581d206840380c491801c4800b16a550002849a84280080503415a001707028810002e414107000541c840301c00011212150b0000e0f00d00402d00d104044129035180d5800e070f0a03010040304000c803102580c030340701c8000c143c0c000003841c8012508407942c040780744c55005502c840035900900200281004240301261400b0780545203000349964a24101c0030030a54002d0918800c0d001000120034442e000015000307980002500c00ca80d40c4482c1640c0b43c290003500034000025004004a0844941030360704160054001111450066240e4002410b80f80400960039000c81619042c26111507000c5007400420f44c903c0700810601d846078000c00e40791920f002a41007406140c00300c5e030013a17000030446030000307000005404611002c2d51070540f0250251800e145602c0c854072021081c145418400e40084403180702520300346020101244000e508580c59184c0e007c103c0340c5001d00351321307002d10103a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 830639289 1250 830638039 830638043
    0x9020d3305150a0b03010501140705030f07020a09140424091b09060b0909090a080a1d09091c0302040902180418080a050f0928081f0213050904 63
    0x2144510340020b1414000744200d00140c460083c4900802c0fa1800c0c0c8801c580c1561020b19103086a9003074031089803094401d0607030041880c17000240005030004501c0203012150b1080f01c888209540d0750340e4134410340d200b81c0880e4601c048800007040000311016690300c20a407104000341f10101904400204584a0a50581c2c0060301e103505c40e202d4200e180072650203894418800c0102c117040c80b000350094000d034201e1a00410703218020648030742b01007081050710b980c0400802c0e902d1f00c0129005100d41c0524161a07490040b103a01c0f0002481c0050040340f08034100c2c1c004104000c01c0543c588420341c4000000b07020301d0340c204004a07075070700c6d180020b01d41d9003a200c50100c0210001d030244402c80e0850318182024100031640b41c0001400700c0115450b800c9285846078840002030341044030340c4129800e03194012012180301c580c62000030f007a122141007004024619076600c8c003605031665482d50540b080080c90754560f8402c9000d980c0907000310306125401303007252034981011400c0c054042d070741 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 830640539 1250 830639289 830639291
    0x9050a030e040c02120906070602040503030f04031e320a1412070c0618170607120e030a0804050c0409031706040b090604090213051608060409020d33 66
    0x7030304150742024060402401800d01c028605480f440911400c1070140711841d41c8240000a1442c00f40704c0c07150140c0f4083c0c00c00506517a5600d0119032030102603409840704850007200342c3e404d21110341181840f0403103c3e07000483e14841c1c418090100c0346048400007010060344240e40b07800d101a40800060149a11502e02c0d0004002119041450096001c0f01440400b0f42000403000140341c02540b10115181c5081020b4943c1d0880c0301c08601c400c190b0401102c0500300f00d40f10220140003e15107009a86c191140101100a00403003030541c3c410030744204441d0310030440b0070310651040782840e500c03a0149090b00d252225090008080c0c0390800b60640000385180c000c1095421a00d1100750008800c45040104054201c01300d121041d0042000d88030395500d004423020b5403106440c0190701034007500d0400080c68044a100c0113179260481840028031000005121800c252161444403500200584144100c079038400c041660003050009810070029041c840d142e49181c0820010184298 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 830641789 1250 830640539 830640557
    0x80405070e181b0120010204080a080706050709140d0303090210081807050315090a050a140706081b03090307120309021f120b0402251103030705030301150309050a03 73
    0x1005141c04490440020404114140f82280e0303038001840c040102d081060b0f441a001c0d21503a114020b00841e407050b68503020f500d24620402002030020003815200d1141085903403610082150820304a0181c0c0da0180c0340c00759201c23003528106068801d00c503c28940880c00e001a0f5010a00d140c01c00b900705004078071800d0902100d1101064500c1e1592285401403500d10b141000095076003050071004041100007502040c0c008500b444840f9540fa000760880d03104a1992403d01e06421004d4034a59043c01a070340301185040c401c851407402255070290010030320460b40c61034202b030390026110481e0382c40100101c40000e99044040c4600403856140012002c826006002ca10125011041111880039507107540c8140c020140b80c07480c3c00c45481c0000d0801509000c60020302c120700e503012044c80030403002002901c400d00440c141e54413920079107604441581c2410342e603024a09004000790010700060240ca0a00c0c0030b00041800c1a24000c54041141d846180c10b085c0e0181c801d40005407001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 830643039 1250 830641789 830641831
    0x30203010507021b040b1c050f1006030309030b0705070209040f021005031311010e0604080105090d0302090618041806090605090c011d0a0f0e01090c0509010f080405070e 75
    0x7100300380d0300c4221400500404041600000c050b40403022241e4826943c6480d9141242c4a454008418044032140420040d8003810250758550019001c00068410442c130900e440d8081c0c01184d0480c2e501d030712003901e21400e41d0344031641c0c2d00008200d1410890203001900141c0c1c0c501e00c0041c080d900a207410b007100d58250044c00085d0301d050011505102d820411b000180c8a4500e00d98a05c1c2d1300144414003c4500c070f00101da100f00d03505003050b402440032801040b1b45406604c05409020780c4012600c41400200d0309400307a021303000e0f1040e8441c4083c0030b01c08418400008014100c40c000f000091624000c3d1041d20741d14002c440c050300c01d596100c5880042203482e1140d2900004448020070f022804480000c21480d09001e89454540d0032210a9605442d4800a0300181c50594400340c0300760303291015494014424481d014480e424000c600c08118002c004070b540380c15040e524540707001c141150550b240d110140086402d40700304000064124403520a842c040c8466602c00303c1145115 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 830644289 1250 830643039 830643041
    0xb0303031311010f050306040b03010e06070f020f2d160303080f151509030a0501020d230411040e0a05070308130519090c0203070f080406030e01140118022203020301 73
    0xd0b41c199814801e24034190f01c00d05030440f0580740d20400484010074a55800c00219000d81507211102606100d05000c0c4040e0903001a0283c1e505030700d81d422540c900c10800704441d51240e4011a03152404017084015012040311280c1000080c540310480390184000c040159410030f165005800042c1810b0600c589a2402449240c005500303031401010b17101001e000a00307003085450341100c1040c1c00550380c010f40d14180080d0392a650018000c40d01e40001c03d24000103031250180c0b4a034401e011a80c00c034010300303000f0740c9a401950010310102d00d1103001c0301848002e282c8141105028441e40110000254003000f4240195115520340c41c0c40f6440250100444c0d103003604041c1c0304d03c0422030781500c9140c061103550704a80c45070300301040c1c1c06801c40301607080d4850300c500078011ba005129140184101d030310051044070f020369400c01100f500881030600320b4400040c1c1c6c40a01210340d00402550700d400380059101000000014504102c001ca0080001c0350301d04500381d00d0000b00003c00940c642 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 830645539 1250 830644289 830644313
    0x10b0702040213211202010c12020a02010b040603080c0c010203250314030a0b090606090102060417070b01080703050c0906010206130c090c080610112a0a03030309020405010812040b0d0b03030313 86
    0xc0b44c0004d00c66411002c2001d4029112a031040104072b0303000c50011078a9200350041900d40501034000c014040d00c90070b1411481d88075214602c80c9202e804130044c8c0a5200101300c908605140020340b100d41c0d030005402c0d080c1e640000007641040081681081015003000046000310074000c0c00041c1d0844550a0000d1980000c00076440764101b8880045242d03000300321607030b0059100e03003010481021165640c12900820201900c030007070f82400469090340010f21281a00e0246080b80c0c1c128803032104101000c0801c4401a00603045400822030031091410039410842c03088600c48401d54952000104079112540350f540040c0f100c00c244411400e2020303007002e49013064036000070b15880030a15241d40c1c8420313581c002118600080c0c4180c000d03052058000d40c10000030101070100e566030800501034541214141c0c031452400c0000154614005280d20907012104e03039842c1001e00c0d00b00040c0198200b030200400880d10303280262203035a41880254882c042c0c10005807a0007105080803284104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 830646789 1250 830645539 830645573
    0x51b01020c1e0703080c030f040611010b0a0b0d020d09060f0b010e030109120c03020709020a1d0924061210060f030203011a0703120f021908010b070204021321 70
    0xd080d0b6115844900040340420a880c2c010202aa8600f00722503020b00d107109080e04902604c81c003003404210305500a85c1c030001c6600510003440300d182001c040094041c1c0e2849058084201013020640760000e0b90080e20800d0b501540020720b000b140d843e03100030348046034100c0e4003030390f900d0b2030003081d0750307041404450312080c00c6c0c008100c0c0065070b65400c1d410a60300d00755003040c4042444d061003054403c0181d0005405103003c02d5454203908100500f4031034a00c0d801070011a020a00300101c0d0800620f9640300e42c0c040c07007541c03195a81110620502e001900030254120004004c81c0062001c2044c24901510164942c4141d80b440c0c010000c20341034510120300c00300350040004003d408580c0290000c010b4151001682d1075401c0d01d401c1e24904203403100c00400d1414003101511580c05503018080743e41024030119480c9050010880b4841024040c0740005031090001c44050f04096003d8004603d04001c0840c0154a915081d0919402400420880c08002000804200c1e40911051031300c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 830648039 1250 830646789 830646823
    0x90c0d21020114011403120c0c010e1c030315050402072a0f0e07050c2506020c1302070812040501020c010b0a0b030708040302070906080106030606062102030601051b01020c 76
    0x6801651401603c41071040e4501c038281c41c031085801c0d960a009220003400c950303805540d5420002e0034030f030b180c284460701d907404504e41250701d40090902150b00340b1216250500300c941c0c18800e640641c010036840132074640020003443e000c12145c849100030030407103019201300d807014144420001e403918080b00f518034004102003001c0102c14900501c5c1c2058900404041d036542d5500e101c101c4140c014510000c0710b41c8034240c000142141c0c00c0d840c142048944144c8030000a446101c20f0b43e640004404843e00001003908500d418802a805400c20742c2c4107241c8035140c03500c00e998000b5081425201075440707950009071107403144001d109008001100751400382401d8074011411421380802401d8605000848000604141c420700c28400541904441001001d44807400940202443d0204a4009280c5100440c1480c0100d0380c101d071440702a00061005440b150404d80650000361a49061000a120125502c440c180c00303000301400c0e038400140c0f15080e01d115107181a0321411864a03003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 830649289 1250 830648039 830648051
    0x27040617010605040b09150f040c03050702070608010b270429030706080402220e0d1101051308070c03021503190501050112090201090503030c070f0b13050405090c0d210201 76
    0x10340c07502150b599000d4402c070194a00c1f1050600814a501d04080065900900d480215180c02c0d0b0181c0c0000e014480650841d0450f0b61111b009a03051003082c000e09500010a2040703041460220b401c101d9515203c07040307015241c80c001e0116060307640103403400001c200941c00300c14003176103100700c40c0d07d00e1641100204411464942d01900443c0003070030180c001c039034144000003a103500c1d034078055030003218401c200a04050000b8583d22414600000000154203504c00783c0c11090500550b07010f00c008805070106100c8073f60704c01030154051603040b078003445c0b4503800102590300c08240354040c1d0812100255a03140080360b045a0010030218004aa444d050051026907404450044051203a000008500045000603100500940c1c00290700d8480000e007800f0f41d400114000044410081c0440d145680700d03001e0072380c14010400c400c2d400003c055020001494181c00c80d94020100009803a01c2e0381c2004085040d1444c000000e407060300c2c131610030038002d500c007450320014807441d84020056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 830650539 1250 830649289 830649311
    0x1e0a090203180a08090418050d030b10050405210a12020d03110723010e0307060b0f011719060806070c0b070c0b01090929010f1202062704061701060504 67
    0x200b4020358243c5401190788041030309210741880c075000847c5401c14116444204800b6000303002d8811018094028808080541c00c241e02071410755042d0b8800604400d1204501c42440c02a200031f160001410301c82d81b50840003046040404616400441c2c0c0501214000c18501800b40c030b8092140c3c0c2c500003400c00c80311001c600c500e0006884880c0400c9040200340740b85030f9290240600304203907121800009068400c0000a601904a80e001074822030307800b80c1e000c80155495542201c4411b41403045d000020a000501426045031207500c0f0400034816440380c044605d030840454034880072400c41b606903c223014840740cac0f8650040013881c1150070200c5564070701c50516010301c200c144450b1652045010081c58624080b114401a180e500059083e4a800c480211b0284900060014580000b0501ca0b0840d5095001300d50068022803070000f00301b4512800d000c0000804466000c540c0e1760107885e545600485c0001c1040340c2040c070003180c2c0042d106007190507603800b0b02d11032403900300a030007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 830651789 1250 830650539 830650553
    0x16050109110a1d15130f050a060e0a09030201021207020d09090b0105160503091914040603110910170d1812030c0501021204080406121a1e0a090203180a 67
    0x4050003400c01c0c259020788456501c030000320038225000e64050070305c0c0110181d10200d075000326034014942170705018035182d0210203804c0b2001800f48821420707890000404510154100108080c0709100040c42d00010741c2416020b403800b5907200005802500c004080c16a0102d5041e02800b00751038200540740b0b603c40013030003910540640c54030200c0090840300a1003824010f948250001900c2c0150b4407103100c0c0d80da140106140214001c880c222013100c04a030030244544416a98407040c1d42c3c07a0303110140304100c4c224500130300003010b60300d07a030002041004500b038800203203489540044c4030044040e44007400e0b44d05440c4140701b02e680b20340320810011a0603490180c0b2030345c00d4280343e048044182042d90191059030706461100c0e4820b81403004100034440100101e65803070341c5000d0007296591800c401d95a01d002e40c1e5880d146208040c8840d4a040e02120400400754200c50004401c000701103568880d45500c81c2e0f8015030302008005400c130314080010340024042c400340c14200c00d25641c6c40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 830653039 1250 830651789 830651819
    0xc09041d07151e18090603050601091d070602010506010e0301110d05040804090e0a021e01080f0c07050f06010329160c022101200301030605070516050109110a 70
    0x4008105405a0300560358080c101183c07082206803a0701240c8800f101c0090300b1820281e18265040007100303c002400705881c032a040c00d603503100010f01500d074a04000c440c054809100079001f0000e080388424203070801001403c004240c80d80000c501441c01d079002414800c00c0c44400c0e40643d061030701504103250141c0484070b4000002e000040c5686481c10141054003440d0080b12025203401420080301c1c800240c80610a0302c202c90b07081c15007800703208400d0607900b81c6802c81c0c0450301800c00b044450109103211a482044128460700b440c84a8442d58a01011440e00d5203007030700804014010310100132205007401c0140c00e1110402100c000341100304940050440c1501c1c00d8044140a00d02d2044880b8a01960024040c2d00c0540c046801c0c07501410408003031001e550b1030b0030080c41c041100c04c120000603080603038100f0f086030302c1c43d00c07204060400205020200001000410034580c3d80700400800c03640180b000141007641032400b804142c5020640a03c02c4006100c2003213500000c4a0007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 830654289 1250 830653039 830653049
    0xe120403080304030e150430021216030803061f0c082a010f0b0a150509040f020c06040c060819090203120c0f0c0406030b040807080705060c09041d07 66
    0x142d40da07640c41c1422141200464070240e0300031080d178151164001c051000d8415101a00c1082d40724503001504a21000e02885c211030700c4202038503028007d480c002e8201b04c1c000311070760305803001c400a02e80c2d4900700c80a160030440328480040140645401c001e80369038546e84a508103400c4100740b24001a01020035000001d00841d40028210841e0031183d0340419200031207008002104049241135002c1c08030000202c2030300e8908100f105503403814100c0d82003201e1680c402130516507041401100c1c203502030509240c00c00d84614003a2800040c510080403103044a40c00b0700020308142c50b00302c00700f44c01307940120f0070015510107015a00800040c41a0030300011000064108681d03c0801d08248400b1200070003004085150581000041107264110f411a410354101611030000c00c0200c841d02d02000d04005c6d644400180081c0401e0020700c0c0240c0606096428256281d544519200742141d12806003072010801b090141407d0051011001d440d0800203139008a00451383e03a11103da10076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 830655539 1250 830654289 830654303
    0x1180320070302091503012c012a051201090903020d03050f0c16050f1606141b07120c060801091a210a05060105100224060f030109030e040e120403 65
    0x4241100e019405d845117040c80640280241c5400800100340d078080220407101c5d803260814040d0407500180316a0804941e840520b46620240e042d0745800c1000402d050b100380f000c2004940040554001c2660003401400340202d01c0e20707a9031600070704042c0414003113001d050400b82030000d2036400401e01c0342d000b01c00400c1d10703444494900301500c81100314031001d8044d00a079411502840c2001c20f40710044400b0890460100f07a6840086861080700b0020f00403101041c040c41d0703203094010a034074512030940c00c11210600d40700c51107080050a024801c8a40d400103030000c01016030402c44075801402100800c104010741208806894240401640c1c401c8401031080b1300790345485044140300043c242c0480d045502180b90050781c40d1000c0c0116442100c0c4003620810051001645110504c0701e60350904442261030054050780c18054021980000e51003094021510248140030030700d4000ea5034203104401107000d2004482d82d5a0000070142c0005c194850502110310481d0304503944100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 830656789 1250 830655539 830655541
    0x1302010507080409050403120524091803031608010905130b040c17060103020f10090905090a0b07081503030906090618060708030f330d050118032007030209 69
    0xb0740914644141d80080c03112501c1d040c10301040c5940801b002c6d003002c03c0d5031400c010b26181c0d0411000e61201e0441004980b400c0c407500b262145c1000c1c410a81c00c40880d091080c24000b00014990841c1c004844006150780480c5069204540c0803d0403801448498030402460415127074141130140c04200240005040d02c02040404c40c1e1000000c00412440048200c4195040c201c292204401e1105901c580300521041c4228504001180c1402101d80c54040300341e494044548040c0c08000c000340a54003d08081001195414191070b105407516683c0403000c1c60004050a000c4c03c4d4204103a0090b8028882c0b002c0c940c40700c80032683c0c3c0c0c0c501120240c0e00c2e40e08101c0c03010002c0844905294000c1c03c01b181640401822001840c0940701c62a00000d00c5d0365420600751401e01c42c401e00c0340b40c91185607040805182c0c04441c10074a90b80242000981900c1e0741c035401c0c20b440c10614820f0032004071100c12014994015501c43d040200300885d10003500031092903d0b03492800c0e00019110b41c240b18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 830658039 1250 830656789 830656793
    0x180402010c051005070201020904060506090a12060902060703030203040308100609140d05070305060105011d0d113c030718020912060106090501090918170c070803031e1302010507 79
    0x4043c408640481c24046842e000d54028043d410601856000308e092441c003241d0352034a80c040d24000d18002e048c0000c03140ca4070084840b540060305013910b500b5a10a407500250311103500034154a4042d48015983c0c0c03c00d860028034140009029018451000400b80b01d80f560051540040b2100d00079402c00403061200011405039038104000d00c3d504c100e00b0700200700900820f20382e040703400c241c88184d500c2d1860510300020030b035210300b040d81c00b52840140a0004030003201c140a0110f001d849820a22800b500c01c200c010305200284c3d040070205090906900322030300500d200044180c0c003070b05030546002c0c90010101d4501807a45c000c3c0e41c0103e084100b0ba1034002c40c82c10034014401c01c60740c132961740b0a8054081e400d50701031180000c10a84011910b4120b600940e4000f008520510507640c1d0142c5914000c004000300355000c44500b002441c1048000f00310b41c401828801014580c0d90602e6244000e841d90840c003552941d64441080103a042d00001c01d0203007460302824a1961034141d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 830659289 1250 830658039 830658043
    0x3061611060a050708070212071203020d05100906120b04060c020a0b0117010c0f0c030f091203200c0d121206060c02032b051e0a0203070b06180402010c05 68
    0x3a010505110305010080d40c0c000c2c64004a001e0403642e16000d030f143e00ca44a04903141c01402960b1404803000b084810001035811003188440b8070545001410800717060200002e0791405d03610122824044001440b4207040ca2080344002c0040380000c001d51030f0706655820360300710f006101820321030355160b941d0202402800200001a0700c292241c2603903031119401e0140052500003900190310701034403030b00d119002d81d501d56941405926111110030360f5550407107545201e1403c0c2c8042040907000010384d0f00b0800e03401034000384030b621116500045d40c03172071036070040610201c00e0360f40d40800c50201080e2146240840c8090300081211002d400005050364181104110345401c40e03e85280051003a13031000311401c080707200710142c85681c500c224880306c10041140083c2d4070418003010040c042c0b0f005000030082c0c41282d2403564a80e000f040b0390604583c103e02800c1c00035130400036020b000c205002040c164804002c88800c1c041420f1500800d010ba07030001d200070b041c0445903c2040078030000b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 830660539 1250 830659289 830659307
    0x80c0f040f020906030c040f12151a040e010b010210060302100f111009051504150f14010b041a0c2d1b1e1e06070b0c070b010501020606030616 63
    0x341405941e0300345106c0c002c1040e44103105004401072482c07004605240303181c2502c0c0300c26400644c5941c007000002003640c01410100e190b0141c1c11207000c1003840b01e480d03030700403c0b0700449401c00004207484000c0000e41082d18106061442d07614104051005a0f02d500d024a0b00107414070b020b06c06540881810740d4108440316031074803c0c0c46a081048504020b54101910390362040c2c0c1500c82c40248000c41c440090000c0e10000c1090007480d0040c1c101c24490790001040351224140480c1c05c441040080b2020b034030a030400c4404034000601031100006420300c2410302c0b00c6c0000380ea0718203000e0550403610303181c41841c807011804981c806c41407286036128503200314480e00f0040d540c140b074002080c10016144900c1c0c0b43c1c000c03441501086c001c4510b54000c01d5005502402d454020014540c0e58500d410f0102d1890764023503028489600450a00c496261050745194001c41e6a54018107100c0d003034030b205911440c1150b1240b000c001082e20b010503030750381080c080e02c025001511817000582d0b260107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 830661789 1250 830660539 830660557
    0xa031103070b160c06050a170702120408100b150706181a0117010903020615031f270203030a08040c0510020105150d0308041401181b080c0f040f02 65
    0x1041550301c043c00e4030080906075100e1850041e03100d42d1240d0590b0140506292500441d0309205c90304200784101d0581944002d8a10554400c02002e03c400580c5402c150032601d40c540c1f110401a010129502c02c07541c07070080441b42020b001080c006209014451303400014040d5485a0004404007602c8010000c0243d000c04119000b00d100c030140305881109109401100e912005400020300040c81744040454040d030260819070799445170740150550607044250144503241926400302c01030100c01c03081c03c4040740040f41c0300881101101c003113000b6251000c01c80e19207610220060750004103e0f43c461100b810040190703901d508224415150700c0e4080c0781c01444036040d1248956040d40002e01c01c0403041600c0c441101072a091008040c800311004020030160004035010500d80404e160021145078008031f5108a91071690140c40040318044655245d48040e54412066141c4c45202400828008100308440c080018a01c1800d42002d1070040c1d03500e031951851000c0b40d8040f00c072412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 830663039 1250 830661789 830661809
    0x504080705300109061a01030f0b1005070f060e150105030d0905010f090e0703020d0510030f080d02040510090501030e010b060d0f0213170613030509040b0d0b0109020408070905060a03110307 84
    0x48189404140c1b00c443c0010030700003840d190f2034950348170303591255500b511009400140044042c00c02070303170640e021640076a4442c2509000600265140c021002c5030b4403e50041c04984865050101c61600181c00c203612a07040000400c3d11103900000346021140c007440d20304852240203209a03200c8519402240c2903002407400c000d82190180c00515000480100400943c2c0d100510101210490702004107003200803062600071a03043c2000c0c26045c01c9480c001031900e5030360000141204989040080070480342c110400141d80c0510481c08a011038200900c01340a04400080d00e83c4070b98091024010b035911442c0740407826903810355a0700004903035512415078440d00142031085c40812400311510504002506d58055040b24403030a540c10b07203e1605043d581010480a4010108440e8000213411210404903481c050b841e030003017980b01c0c40103035590308241c5024109a035503001180740b1410f20f020700c005070711a1008070f01242d030822004030039455103070002410030b24a58440070402c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 830664289 1250 830663039 830663051
    0x10f120504060506130e060a050414061e0a0b0906011803080c030c1207080a120e010f090c05030a050c041d03030106050a090e0105090f0c0c0d050408070530010906 72
    0x405a40d00030b5010b404d0460303000070380e00e503181442810b44092144d1b05406070080070129150301c3c1d440e0445508680325402d0404403241e01c0f4212032400c0380445400300e000180300c12100b000014400716907000307103208505004a00d003010114420083c00343c445410401c0e00108007079220217401c1e501c80903650140480365518480c60100b0307a290000c4001c20f8690003420900710000e40e52400326112640c1c00b400ca5414480180010703100801d10540c4019040c0d110880242581000e210f560030801c000c0000040c6417a9505001a050308103401140c0668412040c25021542c002640c0d0409076045a02140b006041100b0300c06c1020b000e03400e440c49101c00b2002156a941243c080c0416050341d80d00d01c1d480c0f0390341e203c0d0720808038000c0c45400d42040090011074035440728141000e81c06040d08800c0e0b85010003088a8034a802c001803070003c00a0408a01809000307402d013308002414110b6040707143c00b10a803402240c840300001d40d000e4182903540c8509061001b03411110714960031800c00c01c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 830665539 1250 830664289 830664293
    0x308071103160203070503030403031d030c04060801021b030310051c020301051303020114010501090909020f100917010c0e1e03060a0c0e090919020f0d05160909050606010f120504 79
    0x44040d9200b003c034440c1c0200e10001c5035904000003070b6402c40c1d4044d85c0b030043c055084021003000c400880200c031303007600a104205e130b02a1107500452008003440d90005a031921070200203800b54820a42c0550150010030502000c00406c503d00300548a0454109020340e088218100342c1c280c4080c4000c4d0154201030070010802425007001d54032600a030000e00c030300d1058020503040c8130000d0140d40c0c04510071340d07010f0207100034a1780882ca980c0c0c805407015226040c6070000658902c3e601c503462000524048041c010319100d200c030643c0511404009200c50450084090260340b10040d215004040441000340320381d42d601d500707010090740501503508604124180c0000340c80c5c500d6907400403d4050304101c0e0a0306000c1a00b0788105c1c4c501d800340c0040241d030055404ca5148072001070f41d00c0001d00515010035071303410200ea00b015120300014105200c0b034030001e062401c1c042d8003051500f072a02103407201041c0302280715540407400b468404041206010251b035824100c48001310703010f00d001c0400c03003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 830666789 1250 830665539 830665567
    0xf021b040c090e040f03021e1c02010f0f02190311091c0c090515010206091c032408122502210a140706090b090103110a02010c090605030903070308071103 68
    0x2460714041e90944036218000d00c505005000c008610400550060302c0032489e8140401c04811308083e10f100218504088001510039034a981e051030075510f0f0b0000e061501140ca8480a40e040764040c10305100036801803000c10303e41e00600a145004495071031a80360b40341040518903e034161f0021200c25029124000031005000c04c03035502d00b0900207018402450740c000545548200c2642d00101460070340040c1218461084040140605407100e030b0b0303400c40841102030091480510351000c0410307858500b565181801349503d46900c26010803052004002008a07469102d185c40c20f07000f9080254808941d130700d039461030140072414809102c034200c00004104a45910301900f03510450088a0342e0b040c0c2c46082c0d030f01c0b401002c00c0081c4002c00130041580c1c00f4002c0050141000140f0301c04c2800c00c0a101d602c84505000140d54801d01080138507004001480a0001464058150302d003071540d450b520300c105100901372182400008000c9803085404c0301c031500641d000e59403100c1404004034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 830668039 1250 830666789 830666813
    0xa0f0807020f2e1206030b040203060a0605030a0602070219060521070507060e1501061709010204060e060d0902060f07020f09130f0c0312050a0f021b040c090e04 71
    0x74400c1c00d840c40b21189a20b08900c11100c82500c0c0f5541041c64008082d40d8005451140d5003d03060100942c0aa10081500c0c8202e6004500480540200d460a48101418140d004040c64011860058144042d403000034001400590000c001682c0f000300d8000100482d071840341714008506102030204510398050080d1803880c085200031210314012680304a0140012141000050014004100810110342010940f6010300082d80c0c0740b00011560011261001d800103004035800f02140c0f44070489807a001548038140c00001c5041c94144600100844001e1210920500780401da5906100c4c02d94014801c00303500511807551022140310980164124500a030700c107500c00c201d90035480c100308803128452401020380038030110540d81c3e420006d0341050800d5501c02e00c1d1031800301c00920f203040049030050442e1104e40c0c5507000301400509103500003129500710740203107500c40140035220041c5903000c80111000300d200d0101101c1290300c0907007948603c8003010848180400d00101c00300c09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 830669289 1250 830668039 830668043
    0xa021c0905031b010807050924030402100903021003020f090316080c03070332031c06080d0f050318030d0606081e0c03130605040b01060807020a170c0a0f0807 70
    0x5030781e6003820b214403440b0a01d410883e0501282c4004001481e4610a80080240040040c80c04822034103440c0c85221590b900069104d44080010600095240c4015580e03525451450203e081500350390203c0e15a81905903800140358011942052848001007905c001d40409411103c815411900403030f42801c06118448080c0600c05c1c1209507030502103080020349810040103103e805021416190000b2400489a200d0312000341e900c43d0b040090004203003851003241820001c0c89802440001c540da6580301a92542c0400d0003401d96540140704001d4803000c42c02d20a440382c0e10341440100040c0c3d40010804e10703010015280000417050b034009801d4403280c0e52103048550b10800c01115412148000c0f00c44140101c0010340b02011007402540d00444485904411454079a902c1013507401c1078504842c55055800144480d41d800012254801035501c02054a01e6145c0c603105201a00928071500c102000988507030001c0003000f098405650040c0010308140304d13420800c045402000341 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 830670539 1250 830669289 830669293
    0x5030f07060e160f0830042711040305060f1b131e0b1c0605040609050702010c030c1b02030f1204090c180b0304020111120405010314090a080a021c090503 68
    0x101149031100000c101110000c0b620906c10014020600c19194880a0321b0542e10042c040002080e1100d190381100c180c406104904440a0411510001a0360b4503180c02810341000344410004a00000f030300f66000341051004150540b00d80f0f1201d510b0100e47c1d03d0f6240d46004c00504040c0a2810040c001c044811200c48801829580410b4480d00c0c922441303980b41c00802844084880014100a030304400717891000090415681d0000c1000c0c1e80541d03001c08502541e880c100320308a5020f00815808a009181c1045065103071a40034002c030907140c050511b0b40464500000440d00d0401440801084140172640301001e800040102503209020351141c0a007402014040a030040c41c10703038030b0700d45510011100720b4204490f41e140c640008206904100b4400c4041007841010f00544c8102812199515911802c01c0c0000d02628482c1011340200c030380c440c040100b0350801064020a0039409050304e641c49211500481c0303050660020710000c484406410600e940c0c00001c024115070b42581 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 830671789 1250 830670539 830670569
    0xc030806040b010c03081905160807171518040b061806060f0a05070f0302071a0c03040e1b030906220308070503100306020f0901140705030f07060e16 66
    0x1400700342d0310245100b50114002003a584002800313400d0f01540035005014150554492205c800c09403402a2076140305072007070704481d403c19588448242e900c194181030808142521403003000044200501902482d0140c00c15101c1d1a40c0d141034540545038400360b407000b0f605080c1440c0032080000e0740c0e803078410302845000d8101e65002d02c003802d00c107100040000d800e054130004004802d50080d81004204207041082c1c0e4005882007000b02d0810740640d004180003030030642810001c001d07010149022000c20301a02d0900c4000000b2201580c00104c0751406545a00700d1489a008801c0c0406c0d51032000031040111803407000540354420ba2750940b0b05c601104005804121200040c0d0300900000e105800107001a0b020b080216000410380218200680e40c0e5290310040342c100304500340c203480d00041c5004035581c1c8188002490004644800d00c1c10484cd500c80341d891003040301588a541d408500c0c4020b108080d80000c941c0c03951501511030340e00e0104004000d40c0b015000d0702c051801081d0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 830673039 1250 830671789 830671801
    0xa0e0f0d0518010c081309060b070206180f0d0b0402040b0108060f15040f030302060609071722020a03050604141b01080a060f06020618031213020a03020a060c0308 72
    0x6040800c00815440c0c0e076180c04807040d0258448010101e000781442004084a40002c4d1104000d05198502c081038116036410a0340710001d0f100aa4083c0b038100e6020b008480159a0301d004a40115003011144c104200d107840c0130451040c0c003241030701d0340001010580c50500082002e628442c034070848040115040b19801528610415a09180c01c01180d090140d00c504002c01d52048051180d010340d800e183d5243c54401c035200c960740017140160459000c0c4440d900b1310f40d039001c0d000855030078064521099007007001c00c07289000b0601d03401c03800c49200d0050703003038a0200087e84441d000340c00420203507100c5c00e24940d5800d095404540007548098000103802d00030030000b41494500320319214064014004503001c401c05001b01070300303d41e5418005034040c0d0000c1450003c001c0c0f50060b0200e8900340ca00d801e1440e15040a107801d5400c00c025440300500901600d661140707001030280c403150a580081860380801d50002504034240100208916420041c600c0d00280302c1d41d1071a03003a544007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 830674289 1250 830673039 830673043
    0x6020a0b220206070201030e010f06060315052407080a353706031502181017091e012f0c150f400503030a0e0f 49
    0x20314400007014010050100061030208000d29000380145400700e00040d21141d443e00b1288800c1d160700500c1d65603442007000c5038050082011000656a0701102c982c50140860484083d070f400b80c0c8002ca0507030212000707541d4002c4c29505c60540105049865400292002d80300550701c001c601d414580b8080741c038000c1c12501e0314a4642c0303640d094004645440306884a46001c0d0b800140307020b10010f00c00c04002030a001c40c40c400551000000210344640344d402e040c0c40d1800102c0c94140240e00411240c2e1422124443c60510a0b0003618403501e114064541250243c800134031100040e015501031007030b0250005004c060b40c0d00e03c002c0b814a4074114904d644d088880201702c04030b110105040400721048010915104009010105858004c0c164402418035041d0721030460100701c030809101c3c070300395a4200f0f0b6034001c5c0e1003c124100d18603034900c0c201064071324088a03600c1100b4940000321381043c0a00c02030a495010040320388030704146034142d01401d2801d603148080d00c1840c107440c48007000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 830675539 1250 830674289 830674321
    0xf0f0803272b0201111605012f06010602100209030703020402031b0a05040305060a0b180703021b0105250804080c03040f0306020919261606020a0b 65
    0x341e2400081070301819114200380c00910303060352088800300003010805804910000e402d109100341400d5041c1c030720000d00100c0c1c0ca40940140c66021042100300000030042d5841034900c00d0814950035250f55490200c62034501c4014a4074500c0c03203280b40b03249800010b207103058540030740945000200c140c28030030480c09000e0140e50f040d03100c16410405428158019508001c219441c0c2a0003965800000f80d030b40d110301020000614001000c0003407120602065801084a44c0c1c03e2107200c4e045d40002e01d8004005125000e00c200840203d41c0240c00b030344c1282d060b94148142401400d8580000794000e200c2103410120314282114886103194124a05404d50003845c0c85410403902e441d2200e2540ea00006c1480080340b20800012806a0f054441d12008611620000d60342d188440127001d07048810f141c00107802c4042c000300f440031210306016030300030b0203004420007100c01c510503600d403900d421700c03813a00c512908200b8041090341d404030324603e56500803884a4a242c13242e128400340307449 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 830676789 1250 830675539 830675557
    0x8090307050f0d03032013140103050c04061b140a051002030405150405010b030a2d02150c0319050702010f0e0f040b01030f1103180105010b070206070203160f0f0803 73
    0xc54810180001c1c3c042d0f81b0542c03030720b8100d00c0741c0c00b80c0b00840c038412610b56102d1606000404916401082220780750141700e00e80880a282c14051800e0801c0030f40118011401a00280050010f884c8151a0101c6600907030a800540f2910404941c01c58252a25000001510715004210000480340003500850f401143d01000508440070b00c0e54100300300c4003001c0d00c122215500c40c921650156404c10008171928052500001409051a2452100d070b4610215405001c01c503085d410150713640c01000071500e80030440c416614480c2105c031a0451041d6404284821141062140710b29844005803141c1803007038980c03640d01c40581405440300ca01010420390700044110207040141842d8110060781c001c1070401203018070280714440281d814201c89224050800301c10000c044041c01101c2070f42c1304142c1c000308103d5040c140000d1082c892148041c1c050a8009100c49c215107040041c100c00111340f0003001e0440b80c91740941c448031300d9a0b04c660f2800840022010540320400b00480d60180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 830678039 1250 830676789 830676799
    0xc020d0f020a0308461106010b0a0306051c08030a090602071103120c0607120207050f060a0f090b0402040b0a0b0705030a09090b0d030c240204090509070b030a0e071208090307050f 79
    0x11241c81c448140b01160b0200b1740c00b0880a005000c805000410405028100c6c03411050380701c450b00000101143e500c2c0d440a8800d8000d4010011613034005210300d50210f41040c20030380e480d07448444050280001550083c090b0784002100000d0204815a0034142d490403800e81e00807500303143c0a40094000c000524080750802000b18100c1ca014141c008151079100801504210641d1a507034200000000c010307549410807400c000307038206a440b0306641035000d40010040400d03591140340e107044000700000e005036a03408411096544110200f401400c1d9403071410380e40c10f407502d41607071242c01982d00780001c1000040080741d59001c602030f416407010301900e00c95954006403002c44081114440649800501c42c0c0404000f8548410690000060b0040941d446140804050840d4001840040250000035040c01003a2602c41203a400109a0300042014042102c040f0b0402425520001c513148588800c0b8080120940150041d00c01c114160b5a02e96514800d1050760714841d8255036001d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 830679289 1250 830678039 830678137
    0x100e12070f030615242d0e0910050103020304080904060b071401060308030601030506130c0f0809011a01140f0a110606030705031018050604050105010e1005010c020d0f020a0308 78
    0x103062030044441c1c80d84c0444c0b0740640180104c50f120300d0114081c81904081d607441b8024543c03490f400050b80700401209440310522480c201c4501840c0030f1807401210b04141d00040030030706000190050300e50715040144200240da039110814491a400402d007142c00c60038005011948003010b00c00c8030202e07900003000c0b40ca19070b603041c011401414018085a0f00c0211100c290846800d940b00d807058120858541503c1103907017100c041c0c62440c004010445507810003004501948022511980e00402030070302007941c0c0c0281010f013030a406100c8046004901c08542c43d82120341c0510018581180d8209407502c3c2d850322414141c03a2442c60082a400d54000001e24401c01d40e203502100c0981c6440400c43e00040d01c65842d81d040c00390940701038425a442d140144008040044c10b141c10011a200092520b0310b002d00181c00001484d1001e403044030305410000a00586502e060b10071a8020b10851015449180c0603a41e81c010811806590368161b4600ca400010804004076025043e1000380c44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 830680539 1250 830679289 830679329
    0x1020f0a0819050c0307031802100f050c030309010209100f1d04060509041506051008060d03030f0c18060c0809040f0e0d020304030201021902100e12070f030615 71
    0xd030070703405044400350315580d0400d030742c403039049204981c040d00702210095641d08065038001c0a40300d820040c3e0340c0390180d1a02902c0141d94156211b4002c0100d420840544019000f00344c800303014000001c10320340000003c01c02c4442042d03004040d10350049401e007103100c41004045031044c500d40346076000300c1c1100ea5039140b440c89030001c0541c0580d00510204003d6124804a0f400260642e0111410700c0001d4030048150541d0041740081c041c15110f909186503400030007000944003a02c954001c2580b600d4850606200713801030000b0189400050251aa01c030038014036041c0400d8603c800244200000b24045204c2d0020030001900019000d047c00c80c0303101003000400081c0100132034030303075100c50505c00361300107110906c40075486402a40c0c44078554000a41411003000e031013004005015030300c070010b0396031065580746524649000910b0101c054085072880c0319200c508a6240f0071307110002480030150300040b090701d101c4c81c3c0600000500281d80d8282080320f0040c0c8a10329160482000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 830681789 1250 830680539 830680547
    0x21c03140609180307030305100902070201021207020102100e06040c06050a09051c020a0e091005071704061512030306080c010507140304030206211b03070e060d1b1101020f0a 77
    0x60010b842d0503c0c20041041c0000031455a0700168048010075102c20070800c1c5064910007840062081d25015451324049500003510b80c402104c4001c0c22000c040360080641e403003044220765a0259440c01c10803a03131041c02d41c59403401c04a50856008540c01030108002e4401c0d820741710590990f03201c1c41003907400c041c02c0101140444490745148440c1c440c5003005613407203101080041401c03111100c268100100010f0406559100055800c0c4c1490140300505612185800b11598001e4441200f07480f0f51409501070304884601612050f48031001254080c214195007103082d2098808100175076503804142d8581c3c28034110035012a000303100d034001190032001c140d00e4059450701641d14280d00c941c00110550021040000c2c6507103001c1070135141c1040001d08642128032414040e4400c2e56042c100e802a10000348004208080400b04800c036031204802e032414240d076110180031802030300313020b1444498032481000000d482d0b980d100b04005410720071140190502c0c1d0f00107182c550743c05410380d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 830683039 1250 830681789 830681791
    0x6070c05060105060f120a0c02070f060c02010e0d0609050c01020d080f0711101e05241903020904060b040c110a170d0f051f05030606091308030106021c03140609 71
    0x28102c448100103103003809408840091041f00390100001d80c1a1444600901c4e088103500920300350540c1200500c804c541020340301c01c025609280403a0314505100108020100c0000000c0a507070800454000b0410041030401d90f0140c20780c2180c907201c881450454603139100381d81042500a4200116801d14843d0310040f502a000400b00c03071401e41d24020890440c1c240301d18202d0b801822400511080119000700384e0043c5990308420100440e44501d401c02510160500788100481405400c004034070001c808011500284200011316080c100100601000b8000714070079482d1140100d030341d034000d030501d00c5c02c5032a203c01000045803030703594005290b03c60800401c114100380603030403d0140b1350142e01c080112510300400c0c3d030304155031407090031450030500c4010040d0908042c40703191070000b4a00d80c082e60880700d80110b030b1034443c00c0c2051002250006072a4110000022580940002d1820342000b10000241020050100c0031021070f0745c2c0d42e032a505820740d0b4202190071450910152 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 830684289 1250 830683039 830683057
    0x1812021c050f030304050d030c050a0c050f1509060a060e04080306040915021207030b0102190606030f051506040b010813112701080a0c0b030a060803071406070c0506010506 76
    0xc03a01204544403a86842c40088890382154000020001003210900208221107901d05003480030781790b400e0000c0c04074040d0140b210100301c100c400c6001440001c00c01600e8011012041d5a501c0b0307101c500b4052031120842d0448040c0c442d140101e065080035201d00821038080d030341540b4198807035503500c15107540060482540b06072103005000c04210300007010000c0c0711004c40016600c0b100c1700101200c49500030141801d0515020340d20007280d07004940c1403100142020119040038480c43d2410062020b82c00207004040c880c000d0b0400c000c000180c0000f68000622020802d5031194104000e403000a5000d90015140c18007241e001c41c0e440054403801442000400300c03007951240810030156813450440c42c00c20140910840c842031030504140584090b10160401c0c086544480b240c180c002d12421003080c2d0000001405440c655104001910011007902d40d10513207418440210b0070206540846030107010301060955008017006c68150f607014020b014030780e180504208640d04007002e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 830685539 1250 830684289 830684329
    0x51215190518060601141603030f0603260306010c0f020f090c030a38011e02030409060b031006110c060705070e06150f070212010203040b07181202 65
    0xc800120800740903040c031400a4400844a0310706a00d02c00c0c1c5810006082c8a0500c25007200786404141804216603851107907a281210b04d000314a400c4006060040f141c0000720316014000c401c01900c2d01130304a601ca4a41c10a001000c0402d450080c6444182c5103c0e002c0b507550803510b000115011600031081d0b000a0140000f0400070380406ca21032070488081a00800001c104410911144124448130840614030702e03004c034000c00400b00075003415041014446020528442c03ea11604200f200103203804503c10011450b08801303562904036018001d07940e4184003000c200b011007441074a02c101c10495100c5600f0b0314107441a550010034020f40b40144c084d410721503403151201c00040980d244514000c2141a1500c4008c00e0082c00c09820707030b849104490325001105104000381c4100c014940c100e69554440303840012030123a9480034120455001100300001d005211141620400d52900d035040301140072241000000c08600901c0380381180c098210001d4100402c40041d0588000c1d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 830686789 1250 830685539 830685571
    0x100906230409061113030c08070e0c070f020a0905190b011e050d0e1c050a02060f06180103050d020607091514090406150e0103140114240a09051215 65
    0x266081300e54800284040070f404510020010059280c107101e005244070300282c0f07001030901004c1e00c200e100c0a48800030411b0041948402c0c05041140c2d1255198010b0122038019640e140110141c5030031104592120f440d1502450715090a00a81c203417010161b440c42c81c11103210881090b002056110705081140901c198054016039100e5180d100340d144000700503c054010000740381c24040c01c00a81000b00c280a0540000d800103243c07900064402851940b61b0784d400040343d40241d003403414140192202d0300000500c100400e1502800d0056403d03907506580d040002d071070011035403044882c05040720804240e268030800780b8001213000b5102c224500120140041d068400582090543e8a081041c01c0d66141d00101c200c02e81620030700341840300300d95034048006010014030450180c0441d00341c0004e07266440c0c41c250340103500e00c0040350701e612003451481400d0360442400318020406001c1c0c04501c1d4901501070404041d041001070242c10340c03030305a10f00030110243c003200304407107161 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 830688039 1250 830686789 830686811
    0x10030f0b0a0b0d05060307050108041403070503160b1e0a1e020a0f090f120f05011401030302010b0f0405220302030f04182d0509030702030610090623040906 69
    0x45203010041c10b11240582d218001039810b81c0458001408040c03281d03000c0001048183d810070010740d4416081101d0002e18448002554198403c0300c0b03006002d0302000501e5442c16115454016460b4041e112081e416600c440b405080c880c0e100b4036005e50986003100080d071202c2180c10a1081044004161410208081c220f1080e41c11100f405404102c48582c0709452990003e030300e0004040101c80009500c3c50031074035144144001030045c0c01c1400c1c502084041c01802d401201e440e4100902c052225a034070b0400078000d10075a910603108030141050a2960319107400b4050040c1c5041c0c41218001000d40307152522802c50210440650109105180100e50408050002130801c450070402e060351070a01102200c0500c00d813004030600d42c819048411400304c007108040391407030600280a803504000103246000301c0c000254103100c0c1c2810402e06104001c001d00846140d001c06200c0e080d181ca1040300c00300d56201c0040c0b4491223011031a10320303213002c2c1c1000205500032580003c0d20341c028 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 830689289 1250 830688039 830688049
    0xc0f120b160903080f1801180e0c12190b0402090105340b0f010b072a1211090a092d0614190501260304050402030f0403031a10030f0b 59
    0x1c0c004007241c82021a10305c4510008041c07601c2402e10034032346000c03c0da180b0310325005e044c012030196910801c20f000015140c51104000c03591520f00008891480e4034000d1401002c1315125440c22403414100080e41c101420180203491500005031202414240300c0d80744000d0910247c20100503d40050f54800905c0f0383e00f62404500d00d018810142c000e2503c0800076002c080c042c2d0007407400c80c00230000600400e40c50140c011650123006030b40c02c258800c3d01c034006a9488543c000841c03d8118415810800807040e485000c0340b40700317039003001403a6103c1d459001100c0719188054146d10856540f00040c111803110001346001981048100c0030303441e202ca10032181c200039110145500b400a0062846503e0419000301c42da000342403284d5818442c040e514482425404145102c1c140540d4824050a00c240c0c0c01404000d801107461b4904600f0814415206031421783c00f0034600744100a041c400020140200700007c0c0187c0180c200341903044000304500701c012082c4a81d184905051071759a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 830690539 1250 830689289 830689297
    0xc09120a0210050c010b030606060427060f030b0f040b07270905090c1e040903020c03010e0a0309080105160e0102100507090810060f03061112040c0f120b16090308 72
    0x1280e9a4184ca4204806039582114000980d0030320a90280080004540c0d43c08110382c02e590003903031a10780244012340312911032111300f44422440790034103d01042040502ca044421030307002d10561402c503110960b91100500c000d0301d0140c00c00303401c000007512481c0076182c0d10000e0124800d52200b4883d1040c0c290000c3e1807541c0050603415110414022004001c012012146d00201d800031000c00d103042001850510b480982405251103001e1a020f140c001c0c00490840710b40680240302d0001c0044c4180d464042110007100407846540340807415881c144241c903c0341c4440002400d001400c2001030311480380350b2203164118820358442d49810081805210b01a081c2d5403a0f000312503003404400ca040ca42c2005418440074030703000003040769158042d82002220780156000502c52a41c1c040c8201c03a11070090440a075022031814042013080300030004040364614820000c401e0b803511616982820441c1d005881c07842e0480101c2c46a40034501d4010f009201c0d030404043c115902d1f41e5855960b04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 830691789 1250 830690539 830690569
    0x182701030b070908010203060d14070812090909070e07210c08040308161e020f1b031b060a030e01060515070515011212020c1e01030b010201050c09120a02 68
    0x34045050001d16600310f8024005054080000d40c21494188042900c885170100042c1880360355100d241018041842142e010b8640c00d402d0340c13030041c8164805052503100040e56805113a175039002404081011507208282c400d0584000e185403600101101c503d200c03a81110265212010304138060440c0384220300c14010981c139291034500d020308014103000b000800b01e0b48843e1450f49020f86056110000e4840080e10b001c0702d1009003c6503108034540001410410294410100c072406020040c9041c030401e507200301c045840182103400d8030341c40e400f9100344550300107170280700d0984114042d4010f004002510700000550a696400280309a010b921a14403099000600b11090040074440fa042200040c0e01d1001694900200d5190f1100c144501030300040030340f10044c00c120310901c6002640403000300790700300400200c0c4040c4800070017001c0d00b40c0443c3c5030550311a103e5006004451140c2c2c01248a681403450400501c2619582d4201608050149190f640c0041c0d96004031000820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 830693039 1250 830691789 830691803
    0x110a05310216081b010507080907050d03090603020a14180a120c152601080d0206060307060c02010201060506040b03100609050303030c0714100516030218270103 71
    0x18810030944540c80311000c02254a500400c0a1415604814075200c25242d010780566515100e1000504400c0c100c0603110b03520b9420a406d202d9501d0b03011001a014070740c1941a5a4002c0d036820400c440c07c500030400a011400c11801006650302036400ba15200c0c05508204d01c505020000020142d400440301208c4a00c41c86000d84403418007142600251441803968030b50490903803103403191002c041c400d0641d6407824080d212007003803160202000c10074960f03030740040e0941c6810034804e581c0024000c9814500c54041c056408500c006032403402600d014002d801c41c03e08201b001c803200120004240e0541d902d03680002116202c100c01000201000000c4503260700b015200c00000c009107a01020400102e09424000d40e0f50210440703410062102c51541c2c0ca01c02450b120010150001c05801c460041503603171144520680c00c072600c1040613000f00030a40141c4070003501280111002044028402c400015032070030000c6482200500e0001d02400c400e2548032403524001d4243c20071600c807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 830694289 1250 830693039 830693089
    0x702031c02120c0a111306090204150206100b0a140d051b031e060d211e1b060e07080c010201151404110c0f0102090f0913110a05 57
    0x280d5060255607031640b00000030a00d45105035000075914454200050540c2401c00a2558541e071040301e818980015841c0511013981e5a150000007500280f280c4252841c0340569652164404140c10384141e0385a0561450a4102a8032441c6a001000d010b0b05001c1c2d0000980703c8400b1440103415103150252000c1a685841a0b00109808e200c0346e40f40010801401800139800c14500b46c41e65080001c00005081e42e201000102d10449004000e4070a00b003060080a414448220b00a032820040e143c0642908407829482d82807101584200300207496070400e554070f2140c61302e082e441140a400b0201c5c2c0b800b07803c000300b824125254410721040d809548081200e580a00445025560f0800e4641040d0300e40300c0b007003550020140c0d00c10700c596920202404107030060010381e10301c0083c8800320340c84540c001d00003500030b40c0305100c0a845054404104009450200c0b01d0314842c0d1000707401d180744900a03548008184409071096940280c01c001c01207222f40b21000c651801c41240c0700c1d03942e04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 830695539 1250 830694289 830694343
    0x9060c16150e010213050a0e0c1b010f02040303121d030f070f0b190c08010506030a0b0409060519060f03350d0504060b0301090819141617130614070203 67
    0x41f005e1685c0300904500ca040204080582c18400f035520300c04903040903031503904008000e240186402c190344440c51b4800301d40801403503448181c0d0601e418402c0c1d003c1051440650004001642d00c02085007240e0080014119125172ba001402d0300c5842090000c03a245005c1e5201b00c035504088a5429401641000c0c0004403281401141c102c4080e0303041030402941090301140451100403c95420117403a0300d0200d1f210b48956010002c0f00e50802070420440c03c3c5130b43d00109120800c0b140300c1145080540c042008032141c1c010031b0440341d1111000c040d1141122800311504a404e00700450780585401e01d2902c0c18000c030080c030409000001c00542841c141c1f5020003150803a10841d4001d80c54204540002021002100c0e40a5032000000f1803032900060b00700c8072175038410601805c2e00d82c00300e1b0000ea18103944510964030340c86044501c0380009094040582c40c0640c034100c0c149440542c8041100da406201c01c01510307085000c07800c0c600b95041d00828502440c03114801a0000c5032014050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 830696789 1250 830695539 830695549
    0x6180f15210210111203100605071a0c030603010b010203090d061d01110909070f0e041d0318030d140d020d140727270b1002030309060c16150e01021305 67
    0x418045c1d88050a0541c1404c81d02c54440310814007c40041c4000000d4810500c14034402c550b00072000040d03214018605650111455001036441600941c24804d42c0c144641c0040107540700880080c1c80294007000d00d480e2500601307229040002c01c03c40780c507404030542d14207006009800010301c840d10382d10119030313090210441b001440007082200581c40c240c040f942c00000c401c06c0c0c04045078081a1124121b00c0d0400c00b011100200083c0d01c00081d0420800034400103990300031301c04800b6251450a2500240c0d4020719071111a01d4240080005ea818181b455020b42a0030011007000200000c44030000c0049800c2525094003150403045240507840380103e54260b1002243c151100c454a4620f10024480b00c00042c41210f0b9030550321501706481580c0500c0300c0d0311009024050b1240d40403c043d440341d0041c1e40c1c0300864021b81d000511620406c1c030481d007a0448804902c07000c845540c480780413000c05a6054855281c9862007040c103000240041c0c681a0000308402c0c81c403d280c201001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 830698039 1250 830696789 830696803
    0x22701050603091b1c030c05010f05220f02040207030503040203061513090219030813060f0c1410020f09011d0906010807050c0106180f1521021011 65
    0x1074071424003001040415070003c0b5461062400303c0c0b070f1150300c846103440060b40010040c0c401303032800041503c0201c1450340c480c084c450040d00550080012100d800c41507003e60b41c04565500e228071201c10001c44d0a0041e40e10801020301a83c0c07074485641d61503000600340e0b88100f6040c0c0000c6d0b03001c4280070641c5410b210460b044606916003548000581010a5082c04070342420303505030781e0b117024820070b64a4500110b0061400c5402d40c40c2100e8691402407040d411034019083d80c99450034010410303500441c01d040700c100300317a2103180c0c00c1c10903581d07808100541e0122890f0035014801d2194400340c00c0c0d0001d044071040140e003868450f4a000001130005a514000c04100440c410f203c0790152104840c1580090302031900f2202581c4648096445200359002c40401c4e40c85d15100140030348907820b01103c03901440c60180130340d010410311041960030200142212114940c4100208800039860001c102c0969204c907800200e1074000800c20001010b102d00030443c032858006186030180040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 830699289 1250 830698039 830698049
    0xa08040210020706080c0d0605090403020604121d0405090f070803220518100e0f01060801150f0e01020708070801050f01060912061802040e0d20030316030603022701 73
    0x3c10301c0a00c3c00c500104440b070040c012250b0007400198115011079260044005402c000d008241d2034241807900075580c1c07004440a4629002107840c0a80d00ca21034219030740303050031042440da031021401c070820006020162200020788240015120507443c00d00c200ca004000c0400a16281c106038030b071140070006201d0452030300c451502002d02280e82c2c1d201c4064800d00d00c0c039a4564940c0e441c1465000b1543c115041048201ca00104200a035102140c0d50383c1a1549544c0380a000e907694000180c0e580d4012903c00d000c1001d0741d0180e20b1903031044644003103502c0f05104646005940d242150309040305130b0410741169466400708484007002100242c01000c103440d2000301d103841c00b58900201c00410344020f1610344c55401c00159840d010803243e40d85074002388100400311000004503901d40c0c0c01c0540b5004101c0104507010b40d408280700381c86410503140080c511315582c1c4010440e541031400c40c000c09240d0748090200c0540c0b1100d03042c15460081d5414114506498191203035070950503801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 830700539 1250 830699289 830699293
    0x20c240c0a0c08090d0515090d0e0108061e1201060314030403030f0e0d0611280903021504032f04150e04020409080c0c13020421031101020a0804021002 67
    0x24558030707258001001214190002c0e03907aa02e58003411300140110b601040050050b114811000c00f55504403466a40504400c108407a01080200f03002d4800303280e180e10301030100744888000b68031401c10a0b664044003c40700b121741c10440c1c0352000100c40340c607200c3d4416590780d9544014001c212002d4001113014022100940c10031780340d135400601d400c8401d161441003140306d4512460300d0b22070f40341945400740d008100b88212008108848100d030090701900760480880c20003201544207900d84041a02c07001c1d035408a00c641560240711810b01c0202c01801112802c000c00000f2545425402210340c1003096420b00e02d05496048520301c9480d510028840c0d0b10b0081e0603400305107040202000c840c034401f074804040d41c581c000a001041050000342840c41d00140e40c0304800341c04507500104500444500c41c0742e00040c101e01c41240510300800032840204c0b51800f02295440b080207510500c00c0c604404084c1d044072a050a9811107002c2c1c901240100080c0401c5151280070302e02c4051440c80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 830701789 1250 830700539 830700547
    0x40e010506060f130e0a02071a0c041406070b04121403090604241b09060c120309051204030c03021c030801150c06060308040303090f031113020c240c 66
    0xc0001d000d80729490f0800f5581e02c0020760400026502503011005040340c8410380c0780c92030003583d050003a40c0710100031154541c013a040d240d56410104007141c01a00c0c08400380d42024123007011620b42801201c4c0f500c1c0c0c0090240303e04030004051000c480e1095224100c1001c8282c0c20640182000f1880c80354001036100a004020100743c00042450748240c101614014079414006114500d1202d01d1403116001e091101d10443c0010849040c420b0303100d41d07619500307041d550f004e0403200c101c1c80c940003c01c011440c92414078068481d400070b1903080e000300309641c164a5032500070b2045034000d60044a030104203040820552901e0b00724002030308100780d40d5400345182c60f0740050521005006030f4044220380d4201c04c1070248a02c0c0c1c842d299070b40c810000c2000341c2e10f03820004444d403c01d100032400500300d410085040b64600018008507a031160343c9501100e41c08003084040440005c40884e01903082c070110986040802124034807240c4035035168022500500d130940184001000503901002c204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 830703039 1250 830701789 830701801
    0xf060421170402060d0603021c200d0818060301030b0103020a0b12180c04020a05040806060111150a1e0f0b0307080a020f062a0c090f0a05090f0615040e0105 69
    0x5078000707a10a80c1200e0f40c950344c02c0d000c02ca080080049401c00f070742114450203980e42683d14811200c0300680940b02d55010300c180240203e40b40082d0320040340d00180c2234540c0070001208540944402448541413802c04180d64020410a8100341c2c0160b64090410f0010425070030024078000c003400c2880078080c54070014950f581d41c80309010708010042c3c81100d0112004680030300808a185070010030566070b400300010000c0c10780c2c20502601d14203000e4a4045001580500300b03020314196048081c0c503400c00701d400890081000288801041521842150300744240e9819180d40b01d549201d00240fa001e0084210b404c64030350501d914040c1d44191024825594000740344590350f070741102d1510a40c001d40002c01c0d694001c4400300c02e80c1e00c0e03403406845111420041000214010b020444031005084006c024400c0029038800d5030400b90b0318003143d0406203035000150700c242802c00f01c9500095490210380307041d40c1102c0ca644074904d000c0f5400c00303519060051100c00702e0383c00003d0255041c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 830704289 1250 830703039 830703077
    0xa0b0f09120709060f05090f06030a060f2a080f07050712120b090f06040207052a3111070c0308090f2d031005010e011a030906040303020c0f060421 65
    0xa0000981400300c140009d0322030307404200400713085034066030a103d40c942d031080040c00782411080a000060303c00761803901c031504806440b043e0289903a18a101910340e0403500b180000c001d088241044420408800455003507112008a0b06155882100108402c0a840111003d003130b2042d200c3c05980051000c0d50004000b0741350011400ca900603580c40300c134030b0700900d4050701c4a06005c41070000401210948428155445896001e4407030040c22290084000048003842009032032030749084288840c4000b090348100d00c8000006041c501e4030740c4640300d003040c407a402d5204854815000400394060304212020344543e01081c2c45c04001c0707400d64050b6440840400c0d440c2c0540c846000101e52031542d080080384403c8040540c00c004a503190030512200b80702c24090006060101c80441c00509200001c40780308005001c00b80c5100d403078541e0210040e60002d010501036100350007807084215004e201d0703036000720b1040f041d01d040700d08403803150b070340362020019400107000e0310031000a00e440b16 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 830705539 1250 830704289 830704291
    0x6030f02030403210207170304140f10050606040b0d0615090602060103080f071a011406030618042f04060b1e071502030c0a030e0c0a0b0f09120709060f0509 69
    0x1380b1001c0d1011080411150002400f643e08090540490591110a40d400702c40042d400780e800307510180680c0010f45840b80c0e035103407242d00b030350044d50004024800c2c03070055a00035130300b245008002034603041c0d45240306981c43d0408031813985500d03078402c0100b01070780c0140c4066454000c02c0c00c01340d80301890590302079100c140501c0050410000050100c0d0304034400c20480b07540d280c0c4401ea94403030f030550170400914414240502895a007144408290603e00311082e07901c03c00009141800c0a2102c5110840500000c0c008541c0340410545804c08540068031003d26058003032084007040d01c261040200b550075540c4681c442d03030360801941504054458111600d440001040d607903562840c942201940101032035080741910100078448801c0c0c0c0d01005050b60540c554040c0001e1000c103d42940311880212020762207602017000b0406040700e80050499041440141400c00c00b41c0004164200d242c04d200450581020000b88001c14040c490b0802400b0078441c034050141c24580814841c2e24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 830706789 1250 830705539 830705567
    0x222050711030a2a05060703050a0513120c0501240b040f0e10080303010e07120501050a050d08130323030a0e04090602210126060a090201020a1202060106030f02030403 74
    0x2c181007041401301c1c101540300d4901c00004954200003041801c0c100d40b19441640ca80001906000120341c9080782801a01e008640400120411085a607108954032007414004c1d8180401080900c0c0483c800b88111809914074100d615614201304000042c0c00b40240c101103020081400240203080071400740905030744080341000301c1600da1500541c1120b980c0e5200b0b203400c3c840003001045c0303030345003040560003000203403104e92964a019444e002a40c3d030900885410482d80b0104018900d001c00701d88a580d4008d12003946402038180040700c50300c3e0300d5001600d9540220341c000d0b500c034200911800307095400c01c01440c180000124020140c0082c1e58081d44210348840c00607092001d41d50454100801e98001c1da4401d401d11403140319014403d10603410002e182640c030a080c403c0003a4401d41c003c040c800580402d98076008048010401d180d000e034110310445054000082898862540f099032079001040700c0e600d00349000b02030381d040c240701111190061050000080d00f09603004074101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 830708039 1250 830706789 830706797
    0x507052107050418050604030203180f011d010912080a080c03090a0807150507020106081c0e1c0b0403050d150b0306090c0f04091410120b0406090222050711030a 71
    0x10301e42101904003000f003c54017400c680105000d1008254000008020008841405182400b20001006803880503140c0050101d28203490142001001490500d11500b0504000c040740c3d844414420107440882c1c002c491403000040c20301d8030b0680000320568448240b059444c0340d840c10307682141c3c48008181005107aa5408a0801d0411880b4003400c005200c0c0231008100c1c070716081e0f50007800b80601e48140c01540c0103448511385144851034007400851300175140c00c1d21004484040c0403254803036030f05118218900340c114000142051540c4c1c0d000ea401791780d4668840ba40301c100c2c14119030761580243d41181804008003e8404003500352a40600d00b142c00c90a160f48002c0500301034030a030810302122007800100491034a22a0384441c0402417148560300181d0707202c85080714040d00902030000113601d11980500040c1007841001e41c400d205100100d4842d0712540800c0c1c000d02c0d510f505640401314a41c2e80000c441d90340c8180c41d4003c200f850305404c035401905220b52a4480e48294400300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 830709289 1250 830708039 830708051
    0x81207020301020d020c060f060a080c13060305190312090b220209070c0506010819080a0203040b0304151407080a0c03060b03070804050f0303060a0504050406140405070521070504 79
    0x1541d03081d410707500030740804142555581800351003140c40c0c1c90100c9166a0014039000801c1180c00e101110380c080d101d0350300007000c100034104100f00004100b010040c14080c6ca403900400000c04c10b021212203809030424040070822940340140046201c0c511b2b04001c40d01d080020004110001e0006402c2080f60500700b03c100660000c0000015a012019402940b501d0502940d140d111001c1111a401901964540d07600c0301890741c1c41300c00b1b0b0380a03200c5200903802c0010101d10f0400042c158030800740122441c2907541c5803402066042120309403400551002401c264000c2c900400900c0d003869010000ca510b4818805000150081e040d1040700340e40300e5983c1141030181c1d000b4005051106101916850660001001548112021596805001c2c19078154110000c1030301e01442d00106440c5509003004140401888020710980740715403a400c1079044561307070070003c0340150b02402c00307480054100700502801d140542d05a41c444005503403407c880f220049020030968600301c50119503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 830710539 1250 830709289 830709293
    0x20d090608060d05010c02071505030103021008060111010510090f020a0815030c04110d0e0a051507120507020a0c050609180915150f0603041218080102121f081207 72
    0x441c40340038500130900e40c03811040c4a40c1ca03400050340000c48020701114002058100c9045a507030100303100c02500304070b05d911a0340300140540d124950103031040c5083d084030740840c03102c2825140c050751210b04070361400c10184070407400c9008032401848050415171030040340e604010505a40141206130004405c6408441a50144001004020002c000b401031803864602c004007030780a54901c4003207500c0d0511000c1c0c8a040440c40b1302c54140c2200151980b07164002900742194002010401000b08400c08015840003502c40c03607009001540c01040d0608071840c1040380c007880358100d24403400c42807100502c16960109015204170586444820300c1d21007903030485ca8100381c1d4000b04650350143c0100014182881a00c030511340301211450760701903081d01400140e00c41654084c00481c068a01080e4444c0240103841c00180c3d203610700e20100d42d0307580600b801ca8210b000644001c101002c18803513003e656940d140c0c500c0d030350b040b1808515882c0400903540c84034009072240545d000480c2c902c007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 830711789 1250 830710539 830710549
    0x403032003010512071a0c030904110903060f0c0d0f090c0308070c0506070f0f050a0b090102070506251b080409090201082401111c080f0106020d09060806 68
    0x1104a001014034202a4404803200d01a003090041502801c0d02d914034014802002490800700c50b80080b5403030001c82d14200040d541d5000c1403800c2441d110030001007042d5100c41c85401808840d83c040c00742c0704c5030314508050a044018101c2041e000c44207042c0094032102204940c0e5550308071100181c00c000c4680008080e200b500c1010b030044100800000a100416000b8418544901f6002d1074141c1c40b08200140f600a010018100400c42c00308e0100041081c0002d40b4128000c00468654003200c2c0d5404001036400c940344070059401060000c03c010702001101c1c1c1103580c0307020020410303904120011090b41f8079154002000800720400103c08101c0741c000e101180c02044056071141c03030340d140380c1c0540f00021080340021128400214441a5002880c0320b0400000034490741c14000001112140c6010001c1c0d4940d0260550b0340b1502e603103e054405003518240c83d040403074540300e20356000340b2405070b1008041d50840180c0d516420b511000520a4a00382e090110564a650780420 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 830713039 1250 830711789 830711801
    0xa0e0d120f3c11040f0f0305030304080f0d0608030d0609060e070f05190c03090803090d0210050d0e07050325090231140d0503030f0903190c0b010609150305040303 72
    0x1040d40b03807521102c0c543c2d0703d0b1220700402c26a0850b41e680440540e46640c0c0c10000d00180c8400b524542017800454000f03200b401c002d000080c10302c44150705000b42d20b0000700884140b603024050035400007c0d0000703101c10501400e0002d0803003000400005203803111000011500504d480c0c20004240440340101e801002030300c44500460120b81e105c12440103002e0149412100241c012800640d400a4040070000032110214400741500c66441c0711a801d120442d448211304400703100d001e02c031798000c10b0388034407074207240c07444450040403214a02402e1500b0030703190742c4124601e000785c4030442c1d244131800140c0c2c00841d0032a8400680d50803907803a110124280c000502810803007441c040c44446403801b4040b200b0303582d60341400c3d0025000c030810842035811820f4018500d4000380006841410040320280d0700c11494410b90b0710301034920b0a60f40c0c0d1600403c501101042140101c0018401120155805420141000f81a0600305031150450a005003201070801da1074000150405220b50425 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 830714289 1250 830713039 830713151
    0xa021002030c0f242203020309031f05060f060a05180d050609010f020408070e1e09060709060509011b030c0b1006140f040e0a0e0d120f 60
    0xe54a03510b600d0556548404c420103194103103a08003014415129102c2c4403150280081ca01c4a405500c1c0182d1240f021030b100e504160f0a5000c2400088079a407800e215025011182600b031424022000b080d0303404403200a0a414020b4070805100708176504d40604540400e15142000d82d1070300c42e05504942559080f00748260801c8442900d00b04001b0300080e0607000d135a442d0000e004503c0515681c204074012071040750941e501203c405c00c45144a6541c0703641014030108540c00041940c41020501c01040d280c0010340c1e44035804200e05c81c0d0b80b0803100000307007941d4900a441c01c00d880000a0029504404408002001c0805401054090030000c600941d000b91808001e01c0c000300c1d540104102440307103202040042221103099800481160108a43c802d846418103040c11a201d00ea801c1c0100000c00c81c554500350700071400010402d0150712543c960b01c50040030034201142094460601c1e031009401e061032503e00e050030306903c07994104c008000314006440d81205103821092541d07121 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 830715539 1250 830714289 830714293
    0xc240f0402010c0f020a14030d03050402060418020904020f0405180103170307030b0d060c030b030604080a0e0a0807091b110606010809030d0501091b050322230a1e050a021002030c 79
    0x500c100342d5807c0340da584004030291110a0321000090301590400c40300258418010403050042d1090113070345441c007100070703600141041581c101180490303100b400c075000381c1d03000420100714038a4840505403074442e032100076407103d51542e580c0f180c801c003480700080da0070580440000c150900c00d40c000700c02e94800800c2400c0f100741c00e0800b10010840d07c64a040006d040c40c44403051820009400380c010341d400030040746070021041c8126100c02801001d15805445031000241e08038081210101800800200180c3c0988203040154030143d00704c440001e2150028000781c0303919010503410386c000380a0078081c034241e032036283c01410b510403406501e10881c50b01c0004203070350115903c4206a001e4a49012402c140703010016a0300b07000c215124003056030412401008228158a10508903200d04850000c9414040110501c1000c601c210881603000d4080001402000706a440342c1c100d030001c003442d00403495240c0540700c9515900180c01810f01c2c04001244d14420001c40b440d868140701 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 830716789 1250 830715539 830715559
    0x13020c070f2919140a0905041b0e060d0617070f0905070c0f03120204121a0610030c0905060304060e060604060b2a0a0311060708010522110c240f0402010c0f02 70
    0xc000d031a0080900600e40150f280c039498030501d94451800710254505a1148ae9080600300200400c03a481203408101940d10b5580018610645420440c50f900380240649612410042241580300041e4080050141004140144680c0140d101e100d66500710200c071500b900719040645c1c1060b586090780d10450b00c000750001d2803014042d8810031032485024041044c907203000c5015110201992210b901215010b8032085285c0207a00084a00754982403004940f41e545002940d2504101c0b42507132042d45801e10b41110703c0052000940c0140101c03403c0100710b04094003007065015082048600d110815903540c946049000141500d1422108a4070003003210714001f004045492500032240c13141c00007007400d0b81e001c1c0c0c1115069641c0a00f403141d214061051502428400c102d200c0c51465440c060395500d4030800c1d0040100094042c000c100100024520108000320707060410b0241080e04184981114500d500ca50800d80920b001000080c0c64100880714402d41b130402540701c13403200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 830718039 1250 830716789 830716807
    0x1a060301050910150507030201050c0909450f2d01090215041d01080a0b060103090b3909090402030f0d030f0b04091113020c070f291914 60
    0x320045c01583d00c40d90092200f2f403a007410090b4140a000da985903c0004880010310015954065019805030b5283c204441d141c0303000d2144803c501500d020030b80c1e0400308004101507a00300f15548612189400900864200c204071003016401c3c200610320003440008a244c0c0c86400b5040f20548ca50000d291025003d08811402ea0541c001c1c454440c048042d03c14850080042c640345904a0311940c01400411102e03030f40b80a11684010f190350b05142d90388070b810000c0b03100407503940d1180d5070f07000700c0c406240401c0610a01c4440d03c0c2c0305084140d00c080c9036607000704021900762842c0410984500c0d649454a2000074242185880004075503c00c5030b011038411681038025907003500c900c140401510645c0028071054840045014110719a4480d480186080107440103c101c0d1100ca0018104141c01020301d0502c1210380c4181507503880d2032070a224002503240502c00f5261140700c0c0403606003031080030609a02804418001810010484060f041d016200000c000f412507401e242c0c0d03544000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 830719289 1250 830718039 830718047
    0x90604060b01050c0c01050a03090f0f0302011a0a030f0c0b0c031213110d1506120215070b13030c1707060e120706050c040305060412031a06030105091015 68
    0x469054610300d00300000c01815500410448a1144d2401c014061850700000195010382c441c40c68142003640d070390042c2d0f01140407404c403004518070904500da455481814020b083d0b9800c2d4030144036807940411820f14a80d0348015113070407642d000c02c50044111440c10190403901c0b0503405445906130004802e400d404000c0003d104d00e841d50300d604442034032510b200b8600e51140d15070003400c150a20301c2040181c9441000c4200c0a03200740038000c0742c044010b003404182c0c2c07001c1c1d001604441c5030020312021440c0848074025400c3e408100c0c4e904240a5448010003800044c1070130b07045036450f14280303041c5481000300034a02070b04403034110301d22200d0304940e0416510138001178607060314141103441090030110b01000000300302d40c0e0140c1031000a0303d95000901d4080c05c60414001e04100000c0060b00a1200901c5940241e50a541240b6410409400d0351505101c1504845000350075502d1996564243c1c1d0544d20b059400e4800f41d5501860841d0044040d0800c0420000e1210261426584 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 830720539 1250 830719289 830719291
    0x2130e010c08040515070f08190e0a03022a06070303020705190b06030a080a0e040207020307060f110a0804090c0c020409080901110102030c030105010c080403060c031a06190807170906 81
    0x880c004032041721032a002c04000600301913a003800018103c00950b034040e1b21402d886600500e400300010b01d4030550a0007141161703101001c519117904159a800241901408242030340441501880c0f80c003201c3c030388140b4a09100c9222148101000305181c028103200e941030340c90041d48a01200c55040c11001c0b40100704d002400106d4140203843c1c005101410042280f84c11551300c090f044d428010741038002d4030000000c0d40e840d9045903090103110056541046600700070069500c42002c03c1081400c0145044000c0f120b914181c4e00c451106000102c6041c02c03601103e0000c7c5c030001c0c800700428011100d0240303000000e9449400c100f00102400901ca00802400009884500802c58010240707130031307804116140180e2610500041000d5409882d2441125200360401407030140c0f01d6075010100c40c101050f0800003640d5500050141c2c00c10040c00410190071202c00d41081c0d005880e0710415904501c3c000304114880d00070521060280b800020846d424501e50025407a28442c61036035008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 830721789 1250 830720539 830720543
    0x90c1c0912030b011d03150a06092405090601110a110f04060608220c060806030712020f04090c05030d1205150306010611070b03010603230106090302130e010c0804 72
    0x58211104240c000c1c0309032101d10380f041e1506050b080030a00c0641000880c41c0700d075034040c0203d13100201d09021f000406031060042c40c40000b072043c00c2c80d04080c12103024580a50b1107148541b072a001205110043e2021a0011200b81c01039030b440304012250010088081022485420b0301c40c020084030501242d048241500c00030900a1803004100956141e40f0500000c6040701010400f10801000c0044030310a1701c0010744080c05155450020343c0600c0c1d48041300164142050203c41e24050080c040100f600d00c651900800c041c0d000a0000c0034070036000f51055554014080400a404860b5402448020255034014401c0c5c1c10252508003540c988000302d515043c0002c0c0d51414100e60201e038160050000d1030a070b03090801c25030302c03c01841141c1045101d4510300181d56840700c00118081d1040303a03000f1520b150040d078148900c8082c00c011560307c80e807050040c4000d90788202101c044a4046412103044505000250014017105520480a508080503032400340e07000300545005074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 830723039 1250 830721789 830721803
    0x3091205120a1b03020702041506020708151909020103090804060c03090509090304050d211707080613270b06090c0a050a11010b1f030c050c03040302090c1c09 70
    0x5076400d41804111944490b03042c50b00c0803003d40030411507110b640036020191000e0800280c02056411945810b4101d5005031700580c00504140800d4100348111820200425500445400c00c070380b24080b40302c01000ca2140c02d603a110741c02c10940e8825007001d4001900305070401c1c0d84644901004099050b00c4800340c010540d007200028050900d64400c2e407240c02d282000d1810542040100b08000b40400404d81d00309943c11480241400d0000d10040180c0c05603c034520380000211643d90020320042010081c4134041c010401e0030340703422165600b083d15004001401103420300d11074400c4c070380781e1100c54141c5001d03400c0c00042203d24000a40180c1c030890350f1031a66922415a0842c5209869485001038420f225440c411400344c440c04051400d00c80004c074280301c80710041160480f0000e881c0300303040011040c48410a030175216603660b0103900d24000f840c202c0c5654202e6907910031440020700a00c4030000044190302c03d002030303c40e88100c281e01000203071003800144010780600b04d402d031100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 830724289 1250 830723039 830723041
    0x1e0204110c010c051c0917030c09120f0d050c0721030e09010b0d0207020604031a063f0309060a020a030f1704021311070c0f05010206090303010e070309120512 70
    0xd000c2c205440c100821005d2052840b4004103503803000d880e1401080301c01555070311a8032026524200514450702c064181d542e26031451808115422140c20081c1030301e0303080f06800a28140c17010404240841146c2011650b07220b205160b1352410781150b021050800b803002003c42d241911100300b0b07100e50b01903680c0c030306d042d1140410002c40500c00e2250810281080100d0700c90181c4a4005e40200c5000808135410b0590320303101c4542110605104104440005c07003045442e2410181800000e85185e013074105400540e00c075801c1030b00c1007002c600d0141d0101307281045c0000c000c10491303110b000b0250426803030346101200a55501c01c82c4504401041030b0340080380c5da40e44140380e4a80042d014280c4940c1540f90381e000e0007012010f943c0130074201c0d621003040c064107150800c010915280703c0d4180d040072524148201800007004d401450440d00b001c000c1c01142034000042d07074103440b5112aa061940c580c031100b50300409242070300400644c80503040108141c0c02038050400710700c0d6004083e4003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 830725539 1250 830724289 830724311
    0x20a02030d05131202010203040905070c03030e0123040501060302121609140c0c01060308030106090e011d0412020a150225030f03090c051503010f1202010203071e0204110c01 77
    0xe0b0203070441c1003520014400301003040e071300605800740b001d07401070066a2030310384c445007501c09403141100c206021a8020100b1000c147e803520446d03980050040007002502c00c003507402e50000000c00c4200840c0321030180814207020082d4050001198014101c04104401101007512680c06500020130900c000311f000510451038001c50801d0780c034443c1810529a40d5090040198002c02403e561941d030394480840040d104400650192041d40c64168010b031521000c40c0718090140c014100d100c1720600180700203414000103a4010b6808071026001200b054412490400e50351805455442e4603a0810b549000c0703640246141c6018003c520307650b0720340501100c107180300710704020009284465442241c0b0700c6540010000d502c41c00441d001507948000140d520710750786846003000b500000040040d00c1d0301d040707004010000ba600114035440e0b10780010351640034030031000c1c01e4107220401c8540e0018041c3c5806860a500500c208504628444071444039007212039044220f601e001d0345059 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 830726789 1250 830725539 830725547
    0x509060402093106090605010b04051201020c031e0c0726060907060818012334110a03020105070207080304050d140c0a0306020307032003040f051c020a02030d 70
    0x444060110a44007482003c00410b1a081003042010748250341d41d05074141c00500c1c58011039000b802000341094513541401c0c01c10070f11840d103c840145980c41000343c00442c400c0442615414445e02c00d414080305040c1c0015041440f61f482d40e034410740603060011449190958071000300d02d00c5224000c0d20030420780c020a80d01c10007600c0d0104d045d0701100b410041103204411040e8080c03425600c07444c80441c034105060948a4803a40d29610005011501100340483e130340b020340c010307800c44100054809000c0340c1d2041c038941f01100c264488840200c81ba2142c0101c07803050140c0c0d004022107612401d83d0500a000301300c151b6a000c014001d103040040c0080000058405841d00200019005451907640301140d111000c030030205030289a1555040d5070f02d1000718002107000d00f5025030f036868102c0c00241202c14202d01c0c3d403108400b040f07262a1002001d810f1b69440b5522862501c108492802c0403031501c1c1d00100c030301c4040c1e19106403d55800c0c2c0c0c04202441410b20a03000c803084c2081c0680b0583d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 830728039 1250 830726789 830726821
    0x604080f10110901082811221802090d0b011e06020601060f050d0b09010b070b0c07030e3a14010203070c02011b0506010e07020607020f210904050906040209 69
    0x1134006030112012031080128000c3c84520b080c04549425000c02001c0141001e0390304001182c25814800300b940d0741c8504802850344840c144800c1d01451940c00e106444105401c1007001d5041d03540d02044000032a00c803150051102c5d90015907440140d0b0f550600846000401009908210b0f60b405c0006080303400020010b0580e2034640300e40e00104410907040f9a03503002556400065030303d0b901e100d840e070f403640c2c031744540a00001e648860780c84959041068541c00040d1158104400030060007010950226401c401c01c00704443c0d084410303075001d840000d0100c040c25403103113030140700590b0800350982600c0800c01500c074800c007400719121059194201e0100311582e401140c400105130f00150700c2020310050306803404070380540303d101c951503103850180260400091607104400b0b000c2e64540401c042a80800948024a005980321a04e261a51500c07107403486100b85880c3d14000c042c403201d00f07542007500b000d0310810152400c1c0c646c4e07965403503054174141d01590783c0c03501052203246040b00700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 830729289 1250 830728039 830728057
    0x5010b0703020c1921060c1e170a110c0607030e0f06010e0103060e10020c060a05180703030302090406080a0b0708010611030708160f21090e150604080f1011 69
    0x550103482c5000942ca1405a000d02c5c10000f40000050260004800d0300c0380c814010382c80e0740c2d48441d01c0ca29000024000280902d201c080c09030b036100c15200c0d840780d400e80940c4603070050004078400d0005d54070302425000b200a2441c05001d07000030000d0035075241c2d01c405554100c040c12a4141c0c5114018a600d4a80a004281101140c1d600500200b1900e030440d00c9844480800c43d0341e000d40101da680126000404110340581006003444a031401e2401b071940c20182c85001414110512040c07155510300d1032200401741500400e00361100d56a41e0b1040000304000403d030f504640040c54a45550300f01124040045200f9000110b662803044001010b9080d01c040110b01d000c0b156112828590420340385202c884107401d2401000034a25203c141c022807017561030a42421054601a204045203101c441c10800c03484001c00c001c5d0649001107801240003c14000d000580342d002c560300348200d80040036180b0070030a044420700c0c2d0004603030415101841c000c1011118511003c0c40714411001d132 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 830730539 1250 830729289 830729329
    0xf0201150b1603021f060807060504050d020f03160906090c02070506070303020c03040302060c0a051515190302030607110708160302011805030609150c090108040803090a0605010b0703020c 83
    0x503141454091030b0380c00803a0340c007900444000001c0441d000441c0d00300308041840880c1c50701c104100000307080024101070100c5007000c606142c2858045202e000b15001c0c0644035601440800c41a51414004111130345401046402c01c2d075100c81c07429000d0040303882071120a900e428100b00c0803d00c04203858058680040800e840c1c0742c05500c040300a03402001c90011103001c04c03c00080180d5030080184410f140f810301030a072903d41400d0160501c0f001262141041d1010400c1121456181c25800e1303105204483c00d041030b9905800c406100e0703085410094141c8034020a00102541000701003422013480d00031107516903100e03d081a12800c90121001610034072040c00c0c401980101003840c040d26903602c140e10990390705d500192030f042040d900d55007590082254100d03070200c51100554002040189689400c0b00f440c0020041400200047c10008002c00030850162044c0071801e0015080001030145585581c502200340d406904100c002d841810004513944c240b41501c2444881d030710311 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 830731789 1250 830730539 830730547
    0x81b1c02010f0207120c06110a020a17070537030203070e061309080d150b0316180e0105010905090f0a0c0c0605010b0307030605030f0606010f030603060c0f0201150b 73
    0xc010340d456260080c5100c150b01900601003a4114a440304c20440760242000e0024146080d1003d090544d84039014030a41c2c00c0400d020025860fa00c0d00c2d5000c0f03800202000c5c034914030f040325640c20003416410295210061041030699405603483c031101c1615106442c0c46010380c9a440210020704a100081d0903401c101410095619014246a40810003800300d045400e8a444120221213181c01c085550758070220384030381c11490b00d104501c50000311035100d6105038200184241b203030000400c3c150340d0030007201049800c1481a405080041500c804c1300710b42986503040c02036003100900071140003540c550000202481d191030198000c0d9100401c1d000a07442d24003401d0081c1c41c41e404110188036425000c0302c00110301d03200313640c001c0928124807034482c100310500500383d480c150b22441c0f1039800010b41010006011a6294101c4401d08204e001240b0182c001d40203000303030b540050701d46842e1040c80c41362103800000d000110b0403254000c000f481c102c0c4031403074000c00c0c0902494aa04500b44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 830733039 1250 830731789 830731793
    0x30f020d0501141e0d020103110a03051005030120070c05060d02070312050c1b0c0307080705030d05070c09090c0e1504110a0906180b0c16080d08130c030507081b1c 72
    0x10040005c850040c940815502e110940b07601703180c1e000040345400079580384c040007030003142a103801000e070008600910289100c8102902152004042c0d0110400c00103109410409050003001c014075000d0b100b26140d051200da00e900035000740740260081101810030044074015840380c544640000c043c00340c01c050005c42c02140c1410f421110217054858000e0084060342c080180da002841e100f8002c014850505080c181030003c8140d014050150a120400010301b03211040301c15503001c7d480015084e401c40c2050030032076003d503205107444070281d01402a6141c7d62500300d00d9040b015103042c400d00c032101441c00040d100d0103400c0750015845400900046200d56075400003801c2c120340304c481d1703a40c80c0c28444500d50300000f0126a10b5000174041100140e0206000004014510150110300b1040e071010304100b000404051841d41c103000580104a8030500741c401440e040802c45021986402c59107546040b00c0150b4641c0f8039210004620314a02030610546410f80b041c46044100825 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 830734289 1250 830733039 830733049
    0x70201050c1c1409011a06070206030103030f03090215121506090d020d060510081c1403042a091a0a06050c0f0d050714012a030f020d0501141e 63
    0xa0340324504868540c82c2000200f00d190710110f0207074a80f2000040ca51448210845000302d0303c25585004038010701841026039540010b90f41100d41508000440240190342180100b01c1150000c0d806242c403d4880d558038907400103014a0b60300c95041c0c110783d40740c0d22030310f5151100a41c8003542c01042041905054100104035208952018061034080c8085135200c2d070507101c1c100c2c0d102c0d19a001c0940c0420003000108079641c200069400051000ca0423010300410060210b840d8907142903002020608020001040c2c8400b40003c032500c10404406d405103011410461245545250030440002c240c3c584055450317082420003002c80c0740581c5004400c1c3d1b826080790b541540707940914101c10b00103800500c40803502c100d45686055941c501403900006c0320041800c51103061b8076000056105942c0e110820007850030f02000c4051058200d84110302800301194413039042c2e80040354140d05401d25401c0a0b044e90f0011800003450f0300a07005010b01c061000f10040401004072f00800300a04203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 830735539 1250 830734289 830734327
    0x40c0302060906090d05010b030607110d0309030e040f060609080d08012d091b0c1a04060e0102040b03060f010c051011120103030c0606150212132705070201050c 71
    0x1c05041c540c04c02501c3c070001520000075040c29626651960707500e000600e02444820342c070807440c0c00d11020103442f0420761a51040c41c500360106042c3d69850b024141401030349110b0041c0300003031040c401042800c15007c0540a24824140820080140460b20740e8010030f00151701001a43c446d5803e03842c1c400c008922424480581507146c4020b090000d014070540605c1000d81a10440070031900c400d0a85180c074080150311035800c0008468000000078000e404502c12803840d00b0724804243c4483c2004e800521404840580e00c0d0310005001803070035000c2000c1c5105100c2103e105d04020081310066640d9943d003640242540c104d410145c07681000c5c0d901200919469019860400c0501030044034408000c0c0c0081d804a40001e281008102d00742c0110310203001c01440038503500d1400c05000cbd40c4c4409813003941c2c20585020a402d0b000d22400c41e1000000c107107409000c0c1c070610658840a0000c04035007008414a07003840000340b030a034014081d56020702e010031805840d207a1041c11150309040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 830736789 1250 830735539 830735557
    0x605060412030e0a080106080303041a04020f06071a01060309020111061513061806171605040b030f060f090f120a0509030a020405040819030615032c010504030f0206040c030206 78
    0x10220901245d8840c00744038640250801e00d0040da920b05160424905224144401c076141c100c000c802c000040c1c6480742c400100510980d03003162507201c145480405041d464541e89031001c2032400000e034046c1d25811201985000380c0301c4e80851080340f82e005031100750480b24100c90804595140d0317000c4c14000511580420440c00000d455500e0361000210028a482e17202c104544a00e4280614000a8004102d8a003c5001040030a0402c0d9448000400600c80c41e481240d50398a400500e4030140900c90491a004e4203503800303440c014000038121201a502c5903124441c0d000c0208038a800046c240c001c101d0012196800d1224050084403994003103601150503016001702040144c82e540280d5004502c51411142c540d81d002440d080c1c2c0c409282026410141070900030086660800007941d82c0819519020980c0b24030301c01c5140e864031010350b0301c51200d40b1405000349100010f500103070045100e035490f8007600c6070401c8100c0e540c010980b400303021070b21080d9040006152410041551031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 830738039 1250 830736789 830736799
    0x1b050f0402030f0f1e0a020301090b0102031c020d0b2116060c020907030e0d02010c02011104030c03020607020409081c061d270d172a071a0c0a030605060412030e 71
    0x2005c0b031301c1c590440c058030907080f515000704c010f200441140c020000b0719a428801182410040d40c3c0790040d81105a09000c9080d03400940c1c0403480340c2603003041c060020090486041c110390614100c22044198806890754000c500001900201403180310080b102296142c3c0060000c0b038003081401031000c0c14000170306955688040030400c080c023054210304440d400001d0802500b1a002c0c0c00d50f80700804281d80f4a0040005000145141002c4010b90f80c05039451511440c03184040b4006001c0141c004e8a200d0b000710b00c036800310302c415004006160184505228056440024040c0d20301184003030210102c10400003401585626180c1e807400401c8448000388101d44500c03d070800154031958000102d4444a2206a1412104454100500c0200d120751029000c448070103504200007440d22103800050400144030413001d9030a01e040c2c0f1096102c43c01d007041e80c00001d040c2c0c13003954030402080c18842c002480d4a044400d070f60448000004a1004000a65041f104d000355603401036404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 830739289 1250 830738039 830738071
    0xa03060f2703080f22061d101512080705160b0a022a06181c02030d020d080606090a0e0c04170f030901050d091b050f0402030f0f 57
    0x1d4414103901112400340d00d01c00085440703080040c4004801000381c01940c94103001d00079040324a45600340d02e42c0740031100760541da00d03e18008015100102c600081b424400100106c41c0a010845800d082402031041003a880c07041e40c00a0b80344611311400d0380740c4007810f403140041000c403c01003954900c10b405484203e1070a50703880010f500780780c004044003c80418140c0c1100d804200211101c242000c003208a40c21846072805244440314041340140b101003002103c4001a00c854440b2178401071040e1032403065a01d86004000310b503032059110340304038002241c0207800840d10311405502580c8440031580e4140038040f95a010708400340d007080b00c040000a400d81c0c00c0d01050b001d04806643c5503070300d6250105101d2403c4441d15022015008500000542040002140c0080d042801c20641315243d8142000081141d0b0307002520f0310345945500103404080c06418411b8a20445032090340240f18028001240001c4a60206020140c40450b481001b03681c009135101c800881c8008078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 830740539 1250 830739289 830739311
    0x13050303160527040b010503160f050f03150a350a0503070506061f1710180c02060108030a0512090c030a0602040e0610121e020c07081b0a03060f 64
    0x283c9041ca07943c0d1421030003c0e0740400c0d24140c0101c03aa0030009203071590440c01c5c001b501103514403200610005100c14544140100390242007610025109030700c03482d44a190a080c0500c03540c0300c2034034042c400d224403038011862040080003140c42c105980480521b10a034404446d408030513030f1140009500c00e081042000540800c028040c0d244120054131070f50405200380300e4002f05a8600ca0700383c601c10b010300b5180350b601c0800c81c0018040c1c85c1c152542c0f0340b10024500203200315138010941074000c0c2a0b540744a6a6660418241024580c2c200c5125a98402200d41c490040c10030b9a000184200060383d5201000c030310b400e8111001d942a03c400c416208002072402280c04001c171581500440d00300130074188171a00130b81c0800c003074038041460000090001c103080024a1000a025600d080b0f000c14104001d81e0910403170703e408011540d940345850310f16950a010311401890341b0842c0c002108443d030408058200b524050703c4580300130b085551314170240c100e031b14050803000d50b00c14100c54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 830741789 1250 830740539 830740567
    0x209030a0804091d0d0309020f0d050604020907090f170f070609150807051902011d030c010506120a02060715150806070305071b0201110703030314130503031605 71
    0x40024840d2190a68a070b14001005040c1c80b0340d0000e000c2c040d4440100c1007030070038022480030a05c5403a0b1a0010301e42515100107121002d100c4085a0850134081c0410108100026010700842c000c840d03010081e81c3d0080100d070409168080c2c3c41e2031040b500400c2142544055180d01c102e1440c0b0240c81107020021840d81c41d103181c40c7d02a00c00602c0c0702508014a100100361001c84400900d403100c954a04004054021700c104504043c00440040400714014400e500910000d40745449048021850f10300c141d070780c8d800c44102d1100a51914011410b64603083e403014101c000000c0c080c5c64040003e03001c100e86504070800a8514040c1e00c41c009441c025075119240d116041242120902414945603501c1c0800080083d8185031404d0103001c24103402c400065040001070341c0f840d01c4c0100314401200c0189c1ca80548010760f10801030007104040c0c0503000b00c0d030608070441050400356109103441014013510b01024102d42c00030400314a1a107170a90b10b466451246041c190f15051010a00300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 830743039 1250 830741789 830741803
    0xd0c170a020a02010f020a020612130c060e030c030c030d080403271802031b0d060306021206031c0c110d02030307031e051806160f120f0c05060a05040303020903 71
    0x200040c1c0180445200f10340e00031003c0c4007002c1c5c45200504411420303034003280640c40340c030400384010b0801a00064104410401501440d917010340c424140d995a040c02400e614102810188640612038000c002c90900080c0c060b12450000e00502e50450702a10a480e0050050815020404650030070111184a0b50745600b0074142c4a040c078800d28500041c8208000031019402d070064010424010110314544580032280d86101d00c40f0b6540c0780c8031300000018905036000504082c004900c40ca4030079403503404a40f00f0002901681c40d00c28150001122043c414001c01003c2280d01e0400c0000c034041540922412001401001200285400003861500104000c5000460050420b05007074401c5441e62054541418042d01b4610900807661102d541b0808640c0592408075101640c80e00d000301007003805400011a205400c194140b42c58103880410910001c14910000f078081984140c81305c10b84160420301620071030316076908140162002500680405800340481040e60390f081c0000703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 830744289 1250 830743039 830743057
    0x605040623010302091522150f05040606020a031706010905090a1a0102061e04080906040e040b0112020904032d0201020901091e0e0408130902091e01020d0c17 70
    0xc0d003250f01d10310400a0401c40102008044454581400e81e1a2030704c020034104440080808131000340446003540050134000c2007000320007001640042c0030f0640c0d0a1400c191081030341e050240c0380d180e8030244c0e0303103884162006001540720203c80d410848002e41c07150300102c05143c1440c4141e65a000214036107070036119210b182c0e54403117010301200b51900582020386800c0c0045c10140c58150048495804180c05840d1041d5910000600700242c2604880d0380441c01442c4035107a030384031103c0c0c04041c40c040340e040b15444510b03800030601101080000503c580e0003030001405648580d0204e03903014405846c40f251140303000800855601d445524210704080c0e600040c2c503181c071540014008000c2c1d6210203142c40360082c00da40112100070f03c1c4030544085490031220703500c0b07a107414180e51090b00c2d150140300c16003040c007240c074020b56001400d1911341140e9104000c103c0001254049000c011028003581c0f0120704010020b0152014130f9156020f00c18a61155100031107410003507002441c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 830745539 1250 830744289 830744351
    0x750030d0c0e0d03080105060d06090e1e0703020904060207080912010b0a06050c0703060e03131e0506160b07050c01330b0a0518040c0c2d06050406 65
    0x2658565020040c600d14002c00c4403041981c190325100500809410700860f401b5140001e016030702d141071a04504014652407001f0041da40002c060103840c0d03a036490071142c59050110301d0350408440020407100741c9400a2404540f40c5481e590341c00254440c41003112000390a10403103801d66100d001c4812401060800403401d0066038040203520303941d5400032014803109108034448010001481025a46e20600014449140340038042c590702600d03100e14000c120040d004145032410328842d03c1c000d50451400c0200f035407220100150b074040d06c5455540c0481228144001c0b070380b040e84050300700c405030821a240003000b20001d42561030140c1441540f802142d8100d8034580c2e440300a20002c040d250b103880b042800c0030b40344009486104080c2c41044400f00b40c4004282d0b030b4034149200d5960040080006903442d80d4080e101c180450001c0e03503500d1161401c03504041d08030b902c0740c0461520861600040300156110802840c01074420f9581541c1d565800c04040a161440d80c1c4800701708075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 830746789 1250 830745539 830745551
    0x30307200123090f340b0a1404031a0c0d092409030522050405151e1302030c07050a0b160f0e240d020750030d 49
    0x802070800e4801622020b070715840036507080040000030501c900044102100105281c50011711001c0080d5541140131030f0070003040d0b002803003103190401080c14905903283c0e0804540aa01c07014414050351001402c552081c00900d001c0100c0400358960080c030700e4000318240b47c2c000100800300c2d00031110888072201c074205601d01d02e0200350040240001004000e00501c82e0b00d0350020014012100801c0701d41c10108920f4a04441c8100d81c0405014003a20810042ca004c208800c204000882454000d00000c001001c85046440b610b80d114030300680311a0101e04120203e4000354001032001030180790500018001410501c80c8005003801f03051401c3d66420650078040c503280403940c01030240402c1840d02460150002c1c41c0702403d040031103400c6002504c0d07051030a854500300c03071480c045050029481030301031010360103845040d004040d43d048203d01400a16036250025540048444400b1f807907020702e00034140802980ca80c0d140c5000c11006d01c070b03100149190040c0d9000565161184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 830748039 1250 830746789 830746841
    0x60303020705150f3f090c01080c090312040609050a06180611031201080d09120b16110d0e040f020307090b0a0c21020105010b0c0303072001 62
    0x120030060541110f4240c80311a4420040110b403107200f001100c41240840d00c10101004151442c0c1e0600001ca40c0840b40c40b1851031000301d00841c0c24020b0160b11940f00492849000050180074110b410384601e425a10f885605044030f41181c0c1c1d200c0d0341441450003418081c946980504010140742d103510680500341402c0102c48005034009204004a0048c4610404a0281524101c0700c0c18144149002c603003310a40c11407050001c42c1803d0002980000f07811100001c144e02c0c010b42d00e03a12000007036154040300200c510f44400c003421000e66079000c510307080c11140204010032b0072801c00901c104080c1100b6400e00310b48002400c0030492a10302d00e00a42010b000305c01c00038414043c11440c0d86400c0c1400341c28203400c0c4c0502c011614000c21b0030303c0c06501a107030030141c86802c038003400c03061900c2848802865030243c07131001c0194203080001546c1d2088406440c42210458051810742d501c2410840d0304416090780385603682c030b03150400c0d13035015000c0c441c01010222070030381a0190060700c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 830749289 1250 830748039 830748043
    0x30705071a222d170c040513210f090e072a2009090715300b120d140c06090d020f1c0809120d06030302 46
    0x15a020119040c0e42076501400c00c501c003011100c2e01055400d058000381d41c100820700c40740301d0581001408078044506140540d4036100c08400078003083d10012000e540750b44070240f0221581d601d8482c44d92100d01110310342c3c90a0382000e41e0050041090344154891a21040003d50b204401e00c001950a204040c003290b80c0004920500c0780c060501300307869481c0c16601044000c00030300210401055402d40e61101b460030006075070030704110480c0144c5545904010501c02482d444013802e10300513400103e592308104220911a40e114005041c400d80303019802194143c0c02c0d289402048400c4400d441d584c580c408154030710540e04400a5261196020712104496806400b40d206100e009845044014001941558004c0c54505420b80005a00071051940070301c2c8444102030140800300442038000045584140304203900711101000c82003d6907485420000304640743c03400310710715807481d0760141d4174454000c0d030f200c02114507092019200c1c1c0c4c2c044d080041c1c160380740c2d0b0f101c12080090680c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 830750539 1250 830749289 830749303
    0x1804050c01020d0c0305130510021f060302150d02091819060f0b091c032a0b060607050a061a040c030b1f0c0609030806040f05131e050f030705 63
    0x100780000d2a500b5100f443c041d000c81000c80c0000e041203000196200e0050050300300d54024840a072240619041c2d80901039112110704081c1c1813690600e6900c0f070b000305d40d980a17140490307030050100e29140c250250359401d16400440c2c50819150200828407054440300c03074081c0310b010340078500141030900240ca0f110382c0b104024281065400d00409008a12510641c48112808103149587c3e841d136220208040e049494000c1c200f0420110080c018150846000c80c5087e4054420240003010350340c0000c20040e0f40b0002500078450800040c2140c01c0050042030124080d8048601c41043c980d41c1009840280580740d03941506d004141901c0e091600544291401030304082c040b200108010500301581c4040440c2c1d103810b00302c01c40060500440b03500300f0725600603500f8019520a410007411400c002d54034a40201d1408460300800c40705441054020031114103140d56001ca42d8444101ca1958030040088829040000c20001581046104040c01c0c034100919101c10081c1401418115 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 830751789 1250 830750539 830750563
    0x2040c02060f01052b060e060105010f08010e040f051b030c010e0f0f01050712030209180702030d050a060f090e01060f080601090905010b060301120b1005010c021509180405 76
    0x2005500b40881d076850700300c100e415620142e50411a00000b825a0b89a070301288420f48a10f640c1c5211141c14031200360014283c0c0c005075030440e00140d07610801150310340000360107100000c0501d0014000420b0710f030a015000b601828401c0c00d1800541c81d90b90070f2010541c02c17101c002585000d40784441c101401a00d2030102c003401c10f6100d004107800800c11500c40c4440c80c0744240b02c04100001c01d42e00036025110425000350740540c820a44010241c0294064101e4900c00e110420b0420700b80741c40514107503c22466580514100302203054810007a002c080c2c41d01c0a400e81315500800c6c04445c402c0b4010080c004d01c8408a2015807003000d8508580007034015408281071a5020301070118000341c000d046400c2000000341d4501d003810990700400850420f1a4490000800000d42d03d2400c03241c00b200c0b6008c0c00020206440d05105603010b1b80f528800d1f107011900307030740c40c8001510b000210030720440a20282d080c9032001c0d80e000504500703403480078042a00b0f564828032051020402504403102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 830753039 1250 830751789 830751793
    0x2e050a051302060c0a0507030b07020f0304060504140a050301050a0c090e090303060d060e0109030806090721090f0602070c031a01030201050702040902030f0601090204091a1f05120a020702040c02 86
    0x42031800364803011240700e81c03010b4003a01c1e000a401c01000c904025158609401c40300350343c01c41c0d840380303040c0800035801c0d070b0360100500c5400c446e60003185000c07048400712003440e00d403140f80c035140c000c690365025850903140b40c0c007013040680021035413001e0284a21840020400003024862840041c2500009400a0080042582c10006910000801c694020008440c131b0000340c815441c20030041c00b50b801300b41455500301a807400c10190040c0b903241c05420100d480a0150b542c603082115110300205011644901d600115814a0460303441201c03051b004074440c586885240d21050160f9100751000c9410019040d0f04205012a44090141d01103411076590801c1d4519000240f5501801c40040e11860344d2b4010f840c00c555040003010000c9540c4415103c1031340c0d507108201c0003908a8460b000820f42003128100088104d440d9120075103d0042951244100c0c422015080b001e1000c42041440010840d500d01201000441c520425040030090380e02e00303144c0305200a840c0207058034010744d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 830754289 1250 830753039 830753041
    0x10320030106141c0f030503250905010f020105070e061b07081c020307030c1b0905180f070501051c060e0405071401030c08041b0b0f0408070e09120c2e050a05 70
    0x3d05c40c0942e1000c0c8075098038049440351110900c0003d4540e034500309080c103a03100c3c2d54811030b41c2d8004444c1e4080b20403d0300c0796180400c81200590a950302100c2910001d00d844000100c1842c1140c00303080c0c140b07014007055480e400c00c90074079440c003022a04005000c0c2d1100381c0c1c107800015030380f0080044404034030240d81040c4056802500300380e18544000d003480c0101c442c12069101c165040c0000b0b203280031050200b4103168000d280148015460b01955010b150101292002d001030384604407241079460381d00c0d10305007603040c111000c0180032601290340c44030b400041c0c4603204010030340141e00410150108615007040000480c044012441c141400c00802814803500220415842070300a00c40c078030244d0300c2036403c540e4908190803074440c03210b0105001500d1314014024000340d42100d400c8688007500c0b495851701d6000210fa118045501000d8071280020300e00d03001e042c4021640d403c03200c04095401c05010707a001c01c80b00607001041681020744a84200780261034003c00211410481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 830755395 1106 830754289 830754293
    0xe0105010e010f0335270901080d0c060906060b0a3f141017010908030403320705010b09091009020a1802030601140a0206010320030106141c 62
    0x6c0013070001144d401c5400e141d0115410f07210100c00410313403c02d00c5c110072550b0740c031100b408486180d200d0b40da0b00c000a016000300c40140008204442d101c00c0407040c0142040c15103a2400d1185011000502500483c0c41e0078072a9400341b5910a040e210081401401400c00070007001c1d8440482d1007000620000c40d010b41040d540d12011002000040c481618280d50403124003401c10b030740410110340001d004034140724070410f901c07100607545c0317451521030140f21711090380244071608000340400c100300003071040300240b190032542e150761800c000d029559240d440c0042820150758814581080d0b54541001d0320040225228400d10101e14801220103074109031040760119428885c0c0c21540c9006405584492400b5401003036281c5c03850316201079103111849401802a50440584c16a4800303008a0014011207688200407082c220140400e9502000105100030100b880400c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 830575539 830755395 := by
  have h0 := BRFrame.cov_init 830575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 830575539 ≤ n) (h2 : n < 830755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
