-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4624
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:12:52.631981+00:00
-- url     : https://prove2.me/submissions/d6ab221a-6124-4979-995b-92324db00e54

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 831474820 ≤ n < 831654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 831476070 1250 831474820 831474859
    0x60c0317070203090906130c121424040e030a0314060906180a150314010e070b1605011805011d01180201080403050c060106120e010905030a0507020a03060911 70
    0x9104010742d501450604114004124000c100036002c25408101034030b01c1e90a10300b20313110341080c58801d6111358042c41004100e240648400304074203010080000b003000340a20b4402480f018401f40031000304018242440020020301c00740c65900000e2201140d03900b4440d400d6402004103415802100700c2c541d41c2c60b010001520411180e068002064034828000032804000715600301c2c400420104066a10003610702e21456298000d0303601c82c462132501c00c2280e500b0720852502e040c1900103044401c0c10090420f000f407045440b098110284d8a0700c21080c40401e40c045564440e0303080b440c0095440d84d0a01038042c28901c1d0304018012100754442800c5403051180c8106899000c01900c43c20445030019103d2140040c029828013001300560584120180310040c00b030b00e01903c6856989200780c2c4801c04a0708885000d00305a80340c080e001000c14400010340b401d06009117411a501c041510100b01400e0b650b91005224906100300d00081150626048410000507906018040d000213141c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 831477320 1250 831476070 831476117
    0x170702010c031404050d20030304050a03090501110d14090a0f0e0601170a020a0c15090b0c071a070e030a030905101d0909031303260a09061b020604060c03 68
    0x240254007042e9000d0105001c0e1f00c5500141290000c5074060310b00c1d030683c01e401c55004940031100c507000030150318100b5400004002c06400207182402c1c4524a05140a540e001c081d1207800500042e030846d142d440c00c5100c100c0d107506401600380c3c144c2d00d0303480440200a10740d40c0182404806c104000680c01e512403c00e80210f4900d440111440c0c1e164081003200030f5204005100400408041c11000b0602c0e14080c54100300d026a00010181154103100c1400100500314100001c8100602e030080b5400d020304956110981000304599120342c00c01f658040c52003222140c2500862441405142d0400c1c0c2e50000c4900c1640d007090f8100046104a880107540007018120030442c1c2585081410f040701030b01c0d840b243c2441100d25121961004501c00c400503032013140d0002c128807261145185021201454403145c1003240d0619070402006008075010303020b510100001d240c3c2c40d0304800d00c0c80100000030741c0c01904a039592502c405c030081414420034400c0e000b1490283c880215040d40810f01c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 831478570 1250 831477320 831477323
    0x302090105160204020d1806050a0c0e04050a09050a050d020f010915150f091a18070807020a02091e071e2006270304030b040b07170702010c031404 65
    0x2040c0c9424102c168403035008507038400581e0450b6003409000100c00f01481001504034250880d410364841520b807180680350000c1101204500741b40452030302540005028131110011580800da5580c1d00410400a042a0802074998410803089009006002c030b49002501065400e40b60555001e5420500741e40e800307a0010141a2010714184040c2515445015030b081c401c40701e0042e455940140101e0307024190418210389544100700414810544004031403460f05a030304448243c060f010980c03100300c0040410082c049036600080b0310b50f209020500815500800e0b01c052802c00c8410300600c840820540c40b245807a580c00304030454081c02c1c00c0c03811515198400c00750007410749812128003240d2000082018089000c00c411004203000e8180704007892009540c8800c407c0f0b42a4150700c48002188803281c02c00c04c07080c4003040c01150070383c1d070003500540c401555071280203045500841108d04020100012401d00048036819000402c880c94969070611500e00710f04800103c41505840 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 831479820 1250 831478570 831478577
    0x20901091a0313210914011403040609020607052406061303060c0207091b02060105121c0c020409030c3e120f0d2006060d050c030d0801051003020901 66
    0x5903000c0204441d42510b10300c2007600d10191100200e41d061244c400600740d07400f01d440e0907000c0c09044501c4410700e0b0040800d10700100a28100340728101180300c0580042e02951f140c55203070f0107541305c00085804055001e0110350b0100c9156411000c1a00c611010150500003200420001d1801c0c90035250341ca081c2c0003002d0821883e41d99101c008000c2d401910040d40a141000074103041c262081c55200e501c1400940d0854015000c024100041600510310030104035141c042c45540c006007118a0280c00709542244c1d98000d40306039107600e40718a00951150030081107404156002c020540003d100700342d21003a5031100d081030308000c404030400341c00c0003c041c0d010f041302910b203813844281090301030b01395180f00c0000e806150600109089000056210700014481b1513402004c034840f0f01d81418800c0c0401804511081d194072019000d03521400700d41c541402480170520402003c10300080403141003007ca004c0150000b5400d109081c4a21786144600c1c0300350340280220307502005c0507034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 831481070 1250 831479820 831479827
    0x9020f030a0c030e030d1a0d1707030302160f020a050103271403030915010501090531020d1406041a090901060b0307050403140a0b0601030f1806020901091a 69
    0x5949401000b800500c28205a00d8510850414806200070415070309600c40200e001541203000341075541941d10500d010f034030340c21240008030340b01000c900c68141c1a10321441c2e4590729030408401a004800c19600b128105949210400071080f81d10801a8800e480c0344070499950710054003101c05450080c42c0c409444004420f114680f0180c41c2d41051282e1001512060403120f5140b4540003100c0c0c1000d80da00c001d100500b002c40448425006140901e0010000c03030a01c40410301c1c0b050300b0075502034080714884404000c40c9407a44000194201c80304110740b680304031a0342d180070b80a410013507038011881c840803c0050031300e806410800081c140342582d91522140c244452000000d08a070700715580d4500104d03046c440c81000b94040c0c021641ca464545041d0700304005040d00440780ba5140760f0254040000050b81e40d01d0039a804202428001004403000c6001005001c61050754043c3d4288070303150800f0072500742e001d4100c40c10701383e0312151026117810100510751b41280140d00c40c0941031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 831482320 1250 831481070 831481081
    0x30c3c1406190b12060a09200a060503060f180604060b041406090d0c080622030801170111340c03020d08070212070905090c09012102090408031009020f03 68
    0x75002021005400f81490390340446004c165400d000c0151010b950b15501c0300c0840060203502e5680240d0b205042d40c2c0c0072010055100003030b503c008a0700c526010f1010200c002000d582d149100340100c03000c09061800703444003440c0c82250110080f40c0441c4a1443d006010504055480594050780d040361122410b1240442c2041400c0d08541c2ca030990050300d2404001c00984020020340081c076641d0002c15507400d10303060345510300e502240040060304000032003902181e48040520b0464141c1d4049000321060008018050003000702500c450316400540f07032510710741000b0101205181200501039071900d4004200080c91181e40c0907204411209050001d89000c5008201d028483d104403460240154080303100c0d40c2c40242200043d801c12130040000070030030300800c1d51152000000d4503c0309505e0000030002e0030f040c0660302050115200c2c5190800f803e0480c0040e0b10380040210a10f860b09290840050340215a0505010050000021018198000d5400b05005400441c1c29035a4a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 831483570 1250 831482320 831482371
    0x60801230603062d0a060f050706090305090307061707022a0a03020a03240209010c03051c050c03100f050d02060913050106050a020712030c3c1406 65
    0x1500095020070312000e00108980c40525650411000d001c0d0f401e5130150b28070400520b100b4650095040c031804100c2d031460154000101c1c0c2c0220b40c0f002c00020100524102103566000e40c10300c0701c2c1c05200d01d000100f0000c1d00510110b8400c04403103154170359595090412602c414600304002c59105060218403030341c002c0c09143e030000d1500a00b18801c45940d80d00051680c0342d02e03500642e0319000034100c51a8000703141014805041c103458040d07107880b41c1d000008240c40d0880e400030b0208240400e40911040c003045030304202c0200e1080501041c2801c0c2d1060b00541e200351240358141c0710400e40000c18100d1000c03448100c41d0000c1c40034031400d0035a024412668440030340e065101410300c940e9444044148240b6020300440c1e5209c9841d003160303120192405645402217031810304586039040c00242d110035003040e2558461030103120b5000690a80700c03c40c4c0449003c415920aa1075002c400c0d00e800c0e0030400f8402e0144000e00c40e440072080c100c54980c40140c5914512051001c85540384908 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 831484820 1250 831483570 831483577
    0x30f10060f0b030c0d0b1c0204051803250209090105011508070203040611010e070807051206041502090307121a0c09010e0402090604091503061b020303040b10031202070608012306 79
    0x201040081503110041e40001c01f40400d41c040c51703080301d44424800007541080d1045580c0420b1040900500c3d1003200c1c2e031295a40145456005041400c024800b112140690b145400a50103011040e841c00c20190003400b03400c2c01d00400c0e0a0394200c81c000002a4030840d0000d0240e40c3c01d4024518003070030400c3c2140d0000c05081001c88945d0ad4030040407400408002d06802000c00c00f0142110b60304050411200f41c2c050950840c03903a102d06d0502010844400480280803031040c00140c1d03601104004c40d0400e030b116849070301403140007450b020601c01c4200d10100c0c06603c5c411643c00580d5040225031080c050003c82e5070000c0e4510142c079106082c0703a802040e210100420450900780d4401000c400e44403942402c843c04182400108108075003402094228585051800f5080384540f40c006d40c4d9000050000d031040d40c55030041040c030300c0401c001101031504400103010314107089401954689440c0318020000b032180d4000a50a03400405040c84074800041005040350034a08000307141c0c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 831486070 1250 831484820 831484837
    0x10e040201050c0a060b19030305161a090c010f030c0221042102030d03060509040b250c0b0108010501060207181b120c050301031113060302030f10060f0b030c 70
    0x2400c010880501c08200304159481780b280d03d01080b000c10902c28426010040c3c0c4000d088803001005c2400001d4000d01580e155200c1c21070341d10402c0070b40d801c1103110011443c035030030304904113801840244040810300c8000b4040a07211900107c41182c0c0480c216030884403004016000409017401410548211951005205018904043c3c07504248854201c0d8520b610301e0400e604d03407644003142020f000c8090043d95504007040014034003000b1600c0358400810003071103181d1080004108184504070008100d21030340660890400840b80501f0032007002d042500c0320701c88800009414601401900d0584045901514410f86003940740355005281100c0c00e901039441d0242d0b660500c44540d581c3e2484000303540e401c0300044802124074100c0f03100c0018441000000c200610226040500524144c08181e401000c0c03040d4840c04240104000c1d00000d505000d00c0400f10179034800007400100c03e091002e010040c0710368590b100003142c4694822280c00079030a00001d44c580001c070001e0510b02e07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 831487320 1250 831486070 831486077
    0x1e0e0f15090a2909090f06010e0403020102133512130e070804140303060105090609040e0d0917010b1503060a0b031306060e100302090910060e01050f060a0503010e040201 75
    0x10f4000d0003180c054581104901c01041e0142d00b004050b610340080ca0640241c82d02c40a0210300040e5a06281c841c00140900400800f400b408070307040600c02d50441e12440c84e02c00b4101c084540f00d00d045404140392044d218407103c0b5804c0c40e0b903901c2c2003141b00c0803200c50924005107600088419405071a41080440c101c00c1c02c0c1c2e14400164a03495a0a21881034102e40d442d50a28a841c1c60010301b0a8403100510003240c0c000e208001c9a40d80180c01ca5003c0003084a0041e1254a80c90004010302003d4420319014010b12034101403180e08210702d1401c0c0e565040903450540c0345518820308860f503200401d40e0001c14800000511800440210741201000d48508801c5449480303840c1d2951098501131b600702680d6044405114643c45001301501640184a074941403504060440d400c0350f0101a02c078000c0b10000c47c8011208000102001070002000d1007401e90b0703141010380c081c200740b041900030200010320360158078004048442103103058480742d041d0707401c0030000c41440314010300c201d052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 831488570 1250 831487320 831487331
    0x5010e060d02070503031e070c022412042d20030307050609010636060f14040c020111030f1314031905041514041e0e0f15090a 56
    0x114070380c0303000800d2014042c800a55032818142005103002401c00e03141e00c90b40c41d15000b03200803103900045120000790111a401d0400c61500840d1000784800d149403007007100b0002d0700000740f0025a401603c20f50055002100da511000c04c210a100210070450900c0e0804885100015203209039500e00303491104214920a2684030100713246138003c2c2020780c0c4c40e52000d820005621001d0181802824551100030340302c150011600241c050520381c40140b003001d0038146140c0c08440d0784003100410200d2219003000381d6034a001c5680c0d180c6220054003850811001c14105401401020050012044400d04c0d41d92903038010060000064204080c40e1501e400700c401080310100e0302101c0c031015602941c0c0d91720700b5083d0550810040c102850600800f40001c228101c80e85507040002101c50400341e55665440503120240c0c45250001900c0440b4003510310254407140c070280054a0300c3c0e01421456465a0031541c9002c0c200700c91044036444007035502c0307050b42040c0580301c0d00050301a401080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 831489820 1250 831488570 831488587
    0x132090604030302031309090803010509060d17070209010e0124021009150507030c0f2d020708060a151401020102070b1501022802240409020301260705010e06 70
    0x40320740c4140c2c0240c3c0164404a00c0c8800440c001c070b184c01c0140f9400d90200018541360b03031006c0d8180030501c1454466020381001902640f09c03030f1004151070f6030100d80c00018015617552400c440e04582010390294280c0400442c48220368446a41a90441041442c15050b030704465050142c05030a45402c6000d140c005200c030358141d01442681030701c2105440d0b15140018013140446800401c804205410448081407842c0c00031030303503c2e03c010103141c440c10302c2c41513040302043d40c29595230a110300301150001c00c4500e50b0201e07a20090300c040314161801601c8214000040d038030118070380d215400c02c008003084030818131941e206c2d0908040c0005810a101c03504c8134916920b0446141000111948491015603418042406040c0d1104280ca41d000d482180c812810864210001d000d03094100c40c00c448840c42e6446072281039104041940d0751078451003010007a400a01c10344451803210303000d0b444654120801100d4100b210380042110900d00030044401c60400ea400f01e4110340b04010046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 831491070 1250 831489820 831489829
    0x210705030f1303110301180605090712150b1801181107030f0e042315100c0501060b03070518061309050103020901090204270b040c020a02010e013209 66
    0x3089003000000d00b006518605041000d49144903c10388264506080480e914400181c000c145a0f042900050700380d84401d031440c504055a0001040b20003030a290a08004401d101c826900380000420703c0603094000900c50340e44010210340c150707000da030001031045441030744124104402e110404582c10f8000c02c980405070384843c509900040c5644420300c00b184c1c1207600003004e04000e0b60100400082036010b168001c03061003c21040052580c0844d6a45c1c1001c0d40000304d60740700070300300c0040074262807015280c640a500100c0d040c3d400e0460000b400c4c442101501c2c0b240d0ba0688800f80f43c103034045413440b001c43c4601c01d0554411418842d000f41000c8800700300707029101d42032000402e541540100318020701c05134014034030386004000c14040c1d0724402221551541d070034410091110307460207040c8003901080808a402134500f00d8066030780e42c2d0000d00030072407038000e0b01c401c040030903e0801107812170b6411541e0300001d580f03036198042c09244028090715001c000d01000d401d2a4120380050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 831492320 1250 831491070 831491077
    0x20a0201090210171b040b09030c101206140616051f09030e030705010c0f17030c0d0c030507051e0408010c091701020c10020304060f060807060e03210705030f 70
    0xf2000102503c2c0c40da40100084103410307420664964a00d00720121404040038180700e903005408802c50003142c1d07000c00352410011607844c240001c0c070140d0b0320500d00c50018519140138905284d200d05100d40018001401840b04a83d40e40181a00d4905042d07604000c103003100302e40003124035116880c0000c0641d1110411182e1880900c0400300b840191810014034504400b403020703120b500318180412031684c101d080200803642c02107800d0420800c5080c40c90704030805102d0418000000420040c0700441d0b0303002440c0c9004a40c601f000840c1880710300b18122002250703980e020070802c002c000301041c148005c003450b6250000d41c5a00d45070701c4003102c3d401d403400e200030300020500d0444244035900045c6500700d550140e5800031800c00750841022640c8081035085020000d50000100c2e00b48880758002510404200c0310910015030360300c900b00c0c3ea94040784665030001d9005120001a46404922810308a40c2045c03084e10700114030101070159031040d00110f0b1203120410161081c1000c91018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 831493570 1250 831492320 831492349
    0x3021009030c02041a210f0f0c150c03160b0a0c08010b0f1b010e0606090408030a0b120d0c061a130b0319060c08060402040b03190f02040b13210303020a02010902 71
    0x19140707106c4540c1d1b041c54820756032805851500030b8109180000c0c000902008154004c0f50702d01840310610f1021a003611a10509000f1400001031403500303001c0302c07811166014412005000d4550312048080c044410440d0000c0c00600c1e2100100450180300b40540700308900b0580c280d10f40108008072484681c40d112043c2c1c0165151240008034400900c01190710000580c3d08c00003600e0700d6500d2110034480104043c3c1d80581d00d1901d0810744d00c4100b0701d9400c40f15034004490700c234409150081e1204803284021100582401800c10313a882c00b2507541c2850010140c0184e40b0151050309140103081d1140026405100f00d40c2d0001c282c416107000e0401090150f940011861016080149080c0300101814010303401044208a00300f441000c890307008696035061b00030000c4042c100c0014116120005041d14000b0402040070f0714200b0007058908051608a220155038117040002204070703003c03d40c110403c840d04400030130302a4005005c5810340e03200004564005500080d0040b0f202540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 831494820 1250 831493570 831493609
    0x3110106090b0901090506090a0e010b061b0f0d020c0f040b0d0c06080c090f040507171008060a060e16051312110130020c0706030903021009030c02041a 67
    0x41d65401070410200513400360030b804c0c4007401686480008510f03c0c4d0b82c058100344100b681d61b155400080000c0d030255031000d000a10030303030751040b0701d00728040308000081c40e0b40118041c6815050f1086000105105030703443c03a401410ba115215403c1259400280204503042911890042480ea5860784c4034412a0b00c1450014100d42c10001c000b481400020200c16084000b00700ca140c5030303a00d0304041c1b0702940c0b003181c020450b565680c80032240681c9041d00f4030f105400c43c0091107044801e0891000c181c2d8030100880d119a9900703202e1005560562140011110b0950086584102100f030071100c0e090312820001d10b03064400d0074071060044c40d6030004100440b0414203d04100c8103410412180d4001d1a02c2d0011b8035104000301154603410380c0305061110350443c86080d1802e25016188810000300941e4003180c1d80e8680500900343d00300c411070050080280703036941c1ca0f880b8403c5030119034160366000d07030039490766091000404003214400c2414408600b00c03550f690700c005c80c04203510080b45 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 831496070 1250 831494820 831494831
    0xc010f1701060f1d010509040e030c01090305030a11040b03070503060d12050a0813021809190506040209070203032503020d0f061403070302010e061b120c10020913090311010609 78
    0x3d0b0042550683c0b016001503141e1440584040e81e0344a02580c0354074030101c03400202c0c41c0590340c005107035224241000c80d065080542c045c0505401c44007451040c40010b0003400030a014001418842c032481c0903000c240741c0c040c00801c0e44103104030042c6030b200c0005000e603600348041c3d0f181c1210442075188000006140003075031900559028042c035803c103803078072021120b0500b1680090070084000e2055204100d2042c00101c256000308241c18810402e02941501e41a540c1000d607290701045805034060031880380444c4a007840001140d20610480448564440f501c281c0c0072038270160204c00c002010307006e00c401e506070000d40c4910700c140700e202200040e0707452030140882c40e01c088602603648039030080441040540d8200c005603113030040440c0c04580d103400041403c1c43d82d00c4c4002807a0030901c214403c4802c5088040014011411640c04407040321034090005c034168803130030f00640c0e08154104d2000595a0f41e681080c01ea99201c9e05204040e5680c0044941c2150311541c0800940368440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 831497320 1250 831496070 831496097
    0x711030301240305040f2d0807020405010626060114030109050709091e1107080a05120606180d1401050a1d010903050a122c0616020c010f170106 64
    0x2a0401001e506183c1002e12440c58103403580c0105043c144406020000195803601c0c1700380a50441d080480c00c42c00700b800c10795079203080603503094028800880c0101e1410001103441401040c49411412220758030711b003c0d00e501071a6a001e100c000d40720506006409850304814806140614040d12041e0400030b02490301c00d500604110984e4001c0d6041d9140c4042e080101400c11449203015000c180007091621004001551038481c9035806440b504010568200c015480070085c180c018200e0a0340180d9100c140412249102d41140b18050f09074182c44d44000c1c1c01c000309980c80c9035014819080300e1600000c14a800d540301280c010840c80d40d21480c5004542e080050100402c14400007001501075a81c2e0240c210b200d010f5607507003486025401c3e00040c1545800c141002840b041024a40c02c400c041d5401c60710309111803200503400f9000001d802c0c62001e003980c81c00a18194001c01c01030441d072005690384444062100200301800c04600044c50903000054024203840c0e0380d80392010f018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 831498570 1250 831497320 831497369
    0x70e0c09043905040f1409010f0e04060911043615050c070f0602030a230105060306030c0901170f060702070306151203180b210711030301 61
    0x81c04541e42e1140c081e0300d03440119400780309801100b61541080000ca806103180161001d00483d4040302e0162001040800d40d008030107481d03441c9141c290780381c41d078598807a10b0146408a130740c0107a5120701040000600859182c0d0000440540190080521002c0c10004030f001d40d07240701600003000c0d2012214114400c504028000003a041421007407a03003946030355500c0807424000191a440b9125808150102c01100071940c15641c050104030b681c0781185000d2000e500100c0c1c001007104d00e8986ca903a0400e02060013092981002c1401001c6a803c080800c4410303000a880130350507104103513552a89484000c00785018050307480ca4401c0c80041403280c14602981500c08100c0c68110000340081c2540000f00d04050701c0d8000c0010444203c10002c3d0a02000c482c0c0c04030101484602c244024141c001c10260307210f000140d0113800481e1141c1e5501d00c28401d140340c0d054590000044d10b0345181240b201d039034101400f85003c3d000c2c000031b82c16051030b50300207801c10b640c6040e01e100858000c110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 831499820 1250 831498570 831498581
    0x409080d1a01020d1215080f01050f060a03050a021012020f0301090b0604081c05070c15140c250312050307091203120c110106080a02040b090105091305070e0c0904 72
    0x1e00348000c01001c074000200900322410456612121511100043c16030603410f240b20f0b010b0602c000450700c10700b0410703410a004e000305a0301e1120200701e1002146042c148119404242c2e40c1140041c48a0000da40c01d01282880c080140010800c000c0200c8880030014001413400c80407403c00c158495040c00f00101c101d90310000c0340ea12961042108000c4180080b60800c1d80c071144075450720403e840b0b0403003540c051091030001050061420340100d0305810a001e11002e88a081e5188001c464910044880b035102c1c103a41140164852560305240410451391802d10321081044089003c1d03882daa0704030412682d0318460301040001c02040b45947d80318085100420100f01da11100d52460748024024584004002d103109440710ba5404a0398000c0785a010010b0f17008000704801d69451200580f901c4079808100c0c41a82403903180b0240d45400b03204a41600c1000b0700f22100d60b101c250040300b5440001604940703500803ca40028400740c20070340385100f0880544201d0362004031038100000c849 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 831501070 1250 831499820 831499871
    0x10b1b0f0a0510021318020c030d0603030f02011e0b0121020306011b0b0f04060e120409140105060406030e160e010302040b040203090d0f020c090a0f05060102030a0219020409080d 79
    0x280706004c0e4407241c41c000b1540d1421188050008050b00d0010501b0700c01a22a0011089080c0700016460160706d800b91f02260440340659180042c00803000b10881c01d8501e411314002019070761480303070111000c1c507a01c0441c1140d4141442c1c0100716100c903c00d404504140001e50250b54040100310455030801d401c80c181080c000c0620a401c809507950008084000d44100d041d6034a1038001010015070340e0113001ca001e021001c542d0b0f01110011000c40c258058020319aa5a040c400740c0f209031421b02c138a80781071720001010203090a0500c034040300200480d804d010000c0c425900f40c0200380040c00c08034030140076804411501c41d030440c0144801d41c0d15454445018a104100304200e401001c04d000b15091005d1034003d0b210701c041c40b000c80c90308010301040c55100041d0000d015452241d03600082e803c0505400a10499840b5001a601d0303000703425003103015810039400306d5040f080480032007042d00c0c401000040c0203030f00d6072107141d01600040c1c5040d48040c0c1d109680320010f00040d8400c41c205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 831502320 1250 831501070 831501103
    0x10609020c0d0f02060106050304060b180702011503110f031e0604030306060504060e0f031608032d1b01060e040f0201090f052103070501021315080f010b1b0f0a05 72
    0x1800f0700d5030001e41d40d0205100781410408040003140c00c000d4150401d59000f6001004040e1030100d0303030001c802441090f1000c002540ca44403601040f00c504400722800c490700070788400c06280a03c01401140c4c480001c0301c1d50326000301c21640703400c0c00c0e880c80c0c00c000582c0501c0090000740b81c01e140c00340484000341c0125003440014801041081e40c44030b5290001c074030944041d81001280400310345060340040300d510400c0c8454030040764a2000001400074000400b8100240c440c154026041129141c22501c1c60864100103c0081e50745810301c00400312625800003c3c1c9035a50b008490044400791421280e69880f40440c0040d980d00a4002c0083c0c040c0c00c008001840c0380c00300043c2c0039000400d086285d40040800101c900006105494125030041d00955503102044054004041240a0b43d0300c004404019260b040d48180a0315204114524040d1410b07401c000b0301001a0b000790486005540c0481d1480c11800f000340100d40f81010b07104018504403415140c030500300b4201c0810000c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 831503570 1250 831502320 831502337
    0xa1410090b04120816030e012702090606041d090f070f05090703140105010f0c0b01290403030f0c02120a06020409110705030a0509031207050c090703021314060c010609020c0d 77
    0x41c2d070701c1181740f50141d140d904000448204605001c0d024010004000c511a02a0700d901d14103008100e035100c00e503901c00c039510350081c1d4981041201c0b50099015142101038000c2e01400765018021140f50042d0000c1d003190700c006c0136024110b103020a81e810283c002140711701301304401d040c50042150882081d050500505003500701d403c440342c0051244504012182c0c2552020318000c219000761150020149581907844022103a1842d0b14420424824009a42e03c0030041c0c0365007099400341e85d490740d00d000341e000c10000100c813200341000341aa484901001c08284001c1c01700040813403c2c0c4a00005611645040140e0302110500207100c1d601010800c1b502d0001000842160307981a02410520380300c05805d80480e240c0700c0e130b061900c5505200003689000384940041c070403202c080e0407500300400b583e1380c070b4045040e400303280c14680c43c018807080144002c0c0e454034500c030011480508443d050905900509003550703901d501400b01c095001550b42001031040c0705074030008040341802200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 831504820 1250 831503570 831503581
    0x507110706022d0d26010806010f0b07080a050d1b030f060603060f05090a0605121b0f0d060b0301110a2c090708060f0a0311040f0e0a1410090b041208 66
    0x8880c4600c00c0c0300f8042101d00f60084020b10900d080c1690702c003580b078141c0c0d4211b40e140d5811070360b144028000c246507201c1c9880300141c11020181240d8211354009405810301d446400140c3e110380020303c44141440c1c4402a2480505000d144440a482c00d50741c00300c1c803d1800041d1808a54840d0498020141404400d0041d512040000307000c9400541e0b00c1903241d81d450b12580010005504400e60201818a01103203810b00050580c1015081e60888881d140d100001c000302031461404054028401c803035501d0210b4856031000859880240000c034010810441d44100317a800110f1040200e00e025100b015000c1c0800c180344410300221040c4400e82603150001445254014082c60402c95440000343d142c0d15407140c012170244001d001074101c6074507841d220020394401e550850240b8588441851030114a015041040d15402c0c081c00c050461500e80c0d8140d0a500300c0b03000158440c040c2d00c0c444051081c400c204600d40a45440c5a140c282403511603500720307500090b442040b0382e080a010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 831506070 1250 831504820 831504823
    0x6030c0d052413020d0c0c03140901080c0c070f060513080105041a040f0b0412030e0111041404110c031306020c06190c0b090601150507080703030507110706022d 71
    0x100d1008980c2d0002003082c00214801038031803100030b80f1101b400c0c414003242c2560040100031105100c0d84507000c50ba9110417070542203005902e0000d0000d84880086004a00100000c154050741282038654554440300c1c0c018000b0001c2e440000010b2002a000090810f40030540c030140403607038001d00950501d5210f2110003000305002c2d401c0402d49a0101d4104224012942407413644102c0640a0340380c24101841d003004042a40b0001ca42030600300400418103101e17901035244820080f50070503042002441150710601811038100c1c0c1e0f1030722540202c4514402034100758908000950b0741e001804000541c100785540904191351200300c040016036074400c2998110440c02c0b4815485421615048038074174040756014103515280d00a000040700b003c90380c503050300e58589038045240c0f0f051404607071038450328102420440060207600c0002c0d109801c03d640240c00c51501c0c0c074400803107440c140c0c1404629400480940e000442c17844000c9201048000300c080846944d0100f001c0412078207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 831507320 1250 831506070 831506131
    0x32f210717090303041208270907050d060506040b070c0b0a09141f02010506010e0a081e010b060a080f01170319180e0105030613031e03060506030c0d05 67
    0x8a107141010400550320345041069500402c5040480d000143e0301c0e0411403101e621081d800b44c0e981082084c1388208503403c5100780710058000d440900e00b60303220350046495420031116110303000d44440c000100340ea10030002c2c0004d0181034500d55910b1243e80307001e0000320001d5100485003034003409540c2d20507800001710012200802c9120241030040030003e0101c1c902251511100c4045074500c03c1003a0381540000c1c400d40d02a03e40d581000c2e4040100046050b40b4428024654460480310b075220441d80038141d00d9010040000ca50000d40030300091298010080c0100058030000c20005031003031841106005010f03d1103200003005018150359240d1050014008a2417665a0707440c43e058461550401e10504010359281c0c100d0f11070000d107410710400c0c0b240611030321800001c200300a08440702001503039403540b564407208080c06030070912283c10854800a160b580c180020b4107448480c01144150b0801c00c0d0140d6842e5070702c0c202411280c0251012100c035821800321071006034600c0d81c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 831508570 1250 831507320 831507353
    0x602060f130201020a0c0306090209060319030e1206160e09060a14150d230c1e09180a0e0715120b030f061b0702090103032f2107 57
    0x10209840068001030b450017103600030051120780c6040f800011300c2829031042e070b4030394400c0f10700500030707280d135802c1650300e524014940501380e80b240c19800c0040c0c007500840080b80805801e004211925584d41420030000300c800103914003001401141150740f1248540a010003154034154074101a008a0491443e5000706201c0c1c0b0641194000541ea510001000f002c036843e202980d80c0344815408005440300c0000514040000b05815840140c070b564611300c2421151041341c1010030200c802080c10604002c016469541046803001544034000858030380140300160781d900d81002050b03a02125001c6801e2030321034001900520940c0940c40005009040d81c4c0303415101140d80034010801004000483c41d407500c960585100c110001081980c4103080641c440b400d00103501c02009164031900f240207602640c50b1006000190007050b090720403980c3c8103900018101c0040340700100c008c06541082c1250700c0b2101214100b40b03801208d01c0500f140c5c84100d41080c41d1a0f440610b081c0040c00f9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 831509820 1250 831508570 831508591
    0x1060e0906010e1e0a0e010e010b0a0b090603130c0e0439060305070302090301060807151b1502070813140406140d0f0b07120f1b031515080a060602060f 67
    0x81122084550806c8100401c0d01b0000c0028401001401d4020045405400c2c0582c5040000281d90f0064400307540c81c04102916851840c5c0e80d0402d5540d40ea0901103044400d10b1100c64040b0782101503503207691181c0c0c0306a400c0c4078600309003542411420300102c004820a2a000c40003a0840000c0b0440b0040b540282401318664030b4102e0150003a0041100c0e6903059880e0003000503841000240c540b04035800031000186038002508200c0e08015201d034400e140c00c00348502c0c41d0000b00c1d2128806441408c10358010300700850703650340200303507440315941507224118518148510583c070481f00c840107004544c100449450301280444e01000c15032401e110310311300c02d9a9414032103141100c201c40742d030105c01040e061a28143c098200c24038072030005901ca181c201e0000088110380300380341424200280c4116004542001100502903842441e1880c0110349400140b10303640000810380e07003030380380c40300f66030762520700c0c103150032942c1aa1104d030455003e0310078000d58110713950006410141200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 831511070 1250 831509820 831509881
    0x3161809031e0801031a0106020a1101050909180c09221a010e090d020109020f061315050705061e060d0f1b1806050604230301060e0906010e 62
    0x2000c0e114000840d24002d402000d28200d800700c15400405241600d100f842d5552840c8004144209031100c240120340140c1d107c0840000480c20350300b0030510780c02052500501e85401e00d0082072540c0c3d400e843c00c0c01841d41c0c000d40d0b50031b150341c2400420300c0d2048c1034996202034945100144a1200c60150b848850007180303a001f4244028444260740c3e00000f8441c01d0140e5954070054898110b00b00c8000c0041e000c0e15034450590b62040c018981800d800070700c2d081701d1189000411504c0c0c0c1c020200212902d862250005042040400380c01080384a40c40d41c5407106800c0c00c00700c0c141400180301c0039442c0000039065410b000022031054000c003064580c100c01d000f241c50700a000c100059005844008030240740c498079190b0300501c0041e629a40b039010b80d80c040300290401a208107010300c40d800b000600044c4420b88a0b0035450b80036003401d0045a045a032004046400c490154100c1381d29243c0d500100241e010003044142d005080c9000204490701e03101c030300e1070f01514024134014100c40030304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 831512320 1250 831511070 831511073
    0x140c04091d01150303020d080103020a150e0301060611160f030602090315090a030f020d0f05160f0f0209060604062f0d110601081b040b04020c030d02040503161809 72
    0x40422180400c0070000030014007006900c2161070040700d00c8103c005100c0c0c3c2040070f000a2203950100c4c1225805004c4940060410030390b460709110240c46501000501e4580c7e0517030f99030900401004000d03a031290f12001814131b10b4207090003a01c0501c29542002c5000400500f11892040c00459810000043e1038140080009042401d6041d509901c0101c0c0300c1801046030002c5081e01c01c1d00e00c40c2d201c80311100e6500d0000d0f40c41d04545003403e40428001d60710400c1c0c0341d024200030710050020a001d609100407035a0780050821000c002961f81092000d96001141894880140c02c00c000301c8042d818140342c100c000b0712000382c6100d8681d4450b25041070300c1e0300402680040c4811207101c0141ea2401100c100d00508243d01c40c080c6942920503840000f0382503801060f503129007000710444420f4901030750144000303400c1011030a500580c2c20000940104410301c042e1200d0b42c00d0b19000750351180382c00105454046035041d28046a2902c441c00c000400940c802240c1c4006042c4012035684260b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 831513570 1250 831512320 831512351
    0x605090d111201021306170402010f1404080610080703020a03080a0e0901030303020706110c1e0a21020d020d120e0a0605160306170a150608120d140c0409 68
    0x800074619004059101d0300e105092040d00a042d4800455000342086a81c5a004841c00901c82d034000054040000204000d944151456041101e0310301b05402d00344002056100035500a5010341b06641001051240340c00880c907400c00180b80b404018035030300c3e04ad90005450004103100050505000103038001011b8065081740280031001071402d4215071f903030300780503001e5400700d0000c4840305e190045c1128000694029a0100c480030402000e0100724510ba1000308803072581d40050701e01c81c0e000c41c0400a2014170000790000c0341d8144581d0391900425000e4503200664800f4070554012101007664540d0103d203102c2a00844540400c0000d9040100e46c01d01070071150260440b41850b00b0000c18490301d02c0d907044a40c2681d82c0c00c10019a0320ba8031004141205910b0070481c3d0410610b1402040321540910448400700c44001101660b07032a84074940036030841405030061010810000c60242441401312040320301c007203002203203448541c05055100d9400b0f40c07217049a0f50000611940039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 831514820 1250 831513570 831513593
    0x8011a0a260a0c0504140411040c020309040e070513020c061303050d0501031226011208120412080108030a093b15030a080306040513080a090f0b040605090d 69
    0x1c6100990344940340c1820034050f000d10b1402101d0245080c0107642c00210915103805205580010b1030000500b011401c020241060300615400c51000307009121265845110710004429001e0007000490314120600050f80303220300b0f840c0801031052040050b80342c000b0502d540d108450a0032030207200c0041c03400b0345e418003604000d48001840d00b4004010400284000e4103510b0070754030f07041c1c030a00414890700010946482c6500354000410700410000d500c4d00b9134030b0000780c0b01d050b481e41440480301d207440604c40c3c103c4041d0344401c0346800d650309168006000078003500b59100558507000e2240310182c000741444c410816180c0740f660112090760311203c4000d000e41c40307400503240c2880c44040380c0803c0010a40d040d1400906001000c1a1032500041c02c84a2a5004900d80e0540d9110b078100001068002c2a141500300d1200003100012021002050110b102d80c580d24641810700300400782d0914580c0040c602e00b04100400d004c600d4014085d2905144102c4105080320860f2a0074110b542 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 831516070 1250 831514820 831514889
    0xf0a0305030d050a06143f0a022106040f030909020c01020910080105011209050106030b010303080f1b070206071106071a070801120b04111908011a0a 66
    0x104070007002c815540c202c1c3c0e0180400003414000f294036031240c62055440c081d50994030900c12280425000f04003240e64003c0c15058150036060244850f0b01104401c1e10030b030300c05032500403410360803c5241814006c06003292450000110407040100036035107010103000a02594184c251003010988610744880c0035240214040d51503114192440d4080e400a08420b84159501c1042014547c4210902412194140e50f621408003540c50754100400c501300c030589242d520344a010010a0501c40d180d0b000310f100b907a440055251406002665035006009040740ca02090709150241c4100020303079501d940c040304d880b44e550b40c103460204117090016400703540081c00400c0b07000c04d100742041d00e5114030036101100d10b495507690000703c40f5010b09001d00c0500c504086020004034032103400095125102d540e82c00300146c1c0d41000240c1d5001c851002e2074007034028050600100f1000c1c000e03094015180001000038203440000904070100d5401050525402c0480091461421449442218 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 831517320 1250 831516070 831516073
    0x30b15040c090f1707050909011b0e09090a0c061d0405070c0302150c1e120f0603010b0d1a100e04050307210e0103051003020603010801090201030c0f0e0f0a0305 71
    0xe411541002c0c004050350300c907085540441241c000303400198846019401e480c82e03c050301c441804c1c1010890580e0001d801c44142e5940c071025044d05280c41c100c0056080a00e0f00c1d00c1d110040c01d001088220745000380854016001400880c0025002081c60801c2e01c0031404d10b054660302c480540c91003140448151680242440c0c24004155040300158840300d00940c243c412009a81e42980280c040a803182800d0784000c00100208440040c0c4215200ca414030603d490035908401c100c0c6c09490130b40d00d00c0c0e00308002405200c400d02d424031400c06008410b8030071441030040394072080403008900351010403195418000481c4080361562a070003411840c8a460054109410081d68076001030b44122126024680c03400051542600e0050300c044296650303054810381c10b0011406410003400c50380104544200c013000594a00d40030b18082d10400c000040c06070080c0c00010242e03520000c0480c1485001d44a11401641c40a0041e5281200341c41024560404ca0b002c40c04005060744050401d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 831518570 1250 831517320 831517331
    0xa12020d0e06060303070b0103020d060e030a0305014104090c080c040507091401200f0a21050d020f090409050607111c030506030f0304080d0f140301030b1504 70
    0x259469000c81c401d021060304a441541e03070002407659900c142d52015000d01e04040041006141a00400c064180325040c00b18010010001c254919040a80d1883c0030a4031b07640140b00540021412280760000f01118030180d100d901030800f031584c0d84419034a1034103000d024203400e90700e507a00b103104107652240308034949903030f2140c0031512404078590036840740782007202054499100e0003411050b625080c01c50888064041c00641d050840180e0102c003000e00c410308034001d9030b41404010180000040074003e11511407901d5070551441d107143c0c080c0454940309a00c4440c0e8008140d95040707a05940050350f4800f031004491440c02114080c1e41d1290404014100b00302e0041185030203500746849981d400d00c510b00459858144006001e8182c005c40c901040e0b82c0c9102e0380145401820140c1541d0081034120b0441e41542d105410403021540054040e80e004c507400701d424480304041e4034280c00000d010941400d08e0b0311040c4000343c0030015440200b030000c44011074a50400030000c200b00213 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 831519820 1250 831518570 831518587
    0x90a051623030328121b030903030f0c0c0c0902041202011407171b0106030503030c07110604080304170c0a030f022e02070501050c060109051807061205010503031e0a1202 75
    0x40c10714086000c3d90003c0c0c000980d050349294240186e5004460900301d03582d400e01060800c0b401030a50400079000c05032500810060841280301e020703441c8460b950360155080242c117108080102643c0074451513481040304204144007001e03400131596092030142d072a8004003c010119015000c0302501c1d0302a0124040c2c41902000000c00c81c0e00c10403140900c0050f0380c48501030884e8002d100143c0540c00c00c10009803815481b10080403598805c44442007481e40e00d002080c205e400580010502c0c0e800041c05102f10040e80c00b1115442c0710311070040810221620210307440000a21004112010000809045644000840403200c0c10a4101034a10030032194016a00e02042d92500250061150104a5510901c1100c91109203a0f000b42901d03460202d603100102001000100d44213000c0f0056000d4000a1203100002c09039551164948580c0b481c0690844d00c3c180e01680c0f00b940300b0840c450340d030b6011050820001282803051515501203140956800b500c0940051441d84000380448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 831521070 1250 831519820 831519877
    0x80304060507150b1e03030f0d0f200f0a050409020d0c11031e03040f17030603011107051b040b0a0602010f0b06030f0c0d020909090a0516230303 64
    0x42c610b8021508189202e048400400498000d0880103030044c000030042c0c000c400303064a0440c540100601101c1c50408150001c0c002030b00048414844a038036203501d96000c8555018038003004d91400c4040504102040070300d503c9100e080600d642003400030418512550145054400803d501c01041d9680c181003140100149101c500a0010808040186020b080c1c0002950f12500000d10b14100a0001d070070003991581005200f181e45192002e50b92000450041440c0707070200d101c1419948904001c810182911102034060104074170520a03000070800000384a02e201d84951160f4422018140c04100600340b078a48651b00035030b0140000449590561000070321043d03490081210a009100700206484169252401ea40110011480304020700c401030145640c1c5030001460705011002007010050120f4481100d500a80020421b0000a11100010014111081c01c1c840d08005580040441030260b5010082000040f4a05510204100d1b13061046003401110b03040d0300d190205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 831522320 1250 831521070 831521077
    0x2181302010815030c0103110f04033e0f0d050f0f15010b0a0f0909062c090d0e030a0b0109020a0f0201060302030312060f090a0c032915040803040605 66
    0x101c1c0040c0c00303440010302c2002c80c0c80301080c04020050280050654110044028100c00400c46410400c05c10080e1400c105140007072006502c5404070000d8900301e01400c0e00c5480c3c000c40c0c0034103ca429030295950304082c0c0121804001c00807145542c500c086c01740407a5904804540017030a5100304c1242d41440c00002484081d0b20061008075515a1954804010b0400c0c0a203d102c08103c4184404011316000e0354803818078503050702d01001d0040e5203c20480c10344945038000d808070f000740c805001000382d44d612007003420004000030782c055081c502e035015640d42c0b00b2940361b41041403e4425041075942070003040a901c0c1c21030b84000e0b56585501188009510106031030000c9200403520000050040c05084101c980081c040c42c00c1c584d4041016400306e80040110760b00075516252003000b5904c0b90021805890200000650800040c0c2d01a00b251410405c1c3c1003503001210b1003524007507020b4491803095005880c1068000c0c03070541000c0c0c09021355009840760380008140032400d10f40c000042c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 831523570 1250 831522320 831522323
    0x120627140906060f010311090103050403110105130309080a15021b010f0c0801080706020601030b06010302190f090902120a090f150903180b1905130305100b1507030309021813 77
    0x1005603140b1001c0c0107408403240416008042c89040c440c0222540c002e4bc407050b449402070811041c0c25442c80d4000f42141d80445076500d410086285d9075090651003041d00c0080c2944100610340d031a0142c43d07860f44448032990300694140c0002d99071800b1602d100c504414180300900034420f9801c00c084c0c1c00042c0c6017840d8001d0010340c407a4000034404400080340c0088030115009088181d0843c0c660100c90780008008506041c4c00b00803045a05024410f0864005c14580d2410403044180781c0003841001c181d881180700d2801440130b4840e000301080010303000010140e000401c105146001241a0f00c0d808001c2c21200c60640100f42002440d0000400b0a210741d0b2484c280c00c0c2a03140c2c82e610081e060203403e803007180911080070380b00c1c00a0000440c5024900704241003184a40300160500303031a800c100d44540210f488003c048545004604181c4d20440fa51112102c00d40d5200e005406162400340070191505845070035521940c0e00c9a034558000c906512840c90045100740d250001c0280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 831524820 1250 831523570 831523579
    0x3032d04140c0604230d0209150a030f03020a11091e2706010e06090709030b06010e031f0f02040803030f18060703020a1d01020705060703030e0d0c0312062714090606 73
    0x2c1e0017910b460318200741d448056008203216040d845405a40c042003214442450b008489804040080b6100b0900c0180051281e4000c00049809140c01d0b001031814950190207201c9000520015015480000404689000503d002e0f0782c2e0b2641c04900e000011110040c2101d200c04002920080106d03003103041c0d40c402a00c0c000035881d110240289480100e40c00d0700044e14044041c00040c0032042d000c0d41107501450246840c4155000280c01c06206d15607103001c000410b1002c1000016600076800b850b90229800c6003007074074ac9400d1540380c0c400201086105e09030070000480840e045001c45044200320011942d071481e02c41d0000e00290b00a64401000c41c002c1080e00002c142700ca021500c45203010b038082c00b0390703916102c18000d00e5000f46404070141929640750884a41d410030060080064a60700d4011150341420090074011060328034004c01c0e800e0407007c2c4150045104199100c0f046e41e03140b1a106120b0f600c60078000c0400051881c0d00440301070078808400740019659004000803039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 831526070 1250 831524820 831524879
    0x18010b19060221160305270109060203030c0d150807030506150618090c0d0f0c081b0306150d0c0c03091d060904030203040f0803032d04140c0604 64
    0x199609082c284111000440304010071003207940201c000001c4400030705c40e00301507052602400c0360340d51070b03229001000361414060700700740300c2c035030380442207800800c00da001441c5181000590400c80c2e20a141c494010161951900c0319040e4030703080d0001c010000d040a40d0183c9840b8500503440b50000d0b40d040c00c08020806400b00c1618000c011641507982062151150b6800d1000340b0116400080207260142c40c00c1c4003005d21014203024050b4071136404440083c000011020140c812803025040906075440070400c0b800c200044422690000c004440a007561070070001d208016101e00f0280960944c10105103003035264000600403912486510b58101c1151a403541005800c3c4040c40002c103012148085440c901306042e403d50860700a1040c0c030700c0d080e111524548001c200b0f511003c282e0b030000040100c00c1e01d407081e100d072080c84141c10b804c25100c0c84c2c0421003292040a84003a2a4000c1d006003200016070400a500d035401c0042e0009840d03d41e030b903103000020303858140b082c1030004092 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 831527320 1250 831526070 831526093
    0x1060f0f0302041d0c0904061724070c0c0b2106370e0906010602060a0b1f2007081207021012020c0303010312030e07080618010b190602 60
    0x2e009032010342d40702d01c94004400c0040b503181d0040c044041c01048014408020030748a944403401080b0142041c1c00d10022124042070045d481d24034055034001c1d00600c12003441c250412a00c0341c00c5e411050784d28210315040564103141c2c40840590344101c540810009100c2c40c0d45c0541c00715000e416003850140e100e02c2d91400300740a8514441001907020240652071240c00404808000c0020100d02e549020103030346034140c00f41003110603945100e460f13000600400401e941000742c9a880040c1030340900000107002c1c0407540f0812075902c0d0b801103609a218031242c0f144105e10348503508445440c0304a80c1c03803101884549990715402813514030300031100804800ca001074100e0b98100d501408011005094280484240300c2407902001c04070b80030004210b00350310400185000e18056a91890301480d0711402900321030b0b95489a007000e421801e0100b041c81008503003c0d511a076800b6007407420002050030703107004101424031258410104144401c811018088440550700150200c1e00c030180308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 831528570 1250 831527320 831527327
    0x4021203191d010221220f030507120210030203070c06090c050f04090804091e050106180510120c030b030109050f011104230f1c060f090807080304140601060f0f 71
    0x1d0990100300220708002c0b9000801c1780001404105d4003002400185c4041050040e01591150b0007606081e002c0306050041c4241401403400801001b1041100400550301107101c105a813400782c814564040002406140542c840c0e100490f80218200000700d240d1030702013042450350041700c0c05100010b0581c00b060815100780900103802090243c10145003004c0c0307002800604044c80551044662005481c002602805010f0140e94881200c0c078240b085940e050a20240d1049108400c544040304000d600304020420344025a07034040750b0038050f103009802400f6220700e02c035010b600c0d10402600303218011a01301141400308000340000b0005042501c0a802a4080c41c0d03100d8851a44401e0540d0f030b1580b90f102c800c0340c040e000c40c441380303803500c0000c140d10703040050381c0e942800e03000b007020400c4034030310940c0240c1041441c20461307135085445080740f0b80944000100041c00001c0844d0a2080c0e0030002e54000303042404650030f66071a40001048134010050210115803e480781032100ca02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 831529820 1250 831528570 831528583
    0x201110a0912140a05071505270402091306170304081b13020a0c020a0e07230f0403120210140408031005060a02070602061303050304021203191d0102 66
    0xd40399150725040d800c200c2e2100d10384840000c11209640d0382c3d070360f0300724021040c08001201400f030806000590f01d000c0c0d40800083c0c80f41a03c808201081004030041c080c0150001007808070711001d119a5800180420002e02c5206039880c3e110294031002c00b05481d00b900a0002c2d500c4000603c0402411646515500d020f54016000c2c0ea820040f150b0400c0c950728003003500c0400004112005c0c0815610340b590803a40071b20002000107482c1d81504043d41000041c03480280b2001418205615140304003c010700c1d9007450740701e030b41d10b91a14240302c1100d900c410b960301d180041703044559460f502c0c5003c0307420701d03d8000c0315409401401c40d5110709004501c600410b8218014911401c6d90b50b42d0386a1b00709038801482d5050f107449001002c241c58443d40040d05c078440440e0010a941c60600e00e002c0c1c40d010340141040c0388001c5c4040248002544501504e4106906803138074400c0c0001056114118042c520034640c500100c0c442e062495540124540c0f62310a00070b0140301c0c4200a4001280c6414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 831531070 1250 831529820 831529837
    0xc010f14040209040b042108090d11032205060a0819050f2d010e0717090705150c030d02040e0c07020d1101030b0d050a050c0613060503040c0909050d020111 69
    0x802d440004001c00c5c1c201c04110b52203440350a411100341950078201005085142210002415400070008848810044009404954241407051852640c0c07038603528412045c54164580842e852140402100421300d00908030090455803200207094008240302d60894102921440800c00100301010901c02c00e40212810000e10105070741b00071000018600710307440e25820300b0502e140741c40440700300c4112034047e044103500c0400310b0030990001081d900c01e08080a0351000c1305000d1291500c3c002a03618100c13282034032580f4400380f10b40285135580c0160b0704005c21f2030000040004402030b581d4014015606a120381d4070154661400304890b9010b0800025040310700041d8040c0814491000c85c1400c600514010859050b0200420f55806514504840e60303885003100000700181031080360749244041e41c10390300701100f4245d4208040010300c20441400310020102e4140070301001c03c00b0103454842e00912002c08a0300e8081e5030b0b0f0b11030081400055290800e10808001d8180440b450034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 831532320 1250 831531070 831531079
    0x601091503050601050405042c0c1e0612010b220602100e01020c19020a09140a0207060627050a0c051c0e060c0409050108030310030b09120c010f140402 67
    0x100c044010340080101805071414000d007400005215662400780110314800c1c80b0f89910040c800241014845202c10714401813074028100450079600d81e0003c0b00c4403040e01d040c100d1000e07103065010600510400800e0a030786034000c0004103540c00340c040100300c100c2080d04c42d451000f00200c000005030146015203001a0001d01c002c0403600e100c0e0f013240540100b070703200042c500004080c0c00c0d840c00fa014050803405288621088040d454100314003002004000428490503010f11200c3d80b03020002460803807419808251074040c0009076118401400082c1046001c5c0000030703030080110711744414048905402d14000802242c0035001e20258030043c0d1726140e09002c0d609100c000d410100c440c11074282d56948605d507005520801286000c0d024a00c0d209030b80798280480b05d02076900c140c0001c90154420400d021901100c1310a03030003101d41110790410651100c0301564205055801c40360030f00c1c54042504100c0d00b1040d8004207040c0e040900c00c021300048101070f0400d0703201c1100e019500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 831533570 1250 831532320 831532349
    0x140d18050c03071a0c0c0a06020106031403040e240a140405091c05070503090319050f0c0f0f0f03060a020a092c1e010807032d0201110a05150f060109 66
    0x101200e14050b1864000d8174003038a000c0e904c054040b07880c1038404e51001c0d0050391180340c1003052000340c040b00f0304a10582d030061481d250601d0030198040b1030251030100504401d21071551040c2c5032222205c40c070f800080145401a5440c0f0440b003200c811082903910036440c05c00440d00340800000e003005820004205180c846c8103822084e43c80341c00540098800d0701081003031040c903590a00c0881004403141013400710740705085c10124a0120701187c10301443e40311541440e4a5541c50032804c203141170880d080c2c1c4018446801280001c0301c02e0380c1091f014402c8109214014440f81c01070b2407200c0341ca47d1380e05100d90340d9220311083c008002100d102d000141d4030300c50403000001614564002080d10b00f284441c0842806558851400d0380b01402c2504040c0081c020803460400910744100503440c0240c0c0400d60003070700ba001d40d014060090500000c0781c00500449818040c0c5000d40d90000144c440715100326540510303010084030080001075111001946660044030504251480f22000001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 831534820 1250 831533570 831533609
    0x50a050f011509030606080609120a09030204090812070f0e040908090409110d15050c04030305030a05090f0f01090605070f05040b0c010902041803030b01030219140d18050c0307 78
    0x149030b06080440420040700150202c0801c045004520043c0318410080a080c5080810365003444889910000b54546c2040f082820f40d51001148068a40445000509a1062038821820300c80d0b090740c945816002c4081001c80e50308052010140602616002004107085040004842c0040b1000f003121743c090111b8a118140380c0c0c40400042c0c880c112110348101c0b19400582811010041102d07090078800740c10082c0300181c0281c5812080223070302c0703505050456602400500005142c0110240d4440c00100248001c00080700c8002190003a21101008520500e01a200c0740c01c0075a00541403801007842a8442c001c021048400c698a4600381400c20281101c0c984c003540105555640754824a00540d55034418204a00700705883d111084806140c043c0075a141b02e007a250500d4414412040210f410355040307410800189019a01304084078100c9449003e13159500307442c02e14100d4006031445800200490a90003038003101c407074030307450010555100043d0084c008401881c011500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 831536070 1250 831534820 831534839
    0x601030506060901091202190e01030309080d090b070c26150c0708030a230103060c030c0518031213030c090b0307120519050303060a0f05090105220f0f050a050f01 72
    0x1e41c1d98402082040c08d24807091804000740f1494009110b01c905010040040503003080f40d0b00d006195a44c003401d4442401e41001c0c2101d0010311503110b486d100042d4840070006c00c014107002409a25244400110030014040c00100301d10071015414800c000812010014030ba40c090b21422640c003080b46090029641c0741000d030006442c1c0c4184684414000b5041c0201d80e010b502c5d2119100c45001a644c514100482900c629190080a1620f08a800307000759034044100c45454501440b03400d030403132411000c02e10f00109407086541c2d40030007061000f120059264400f048074060780c5040c00144c2c4643d0810704440c0040c0100d42d25620109042000c00002c80300051200d00403002e40b101107003101700000b028045007000712a107400000402c1800d01e8078510000c040e120200c000c0d404241010040754450340103001d1948240c240411058180a292075a0200f034401c4180c01c0c016982411418406000401d40401c5818189400141e0609141c458075104102d111624a281d034600f52044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 831537320 1250 831536070 831536099
    0x1401120f02030f0d050307260a0c0905031609060b040b1c0902100e0a080a050604060f1b0806011704050d120e0a030c02090c1c02161208060103050606090109 69
    0x40b078150140d5600e40c20301101c2840480340202190f100c45980b8584040000c250304914500f411074402e800810401172510186070079031180c015a40080d51a03e045400e85102ca9644d0249505200fa0032070040940d859680b080e0403035051907000e01c0025103070428050302f8000e900422140901c1801200d040060b030407004210301842100c009061922600881d940400020303541c80855140041d0901c281802d100711801000e040c03010306001d21041e80c416445000103000540f04a8607a06008000182a4000c04010305801d02c114890031800340d025081050849896001c05d4150b0000003040403020000c52103254090050081c0c4824454150380c902c58511603401c06d075076101c1000c000d0450403c0100350030383c042c3c3c1340e42d00e40040d0b920401c0300c1d66400802c44ea405200501c41410300c4200c2d02141c12070b46c06a80c1d000340e11140c3c002c80768007080203504009444180400d48c21210a80c21002c0140214030a80e0180071070794440341800581d203c0d85625138000342000c2010844200c00c400e00c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 831538570 1250 831537320 831537323
    0xe0c0c030313020621090607081e060f09042102070605070206070f200307140102030405010c050c100f020616080a0209040b0604030c0e0906150d2301020c011401120f 73
    0x3600e0403d501c5e143c0203110a004803a59404801e550418001031002c10006268441007600c0c10152a292012208100c0b11510720b420018035040300c0840c0c0c00c1d690f12000291001806480324440307107854104203090300100b102c940b58900c0305d440c1c0c1441261012644d1020303201c154aa1a213014015801d1010940c0321003003d56a9012180c0410f000806501c0001b00d482c0400c0c40705a004820070081500344441540320680c10503403103241d551075980200a807000c48030b007402e102030b20b0885800d180d400d1a06840946a0010110010034030240e00300d4040030390303649607500701d402640d1241c4491150f144c140700b440b03011501074000034043c140680c004042806024102280e1040c1e50001f01e00c081e0030603001241c2c002c80070501030183c1452000d0482d88a842a0010801800c10b180945122a90041494041c0e01160030120501030341c02614000d4110901c02c40b40c0d643c004100f114000e4000441c094041d500305018031042c1180340110b141a00d4000e040e0252038001941c464040034107a010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 831539820 1250 831538570 831538579
    0x50a050c010903030e01060f0f0312020a140d0e100903171e0405030d05070c05310e07080a0b06060a031e020703080a0c020d030902010e15040e0c0c03031302 69
    0x8040844100b0300400c0651071180e103001c00d4036103000021a00351176003a08800c01c0d030340324802c04114251408068034100e94022034902448081e40c0c00c12030070b05d0058980504811205481c1c0b41c603015001501a003020441c0c0e54291241d5582c1c400c1042d21401400810000b07150102c00303101042d010211130911580e48080d040c9001c0500c0e10304080703031810031860802c501011034100028101440080102001c2c1d20741285002c10700d1ba40c603e0180102c0c00b90f40d00a40303c25241c100d0b29280c1c604002c0500000b510107582050080405c80d0140131103200060035801082000103500c600041e0030100740350311001410082da100c1050040c560000c11602c0c04141e110010015103000038840c0328001c0c208001c000d41d841c01c00d030030b010b011101d01030705900380a4940044a00900c0d07011814030070a5140d4940032031030200600040301d0700500e015115078007101e64100205080e2150008008032011500c18200540e10489110880c1c02508804d40703180c1c1042000900105c6102c1c40000a18401030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 831541070 1250 831539820 831539827
    0x6050109050609210d0302030405062811090909100c031b0e0a0314070603270b04020d05060a060e0a0911120f0106121112030405010c111f1b0c0501050a05 68
    0x39a4140303020031141c42030001c04d0f400000e00050240c00d000641d4443c400c0000700f05c14503580c4224ce00741c50320b81100850f00300da032031202d901180c001004440b071100004080698178200f4056554440075410640742c1c940b49021b0350084d41a000380980f00e039600080400798456600c5400546012181e410360543c0541c00d02c10100001d0211400a190407410034000c101c0a030822001408480d0102c5070b05900d11010784e40034000e544200d0760cd0122036070000340b006440c0c64a20100e001c00203240b400034412f024034810401260000da118500700c41c19103808030515281d400020044408101000d001009034120080060074400070b0f042d62044020121a0502400c081403801c495482c1c0003850385c1d140009501092100b2040840030420003107601910714240305413000d40e01c1c0308a1194074140640015080d0a0002c900b5100b4400300c006840a0803044800c28420384000b40000e0380d4011817155130060700300054140c1c42035216a13220284d00800307070400c00155125042032202c0c000f042800c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 831542320 1250 831541070 831541129
    0x3301a2d240909010b0306030a11010c0609060b0a0b0403120507050f010606030b0a0b2d0f030c0a17041218030f1412090319030c0b01030b040606050109050609 70
    0x500d01251a0400c01d02040d00d5000707600c104015040306038004010740400b401489881c1d580440c0070000c2d43e07071104042241d40040d0005039003c404041020340003501d0301005100303001c1c0a4000b440d946408940d044001520365200c090310780584c2c00082c0258256800c48110a070040004040403400ba80071540008001441035080d01c042c1d8015500294907641400b080d414826289000750032150551418011108540004515070030804041010b0b0b00c0c4001345035002d0b0b1011280501ca005180b83d40d00d25002c030031142503a000b0507070500000c41080c0300503d0f408030351100600481c0e01ca094055500b42054007150034070080d222101801961010000000303051b141c903000441d01c2a02c4450200490300d2080d410a00d039a00401c0c1c2c1c1c0b01b0f04101100403540d0100710020340b918003500d03102291125050407114809a0300004019003080c1c400481171047e040c000c0780c4900d104100a01010381c03101c2c011140200184503060700850180725002041c07070f12061003440d1401c495440c00d07045002e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 831543570 1250 831542320 831542359
    0x90218090604140c19050316030507110f030903071e1e05040c1d010f1b0c080717010b030703081615020a11010f150303301a2d 56
    0x180c0d500b10346a880045d607510292105202d100c000d02d0301b418032508614204d168090b442c00c22414130810540c0d100001240b090042c1d01025102c41d0601c11681c070f102181003959502d521600f60f280c401d104011780060305069440d01c40c0c0c64040c07229568036600d4a0507144494201181c050344c1041c00c02c1103000316840d15184524038010740315039182c42c040c07002d850400004c80e029504440c100300d01c0075009000c07140c001d0011040c41e10000d81c4480d103860b071410006002c82854210382c800740241c00c0300054003a080b002d6901032911103402002075250280415580b01d01d580300040442d6014414903203120980141d0b058200d0054414101d45504801300c24100c0e80404452404910512002040f04100748140d001e8142441000c000100801a40843d800d146220040800183e401240110b000c0c0e2056100003c18001c0d916484200041d10280a040c50355142d03070343c00d8071281020b001031030829008101c2026651b445060440240302602185824842c0142c210400c3d0741c6c8842d41055 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 831544820 1250 831543570 831543611
    0x3070305120d3c0b0303090d021f0c03080f04030f1209050f1b03070b0d0e0a0c080c04050901050f1506070507030b04050607140d05151c0c090218090604 67
    0x6007109881d83d81d4160140e40c0d200150040881100a441c00458120f241c60000c2100d03803003142100c0d01e047c980c071075100060461156002041050701f09000c240b52581e0468045281d0300d120361100051a03a6140d0500a0117008450140001380001242c2c007109000341001054075044020206600015407500d5182c9a140382200c0072550211140740b0303034040710f03642e00c00710400100c1c06402c5c054a81441c8200b01d001c0c40410010599662040c040f00720010011400d0240d800300321400d01075900c4d4003c503100d141c40d140c510301807400d1500040580d1010700c6a00d118800c00b1051010b291140700e54102445403841100d41c11510070006c0c04045541000380400440c0b1a03c03803540545080d18000307003448000b910a20911030700340c0d80401040d02490645081e040603180001d01c40c1da0b0031038402d41c0c61f8200d0b10300540101404d00310b1910325006c20002d481c3c1c1800741d000382880703c2e5181c00140c01c0744256080d000542d52600707007540e080c0c6040000650030903001800440d081420380d400c1c040300c07034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 831546070 1250 831544820 831544871
    0x6140f0307081e090c0118270204030c03031205251103130f050a1a030c03040c030f061b02060601020709110d0c0c0c080102070c0519080d050702090603070305120d 72
    0x41c0303c0c1402c45c0c0c040d030380400c0402e031004184045160381c40ca080501d015034009101c04807103003241841c401d40400b00e207606407001560001b00c45203209a803420047c0c42004a0341e8030b0800c0a007004000b95202001c19081d504050003052100b0038265101c03400c40320300100222109050008208901003900380803929005000c1c100d5081d0180d519140030003540c40f115a0180c41031458428894000c0d40b4a102541d501070314004c68203945e503070780f403411008407600c2d0340005180f1002c0500070030900c029035019650800c90102c86010171400c0d80f034180e9441c5400c079030f240c0c0103074004c3e9000d10003c211038000003008c0d00d10a00080c140105040c005041d64001c1d4641400246e00d00581c5c4184111030050000821070311001310724101c41a2101c2000300128041c1500031248024850207540800041500401c11101a1030181454440060050b0b01011003a841100c8103008034032613190200301c0c4800c4aa121000703210343c403d094417094540e00004244107840d561107814000c80c144c0320b5000003002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 831547320 1250 831546070 831546073
    0x7020105092d1c0c0b1305180a230a0b01021501030b042a031e0f11040608030c06070c02011116150e0d0b1017010606140f0307081e09 59
    0x401070140100c02800c14400c0c05801043c261440208210300120019607031001d409030364501440f201e45030b01106c2c1c1c1e80010340100100c0c0309124100040030781c03075000c1c00024005000c10000c403c403500040805c442c2061503605010041030500038a40d00140d030041e81030054614030300710503040c1000d07090241c3c010b50316480c04104010802c000c484800c412a01c9100110f0180208803141006d030240500000b0b00040043c0e4041c000040701d1456503900c0d0364010520f072030042051034640c0b40500c0ea0800c04c0d024a0400b10082102c8001200383d17203c081042c4010040380c0c1e62003c088484c011a12001c3c1d06004600314442140601840143c20443c480d00c03000490b0b600e81008000c1400400020804000007444842010f0755040c8030b9040030754002c88808441c2d01c50049404400006601c800950400d00c02040440241900010304a801c01e403200b050b00361001040c0d901c0c61058002c000e1144400b00000798079180910b105c19002021600c61003660f244161071601041c0c026151110706 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 831548570 1250 831547320 831547399
    0x9140c162108060d050d0f030207060e0106030210030903020a02040f0608030c01050906100503030703030e0708030c160506070b0103062708130501090f062003070c030519080702010509 81
    0xc0390040000c83c2c0216003540c070349585040729200d5603100c2028000c00130030000007071510704485200e41c050300c40040d0050010040c6001a90005001b801c07103200403401250221010200140284070b5040041e4054010380705e8203415500b040000c2c580c100050085c81e642d20008117410320104042e003c150440000003c0c1070070111895440c00c20010240b100c0c80c5240b880034171150710088113540c1c000b40c0c5410041034104048035698101085a04210325902c40402c07140901c400000303050b030304030441000340048182c941060020503c0b6030346000c3c100c0d4400b8001040055010342c00000042d0386464001210741000c504403107240100e50741034940c500d012648604010001d047c00c00148000d0a01c580c09a1030080810484481445a0070900c01002c80844152103984d81403c40c143d25441680d0303454105180078000c0024502041d56a40f10b0280400d40305200c5000e403041c1a07411404550802066500460340b40e8030111440c0d8204054a034118110075036a400e28024025800d40c0194 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 831549820 1250 831548570 831548633
    0x20d05090a0c080102090a0b0c150709051212041e0302040603141e0c010c030212030c1e04050d12031419140c03010e040c0308030a0203010501030609140c16 69
    0xc42040c240c020f510b0a034070401c1100204da0303da200c1e00084404014101c2c0c0c56902c01b114050401e01419444210b0111440821400b60391040151056540407519101d40e100c2107050300f03540301c000411400403440d042009000b26040c038691003084118824100010b2502e80d404281074603102d61003266007440250512245003c1404980c031141c8a0081c1e81c900c400c808001f265076a80e82c0041241030103100000c18041c54802d00c00401d06140040c12180e490900580084c1107500c50010f0140c000d96441110401c554100e0441d811030340028491402c264503902c034010301256085600c414140e883c02030b020b145045552581c400e54009041c1c0c03640503141d000105c16107a45024041d204443d00d810042c01c21046030a0300c0c10760b0030541c102070440d60746140200450f002500090a118404800c200040c41550010344c1660002e03078003440070b55a543d401c98107403298400ea007a5507400600029591f0340d2280d0240245640e41c1005070788050490300d855180003010310342c5a0b040c904041007540c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 831551070 1250 831549820 831549833
    0x340c080d0f0e0901061b05060f09010b01080714031015020706021605150a17090604020a270b0a0f12120c050d0f021608010c0206061005090d06020d05090a 68
    0x507840c62800d10382d03036850441e030004030001c005001d404140000b40116000a004140c154425035610401300ca0050800101500034501c0840d94143c180d0308100c4000d0080d4884c074069401004140c60304e04100940200403007090704001c29040c1144007184002450701000c0c8040b144664503500038014040c20908024142a8440c21940c08141c520000304043d0303d411118110614031582c009440d10002c0c0c50494444c001c2c0c17420700c001c1c5c0e461107050005c030b0000400c44a01580c03085940407251a921061140604040100840f00310309294400c4415001c42d000000104e2000700b90200d4031340c0324400d00d800c03160540c03c1009001a640e030f64604000040801c42c0d21784600e401d010403002d00e90790f01d0781d6640d03480d02280420002c0003202104081d000b0416050700101d15440030711840c3d01e030302003a8000c0080052001c014840e1b1000f15205044c00d100350000303001e081e507402d0300d404000405d102c00020403c03401c861496080108844485051003a0782c060754096001d455600305900b81103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 831552320 1250 831551070 831551087
    0x40e03160f0f0f03051c0506210a0516090513020607021306050a1d10050a0605071a160e0f060301051210020a030203160e03100b010507060908041505340c080d 70
    0x10006c40e460300303040c00217a50398007200b420351202c8040b49096070070081025074104071016000a00c81d05c2000030181100c4000041c180075200b018208000542e5011481d5162281e2404083d410200030411000035042202c40000e01d10214500458299580c901182100c40a68880e0420000f42071400d07485500701803640da000585012020080e50809000603202e000c50b1041006000000810104100f07058901e1110140c5071083c8014904c0c0900084403100300c05081d250025011903812022480d01c058001051100900300303500b10380c02c010601102d00b194008440c3d40d40704a0720003100d84441c5000070440710015650240e02c07810045184c800b400c100550a00600c4048850700d10700c0d4900098003070401654040120f05190740707600694241c0f0600402900907400c2004000500c645503005000321031420200346103c03502c070082110329008490313000004d0300740454004130560445030401b0303080340c0d080d980e040d000041d9900c25411501c240c0c041c10142c1c03c0712003041402c0c0d8004158 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 831553570 1250 831552320 831552367
    0x903031303230f060105270702150105010c0f0b270a020907020d02060f07201f0212040b06040b190e010906030503030f070912060209040e03160f0f0f0305 68
    0x43c80f035441003010540d00c80d01c0c1401124001e810601c0c0c0e001c603840207003c40514000503544800c4450811042c020b49444207101441c1c2c541d100c82000040300c3d40f0031442c2402d405d0f04000045540f25050741c9808100e50301401d01400301c03d410041031243c507403641130303d18010b241c031001300460400c0344140300046038010043c40940d00904900d110280d008640198820750300d000c0346003550703168041502c01c1608403c6a600382d005000711400000000500021807044840a00210000d00e0403c04107130f21401450088040c014400f09000582e20380500d508240c000384080b4801003400c0c041103c1320200c00c10081c00e810345600c104551034800421078058214810140311190640d202c00740c0c1c2e1f100160004040360102c00001e0b10080c4100e00400141034a0f250760030350f0075982c0c200a40a9004a02410f201d585408084044c0c0b0100204444540c41207a040c000c40380302c6034a9034078541c030300c0b04815601e6001407a84200050007802c0e940142c00c8c030a413102c9403941c40519681c040b80e61071088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 831554820 1250 831553570 831553573
    0x605040c120c08070c030327122d0309060216230105060a05010f0908010501062a030f14130f0e06030109170d091a090f01020f030408090303130323 65
    0x380042150b05c07000f8089041d41604000c20010684a4410303042c0682c41603c030044841240c201c020412800c015070910415581c4018000030410000c4002030603003400004408070700000b1015090107a00302490a5010341ba00604019a64028580416a0b820112038441c2c40701140d5041d60304d41c80002165003101c078000c02c400c0c5000c0340400c10001c003074010703203043c821070540040300e0510494065001e0100c0c1c400a11203569154000b07013018041403402c612001c016044806081b0400490043c501d40590fa0100824080c2c2d105031054010390703503800c0c0d125504000603040303914010701c00d500400340b0034040903041c4d103403003001c3e000400041d00c1e06110782d0400001c580452180c00d000080384440b0b07041e069450308035001c0e1000626100380e00600c010640e8105014141d900c03a861446600a8015a086803005810082c202e1240d8481149082c0c5c0c14808240821440f20103403629880c09011a80341c0301442d80c202a2007101035008a803805005010305480610700301c10400a50340100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 831556070 1250 831554820 831554837
    0x11060703050c030408300106260a0e07090e0705330904180b01061707021b1314040c050a0b1603020705150405210a14010605040c120c 59
    0x201c900c2c0702844044c0004d041410003082107900414940d080700413020351035410703025a08442440c1c107a4131600348070309004181d07485840c0c00c00031008031001d04030007038800c4001d2590344c03005031400017032206009402c0980b03d0104042040482c521441401c0c0e01844010b00d5000e280200304508041c091001c034201000742c48507c000036803044e409000c1213115081140e2102c0c0804c011400800002803512201d03070514506005009034070036140d0503500603984611104c10000341da800e2058040c1c0f060b0006910034500030007401c00d281d0781c1003607299000b0102440d20b081d85101e20140c5203070540a2010750810070502042007100c1e040040100000d944220180346080203541d90b81c0100e040400f22800f402030190101842440030500ad0301004080740580da420000c5019030342c00c1f501a550042c1208900124603194000310700312402041002002c03003110130390300c0d0201c1d000e0303070766a800280d03407540e0010505640c0e5003e4103000a10940e20492584041e000d00360541e0300c10f1040b07a0502080d02c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 831557320 1250 831556070 831556081
    0x170c030c061b0a300501050f03010c08040b150a0b090306061e060d06090608060115170403210c020c0301062903090f030d14151f0315061106070305 65
    0x1040c3c8510316900d0820207025804012480303440418030360915103034029410311000c1ca20050784098141c9806890300d9074482022001e0508036031079002d000c0b01080d810000280040d441e80b400326031150400718806107603400d20002c07542c009819007081c0e021503c00318079041281000c200c0309600120458006401e0001d595020316801e03000038469008410020300c201d01c0181c15004500100425842088403503a140100f5403610700a010761807103030303140019100b0305a1051304031810404201078079907020b465503642aa03040024176200d16220b45035542e203902d0251300b8494941c402845030003030700d030080700d400070142191200d030002102200d4810040b0050003018490030b4190315400c0503641d6030340b90340c0b103c1b41c500500081f9454061100080c0c045806845410400fa1810008603c8481d6203e58096003103400c0800d00e016084a41c0318903031131458241888000c2218900c0c1000036000201080c415044d855980100d40415900c07440001070040c02c0000c01c0d40a41d061400b0000c60070308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 831558570 1250 831557320 831557371
    0x5011e11030d0204080c03070f09020f0f04080a031d0907030c0c02090a0c021e15060109030609110a1401020c0405061903050d1403070f030218090711060a06060e04020304170c030c06 80
    0x9c9000f500324083e400329400b00c0d80c2d011b003811640c102c1c0a8044090b121903542c0c9000340c1e903091207401100050f440d03c0e01d1084034101c400b04514400d130010a03010a56031503801c11001008201c2030b000c100040e4405a0025880d2040c1c80e500136403001e4000b203858904100003901d48030b010804c032100d45c01c040d10307048460407000c6003502844440d024541c40548400004844840464002800151400e401c1308204891a8240c41d4001c605403400f880d400e5a8211007040401c03a20001c0740540c11049900b1094505640495801391005118042d64421840d01c80503400c00c81d0000c8915601058403410807a420140903401321142c55145461494110001808642c1c1000004180354001c20b0805241701e50360844441d0003c09008442c09192821005003024071010030040e1030300483c4085100e0344218022403059030100e44031381101c10045400e1100a620040c0252030150040ca606610502c502004260b802818030046484401801c0702c98141000505090074688407140c00c035168226 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 831559820 1250 831558570 831558599
    0x90605220209012c070806010207060e3316021801030c060f120e1b060306011b0c0909080d05070c02090a0c2d020106050a05011e11030d0204080c0307 66
    0x111100d48203500307031300241d80d040c0252148a00340e01046584100000c3c140c0c8908100e10170b40007642128109941d44c40c040d9858070100c0c12043d00070103945210795414000301c0440701040700078410718500c01044128815540c01034010010b004441d011040306602d0302c0ca41441140b02c9000c110802545156158061f2041c01d201d500280807070003400b0040725000310300810009114900c00c0c0580d01d550301d0126210080011005080040c00d620003004c1e05041b01624418041078450800803101c01d10401c040c0540c44404036003076014240003141d051154092001031500c0b501185445494985107070040d21001091841088010003984c0b0143ea18041340503005200c2403c0001e09180015007140c018240110510814004440f07152a507081386a0111201d0950b034000c01402e61103404100742410207125150003e112154054410100c40c40007c011042ea8100032110505080400707045801034032850315000c2d03001c01c04100b0901c0078031003420326000413400790104a04240d001c008150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 831561070 1250 831559820 831559829
    0x31d0a06020a02042003061c08041403060f150607020607120203070221030313020d02090108060612030f0f0913090602130503010b150a02010603020604090f150807030204020f070609060522020901 86
    0x82300c0e2900189030000301003018031290441140d1796143d44444207415003180140e820f5003e071040302c0000b8946440e0242c100e0160b603003102c3e00303100c60400300204a25604203d0040c2d0b4440e800300440c0c400074000e20800501085150042c41d11900a40104491461501018015841300b0300342c6d180101c2c0c8c044100d9a101e603455045040402190010a821400215000f034100841c000081303842c0d5030000b00d451007240c04443c218001400030104581303a000c0d03008030f5640f950084c800305002107a01c1c000750800240c0500f810668a100c10661402e4400481042d1141980011038519650181880c000036106c107800900801c491040481c800d1410301c008078240c80000b1600d01d80c2e0300e10130341004000759002020f0544541d1039444443c000c008210014074181d1502a151003051541700b801e00448040030090724400e4555000d0102943c0150321002804108001110000d120780c425060014000c1100007103c0c500854101510000b088900c0319551140c520000140c1c2c50035034860642e0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 831562320 1250 831561070 831561079
    0xb12070e0f13110d080c01050a090203101503020f032b03200a030911030d18050108040b0112030513061715220e1e010621031d0a06020a0204200306 65
    0x38040c01c0c8181d01e80a1b154500340a5420035041c05420085078102201c814002c60523a04000026500304040700c1112980791602c1030050300800c054580820030024000002e800d480b0710581c41d00c0741080304082034180c16580038002c5146800e02c0e80c94816201c1543c0c002c191003c490341130b050300e502540685440c441c04c05440d240200104040c0740c0c0d113036881c1080078040351148c0414040c09001955880c00703803c0003600e503075000500ba62140f5000c60040ea00403041c3c3d507860342001c03024002595505425014020100301d000410100c0c6a100c000401460b52143c5e031034000e6644401c2c0d0540041e22022401d8203840d240340d0301750f484070845c008180c8015560b031941030150501d8806840d055248102074041c2100800000740d04602404c40510860020400c10b61903c00e07a0314030030310300b50400181441300400500001d000350002c000c8040411000c40000ca100c600003402c6417099041600160001e045200841c10b2034080c1c02030300c507850550503001c505030082101d41d0b80002080207200307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 831563570 1250 831562320 831562339
    0x10f0f1e090b0a05270a09110607030309050a03080702010c0306080c040207020a050307061107090218040f180c090f050105060a030203062403040c0b1c0b12070e0f1311 74
    0x200d9450f80e407100014140503041301d0100e1800303000019040401c0c0e00502c081d0f80e4000001c0c404124a00c19404d0301a03121100390040c0003210140115500000c4048085c1640c1c2c0341100c002c02e6080080020461080d51100d0440c076040d14020f09503034071300c014034003410b0805406000c011001308610340400c03400e5500585a80f00c6000140c519503103035202c0340d0180a002c0c408113150b030784441c4d2480142200003c442c86560365146002c124803840d250303103a480d0500c5468180525294011602c0c41e410418042015058040d00c0b00c0700002c5035804840785003035180104a01207107405542d02914558008112640c501004104603104807d203420030954000000740c2d840d80d070004000b96038460b05070f11183d946082074600358940e00984096401060b14003000500e40c0303035001182c0001e00201c007036500343c000b03114820024261b5441d0180d4070003201c00005040020400000004101040842d0b015003046000c100c041d00025000301d403050420005d42021840d840d0351404180070070381b0350054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 831564820 1250 831563570 831563591
    0x3110603041703190516090e0c09040207020d080a0c06050106090e0103020622060320030402130b03121810090e01152001140f19020304110603010f0f1e09 68
    0x1407412550203040c0c0e1252900041c4840d03206c0011085140028036150624055102e00c002108558100c8240c1e020315410000340b40e843c02d058001d0300c4c6035031003c1e16425408402c2d59661011f07800c00008071000031013000c00c0000b0b000b254001c1900500c824204281103a0912a1100d8890014040640190300c001242015072083c00216000c9459044000e6481500c0d37040041c00b602110017001c112840c030444400300911404216401290b00905903841e91031454441e4026115020080d9410f0242807441c0031102c507008024800d8071584074082c0c3c180803009080020008000744520b01300b10601e034040c0000b03000e160440d41910601d11501c220000d002c1d0b070841350591282c19001a8003149104240c003401d0540003c0158880b91070441e44643d13404240c485025411201240d01c1c41c43c0c501d6803070b403041c510360056030014002c682c4d5500c2107034100c000c10026031081e4015001d0000d0588200702c00d024000049000d85481d211440c10141104400e100c568214024220401d984241001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 831566070 1250 831564820 831564841
    0x20307050d0207150e0a03020f030f1b0f010507030b04060e010e0712091b14030115061d0a0f080f0313050f310c0c02060d05040c0b030c0403110603041703 68
    0xb070840707841300700c28081c00340100e20680d210400f00740120050b1050059130810440c0c00b10079160038080b40e08e0b401d802e040103034140030041100c00c007c2c4040c1c0d01070000f620744000004e00485100d1724468502040c5003070500c062001305c62984d0300c8600400c5c030000051140340c41026103141c210100340307840000c1c0c82d09c141542c00100402c46c402440c500d00714844484007868620010100c444007004404041c0100050509a40e68140411810312400c0414469207008011205020007000754030343c50908244040385004c009900058608103131503a0400003c0020000c5120b000c081c007001d5424002044a201a407602d240910340c460000350010034010380311040001c6505015400207504c0008880011610f80e0402c1040300d00e080c109014076204034010b41581d44000d81c00b030701040c90703c0d9200c3d4004005100281c4200c1e40b4018000c0000340514000d0091809008003020940d0b60714603500d450b1089243c07034104036000d4030b000d00402c4089400c81640600621840c49550795a544010070303071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 831567320 1250 831566070 831566093
    0x50117131a19050601030c120e010e0f070504111305061602030607171e040803070507050f0105011d0603031c0209040c09140301020304170d0b04020309060f0109020307050d0207 78
    0x250071202141c4100080640d10000700c10820b00120740030451611064011070682d44415846408a6038031405c1401c51207035640b21040d1080310300b00004002410780c01c0642000c0d40c400076651a03034007100c824031252802c1e100d0f0300700705c80e41c21241c6032178212100c11540c1c121086100741440340e58081a07201c1031540c01700c2c0049550340c0c01000c0c0c50a520389a04003500c11740c0c4400d00480c9014140303001074244a0382c40340102c02c4940ca015039102540e0b45580fa00c0c2c240c0d100801100411809000031000550304000c400d41031035081001140560500c1d5002031175030a901040800440954240400303924003204642e50340307400389120317414102e5100f0084086e10070b042140703800616003556000103580c42200007098488590004040264020801d8240d0105460181900410714588a84070700701100a107030106001c240821184102070010b02242c00407641c00d1602e4000c1402c01c021b410f908070030a805011080c0045003142401400140795009500b444408550f0000e00181482040c40d400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 831568570 1250 831567320 831567353
    0x1605010c060c14040603090c0503190f020d0f0f111005070b0a06030c081e0d02070e0933071403070c060902040c0306150306120209070309140304080705011713 70
    0x2641e139540c2d502c0c18010010031401c00c00b611080d0940c0301c086954580441c080d2000c50000ca2060583c00090300e40c11401c4d80c040508070782c004003c1c1c040600086c0710382680200c0600803101401007540d90f0501080b5189020048c52145a0b550202300102c0c0e042425644c01a403c440710204079a28884075900504080c3c2024204d03260404000801c1c0d24000f8040340141080301c80b40c4100d03800e100c9070741d58552429a4400c0946c00c890000e11200115110a41d0f07c00c1d800011681180454102a143c00c884c00502c0580ca082c010350075000c03483d4812540d40c000f040d0b80780200204201607100c020502024090b6020848a01004400d10900350001c0041c00d4005008000d01010309001a000701a24400c044100150304c0c0494100342c040e03c105821a2a070f51402c0070500295400c01005c250001e0082003455510f1001130003060590f0717030354080c0c8203125000f0750360b41e0b007001100307840e151305a03200da41000340c40c00c0389845061090003080d401a0703d072240d04680303880714548910500b840090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 831569820 1250 831568570 831568607
    0x907090602060f27011509021206100c120206100e0f0424020c03040302040506060c07030f020d140a0c0b0c10020d090f03020a03170f0411010e100e031605010c060c 72
    0x448131640106500081d0404401400000540d80d152100c109a003da110500e240f0b010b008000b804908040c41d071420f040903240713880284201c69980303012480510b2800030005038803880410496003a04020440508108003103103075a454010010b520180300180000c6c000115641000d0341c3d003103a00300860910304104070641d02e81d18900003050f41d80c1c02600c0168400d60801010a116080480032114000950409006404d007191500082c9011341e94089030428104200c00c0007060b1b031115102001d4549001510111081d03041c42a205e50032508000c1380500200b2102d05889000214200103401c560005a1030f0200450280001d04003400003900807201c0009040801d640131030034444841c070036103c00c2806007800c078161b201c0d901d04551781d0040b0a80c01001c0390108800070300422400c2030502d001f0a01c462500c3c041542d01d6a105044404502c2c03030000010603180c00d001001091941405441001d8503100008004007102000540500c1d550284001c0c1c01d80700d0210b00c8244959850b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 831571070 1250 831569820 831569881
    0x1b1103120403080c070e1e07021006030f110f0102030d0e15010605030703050115050306010509040b1309030806032e09170406020d0305040206090415050d110907090602060f 76
    0x9040b4015800240d40007400d0103040804101192840c01b054022040c0038164a45810008104a20041d024210206610954460020440c80741c0900006584102c0c2a41017200e814a0f00101100050b04414456103803044110000d0b40d000043c0c941100440802080c1d603a01c41c10813500b0702c00e10f451548190b4044000120f6000d400c04000c1d0301400e100d94041150703a84c0c40c070600c0c0a8281c400510800544104041001580b00744041d2034007010052000a40c0c403e81e500240741c0b10b41048480b00305540f20583c807000c0c07580042d079540d404901038000d4900314159a182445000c0c503a4400b04260303520001c0c0c00500c0440d507001809540d0321115130480921030800070011340e0400e04c00c240c0140f2481c26091901880381c010140640e50141c106403c0119010800000e070041400b012086061814002100c0e0740303004003c150203028040106500443c241071191401c4000c041c10140510700400700f113900d0b40012180d07803003900b15210020319111440c0c00100032208009a041c0344160a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 831572320 1250 831571070 831571073
    0x2404060503012a0f02070303050a051b01061e3008030108060f0603030a1409010201090c0e0109060b04120803130204051e150f060708040b03010e0907061b1103120403 73
    0x1200e6580e07056070b00040f840341069019003100c0039600c0e061198010380207200f040000a000f60042d008200007810852b040903040c110091900385d4a503150b500751ba441e42c0d005c124202144110401c6404149042d400c4641041c1c211603481c80d94600305050801c4800c607000429858012030100d00c0d610410555032541e5400100307603226401c2e55081e140f80d807850041100d80ca000012950724054680301e49a06401650f503075110358004242141c195500c0b0203215000900040020000d80700410003903905504200c00c001c201c030202d4021191803041048288580b0801d0705081080e5035004285039035903616100c5041c8041c1c02c80c200250010700f0300d0140701441881c5014109960b0300306031000b440f6071b1903040040341140003001d8643c01c03004803141c00840c0e09000004151050241c041c0c075141c503555440d00c6030154000d03804013202820100900410000511205004296a1410350082040c00c1c5003d1640c01c54000000d20000d904407041c1c1c09602e0511407690510344240c038240d02c55580307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 831573570 1250 831572320 831572351
    0x140c0601030209010e071704080d06080709050901020c07090c03150824130b0c1b16050105070b070309150c1d04050f19060f0909140105240406050301 66
    0xa00003207100b08500f50010503803103000341e90b6a206085581d990000640500b603030041c0100080d2081c0e4000340c040107482d43c08500d50190744020100b510090500038034001c850412100007600c92100f40c4d004200c40c0b0082040024050140c542e000e000050a650384003095008100c080c40f800440a04840e00244448000ca003141d442c291013824074946484403a1405c0000504640c5440006032024803100851040160340ba441115126038602d05591550a00c00d101484c00d440b0304250f00210881e828415144240030082c02d00b070a02c0da0070624030f50703154140640000e018504141c1e0b5061030a06118036840c4065442500c0ea40030003002d50302d118010607459040350119121040051f80c41401e0800380300d024415a5040b9820880c0c4d00c0c0d0481e2200e02d0183d82108600321a2a240d001c1500f68070950040c00030030a1140026040003545040c000ca04100106c0410780d9150404020340000c0307544540d0a0381f000b03950b040140b00c1c4e844000a0042c01103401c2680c0540ca001c59030045c1022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 831574820 1250 831573570 831573583
    0x3080702060a092303121618030302061503030904060f1a090d170d060e0a1b080403050a03111803070803250f0515150d21140c 56
    0x1568207940c86955007805403800c0e6251000010303c83c040c0c00c0003840c45510038070b0303d42c26000301301001d481ca00440da152282040c0d6080c0e965440c01c06941000d45825a00f1034a00100342c01c3c0e60400303507490351458401944801d00145000d08200c100f0744440b81a0f901172089843e1158000d10812680d40c442175070311483c00b41e6008090542200100c0c0b465000c0705103095030001c0c000284441c81001c019507900951031402411001c0000d418818500301001602818000d010101c010121a14102544e08240d44640c0008403405c00e14001215a965000340e50039801505414000c0d60b401e000710040700100380c0140043c044a001094408065030702c0e88001c00c4403842101140e5043d5283c0c81043d8582c828400e041183c01400c11515074410400007205510a0003409014407030340f2a030312014100701e0007030040c042c103d01c1d44d010060948014a81e2141c0081d0036941d400c1d030203030300d80e98100c00c0b05200c044a50203148092906400d09205101a562902030042c0309500d0301c4a17152015035541c3d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 831576070 1250 831574820 831574831
    0xa0302070603111204080d0209060d0905150411090603030d02161202030307020712020f0904030e1816030f0f09031701060503073c020d08060303070b010303080c0d090308 75
    0x9041840e4280f08080c1002900c05804021025a1030b079141ca07500d0a0f216840200311140a940034000c04825603104000703400f00809850000c98085030740d207045802c001c00c894104004000b08401d000115200066803500303601c00350f56904003034840100181c5140600316088140c1400024a22000d0401e8141e0078401407045c8020008859040b001303036205e000c2100c4800c01030f0701050307003000960042c00300d50080314000f03401c5462641394640480c00d01c2707100f2078094001c2080d07000d444d40325080c50b080c2d0050a9034088420707445402c04218000c042c100782c1050500305500c89240c554907000302d602800811000590404c0742d0030741850041c000030290500c0b03071180d8a0103400050304038000d000712842440c8550f03400f662860085030700400d0f444528540301c0d034012000c2d603c80030000d0b01c1c1c0d00005117800ca5001080c2c00b402c2a68002c0483c04010303d200c0c001d4000f404108005140c0c1030715141965414180351110b5035400c044a02c0a008103412090b540e420f10b6007440525070400f03283c90158 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 831577320 1250 831576070 831576077
    0x90204051f05100f080c0d0203240a1404021803070e040b0a1e020c0a12050c010c030b330d0501090b0909120a090b07050705030c12100515030a03020706 67
    0xea9842c02000020301030003e0310740220b1204601408658807458401c0c1d401a043c074180340c2444140d0358910200d0700308071500001d200c541902c04503a500d04c000784070803150086404084143c100079070428000300303291400380113980218950981c411902210907140c0009005c0764503050341c840b030403003081106071801d58490407000b0103e000c00d2618052110400201c1c0c0c460030301074501c06e52002c000d40c0814031010490040c81c94890002e210310034007620048440e5203c07501d4054005000742100c94020303004051600d800c2010800d40c40d000d00307074840c45403c240810a91400b400c0401941c14078074940d00780c40d040c000341007090280d156004a040c0c1d4a41032040008112030820701c003044a080e16401c540b03a200b00760b1401c52540c1c60b801407010310003a10302500070503038480e50300c000b50300004011a50384e0026401401581810407601c561084126544150580d05810050f00d8604007050101e448ad1038000040c0c1c41c070200c0c01c0d90880484082d049401d15078041c00c0080d00e4088170f00490000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 831578570 1250 831577320 831577381
    0x303050310170c012703030e041b0e03100b0a0e060a0803030703090c090c05160c05040f0605090618011203020102040314010e0105010b03010f062a03050c150c030a05060409020405 79
    0x1001c41e0313500c0c80070880c2c017400c0c0c01c03051421920300769405040409400c3c0d2094541c4405c0052503d00b044000c11030b09651200c904d04c03980041090b082040200805a015160090038a441d554031400d11084861002c500701301d9407541c001103400c208150304100a14840041400041c607495400300900b58041c036440b90140d40c4400204007611072106c05000003410501100381d841140d9034821003242e2042c041d040c2000c5d5600040b80990380f0300100b2210055440c0810004e40c00c060650350b40c009800c4694824101c5001091511150103014070f4070005002400c0408041c006d60440300915000010b49100c0000e1002c0b040c0604070112940f00c45500302000040e5004041040c1d0341a01c17003903111007040f6801d104045660b0441c0003c0290046080c0000703000003015080c54940c064000c1e0340d40c0b50340740c0c500102e4a250400c100c2c5200c0b1105a0441009100d5840000352508801d01544c04180f41e1550030010700501038018020703500c146040c042c441400d501a40c0200c40f0000f8a140d004c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 831579820 1250 831578570 831578597
    0xa030c060e07050108011527030201030e030a02070b07050a050a2907050a11011d070303081305070b0c0a02041506021213060e0a180c091e0303050310170c01 69
    0x4503144035200d20f0b80441c80381001440819035005004074280c4403860118a0a40c0c0e00c140c2850011921040503060158100b017482903503494040c00036880d107504011441d118003c4002903560015205611100e40081170102c1084824018013211075049000c460140217141000050190090286e410081c0000714100c00315a0b20481070b44a081d46071149414105250700642c0c031004a0f046e540316555807843d0700c3c800d200285141c01c14041711030f0010803a46082d880c01904c0844003820784410152944800800140c00203422001d0b00d525102041d12000c1c11101d062600c40d151800941c0141040308400f00101c007006200210b58aa40c03c45810350720032407095080303115803022005011041d06051000d140650701e160700d4460082c005480c1c1c02c2e501c6290300d41850b0070900d08400281c40d080038040b80c6600000d0000074004003560624220100c0c0c5502c410700200b44402014000d0100000380c0b030740d1306a80f50718001c1c80e1a55800d03c80000d4003400750b0701c179100c030800940400c0c60f1b81e103e0079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 831581070 1250 831579820 831579823
    0x1716030609090b06190305070305031305092509150e030105010f030822031b030c062d0509041812080606040905090309060a020d020c0111030405040506030a050a030c060e 75
    0x414460f0090824840c03500d40034144080d0340d5445582600c0c080300b02800000090007088074100550248000d540c484070889502041040301c0d80c859442029403500340b100a651000209101c1c4100c0490f0400707075082800242d0b0020181e6114580314288040c0000145401030b00040c486903040b40200101e07030303c42c00c0b45003000940c0d02024010100c2882081220740c120796081c0b088401008903800113550740d03070318540d000c0d008020020706015404003c1040000c4007000e4005822f0394200050b080c036040700707410760100030001c6050f41c22036030b4040e034035607280190300b22148448042c0c01030024204610b4050448031011200f12170b165050840c1d0b00105101b8140701d40689401000c041c85d00b8070300011180909405442054140800c102130085540c1e11401000464280e0700a401d0f44503140001074140384449207514140100d1014800c04500040200c0b030a0f15000c440004580d00e44c032002ca4075202103040300070498030450000340203041d0272000c0c81203502c0c0300c0c0d4030600c40c0418116515 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 831582320 1250 831581070 831581081
    0x906142404030807081909031a0112031d061308070801150611150f16172a0703021c0f0e0f04020d110d1802090708071716030609 57
    0x100c0600300140001c0c00002d0b40d15009080712401005c3e001d040074580b00a00c0d410700a403481480c0491040c460801c10013080b000782e24904105994000500d601d0710703c2031a85e50b201010001c0070040080035825212003280c5405600c10005051541c44444480e0210707010f103140d0051400f188190ba20009074100140500c8075a410010000c911140c60a00255654541c0c010320085502590040c030000c2d00303004000a00c01d180030040c10503241007000303100001e240901000420052989031130f41641e04001d0080307401041034400d00c00d00c1c40844110030780c480741a8096030b00c99072001980c4400e140e40044c20640780010307a48000521804410240c48440b034101e6a480418041d03400d00c115480c00350703640e0317558643c00390001d4500104545041d0458022040b00700d81c17100d01040402011172903104041c0002d818010040c8080c40316000500c00d00b50081c1040308000020b40000d503c5880340710081c02c210840038034200c0504150b907080201d444480c10300d0001a14041c1c0020302081d0303d001e03071b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 831583570 1250 831582320 831582379
    0xf092907060c02032a0a0f050718020910053112120e010f0804080a05070204020d0501060207090603050a0809031606081509010e18120a171005060406050a09090614 72
    0x6d11030442103590350265030b00c520300b0545450040c06800500d0308141d80010350618094000140e07960307a490f04101c6140c440f03541e81e008100d410301c1940c0d9a250754900e140c0700050300040b0004100b1010401040d151005d0308040840300100b00c90008120304503002081090070b644407281d078907000e00d0046480401c100780d440c0010724000041408203460308014103504004d440d01c14a080450b0f000705099a104445903001d280da141c00400240742d06011080142c410080c0070b129040c40c43e1980b90380c60034500e801070301d60b645c00100381d075150f07030200103840d6002150b06140c04800d594641c00b03001c01c0707070459403d0514041101d0609003441d11000b02070584051007841c1100e500e9680102807920b00b6405840c03660702c034401c0303048454584503000c0c0c003200083c0d50f40c00d0070010300c00b0503192143c54041c00d001441d0440300c50900103a030b00d510a4600362442480c250380c03601044641191b46605c0b542c0440750345883e0590114070f1110304400190075400546034008140d403402d054442c51122001e5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 831584820 1250 831583570 831583573
    0x3020d0f0207171608120403090504061a030a09020a0b0c010b04050408030f070c020301020c071404180308100306022808040308060607080d0c0207060f092907060c02032a 75
    0xc50b2001c4080400c05084030000034a4605024421a170781e00f110780c1e000711550340342811200200020107910500d40e4000e41f400380d405000882c908006000d800d6401c40c490055103030080009002c40103540e02840b0013070340042540000540c4c0d42038250706039100303071002e4000c2d5090030100781080c105402418001c50340104c04524594840701c07100780400c809810441000051411040941d031300340040d00840e415000905001c0d0301c1c0c03901c80420345400e400014000d906100050540d0030300000c11004940e012304000c102c0f0350300c0034010660b07031281d900001d04040c408503071161700030030759501002c01010bc1c0b00401101c0014030025144001c00319401400508400700040302c90824038085c284c0c05100720b00040c04d1103064407041095918081c0c4680c016809a0003c2088560001204102c6a010300304022528208901d9014003c119036140404100151000c0b10211000081300c0078240c02c4031040007070140b2414020f4a99014070010352000280c6203603010900c140e03400503441c1040600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 831586070 1250 831584820 831584843
    0x1101060e0c03040f0f110a051915090f08010c030522032a061b0f02030906090a08010c1d030c010903060f02090306040f02090a020c03162103020d0f0207 67
    0x80784031a940024400c441c00703040b100c400c8001528481c1c0140143d4800d400c0c1000301a107803418008044c000c0d5004901c103400d0140102c0b81016180d01e080c040d03449910760014032000350441500c4c1394501d5800f0420441000100203042d081c10f52021812208607a000d00890f12403c42000c8001c049121030458440141405000640110100d041c5140c10b82080280201e480b20304440700105c461054a017251114040d5031000030030314240c90501d0460805206031490f0038802580c80c0a02aa0540108130014001c3c60556803654400001c00450b0002d010310020f84000503e006110780c0c004013044510710712143d180c500407030301c1400c40390180c0d101d6071003500e1902c038200a06030f09109844c08950030003e064580d1030511005220318000c1d0066843c410591050040046005050740003ea02c10f00c00c0311074200000c07003201c003c00688244800000c0032400c0456403070420301050003054003a80355a19100d03030950003070038540035104c1c400c11100419000440036481102d9004121580e0203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831587320 1250 831586070 831586081
    0x6070305071b0606090207050604050c010c080316180b09090705041d060402070804060906020c010305130b07020708060112170a090302012001051905070f0206060105210103080a1101060e 82
    0x91a4200d0b190f80662400314105940702141c5040784d11890040d1643d4000c3c40800040c040d0030009209940c0b400c1c038101840c400306454107038580c0405070500c00c480c00348412920005d840f4404100503440603840410342d440ea6181031529907400901c40500900f13041c400501d146001d84141c03001c507040c40c40a400700121142c19219101001460640c2c0640d081c004007010a040310040c0020302101c0e11a00440c500308000685041526101d060400d4203184c1001007510b0700340400e00741d1961249911040d61206407051b41440346641108006100b4040001206007140c0c050910341401059214480c100c21690243c6c4c031701c1580510000304a0180c410801035100d40d0201203603440c003540f03000113103454040752429210300f551981e1810742401c040c450f0a40c000e209103600201e26043c0205604c06020000e51500c1d00140440d05009000c641255445803078001d85600c51780c81e8070110502c2d070310b928003481581c020a201c0701c0001d44150f0080b81d2003005201360b00c240d45e058008400d80381d9a2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 831588570 1250 831587320 831587357
    0x3041e051906050d0e120706020c1908070f0f0f031d060705120f040b03040c060e0d051f02040305060903031b03090604080a03060803161101050405010e0f040603021c050607030507 79
    0x340385070072100344240100ca40707106000740044e160b508d1140c1800b59561806209091510070401d00003170541003000d0010300007e0b01d50041312441d40c0c0c0080e50304070b440f0301d905044109062290000d41800120f511907801c050380050104040c04107100042e05460311002805201d0080d614010001ea00a22105840f8201c10018020502103611420314041d250b210f80300da0b130703081a00c0494080302c0d0003a061044a40015200084420640d004100585c075034503810b6071944000d004c001c00d1383c030004500d0380c00c180030b4040f81d000c1d5401c02c0c1140c2c840e0900c1d883c2c444d6658011159680302c03c2002001c04450041141141c0c02049008000d018036141d5450300700c0c00707034410740c010030a06a0380c50000403110000d101401442650f921094455015818001c66a19045a8240c104801080184100c0c0c1e009024032441107801c4d2001042c00c8c444201141c002c1c0603580029508c540c4c46401c00038180c4982006000d5148030344e040d80e800f500c4002e400d40641e842503440070081111100c0c248801c550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 831589820 1250 831588570 831588581
    0x506010e150310050702070b070f02040b010e0d0308150a03260403140c01030e0708030a140f22090b0f1003060e1005011715090903041e051906050d 65
    0x1010380507078000d141c482000a260645100801829a844804102c4050b4040c0304040041c0701c6179440c0c40c540b4280740d0f16442c0b20114660002d1255a03101800c1110307034441c10798540c0050001e012134000010710700b0040d0a14030300715100020707540407515590386401d00c10f44480440c0c0e8020080325510fa40d020044d103034010702918840072a4800c2c00000003040400e162082c422961070058001a50f28000050513503081c0300c0183e0b10742d80700007010803001c1070000854990000c10328125100c0e0031000401e081500c20b01080c0141d04501045010650601002100721344d0290740907860215920841d0805442c102070720030f41c0c4007810303c3c1c0006c41800d05079440d94060106140008141d43c80b2400310b07d01403420b817040000c002e407040c010b2246503004034000c000710101418503002440c0c4240c4103441c22142984240c051104a0f01046a00700b040007514090142c410941500c006282e000e000c824004d071041500c601c0c0e6000d90020003c4d121000340c1c0645a940d03541030300e8070701c00b800040090032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 831591070 1250 831589820 831589831
    0x209060f07060b130501080d0206090607031d0303160809070b0a0f02030c0105010b0a1d130b0616060f06062303060d050a0f03031508031e1c06060306120506010e 71
    0x1510303030107000003960700c4c05940c2c0052004540005055418580c0303d030f2401003e0b0380003506550211040c0415260001101c030303031000840c0350126508680c0ba001d2f85071103843c001000301911010040c2301102031022100315100c4456641d8589940e16148d420b6034403e240d103e00392859004020744c4480901c81c1800c3c0d24030880b1401181c0c60308040065450840703000341d00ca055039100c0404d4408a09031312107040564202c101e5042c4082c4c0300d040000a85c0f50f500303c02000046651420110b074117403180000d441d08044042000c807002c2c1c3d0182003841c094440d18200c1340b40c4510744a00840c2280c000c980c81c1424000240c50f00340101e0b03886011120540c0040d182a5200e40c0a0283c01e000800030402d0704042d038491440c030039100d084d0745030190580f402910164250320a0305014000c040d0000300399000551280042d091940c00034118022500c9000316424514101d1100180d01c00c6c0c2540014084490640d0100a100d55800e0541c1001a503a00000c0072078000000401003000e51010a64011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 831592320 1250 831591070 831591083
    0x30e0d020a0510030906180c05360105031005071704050712050f1b03030313061401120c0602010c0e0918031c06120b04242d0209060f07 60
    0x544607400076000c41604001600000c1c0c5845c140c00400140b03006003c1c2d800b4031a10400402a159565030340c11102901490380150541100c0c02c411100d03080e450b580403c039561040d1100d481d820095204020709010b400e00900c0380000140322a00c440c40303030910414050796a100640b00800401c3e0140a014009907440e1084001c08501130910500040316184980010051800e244122905148110030020050015655203003041e88010003181e61200940c0074071921100c052408800410140010300300b003e15040010842a2101e00080ca0080c01550388541c165540d540c101c4c01d07110341407403100000c0c5010684031b80300e0508241803500301c0f40503000c80c59070050344d0110501e0360b0401c002c500c5001003040c0c00306010004902c42d14001e0492016522100001b45c3ca8100140318013801c01090300710804201107900c80a21140e120340305582c1000c0c800031528916642100c5006107032445480382e02420404d10300518421543c07100b02c013500c80b5080507800210704140343c04c40402526071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 831593570 1250 831592320 831592339
    0x70f0215220512040815010b0304020d0308180d05041806050a06110109050d08100905070c022e02011a09062809020309060103121b0b07050f040b03071b030e0d02 71
    0x32480310343c3c041c0c8040c1600f90010240c10f2a0b034124001c1c100300603400008600303010428007000d601d0f2050003802032038160401852503111404100ca22010a50a00b0050f01642113111131241c1d10500401c1201c01c4040c400d410b02013503445490454205200c0c16909c01060501040228020500e40c07034044010000040c00c0c0045841da41d04000080e03016400195200702040703003500880007914003400501104121a20780600003130481380410780c000c4d11442d502080148040303110042d00e403142d40c09072040e540c80d081805020340a8903000b00483e18003401c0000f9101181440c0003050b1107050000c10109128120030041d462403102200201e120200100780843c02d44000e00040d40108401e0004020700d61460804404a40403e80b107002004214140080018032900461801f00d4110803a0480d54135880829107261083c0e07000202000c0700403600245030403008010b144204440c0d12204009039524803520700c2c0c180642c1e80100030907141181d41c510f070b0030050b028100461002d41500d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 831594820 1250 831593570 831593593
    0x1201090503030c03010302100c08180a0b0c06041e0305031308090303210a051509060f03010c1101050106090513050603010908040312031a13020c15070f02152205 71
    0x7103901c02c44a00c407000d4000001001107007002c240110800881e8a0101a1a4680d50b111300c2240700301000d07040c1d4020940c07a001700c16510304403880002c140c4460402d42e203130802411162105400c48098401c00d518100e800c0fa490031440c28003c5040c0d1641d200c4c2c0ca136070b803400304803400500c05240590340700304244550982ca441c108000c03c071001c4d05941400213650540703070041e8540c000034488120107040c40d0910491001c0d80b491405500021a84d4040c25540c140104454020228900d5031640c24800c810515503005100c0b442c2400c20f0b10300a008903070b01e503c0241d401c0c508620800f5000310101c001c0c2c195407042907004c81c2c0c1110000340003052465aa4452400c2d5030003941040d548004c200008512068040c40b4418003100803070035400ea0308100d400014176001c12071260440a94000a8400d8440003d100c0d843c204d460a6840d482103003815000140f0092540c2d00b80e03805845059180c40d9070040080c0c0443c820851560210b02071183c00d161901394484024040385c6034421260f141a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 831596070 1250 831594820 831594823
    0x4170f0928121217070c060b090c04080c0607050312040c0305030a081602010e1b0f040e01020901170606090d03053a090c0e1803040303080a0c0509010c0212010905 72
    0x4010000c2d8852901d024400781000141281d41620800603c0940d442c00e40d1420407045400d9440740041c14141e061460702c0c00d250002c1e00361820626407184044042140c85404030b0050400e45407800221220581102c2c140318040c41403220140c4140d10a01084100c2e2003e80007156001d4420b441c0c88604690301d030380340c9265030014543c42c408070704060100965080c0510390300304001528802031103880c4142918544440740560801c9184140740144a01921039440e840c00380340c00500100310107004180c5240c001e42040c80d149002844440304203440ca80d081e680301d0b000d0b0200034001843d0003040d400300041c1e101c000b80100c0030300100780303c0f904640c1a5200441c18208900c24401c00400d20030300440032200c0400100c42c1c11a20740040701d000708030384003860f206603944080032190790b4603100d1340d1420310700360101248514440020040101075100c40041e00900210304280031548a1142c02e88803030040303030300c51400126502449000b610f4070307203004d0782d04200e031000003d100031041e156603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 831597320 1250 831596070 831596149
    0x60f06030f0105010b0d270303111303080a03060e0106120929060a05060715020306030a140d090603060b370305010302101707110705120604170f09 65
    0x141d455502050986140b501b40c05422007030315034080000800700b02000104070b604503101000d000c00d55074008903c5094050300c02c0384d0300d040480020a1110f50b03203250134001c0da40040503000c00641032000010380c08141c244030f14180d42d425146c080b007074822045640003c0070700110a42d9401050000b07c0364003030420080348000310150b40048001c0ca000e45c203100402c09540e00890064000b04810008030380380c5506842c403200b56880c0541d40ea19044000381c0303480016070010741a00c4500504110910b40001c03824640b00c2243c50b040c441139078815090302118828850700c02030010420400031803242e00c4003035410030a11314140c00d50072914814078030704103102488080e01190307951005206514001a00002c1c06502e860980511030a418401172030f240d0140120381440302c54060904540b10500900c00600301c06040c4e1130028184581c85540d4038415901a6062072407059900e0303e603a0020304440d84880190100d61510203001c00748407180e4030360349070005201d110000d040d05800707810304c14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 831598570 1250 831597320 831597329
    0x1203061a0a052b1406031207050708060f0708060609010909020a2a0c12020a120c03050615040e0c100e0604080105010b1c0c1704140d0306060e12060f06030f010501 72
    0x74001e190440000d12000c440841302d80d200a08615001c1048964000814042e1100d400400c00e84074081071521501e030081c0f5400146250054008210b007186404c3c42c1c141c8165070700e544254032915410180031035441940302c060b00081050038140071040254000b421034040a19105240d5030100c0c3d024480783e150182c401c1c0c0c50b40040041031090000c81c1e00302101820000b5240504181282c0c00a42c411800303100b4901d11b001c031000307100309129144019000641e0088103445203890080c013404803607117030082c20741e10032440c05091081004001403030440c40c940142013241002d40902090744d2002c560403103142e0101c0100004200003d082c0281030080c03c0300100103881750000c80600b40c4440c00c9205040340545403410300b8205035480309081507501144070150001d40c84038100750010058800029800703101d44d01204071420fa06038002c0c002c0300c05a03964205903403c050300704454800d000d000080c482c6d01c01c0b00031894084100740041d030810350040840ba0314024110145003502c00036880b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 831599820 1250 831598570 831598627
    0x807110405070909060b13050f06040305010207080310150210020306040f020d05100b12040201140c0d210908030f10050a0303080a18050a0b0402011115041203061a0a05 74
    0x10070000b400e44c9001d1907026084020303800d4100070900903480d40c100350314461ba510400d0700b03801e215a0394480000700d9018541150007990703078150070b003480b10382c0354000d540b00d8041c40b00c2507400150410080060f04103291241c5e002d4000d4400d20039043d0040c0d013018101c81e41c025030303441440141c14128801403072403481904000c100d0f40361502440031015400c1c2c0c806a40031208010800103502061241076201d81d090800fa00c3c4800190b2180c502800b480043c43c00f2403207254803001641c0e80250240000301024050107000d01800c540c06415201020703001840e070b120605c0400d00182920241a0b0301c80343c4101000826681e032000203908402542c81135010076145003c0c0280300c0604d026400c0020010324070007c031f012250740c620750b503441c14030000303001c0c49841c001140031680300304c0c040307050980224100e40b22030038998045400b164050707504844201002d404200014003038020601154030480c189203940840e610403546961003003400c81c04000d41045444a9a48500b1300440064403116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 831601070 1250 831599820 831599837
    0x806160311210a110a030e120d050f0606090f012001021201140a030201080609061f21050403090e0c040305160302030f07140622030b1608060102060103080711040507 73
    0xb81c00804a01806003680301c0e080c0300d04c4640340f0813413030125a941c600c6851b002440211390b44440d401c101c805c0c445480d00c4000012100218050742c1c00c0b240c0a40702c0c0c455407503a0344d1104e0003008414410117100035008140040b94448960103814900049491000c07450000b0301c20a95a0342241d03c40c0d002c5a0700502c0000c014050b540c6099241c0090340c40c103803070b05a442c60071a00003800351280140f003980b055401400180352516414034400c80c02c45c2001c1c10703000d050038050380a08100240f844006940b421400c50000010341030040764052501510303405080c41c03c2c09a41500018003c143d0a640841000b000001400400200c01c20507545450b01494908520416040007040724298560f584144424014041d00c07103409600b41c00120750256644920040482c2402c5c041d608450801c20380760b0340041030100201a03540f09111914000d00030030f040400a45d80b246041d01d04030300592141d001800007036481e00080580740d02590b60070078015001000603040c1d410449400300041c0440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 831602320 1250 831601070 831601117
    0x307030905070602030f1c231b09091317180a0b0c0c060a0903020a081b0d0f03080a0b040509160b120a0911130b090a060806160311 58
    0x600c4030b0800b40520344051032030b20030300e01e1080b00301d40550100511700d28180301504150210030780c004441d0206004d003400c0c0c0c1c450f521440c6490841c0440b601c01d8203112548030300c02000c403400d0031205d20300d1006010311503076110500c82c013400300885c200c02c440140000f103600789000100340140c41400a0941e002030304400c90b50a01401d0312095100c0d483c1e42000740506d603a0702d40041103071628a10107a414540300c1020300d000312880071140e48065040b541c4140b010522a401045184205680702d03028150740d50410240700c2e4000d84100003501c1d0b07075103154401300003e11610303e194100903100400f18155060701c00190441e030044d01c2000b040d40c000001407441381d0074405540300605a02102d2030a0402c030f045140c2c10803800400c070000c01e075aa081c0010401c2903d5008188001d4040c1034030020140c1451000028110320000500c80c000840c0000c2024180b8021041524912009001d0589448401c1c1001c13005180c10441410785409039280c41140c0703c07002e48200c804200c0c0104048400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 831603570 1250 831602320 831602323
    0xf0403060903020c2d010e030a060504020319051c14040b03060120060601020c01030b1503180106080708011b0c0308090c1302252f040207030509041802090a0b04110307030905 77
    0x75581505000308080c03001f0407940c011074840c02c03403030b000000415a03036203030720000c0c0c109051a200000c60307000e8110941305004000900d000003e0034400401480c1426101c141c4103100740c442e66400c0404100401d200071141c00c40a90340041c41030500e50b101c07100e114108000713500c0f0301081200c2540711404000140d80d04111108424000b800c08006001000001c04e60850201c0154155400d000000c1502c0380b410b030040c0c1940c04490300003040883c0d00d4030b55180d101c0c4000d00c0340e8840d070340c00c1510010300807203498080100a402c036290a0040d02890341c0a5400c0070b4000c00e60030060060700c400390b04580b03c480c0b94101d4940324040050365608001184080106100b542024011260005000041c0032010814094081c2d24521142d40f1030b82e1604040700b80c1c50303052140c016001082a008040c0c201d0090076907000121018840020091000504101501e00c0654803400311004603000b000305a001c140c0102014001080801c4280880032807540113490080000f0b40d01c0c440802031100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 831604820 1250 831603570 831603649
    0x80304032f06031308071406091005070206070c050312040602030601171003020114250c061107090b010210051e0c1206130603020d030c05010509030f0403060903020c 73
    0x22070004500c01c0c03840d0031011540383c0c0001044211180e40d806000d200788854030040c0e502c815885062070001040d4290340d036445541c180d0341c1310a548142c01d5220326000303032406600d101c0d017201c0d4000d2000b692503407000c4800d804030320026190340c0402c0000418028109c3c1400c2e10880c0038000c0580d03203081c00d10004092490303200030300e4010312400040c001e20140c1009951701301d07902440c01c2c5014841410403000c0c54403414941c01107400ca0310000508556604003003500090244000162847d41c2d50400d840003c003405001900d034006540c10b0103004040e41c8810444407041c81100c0b14000c0c407020040480703a081c1d60011000e0018051740742500c102c4020150300c0100c4030795090808042c8800a1400807018000f1031044503007000c00c21790682d466000d48000e513002030040d04a90040d00b8051701c804d0b03501d2001c3e21b0302d500700030000c0c01c4060001700301c5601000078280145424555195030300180000c410407821030041802d50350084d500c44d9500c8802c41061005111a84080c0403203914008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 831606070 1250 831604820 831604883
    0x10c11060c07020609060f0c0a050c040b0d02030d0f1e02060919020616020d08071b0e1006030e0f03030115030b031f0b030c060a09140d08190908030403 67
    0x40242e840142c940c01c0554040725810b5a8044d02e4604006641b01503001e6120410740381d02c604004082032007000904443c4001c400d4a00700b0401c001d0310148140c095242001a4055002d02d4015880f00c0c400c1e010310500c0b600350f1424240e810a1041174400c41c009041004c0010703071207031381801768040c01441041030300c0803000c003564a0964154003143c080e0080300c2c010f88072070301800109403d5442d00450507040580c04150156a48424641181c1c3c0501c10020300c12102140440842e060780c4040c1070034064041920449040b80c40c00c034045003e4038030014500c42a024408200d800d0b688104090f6000c0c1c411240860101902002e000f0f00300c2c1c00f05c0400500ca540a00a8014000311001100c1940b07440003501103801049070b0003091800701c4005c0030b150001000a40d003101564004615811344200c0d5140b01149034550b800c001020000201c0a071107588108426840e14025400c011101d4405081c646d0342207a80d00e0440e410350300280d005450380d5096000d40303020080981100240f80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 831607320 1250 831606070 831606091
    0x12100c0e27010b0714060f010303030e01060e130204061e080f16150309050709021b060417210c040306060e0907092004080c18161808010c1106 63
    0x140c81e1644400c9000703010b2042e41003400c0d0024058061046002d040122028072804480050801032080320714038000b403000381d000910b82450301d10b03040810b0182200312180030010380c80c1a2510300a45a02140100c412680991f90340400900d6050681c80b004a44100c815100e454501d8104c40c0360600e80706a0a45030705030002101c0f100340e14481e40500d019101c0d0407201c2e86007611481300640c0200054072026001d0f115800d40060550055001070036a1103059243d0b20300140100907080d41c0e40c801361001450704908035030307032041c1d036200901401c0c80b02002c0310313503a400c0008801a048040c40a5030044000100041e06000b8007043c0c4c0030b82802404406140911440d140702c0d5140c8840140c000e0000c8252039506050ba001800086900024014400d0660303856132007a8040d900d501560807603005e1900001061041a10614020700c0703040622030b0b20409002662086801d204198011011009810004030305001c09204481c60407800b0307190312044d00c45680000345412001040c0e440c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 831608570 1250 831607320 831607369
    0xa051806013014010902011101020c070b03060307050a090b030613020d1b0906090b0405090a0c030f06021905120108071d0a0f0c09031b0b03040212100c0e 68
    0x42400d22040081d11002441c00320b0011003004000701c0c07150302114007800d52908031181980032041940111401c0303100340c8800c600842015202c80c01d0780100c48030700940d0341180c1c804200307a01a1500542d40301900400f5500015290000034180b40e0032030b00000c0c0c01a5aa424610b42811b003040015003005032840386040c0204140c2c00514101000100203081082d05c203501009003858407240c2003e08a44603040c06540d88600c00c140040a46020b0a0711450071300c404100c1e001c4000c1030254000d500710500d0703050b4504544070840d541c0c2190b14100e402ca64204a42e08090f110041c050502e00842d60343d095031040312034058000c0d60340c181c005021940001c40100004901c415045c9024208240c44040c4c5035a000000002085051041d40c0780d181016584030880e94040541c40944e48202c2ca01d0f00302d10f00001002c02c00c0d8145020780981000300f0000b0401615000d030030301e2000c1200f0421103a02ca415041c001c415070f1207511040c030116030103030300050052030b000c030340610310095400c0c13000503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 831609820 1250 831608570 831608579
    0x71403030a051e070c02030c091513150b070305090a090207140c01080a0f1d250303050702040b060706060f06030b180a11040b03010612111615090501050a05180601 72
    0x1211040500f013a02803081c881480c10840d00d0038441400c00400040040e01c8034904100c3e4440c000001200d218030403a0091003100148086200c2c480b40c0d442ca540c405c004141c00e199044483c0d920401c1d00703806001052007440680d660328015030000d411140401340e11001d0034a081c1d002112101c2104c62650044e94003a400e59a01000690b844070b007426020a032088050b003900000e11100000c0a07500c20b0085110000e91400550040d25103014441d506e0900c0c480da6402e4101ca0081c0401000500104240000f51500c3d0300f103a03030f208800410007807401c0001d43e194001c5600aa2114601c0c0880380000c20403190144260003e198040ea0b0301401c140601c1c0a50030001c1c40186826036440c0d4901810342c41190403070555026049130201d2a5407541c41c0c040250000d6a13050300070310000d0070903500403400a00c0302c2c103441500983e80f540e021a204155110002c0ba80500000d1030160b5517a00d455010800034041c03940038818407100029982002c000c03400140c0e481864a04003681b00400411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 831611070 1250 831609820 831609871
    0x30c07120c1d04110a03051b0910030308060d0804080628060317070503120c0d050606070b070f050f0d29030718114506030402030102071403030a05 65
    0x294466030184d29a015080c1d2940000c0b020342c1036400141c0741c0d1280c0f100ba61480008100d50000e805800ca4025420759130781c0941190340c41050100500040f44040489d91506020030a002020300c0348c0d500a0809807110140d910b0410b0894202c3c508010442e40c0d8020b00d40c001c0c06402c480181d084003404141e0031501c9603600c0403414546882c0e4500c0001e001c105100b024800d417861030707408442d81166030034000c1a00555402c446561045c0c20b103024007251f00380c60800d08490303c29034040c2070300c450f07507803900403d80300111601d540005000080128401c02d812080003000006031040c0000780000700340c10030076812a5084906020320024012000c81a078000440f03400322100e040c81d5030a80304120400f034025202c6103491844841021a00c4800340090000701c0d592030000725840c05104068281004104a0202180f04014801c2a00407281d041103c0115409030007d40094503201066503101040b410350a00600140c10100070703c21480d05900841c1c0e0024840c55a1310782074040c221601 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 831612320 1250 831611070 831611129
    0xa0b0708090309010e130c0c1202010203270703120903060e0106060917071e2d0501030b011b0803011502030f0405220c031a01110604080a02030c07120c 67
    0x1414400141182c0c03080e40d0f1081c04100115140d42c40034070540c00480c0026100c440400740032144589d0701d00c40380c2d14a510501c2036134424240302c09801091078410716040c21540c81c4c0708008105001d51a80030000c00e22501d0340007220200341d41c0b181e000c545181080011101005c52445169040000400110fa4000c100e0b07401d817a0485a80d594095002804910705415a88802252201d003006082e480304940c04402c101c0f4000030021240340c2c08050300c14051400e84600e43c4141809040c140000d510036805000310040c18140040c00e81c40240d40446400640070307048900210000040c00391003c1c410005240d00e0040c0000c5060000c69583c0b507041b40202d006040c01482000c1142c40c807100c8500c100c0042d95103400301003012900a02c030050150010a40e1080a42c403c1c04002c1d5083d48184881191150500090000c58580380d80d610625030020302000c1c1188001d1207200301c560424003490707004010707803054030004984d5403034107017084800c3d0b601c86030f00400c040c184590001a46900b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 831613570 1250 831612320 831612337
    0x1909020d080a02160b040f08030a08010b0306040e030f0a02070503160e0a022104060b06090312030403050702030706090608010e01150804020415091a04050c0a030b040902040e0a0b07080903 83
    0x1103602c0e4820341104034a8082800340a0040b07000d00200010f00001039801401500c06907680000c403161100c0c41a941c1c0c0c401c07c081a00040e0015004001c00300c00d240255411140c01400411030055134030710320745140c101560010040600080e00340020750100f0449006200660251505e8500e1311451040b07201684100300c07503240003c000410001542e41201d01d4580d66121524080c0d42100c00001d220300100c1d422200c4900e0403620088a00e001c10951f45104802001000140032503070308014941c001902c11024000240500c1c4d0041e038080c408000a0400d6a6a1402080ca00350000300443e04c1a4000301300c41c950400184a41010140c0c11481c490b040d0820344003a0301d035071010a0080c0000c014031088030030750010200708000d082e0012902c1c0c002501003c503019807140100300440b44d00b0b0320303d40c7c01c0d000e0422180c0d0b54180650001440e40800800000301c1c8641c0b0740205003524130035400c02c83d840c1c014804680400c454035142d65000701161501102c40e240606046560380f058017030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 831614820 1250 831613570 831613583
    0x120f05011d072a1a070905092e0b07050f061e01030f0c051f0e040b030a03140f19030c03150b090a0f0b030726060d02030a0c0803031909020d 62
    0x301002da0f036540d0740304000950089404c00c2d410b090012803400500709466800000d03124490004240c41c01e6280300c2d004061941e10740c0c85840c081c10840e15040c071000840481003402d000006018803917800940445c1e4001c4002d41400e10103a0301941c10110000c21064040c40280701e548212500310004a06490b801040c0b5024103220341441040b102166015561200c0000713403002170354101c8804d90010580c1d5448415a543c190403c100c16615003d510303940503803000f68107401182c442d400010101d04070342c1605e0b20701220f10b075690040e0b070700c2040c0144140610220481c406a81407090600c1818949030030041480300c4a12440c00e011203214030b02c100007000c1415440c0740d4800b03132a0801018008160982c0301e5544240208a400490b032090109d89107170007400591162000380d85c522003038050504596902e00f41004203158201c5d400ba6014800c401c8800000345014003802c01030f01c52403005540381c0c6060340d1040050402003031004829030070041c070a0300680751908000200340e882403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 831616070 1250 831614820 831614867
    0x10f0308070210020a0b07110c010519081911070317040f11030f03030108070f0510020706030510170c0a0b0903031c091205040501030f05091c120f05011d07 69
    0x302c0c541004820b018103103c902509114087e600080c512040103a41c01c00d0b1502e28003502c00564160007542060083d02c0c11000c480061944150155980441040381f42800c8040f00b41580045400c08015031106800005009050580001d207030203180c00446241181c5250681c0c81640e0107204400041c101452480d119010341e07414401c594541801d00112a10703580d546081c503503181690b216000040c13005e1040810182000034011301807986a40051010a1800f64210000c0c00024400d015840c4514030115020112590742101c0000c1a001042002d050800300402d01e241c9074080c544c080c40c02c00110300540c4002c010341302100c503841002c9030116040c0704244003401010000602c200051000100c4140d08440070340265502a60104680040b80781c1d010110f40f0299014102e0368001080260700c00c050700c0d1810025003051074121405081c070b4032050159180c40458a0300a80c9a80040c060340d004440030402404444c149003031130b0f080031840581862000c592440b070b03002d1600c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 831617320 1250 831616070 831616099
    0x61d090102090d0f020405070c0302030a0825020303060109081b0105070c081509010f05100b071a010f0306140615071e0803092a01120b06040b0909010f03080702 71
    0x3941a40c510b40b0340507192240002e01c80c40c0c0426600700d4108100c0c031513032414010480341c92040b40b44803001941034008610f00448054150b0b01c40e1402880c0141c200d04d005a48602407075036459001e5507001f2078004540303e0803d880090001d40007900310804691200d00c004844040200300789550103420308245030754a090381000040500b00b5005080c01e0300c00c031005031f04000081e219031442120704400801170281c43d0035410003914402d03101c0b2030000202c40001e005107003a1000900c0c85a124035920900204c1c8645402c2c1c0c01842640a40f0420b0181d042c10401d02011f030144d44a00c03064250080c2c02da1a05000103103000e1030100240c1800300002c509141004400282c4124402076804641082006031070055510380c01203c030400c45000e401d009032266202040360b40d0000490458181c860f50100e07004550b0b071588407204545040d00c40220b140345407100c0009201511404982235aa118030b4014002028810f87c8540050150300e04104040760b400b1040c1c41c406a41211100e001e00480c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 831618570 1250 831617320 831617323
    0x10050301051f23160c06180f06050d0b03100b011b080d0207020a170c13141f1e060f140f0d060e0a090501050702070e0a02130f06030e10061d09 63
    0x300b07050394480c8515a03c910050041d00720b4840704460851f0b5580e08100c61034191440c42c1d0400b4800c0c0b89031065042024414540244050252042d00510010704241040d000034500030f050804100425038074403c2c90000c0d40c0c0085800071000a42d0f941206404540d41c1d000c50b244612010142510360102c0c98a045550341b03480e00700204599904c03498035a14a200403900c83d41003108a40c81500e445000d2182e61041713001f64251088801c252200320307030380c0345442d401d49104403001c01c1410354141c0f00802d2042c405002c1403248848c007215607200905012000e09000c40328002c0100380021415582c544d024450304440320b140303141e0109a2550030078801c1c1e0307001c0c0c810368200030000c43c0e040d0200708180750f99030f010034041d600900c000e001e1900c0320030060340c40e4104be0040c840d0b1030340c1c07542c001595002d040d00105501a209902070039516524480780d0500301c019004600000c5d03c51f1000320580d01c0401c2140c40b46180341408004441c54643d900341ca031440340010400e9140208002100c0b00300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 831619820 1250 831618570 831618577
    0xf150306010305030a0807090608040201180906230109081f061a0306040c1107030b0c07080724061d0a2c010608010507080606130510050301051f23 65
    0x98100c50081d41c4903d06140c4036000f00c00708100044040c00000c880501c940030600c1102c005840e401825241d035001151020040411242800240c0384001340091503031045d00c000701010880042901c0740c506102c1e1180101d0029141004040a028022803202040b05810f00000c49405a00c041a101402d00946165400144c01d024480803030303242044008001d51080c001160108849903a0318802e5402d030101e030046400a40c4824000d100081d1030b01c240d5074000583c940d03110306000007a5aa00b001c0d40c00400200d9100c1c6c501850280000348400c0c4011800c00c2c0080244419814200078145250208520301d68a003007507000300c5c4480c00790358000d410659020f010210003050045400785500040c2c28280ca0035880e04400064451061280d980aa642ca0750b0b0392151340ca0b101c0030010b07281c00c8123004600310900010005504d07513070280c00f4588650151541a02c96141404015400443d901d459505003400411084202d6000c144415901c185094180e5000e00301c9941080600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 831621070 1250 831619820 831619861
    0xb06030f28060618030510110f0a020c0a0e15090402060d05010e090708120724050703090c050402070506060618060d020c07170709050c0708031e0a0c080f 68
    0x703680412449214500b600484241e400548030300c80c1c180c1c120340a44c4025003040c400a000d86d0800f4a0090050301581c000d10071850b003124965040046910001e4400d51001c40c0c02c1002d81e00c84401840b0754103140800744d005240c1c2c14542d02a030302d8948500742204156090b400e21403000c940c001001c540d611000d0325030464003410108850340e1229100b02c22208241e8002c0618400c0000008000e640000c400684119010482d4103000710341d5030305080700c00c407020600b2144088aa000040441d18030402e481400190f502041d62061820614400d0095400040c00340d40104103050214000084080d0010130545809680d946185542c90160110b540030a40c408000110601c0d590342980180208030007900541e05850b82c0c4e031100140c4500d803808462920f410145c8100140b0000394001a400506440c0e040e1401140e9030319a0b10681c0300f25840503007225001c0d600c1c0825040b6452042d40a49029010801a0b040000c00781c10f809001300318070b51034000000054045109007403115041c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 831622320 1250 831621070 831621121
    0x9020a210b090a030e0d14060903040f121a0604020d1404050f0106030218090c1c0b01080d0e06030402180f07020f03030610031a0a060c150b06030f 65
    0xc8005200c2803425040182990764030740c40404210566004504100c525606031181d06445105030113120000100300707020f03941c84100c0008114039180512005108084900c061555581800f03440a00c0300701607000401c56482545088000482c400c081200516488401c0186130744c5400000380644224151113440781d081107280608601000842c1d80250f01c01c80680d0242c14403036100ca401c0310f5582c88040d6001ea10112441681106c00b800c2942003261841541c050703200f800e010410030403140d01c98011a90300c40702036a092151050890340905401e0004e800082e00b41100109006000081140315100000c04a400c569910b5204010700301c290756403a41d189029030041c0b258a208072a4540503000340201000c0380c0d000030044900c01c2c540103042d145044591042103004000d0081b4281042c03409040384081596211005801041da41d5680d030100b070110b1030070314291019100817505960034904e090420b950380400382c950081c21006480c031955100000032a402c4107003c003c8111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 831623570 1250 831622320 831622349
    0x110304030b3d0302040e0c1507030908191a10150201020712090f0f0605030f0402030c030f011e020309070608100905010b0d05010b0c060a0e0c220b06070b0a09020a 72
    0x2411802c6140d28101d0340211020022224428401a1a0b200b81400c991303100301c10100d00500307500c0c500054840c040c000c0c50722508035610342501c40e10f0030401804c0c00302d000f24400550000c01c03241c02c1c0724601003080f00002083c01e04240c004135601d0724141c010f0001344052801c09000c1c052003581a0f0f40f1051704a000c0c40b064840e040d40c0a014510903005070210312841100c041505c1100e1102e12084446940e80e4525641e00d910202d150288050000ca038140540c680089041d5010803100c0c0c0c1c1c0c80b013080c0000590415010302e4004c80006c0c0701c50303905094014410021204008540017003150400d0a10104030340e100605400d44940355002038031043c3c0b0305400441e811010340701904010f0010081003000d6601c90412112a01900d002d402103070303000d0340024040303014640010200c038000b0001c54080381d41c2d02c1c0000d100070104041e80a82c0c0b02984000142d640100d0081c40c0300380c042a54150300e405403640ba0314840410007450301081c141c03a40242c03030454a41028080c01020007000190702c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 831624820 1250 831623570 831623671
    0x30405100e030601030b0c282a0303020d09080c0c090a060806060904030201110c010219080c09220e0102120f01240c140a0203060c0310091e09050706110304030b 71
    0xa998000c45944c40001c2400010341c035019072710004082d45d168454013890080c0200c3d0750131806944203480e03800506494000880c0040c1d480c1000e440c8a807481c10203003100c00e038500700740090404010001415141025000c0015000c086142c9402102c00d0302d00e0001303681d071070038180d014288040071800004800200e1302e440f42010340c054540a29520303000356641c40524011520020700340d5410040980410400900b440c00b51240c100a194100f07521480044494803802184e01c110005141d903500061816030411801c443d8540c849030784905040b080d410141e40d0868060a912150f04014454500409050043d81c40e075212590000c1c1e1a04809020f98240d512440005000c038000d10806000c6094046490182c0e88554092000303c04c1c42403a080d620006032002c035100a1507940700f41c40c0310181c00041c1c00781c020140c0c0104000c110242c41d0440040030842d0b0042d40080f0307078100380410f1000984081b20315401c400c140c40000c501c08181d288a24962020010300024144500e00b0303400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 831626070 1250 831624820 831624877
    0xb04140a1a07140a0509190b0d360515010b070605060a0311040b0121020c0f0c0108060f12100c0f0c050c042309030405100e030601030b0c 61
    0x141c2241c09000040e81500c0d00a03003500d400360000106005980300384540c100300e41c81074000c2d20341b00030001d028008122000401840001ca03680101000401c0000d4154001c3e03800c0c05103214801d030b625140d10b00c00800c41050901c0c000e1010301003805a80000c3c1c2c1c0801c2c080104100b203190602010400002d5a4540300c48140d6801030f40f045440d582418002405440c0840c004002c41ba0040401d620344c000481c2004000e01412038442c1c144889070782c07100c440d04104121000f0300c0d44403110069480e1289610740c2e1408001505034002036014110420880c0d82c8403e00320340040041d40c6a040c22840d0780e0006120064001441c1d680e4843c000c0e40065001040e003005101c41450b032207904d807899030b49104440e114400003014003240d00240b800c2c4014103140d4420540e846040c00760901c45003076000b5000035030f241943c103050541d102280c1401285841d48005211400b10b0030060a114031280c00300e030b103407141444044c100c00741404c002403900441c2d0080742c51844810707140000e44c201210581 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 831627320 1250 831626070 831626093
    0x3090201030b1012020d1820091e060d050a15060f030507360509060606250201021f090506010b03100b0d2702040f0203060a030b04140a 60
    0x6034002418202049224148840f000f0000303021541e44681c4400b4408010020703501031018000050b0340c94518100662140c141086440c0c480c880207041e80941e441912414003215020300d1180209005206d070115614020f14101402004406810b27030300c1c0750001d035102d03005200240c0240942c200d08030406c940e486e84040d4044034250100b10440d212030094221081c140001441640705c3c0100740f104401c02429071b00e030200e421103440d0130702d50a080095907880d04034031065030054694003072162031603040c40403d40c049010b036021400c12000c1950841e0f081c0d07152100148112540d0303200c8043d64804d0040c090000b00d03424140d06c1246546c0705900c020400e1800a54aa005100002c50080034000c02c481c05803400c00780c5204ce090504400f03a000b42c2c0950201c0d1080790f82c0d181c46402150b007c0d032540f1034412400307580072800f185c1c60040c0820788070000600400c5610400401480392f840006200c140c0340c10880c080c1050340c4034a04680040300a4880349894410030503564104800c80e00036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 831628570 1250 831627320 831627323
    0x19032409020706050f06010522050607030206250e01180b0f0721090323010c080a1a030d0f031508010606020f06060102060411031608010c26041b090c0309 68
    0x104000d1750760b680118012401540c2150010b40d040010f490898061050105000c0b1b84100441125981c1c5000500c203501a90f401c5000d6046801000550400c2c0800e00d0b098503014500d141c4c21030f203800c00c01083c02d03101c0e10045040c003070305e0032000301c0b50b10700e03022110007401c3d00c05003840c3d90b5030360348015401580285808451402c990f400c00c4003003202c2d0b1815907045c0c480343d0f10748107449800c5542d100a400d0491019000303180040c00d0448030664240101d4002002c15200c865030f070700b4414446401d9882840e413046080702c00b600070344401d407000590344c3c501c000c151a01ca105183c40342130850103003a030640d4119180c151184003045000d010341c401e40031103c05808440018a10302401511240102e030f0950140e0001c000240c00704600528101c0301e2540101502e450700c402199111060101d600000b4040e951012550115a0401d14048210f150741c1c10010200400c006038084080c00208010242c209042503489800c4e4604105000340400e007005100031103140100078000d001c140300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 831629820 1250 831628570 831628583
    0x20312040c08070603110f0a020a0b24101d0d0c030c140a120b280e07122420030712020721020313031b060203190324090207 55
    0x2c00603a04d4000c3c8100b8007442e4801940c14100849491560a2500b01c102e0303200540c0100040f440000b480c551941d445052003541303000c81e18034103d0300d031400e10888001c8207000b042c3c0081c225040c0c81e0491b159905564a2000040c01000a0008100c0074101d4640052200005030004400c0248014118044d034005080f8040548071200800c64081d05620030f41c0360200c0e04071040400700381c1c428503159001c5e9030240c4000d086244203120b44a01000240c50050580e955510b00c2c0034240140700340c03801081e25002002404440351070f00c105c00c0341c041041d41c1d840411108440090851500415118003078889803034820440317126094403650040380c6140024481041100710082584281d9000c42d401501441c641b001c5000360041159401107600194031040c05122403420550b99490003442c8107190081002c150600b82c60114003090304007005540042c4652403440081e03100c1701000280903d400705060242800b560b09501c0078500810040d44071400c0403c002103d80c0090088605c22503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 831631070 1250 831629820 831629833
    0x21060b01030603030507080d0603020a08010b01120203060a171006030b100909080f0a0905060f0904050a05060f13021306080106020f0c130b0402040806040f0302060a06030b16020312040c08 83
    0x24011000c4440c20702000740403c030280800780200b400a401b4001000125000123a49030f140d800003400300d01c80e036120125580d100d038030304542564400103610401404400943c154141040001c20300c007024024040c0007003010901c100502d03804c0010004000c20390708100076091705d17401d100c0c05500d0100c0302c5144103900b00800003000c00592252050383c503008078080b820000c4a4045548592101c00d1510030410303010030100351030f99448000c0180301c100703051817a074440024040c001541c10040c01d0301d2001e441e02003005032071784500b54420100b400c102e40390b04001080d21200c070024055445140360070b042480000c0b40e5103030888601410780b00039408607000d4410016855550704c0103101c0950b040741e8a840e5842103090310b90405280c031640100050f0829403507142103450320100316401d44441000b03050070800d140d01406210341100c071544007889aa811a115003240c604060081c0d01228822012402802e20900503240441c0d1500d82d40d0509040a040c45083c030611030056248038000e92 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 831632320 1250 831631070 831631091
    0x21008010305060708130c080309030d0915111f0507080a020a09060f0504092c0601060903080a050d0e1c0f020c04021821060c0406021b0103062106 65
    0xa98490341242d901c20000c25040e5100f8004440c2d583c07000c0c000124038605c40d281d4030002050641c1280180c003907103000f142c0364441001054135080b40e1603550024044003000c1808100c10541210212003000e00388540c00204200c0a40e2512043ca51003005d42440006440314401c05074001502480595803410700d9030711007600d030404034030a01820f40040b4100040070403000d13005955020000750541485820301d550703407100c0d4050301d512002100000201400141d1103100f651100c0703030300480b0b15004180a40c140030001e40089464000a804a42c0128017807490600ca6021551066041b000c10b2104444500c152903032060100041c0000231805008010b81c680f140e280036030200c50b241d0041440002c44004c0c040254400508901c114070900c3d05a50242c4800784c01040b0805072000412094400c03080450a1840103800d80c441d0300d208001c00c10143d0750005000c2d11f9601c11034062244900c0441c011f030005c002c0c9602001240000021140150105140a0404502454040c441180b04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 831633570 1250 831632320 831632327
    0x30c0105060103230c04120606081006080a110616110f030105150d0501020c01110d0f0506010c061505030708010c39080d15170105010b0d0f090206070503070210 71
    0x52804510040b208240404c00c440c4c0c98090303000380609031078a00e0240c030749101c2d0b607003c0c0d0752072001c1c1c515648910007009a51410015a9000455001c04000707403414902802c4d25101002e03c042c1c142c200c205201d001c0c3e90794400c211050380400d0364900c0901700c0346142c500010f001c409150380c81092012030010140c1018040d5902c00d0900f6413441c031000c0380d140104107132078100c03800c195031942d800c2c85100700200d800d11a4400c84030324094000c3d1114020791032102610b04000441e4001d07400c100900000e0317600503a045018560041c000b00f40b4000c2e04800c074105040342c0e8804c81d454424407200040c0c2c0b070419885a0401c1e0b0701031380c0703542c8001801350750500c5401e5554052a5011404400000c645400e0a500304806e4800c8108510380914041c2e12400c2d10000c01400041c05a150b1081042540d02488090a00c078580001d100e290b240000700501030007074508500f501030300d41d0095059805568400308109500422403908d40255040403980c98101c0c10b000c0303004070812410007001500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 831634820 1250 831633570 831633581
    0xe01090f09110d11060a03090b0a20090d12050307030b060906030106030c26012c060f01181e0e01030b04030509010c08031602060106050903030d2c030c0105060103 72
    0x10081d50004034604102d0a000d0b051200d4841510600d04d014001801652100020101603441d03130750105000c99982042d0f028008081e080034a2140f80483c0c4441001444034a02c004074409003009844844000c08035003200c03461a00100510200506506402d41100156004030440ea9040018103008824403030107101300e50140c0e601c00c03014001007280380d00c02d42081c01060214602510300b41040507140f210340c21000d00c4100c02a0083e0018401180000b840020310543c028202c82e4a081100b200c1004400c0501441d000340c100a940000c1a40503400d0070042c0b0514040c1d0134a900d581d600c0c44042c0100c4217141c1c0344030480388900002c03030b400000d620505a03074001080c0001034a46550035200c9030710078444c0134140b00c1c10081e00e502190004018510400c00e40c003074007030710907500d00000f800c0a005800c04814000300344202400c42e10008181c4225100c000400103000c40d1420b603003462841900921040c21801c240c1c0850100c1c0080050040381c1518030003030082d900ca28005505070b45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 831636070 1250 831634820 831634823
    0x203240d080909070509030d080f0a021603110304211e02100e030a0c062f0717010e0d0f0806040506060304020603130b09030408070e01030302120c0708070e01090f09 73
    0x700a00c030182141c5001c0220f190001c055003403c1340f501a4030404681006549240305c8041100302042003085480501000e503c281c070800704520b02030300f8070352940d2061b101c0d0744083c082004180305051920410000c0364042e105a489e40080451030b03046e90410303022103020895107813246101440c10b40f0f05450488804a600604480c440880700a0803145030b0300c1000d14a42c58030545031140046101659201e0141c0003e84d1106891041c2d0b02d240b0003604901c059400c4c19901081c00141c3e41d100219004081c3c0d07058188841001d0314640c1c10a014041001d0204841d0241e6043c1c425000d41252018400c52810b4503440b020342c1d43c003420481220350441e1240c1d00000d04000060061030407200444e880b9010309900c080000440c0c460f00c0320602c04407040300301a80005400c0c49050020040b0350024507070000401d410b5815a40e0094a4141841c0702d8100c078a00460104280201803000502600e607450850740d60b50390703445140c07812072028030a560345186400c481d0201a0aa80244940e05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 831637320 1250 831636070 831636083
    0x40606050405010810050603150906150d0b0f0307080a0b0108030a020d26040c051e1e030f150103030914240d06090e150f0411060d0203240d 62
    0x2e00d040c00540340c0c0c203801046441e1902ca5a840860345680c1d40003d103014502d0f4005c1c0c0920b4603c2041480101c480240c40d903485003e00c00004a2190350304801c0711040c3c0784d0850082100c14000001c070740d0403000030104682c5030040030800700d04554009040d001142c007603869003842d66030301ca003060f45900c1100303184001a040200d0b0403130102e0181c15590150590700070820010743c2018030700b4208842c191022540110306000070844c61070401200d01c91400e080100c1041c0c80e03d2440040d01030748040b501141803040d0300c01c500c5120b640510a544059104009903100d983d0224040c06409809020440c0810b814140208003000c691159a210041c0904141c0e4403040306401c0c00456a4100380342041018100190540d2488a015050003401400b001107558000340101f581001144410031081c0880c550800c0102c954014800c2d41054001c940c003407280702e250021881c10712034081400c0300c2da80000244a1007100042c48040c0400c0120f0241c07a140b00c4e002d0401050304081c02018014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 831638570 1250 831637320 831637327
    0x1e02030d0813121e020705030115060e0f0f060a0c02041b0e150d0c0201021b0d0824040203161e0203120606210708070801050d120c05010608010c0e04060605 69
    0x150030259003100010040c14610303904051944820310380c0c00400f1300c403801a00055400c221030b080034003441980c164144400303220310782041c0b0018400005100340a2140040b0f00075402544c445059042c00301c00007504490340c4007000c07003018141c0b1a18000c203e00a52605501d0001a442d0b0200c0c0d1158509555428038407802c80000c00000750000f180f0f04480c0e803070030003049004541a119158054186400140e01e6000115078010080400c1c0407000c29034100e280c2c40510654013400299000c201c014a40564200c0d03065410f0b8400350304402540c0080c80001846580c2415000c0002c6000040d941d070205802c8910003451509907030702209000d80c1c000d0020030032200c641c800a9501501c040d00d064242034810010300c00104602d103151362840c02800c1400303000c0d603015543c594007c4540c00c0c441c0c21945000017103088c1141a85018001e80c802842c41e0324541e104000c02c00d03620303030440000d2184d9a2a00b500a008284540e00d400c08100c401703443c51210300f024082d1404881854540500703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 831639820 1250 831638570 831638573
    0xa290f06010e120d1e0905061608040b07050c030d1b02180a24080312090a170301210203070e0c0409020a09050112091119031e02030d0813 61
    0x101480060302407414815109503030300040c1c44801481008001d0940103002c07801e40144084c2c9403482100540314880301c007001d05480c0c960003050402c00c41d00e060300c41e2956003800c0d5481d02c1c54044103100c01020314a00140000382c04070014007034440a4041e20a07100703420081c00030903070b440721490502001318051004148540130000074445d031190004c2c0040c40798608043c141320b410201210004d0840c2d507100590315541c68180d03040c0401a00c200071960055003030000d840d035240590542d8042d4054030400042203d203080c0182c1411550011403140441e510440d0315480b0342007400740b4410658460520f02d0311200040c25014000d80190280046038207181e881007008500900340307080c0c0c07401000700142005491004011410003503a40c101d020342054001001e0b000c425034902c0740641071040100104100300401c03110782d08200d51807d6040031001320440384c41c1e01988098628401140404c91081485c02040e000501c228151400d040c0d042c2c02c141d80460b8266000704000ca80b02ea0100d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 831641070 1250 831639820 831639841
    0x6220912020d0f03110903010f020d0506090103030c0609171602130605090c0307170c0d060f080d0e0f0613030c1e1518140f01020d020c09190e0a29 65
    0x100d8803061720754649840d00c4c043c08a802e550b4001c520f5000d166001034a0403807030000e4400e090b080750307084038003e815502d1900c0080c010307521482c0140c14030b40e491409100700005424035800302c00c034480c11980c1310040d147d54a2800c42400300140d005114083c4a40c41d801e46074031070081554401040540d0503102c40c08419919040108008144010744030000b8681e84400b00f150b100b4445101084d5441d50b040c90040706492196000306507401c0803110a010960000c1a01c120882140c503155130f0761010180043c01032002e1104280d04410f000410380c9110740f0829501081d2030080d04142c462590b9a81c415040041e0b280e80030a4070f502107a4140a1089401004c850b400a2440d182551400110b0945c0b000705940e448044007102c0ca49800045051000c150140841c0c00d0010b44130200c5d5a22019403100340c0c660340786106110580004400e060040c6101203407518030b5038100309030460750002c00c2e81c84141c2c0c0d0b010390b051001c0c010829a56100500031310301c0041c0c484a03401464488030242c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 831642320 1250 831641070 831641081
    0x60421021e03070b0f090409081e07020f0d03090302060a0302040f080c03031902010b0603010e040308090c010e0f0109120822060509040f0b0409080417010b100806220912020d0f03 79
    0x5421728141001112071558860082c02c40060260700001d0341c0d960051a62005080982000d400c0701005108010140c0d4840680f00840c0c40f00751464075201c2030900d0111001c1c005604002d43c84034011628100141e8564064815075103a0160394070340a44401746180d5921040160b194140c0c070411513060141110802459002100c0c00003140f403403d280300103401600241c109103c8050341e40204001e042d403005d0f03400e800241102c0545510b40010000901401c101840e85001d44020550400f040c0d01c2985208018031408068003030840c428a08001c0c42c0d444a01e261a00181594a0540b03541081d840c0208840c5540c485a161004040c1480082c00c800c0c1062031009075900c00805040d2210701030051041d01c90540c040e51542000032481c002542c1c2c1d15610038581c1751140300031158844040a02000c02e003801c1a01040d42c500c4001003840100c4000840800e44068003a403080303882e90460740c0041d03c600307035241906924110403a0b0b114a02c0b2040750001700750000000c51030740030b0383c0f04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 831643570 1250 831642320 831642337
    0xf0e16030f1716060b061e030919060902010201051e0a05060621070f0302120a0b031e0d020d051207080405070f03110901050303071709060421021e03070b 68
    0x40c03488860303414002d440290815501c00404401c1d6490000801ca405c0c460595114021154541040c1180300441703803040d945003000c403082100002044088500700600401424845011f501c0070f4080e1a0682c068000010100d000d0740c28207020441000d04005001d1064101511758480b541d150341c2e280d005000060000d6800080800c0540f600c1d44845a000201d0440ca000e01081030900d43c40003081120004400d50405205003c1c0c860070b2000481d4450b0050700c10f0340702054001c20440001c0c01c009180300400c086031003180c40030058040100e01914420b590340c080d980403401e28481900c5034451030001ba03c80381441000505554001c05880d50031600400032964600c1c0c9038140160020310b582c00c156514020300030400082c0c80d004981a0142100307070040c2d400e101c0e50740e5a400c1950200352002404910100c2c414219072144400d8a00510008920070345108186d8025000d074203850380b06034058006580300d42c5018424011042c10200081c00038200d141c9042000300351074100c25007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 831644820 1250 831643570 831643583
    0x30c03410f0a120c05040e071b1e1202010509100e0705060c0601300303050403020a23010501090e0a0b0c0c1209030609010507090b0a0c1a010501021504020f061b0106090f0e16030f 79
    0x905401041007407559078090f492004ac10200000070703040200343c08800101035011a8148010041424408a000384140e0841c450214046000000850910400d60030444e0400408070b0b8411607480d00058160480d0254021181c2c0b008102c40400740814601955a00e1b1042e10f150410012b03110713520a5a101e8001d00c1610000c1603140e030b600d0101c5030040f508109225001d40c0036181d2380310a22070725004006ca00020410100140810341d01c5030781c02000074102001d043c00180d200201c1404450420b88100180c07006249811038031040ea0308502e04585c0248160000140700081c1441014021030796502c607425010300e8524940c040d640203140c20b1081062108a03480011130080c0d10031000200c4c00c103420140d60502d0002850111a1446801480607810602c40075032103400c030012000805a80c41c0340d0f650201a4194549266844107040541c680000000d60310541d40c411a4104038514050100910b485001613503200d1114000c4054012010104002850078540c0b4210912030780 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 831646070 1250 831644820 831644867
    0xf0803071a06011e1e0c0f030e03070306060906030c06170a02030c0c070e0f10061403130b1e060406030b061306030f030c03410f0a120c05040e07 64
    0x365005050049004080317095800003600a00b0a2600b00c01220113910340702d5a040c0c200e8951038000800180c014040c040540300c2c0d486203803014003805001e150011801d0218a955401c42030007803102d403006840311000e07807c01043e4113214040e44440b04072100b40c281fa4944581404200950015110300740300c8508001621100030107000c4c000084c8000c541070901c52034520340c5102c00500003002c0140e40c0041003001c0c80010b80014040ea01140550303a91502c136a100740d14546c905d80200c2000e030000c09001c0402104050120703104c4d502c0045a261800c10781c980c5814031041d10001d0000904240751180068698100090750003c03c1c006400041802c1e680d0f51108400c0d420810070030350000381944d150f4003e068200d005860186c0340e5102506c12080c0c07400c03860079401130149800d8100c11661010803200c20058042d2101e003822007020782e5440001940141095100000501069061605902a10740180180c0b02150443e034103084e45a42c40ca407088428034044ca6010f4903207001711 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 831647320 1250 831646070 831646097
    0x1080601030b1509030d0c030203070b0402130e030c011113030f02040b1f1710150324090b060a02030f07050a240b04050108030912100509070f0803071a0601 69
    0x820301ca101480c50403c4d5807880504241800c14120802100038800c400704c0b2040000e50010440b445140c1104020344030f51154400a42030b01b13a4403103820f803030078106001141104000300c001c0c941d4444540082003d41c580071340f407150340e01446641400344070980404102144010608442da94401000000d140c4000c00008018640c1d2030194090030b070303044405030f400a0f000008941c010f02800e000c2c8206241280c0c00d10003040c401e0150040c40400c034624046854000d0b00015000202115080c02c8029a00c1d017000e609585440380c1c050303050070a03841c080315040c80400c8400100095014511f40303c007440382222190310421040b07520380308075400302012908807030a24450b40b042161801601d032190000f5404d0300c03410705c42d841c441c3d450718004110780392001044074044102034502d01001805c43c1c1c18181460413056000d034443e4204410486201400f05203882503503400302607180025242c040417540d82c001c221000341305280301f150b01c04564403a0b10505511580524110030b02c00b001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 831648570 1250 831647320 831647329
    0xb0d02130e0c121c1e03020708070c0312090b13050607080c010e0a061a0a0303110c0904050709140c0d020d11070f061b120f090506010e011d060d0201080601030b 71
    0x501c143d659458004400c901300342c01044003040e00f01642440c124906110702100d2180000e0703500d142405141d800038148040041c980d06a508140c2c03c19003a1020550301e0503d055424407002c0304000141800034081900f81500d401d4030070782480d40fa030303180049081c0020b000b0b941d0310580081c0c6102c8024440340100113804d02400c6060000c078005464111100c0c502031055440d42e07814223254085024a8044c0354a80c400c80c0300480350146040e000c0074035081c00703141c00e213044c40c0d1660341c00821a804220604c03500140220884541c0c020801500c00308a070f0083c90b9060a030b441d070350380075020050fa00003030745190080e10382c1184441c00081c001905038842c0d10759622095085400e8030426150006000c01d500c103d0b12403a107103031080400d800c0e00d92030081401c05004201d428040d60b801c1b48061808055000140190384001190819611585103800801d07091185ea50760113002903240040b00000305e60301d4002c0b08064500000840340340c2c015220804010503c5040541d00c02d00310a5070b41e107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 831649820 1250 831648570 831648589
    0x1205091207060c0801090c0816050c07030305070b07020601050a0b1c060e04050d0908120c03162a03240b0306070e01030b0301091121030d020309010b0d02130e0c 71
    0x101e9400000d22002200f00a000d40805070701c6038141600d4054500c4402e5004000386904c071014040408001410307080c20344042c010000c203541c95220f140c03004000c042d000070080c80290300815414032250b6900804a80e00c03c000d00581d5041a4032070020003403803615502078050341d600000b9100d42441070294850840d1055881041c0c02410319061000b40882800300b1400d50419240411200d414404a02d980d00000000c01300e0110300024507500160041c42601c5414164410115130f980e200d00b0440c0d850068400e45221400b200d05100781601d40c2c0640d25001c407a40144940420310322500400c00305075100381ca034074410313498018030a0035540c141b18180c8941c4040e05d40c1001c220300c1c00d0004084590f00aa0316002c0c0e0301d024191004500780f02d07010b0600b044111405540c0c0a042c510300c00004081010414032480040b662420542c601e07000703144141180030080202c1a0f9030010400ea846a410010b5080004a154040c5000064100c04412010300007100c0000b0059400b14103079a9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 831651070 1250 831649820 831649823
    0x1c2003250c212106050d0b1e0103150504060b0409141605031207140102031515070f02280f0303021908181c0b01091b1205091207 57
    0x60300e0803003038020002408a100c0a10b00c140742d0702c000b0061880c20141c007441c454100c034804401801c90300d94440045030012400b8010180c051031607042180f50244100740203550007a46024280800c5030110040f880d0301d41244e03044548e501848008201440090070080c0c416114941c84c1c003261080c075101c6024070510b02e80300342e0703e00642c88c10040c0e2583c2012081c445c41d40107881e800b40c0030000ea5a000458504000704800b17825900c0c0413070300c2c0c000c4035003c80c1e40e2003c41035400801000703001140358650540b00c61050300d000803142c2c05005032107100e100f4104010841c1c1404c860080c007504014003001240254140f00c000540b42c01043c1c003070b10303845039401014100c000c03401c140101503041c0241100e00c1440c083e0068505075541e40c2c12070f540100c03104010080070b110000035055940e0790380c02c500340d07810000034034070410641051100002d00340243da5140c1c0c100601419240c505031a0405900f0007a03a5078846000030304c0010019000141600c0d00c503104a101c1000e800039018001c140c101d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 831652320 1250 831651070 831651077
    0xf090702100b0117011703070c060905030d05030108032b140402120a030c0f061b020a0c0807050604030b04020d0203010c050a020c0a0e0103030e040e0d0201021c200325 74
    0x440c640740e501c006565003005442c1c10803480200c006580b02c0102282e9055403c510042049442c030b25034114614091802c0280c451407a41d00005000d6070001191010b5500c16010358a200c45005000e5910740720a21628505074410021251a50312a500c108004c5483c3d42d1080142d885840c09001034580d410901502c0e126607400340021440c1804100c1403c4070b903000649086409a02c010301000840000075002c40f8600344107008101c1c40d50300c0307aa512200451900c420100b4100d0080d0340740c80b00003044034100b000c9800415462800261003085403401090701e031501d41143e071002d03107a0700060710403a00710f02c1c403c800c0001a5020b0240c030302403c0c01e5070b8400780c903900103400c001d261040d0490b031b090041d081070380300b07200518040302e4040c1902d401d414601d100c103c00c1004030740148001490016280500b40242d01055410b4008144445a08502c0000318001203803c404469040c1c600c1c0f2110b014401c0d4a50640c2d00c0d02c4080c0d503109000e03054160780c0c8076540f00e87c08042c141c40344602002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 831653570 1250 831652320 831652333
    0x50d0302091206010501080606180904080307020615090c0c120a0512010f030f2d05030d0605010e1008090703140607030c0c0c0e19020c28030c06020304020f090702 72
    0x7541040352038000310080c240010000c81d450700001901c14100a4001405660000b80003500344d0305500f07412000f803801400d1007485140c18100040c0540041d11004014010800411034108a104c01c4d410100301c0200507224546440780c24910b180e20030340c40c20300c860140031440306403242c43c6000307001080745984910b03944621128410801100581082444a4606a0a10126110140e404240d030390104103040c0790303010700640d615000c90350b04c99801c110303014210b11810440d01001405818040240c1440182e440e10019251035510800460300000d10344d500c0e48289110300c0400ea00030041d5826a80407549940f10060034840520501e44541e01c40c20a20825540c03500c41c03806440c03500c0c500f86c141300e04260303221405494944031b0090030400c3c40001c03800030a500c8120f90304890008030215030b520700380610503444082d8416040340c04203840b483c0d480c0b403ca254266004190b030644c4c406070f0400090380c8040094002800c04d0360070940e0344a840003140ca911844900402ca0358005001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 831654676 1106 831653570 831653587
    0x306100306152d091806020307050408030a0f020705090c19090b0c060a0c02030306090f220605060301050a1806110702191e0e060d020d050d0302 64
    0xa02001400c00940303c140e450662824000038098003100c9580c0342200c500700ca01601c1d9200d03843c1c1e1001e68002c00214135070300030f540c861002d0500904164448034a5840e5411a02c0320101103051004800350454041244400514088825900307a2a210b054054180542400705030a644074644506640d07014450040243c80c051207141d803141b51b000c0318103a480c401556412401c520b4001e11441741403020040724814903006c0c001e001244c50b000720001d40000000c140c1003450310549209e010118400100003002805858041200e040c000209421101c0103007007850302d903180003035513000c6d00ba801043c1030403690080000200c400c0e01020000c100d101d0381c00f000354014045049901b401c45e801d03040200380e5030000c1956107000404408030f95071035458080d60106044000001c0d410345403034001d070340c1d405201404984000c401581d0303075403400003143e40701808a500401c0d0035a = true := by decide +kernel

theorem cover : BRFrame.Cov 831474820 831654676 := by
  have h0 := BRFrame.cov_init 831474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 831474820 ≤ n) (h2 : n < 831654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
