-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1630
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:57:16.997589+00:00
-- url     : https://prove2.me/submissions/17876e9b-e6c7-4240-af98-e971ef6b8edd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 292985611 ≤ n < 293165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 292986861 1250 292985611 292985621
    0xc1e08041403040506160618020a15030e0f0c12070303080c0c0a02040e03030109180807080a09170601050a060216050f0310092105070515070c150f1a13 67
    0x711010075203203065a24800034070340da440320041e5039006d40c40c58254414040c4034032455102454000c50004582000d50005201004034001e4a2142d06880508110548030342d010340030442150040f5417804d0313120b030102c0f0365136407440403054883c081c40740d002c490b0702c6404107582c02160350540300d040594a40b10320b0310a09401042c0305000c14441c131584000541e0310303030141c003008a20520140d0780d6541803402800a64000e24500c90302d40115098600018505200b2158800e411291a0b80c4917140c0041c21250180d0340c2d881081c1c0700e1010b882c102403c00010442a0480d00110b8801c01c929507241d509a0f01d40407104407012180d07030340d504200280c2c00c0c41510290f01c40c000509a440c0c1400425102c0c2c2222143d120583d13045401e101d4000000c1c05c1c8650354800504941003140c28940c0035a81c00d6924150a0300d201c0e400e100756800f003400d4038000e12104911580c4071904562300c0d91500825401000c0202260002c1802c203005003a11051341d04d51049a20400b41c03001d80c06c1e400622035503000d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 292988111 1250 292986861 292986893
    0x3030c05071203060602010e01230703020903070b0301090c0f020c0f0406080f100b031f0e0c091e06150a03020c0304080a05030a020606010305010b03060906010e040f0c1e0804 77
    0xc0800c03900c400540c4040078880998038a0300c00140f000c0c1448170003800c59420b102004170981c548401307032400141d20700013000c1d0700390071071580c00b102d95070000101c020380508a11a501071083d030782e000c19034102a0000d14144d401d031a0301041000c2c02110200d4110f80e1551268015800c80304c04a1082d040a500c2030100c50400b82001c03c2c035a03a6825640d191003100c07100c0407200c0d0003404d0b030a801c1c1702c1c0d540103151503c28120000d2612603528110080e030340540138101500541c1e658100b440c0c40c031051082d0f05884070018000001403408140003074594140c40c140860006040c0005001c901c2c12114406510300c014610604000351100241c00940c00280003070300c00d1000340000604039204000030280f0078805e202460311110810006498103401500c0d090500d800c040c014050340075203000b42d940c05a400c440510454690b80010b0328407440401130550840e0404a50101a4010342c100112584159540c5100121120301c55540813420310b82d100f000500040100300415481c1c10410912 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 292989361 1250 292988111 292988117
    0xb070f031a06210702010b0a15090b1308010c0909050603120910030204030c1e090b03330c1806040506160c080607121109030d0315050603090a05062203030c 69
    0x20b074081c142a143e501400c503000d20051307445101005e15410701120000003464046000c0850810280c0040c1018109000390344102c040419040b5a80c8491903132000207014080007000301c0d41014400803d40e04540c002c3c10700c5c2504090100c0c005003400120109540016000c550404a035502080209080c000e219410140c0034072011000c02c0f5041040401808000c08030300026203601c03803054148006130702001156242c00c84400558401168514800d00e10719074140b0002646000b0600c500c450007000d8256403510020401d4288400f0000c00180c1e031802c29504ca4201082c04210446c85a0300510342c000c0d00030310588402d0381c0541c10000701188100c1382c1c0e584030760301c0f00c3c0041e1610008403444400680c1201038040c01c0e124034401d41c0311a500d15920700d880c244000000c039a480b800c9450601c10036541d8905808451416a6440041c00c0020001592070404010003a61212404000d4919018a40120b20344000105100c003503084d80100126810042c3d40f01500101102d103450424 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 292990611 1250 292989361 292989397
    0x21090a03050f010603140a030c080d1e06083003220f1b141e0301020a02010902090703090b01030602070203032109010e03160b06030c030102070b070f031a06 69
    0x14010b01c0580c1c02c0201a000020315140385003002c80c400d50103c001d8881503080305012101084d4441100c092003a0401da460b9039980c004454400207085081041e83c04084000b058003080340550810b01c22606180210b45c2d0184410400644101c650a4600340d00c03c0c0411501140c04e42c882c01461b031141c4480070f00c50802c012030340c0740c0d04200b14450742204c01500c51b1a0390820030510b011030600b903072001c0039049a09801c1402d103084030040c000e0000c0c400c8007a81c101c003801241c08100c0c81004140503000390340b541d2103108003030301038119403901300d00c00e44104001800072846485801c142035002140c490440e403030354480da0000d5100c0901030343c040c0020072100000c0200180c480202e22028414024246058904242122182c940d0030613103070020011406180c06c504c4004592913008010142d5503161100000e16066006801503050350012a0a030148201071100b2803145003251101400040c50f140114101c64103800305200340c00c01c503c3c0784481400d00d0000782c141900d50b0000141c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 292991861 1250 292990611 292990613
    0x10804050309120a1502130611011506020f0111090901030f030909090803061c2f030a140f0610060f021011090117130605040302191209050321090a03 66
    0x81d5603c0c4500112a55011880340003c0140c0d40705180d0b500f0010795021030030288000a0085241203d1080604100c0c01c5204252241000e502500700c1b0701e041070041040b01d54a44c0007030b45071444d41c150340c1280c0d4601044e007180c40880310100d810300c10006190350700c41e82c21907445a01d1541c00c060305804003c614807000c18a40c041d84070300549940130b6510705403285442c60030003803080440b80300c0400b4511800698400918180c500416058801c03c50140b0003031030024000b810340d03030074456642c148a039504d204c05006000701740c0d281e0039510900fa107007000c00484010743c0d50202a03949031410401010304008041c490036564080d40041d20580d51180500107805d02039480c440541c240c11000015041665a0401200d101402d0850039040785841c1c8050b070035000001d0007001a10b000c2d182c1c030002e02090b100344640036001c1c40703240030700c0545070540c10801c00e207107604201c0d007000c03400c010b40126583c600010b404040c54504141d207409890007001d4100075410000c0210780000034044044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 292993111 1250 292991861 292991869
    0x40b10030812060f0103020a08060609040b0402071407060c0302070506070c05091e0115080c0c030c030f071e0f030f23131d2805090f070b040f05010804050309 70
    0x9100400310342d02e9500e03060100801212440c0d40901c0790600d0300c10050f6148554108480980c000003c81d1307a15124000305020601520403191718540c4203200080039070411005250000c0c01803408021130700100d44420040d1408a014032020300580e00801d0100050714281f0010040584640c0e0300f0046142e59501107141403005444c02d1814595040e04048035001e01000c075030041103124080c503450380c49840058002070001d804020190300004001000301400c00459030700c2c00e520b10850f03036140c42220300a030141e000316208540c22202c0c0c030441141640329201101c0050740041c030002da900207130365040c4d4024603612060b00c24880e411020b6007030b0314006180c074220580040b0303010b9a1a2503101e00703a000700b901038110b041540703039550568401c1014645165801620070640c000c011900701044200c1c68500008080c00c1400c000030441c813004042252500c0c882924103c070203441d02e520840c0302c00c0c010dd005800c0000e40340401080603620404000d50098040d9090701c0c41c10325144041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 292994361 1250 292993111 292993117
    0x50d03050f160f11130513081305090408123304090b091510080c06030c04032306060d1104150510030506032b0309031101090b0618010e040b100308 65
    0x19241340d40390300b581010f6404e01d09a0700340301c5900701504101c90b00e40130020902d1084140c2c0d02600004021034099551004040841d02802e0000c05280c002e20300f5182c5071f1025449083c1c001c10a9000781c0114030899010081d60080803030b8070132003142d03611361081140040e00c410790a4550083d2a102401c010075440200d81e80146d103030401622499400d468494819080502202c80d503e034030b41c3c401c015240c0003103011440c8410446a05a40e6110b200c54007250340103d40010b0558075182124080513003050303d240c01148030b4001030f503130107585550070803408181d50b06000d0103800507041101001e16003a840a059485402e001000030b540f40c80c0403d103001f100d0150b06c40800c2ea64030900001e882d0401020100c451480308050a4600903140d04d032000300b00c2d15503141803646441c901c1c400c250107074030b00c030a400e001d120080044400509155450640685500e401107000681030940e40340400c0710141640c411000006044e21a540c0d4009821780007030017114611042803003c40000d00442c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 292995611 1250 292994361 292994363
    0x81207030b01090501080f0609040305040f090c09060f0804060b03031c27050307241b0306050118050d03030b0303030f040c0b03150d0501110a020313050d03050f160f 73
    0x580480140005422924960000345c14007140504000052038003051180d030202c0e050b9480a0141c41e03030320303007030f98a4012600034400f1501619000f141d240d00d15840124800803903524a03054076901e01c41a104e001c000795114001440b8140020007281c429017103511b00b040040d08403864000d216503c007008080ac40c0c83da010143d20f80c541e01c010f290301244410800c14039044002d07802030f43e5543da140d49100c0d0100040060382902090108010342c1e0302d244609955a400a001c99880440c0b144e0920000328100c0010078600100032590754458440030f406e11305001010000303241048100a269660742e83d0481c201070712054114015101800514044c00d1944086039403800d00d0314084900c40f40f1608030000000092080252092101034003020b00c1ea4141c4080c032425040d0306090307000d024500c0b0134500404000404010841d800402420082f072030000d40110b0135118820000c040c2002c10001d00050001e00c0b14550501214000b00b02c0002030301e6071315082080c00e5445408000d00d02c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 292996861 1250 292995611 292995617
    0x40f03021f051b090d0308070e09011206050a0605240f270f090a0c090503011a01080105041103190609063203060705090612010801020703120e0606040504081207 71
    0x100b401500420b2106180f9482e40b540b05043c1040a1040418014141282c0c045d040100080201e44220700078911910b241002408801c419070315004110780c8071100e003004175032061a000020f80f80200302d201c2c1d50240c401c0100a4000c1000c080b40304051110343c0722400745081d904200b480d11411081d030041840c8440b9a00b2464a56403004990700c0040b600b84000d07010310034902e00000c0540c2d5100060b54000c0d030700400002c1d0755400d00f0f01102e006c0340e140c000d290035602c4c2c0100380f042c0070106580b00380208800d90b00e58869a0b219018013050310404521010384400920208481800d403e03039404000c0764502002504950303803041041560403c0c0d00c04074004a0340008200c903000400300e4141030540020507195211581d00121b41c4e0b40100401d50420000046001c101d950b40b040b041303c0c40e48007044400c0d005540c680d01d400f4002d501081040780441c00c20000340621400d82d00450118902d0000a4801c0703030b4800091102902c0003c00486081d401004000c11858905010724050110340d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 292998111 1250 292996861 292996871
    0x3140c010b0a0f1a0f070204140612120f030910090821190b0303070213060501020d02150a021c0e0703200d0609140a0302060a051b03040f03021f 64
    0x42842481c2e0756640280350403440c2d180c4140000080c0e402221500498a055107644034406400c002242c000c2402c02507100c0e00300038150b0801c00c4040c440340d000700421107003003d0b2002c45a65a598820480c070184c002014144a2154040740090181d548942c6940580303003000b4440c81c60300115510068101c82000022a0b104103000071203071100350401840c004c007030307160500149030b058444483e055251155120b00c0410883c4c1c0342841511403481e8060481d010695038140d003e17018040b00e015003801807107002507059945100080304245d511510550700300710346400c021080030b0741c40036512116000d4a402c4a2442030351603c034600028203a00084d01c0041e0441c45c3c448082c40343e0003418400340021440983c4107039102c1604d080015070280700084d940c0241e1409406442840380f850801b4040d5401800130305401082c514810481d81100304825a0b8201207044010301c10100d00c91b10041c00d00001c1c0020303941c8549000740900a004542404003000d0310502074207400251060815292 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 292999361 1250 292998111 292998131
    0x6051201051906060e0d0206091e0f0105070210080c070f15050703060506120a0e06070f0201180c0608040201020f120403060b0904050a20061602010e01020a051903140c01 75
    0x7991000d40b00c1421100380101450010005d000d03031030b03100078544a00c03101c06c110811036071010100e6240e513101400000205a07a03c8040c01c80c0880b440141c2d01038007a031707203c42c001d66115204590326035034010000740048015044c2152044401010040040e00c20488400400c441c4036010007098480c440840d0401c0345040c690098400140c1800145414a9400c1c030180d95501e068030f84d139400c2d13071400c0c3d14155209c003500d802402c07401c075007500c3c80c2c02204144044298410744c01d1034544032507002441b100c803104029540d244002800600341032011501441042d1040117142d8003d801441120b4a10106031806414070f11200541c24406100150402c1005400c0c025001c2a840407920054946007540380c0d1501d80300034400060030314500008002030084550400c028032800546a50b40301c102420400302120221601079020407500f000380c5186602c00602816100d5002d4082c10303200d400c0c0c200b10704802000e840200c0070b0221840740c010a204040d806001c1001240001103103600710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 293000611 1250 292999361 292999381
    0xb0103061505030d1404051207050a1d0103082b2705060c030403090b030c030105041404020121020c0a0f0308011a0910030209130524010804150605120105 68
    0x4100700c4a08048102408210540c0c0c041468440910a070426900c29034000060001c148904e82007503a010310a001e22401da848001560810b64006803095042252075011402011606003a44504600d03428010301c00100000003411045082d50002d030740c07408202d04880e01c0f455000c00003030b640390364800b18400304102e42005240e000d1710504048141c021540c90f082d40342e0310010410352501c900000841c04061140c40c6a074028400c0301e4402c0e40700c5c10700c01440c130b050350301c203108952040f410f20154502c902d5070800a18026035058603403551822041c80120810201089036040d495400d00c01252000001d021890f601d500c141100c035402500c502e005040c1f40c4041e00945a40c607880c90f40c0c500d101c9040411210b40c0c81c4101c41182c41c85101000031400391040304080d64010f50b2941034078052039001d800c07250081c511640c49600050742a485418502c40180d11280010400c501040c00705800801d2516001696600401e015071101d02041201c0140280c000140e952102000500c0c09 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 293001861 1250 293000611 293000621
    0x50405010b01020d26071112040801061d06040b04020c01021305030f06010e040f020307091802150a09030602030a1b0206040506071805040c02071703120f01030314070501060305010203040b010306 86
    0x2683e41048413000f154420510922072907190082014001c41011964280c0100c10100721f8100820848864006000b502c410682241c40360652640c2007010108a0401c079040740000e204510b455200301c0d81d60002040050703c030001460350403170380c200002d0b41d481c0310a0000305488100e00d00f405040514000c241403801c0c40a4020340e003260007803401803003820ba10002c00358006800a418151040c12800001c5c1003645550012070b0f000e1414045c0b40b013803d210440310000b1402244e1a10b034401100700b01554030b110b1108800009010303144280700044060380a160030464814000030241d185035043c1d403044036030106d04800b59000400304402c2110410169074042000d03d809070801c144a980700401740a0303070240300c4c40303039440d10800400d40c0e10800c9144001d0020103944072100c0076480c042d41c0c81e0b90020003800394400305070f800613162100520105040301e6141c0e645400d03030000c00d426410301e900708038000c03200b0b95211000000860000d0025602840c0141040c0072154903500d002e5044075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 293003111 1250 293001861 293001883
    0xd0905070b1e09061e09130504030f03110306120304050904061e060e01050904080915040801060905090307080703140711130938010915290a0909050405010b0102 71
    0x280b000c102c150704544900b025500301c11000031056242d0441c50032103550b1401942202a00591a08058100c490050b005540654040e441d00140c0d5080c4200403002d481d0050200020910100085110350903c180001d4500303501006607428141c5820004a00440070343d0140c07010768454a003014840d000013807464542c14401405c0007030f1032400c01407046030344052184511541c11a800103051101c3c0300101c800143c802003c0310010101240782011036041030003804041c0d841c1030000304107002c091180b14020f00e2454001c3d424240c0c0c41e0b8624000350302c10704044041080c1c4036508035043c2c00352030140c0b010900c5800c5407880480e01c641800a090302c0120703c08010f9040c042003101085d100b42800c0714411300d0700c07140040c1040302130192120b04100700c45102040c000c0c0c0c0c000514201c3d40d51080c010306a55030a08500c25689a90010b4828000c1c2d00f11207a2500985c8641d043d82403042c000c2124413114100541896a1031000c3c004880003101c00f031318982d4440020400340c0d0303810711045041d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 293004361 1250 293003111 293003167
    0x90712030801050d0809030f150a0903170604060305070e0601020d0507030c140c0303160506090c01051903150b070303060f0b0d0f0624090506040b0307050d0905070b 73
    0x84005480c0140011418850140104600250324050054450071181c02c664050300b100c1e804031050b40d42c00e0f5101803421050385294031650128818000c94003d0070004c1e41c05951385050001401214640e020014020325030150307a9640020004400b03201640050081000701e10542c600f44001a0405090b03004140801000300320190000350030004041000340c100464601458158032142c5c80e18080f080215414400400c0342000003104180051000f40306e00c050701c210f52168105e565450081024075404140706100c2c1581100007404005441c41e420314002c180d00c88103403000c0d520307240b1030f802c410482c400c00581041410340500844004101114808410618003001d5090714041c00c419051182c2d1144105c124140f01604010702528a0903081c44010100d1351009006450f2402c009000c1002403500080c189000300c2a24126980782c0ca40526540e20044102c42c40d900c540900203441d80d50700058404508204500c4014241c40003c4a64900b05403118a0310784828801078011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 293005611 1250 293004361 293004389
    0x70e010308120901060806010f03140c09040b13170301050315010e0112030201090c141906020a060203180f01020a110606030703060207081e03011403010b010801060e03100609050907 80
    0x103030328203044498005407514403000d280c0f20502664050003140c0e205661901c544400807800502e024860340c201da02c5003001c400c025468014494941b0b140d41c000395404021800020081100300c00019844811105c1030500c50645035110742c480c00701011003004018010005200d24203041020440072280130780c07492000d61518420b03000c6440305001f0302c03200c18040d4101c401050300075001807441942c01560101a29103843c0c00f4030190000c2c81e00344c0d101e049040809a025400941010140c801c0e0742c1c0902000401500d44d54065800a019082d52042c80c2c00324800a43c018130907040140d09480015981d002940320042c884003c50f4030711540c980148061000c20b903000030b8450201da512000c007503242c03000c3d03080c50f10083c007070a0f098a07100d40c85511744520000c40350004605994134540d01d203600c09100300c1072500702d8900c5000a804036441c07d005000325401846021180c410050440303c2c268a08003010065915540c00940070f241c4500900a00c00702c180040740213003401c1100c883c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 293006861 1250 293005611 293005613
    0xe060103020c0c0112150e06180c03061c0209091617030d09170c010c030c03141302120a110f1c11030c060406020a060c05090307050405131b08070e0103 67
    0x929400c0265034641406107503421441c00034030300d820a46d06418010810321034070303555045e4003a032540200d410340d01c11002420100c51120301d018205002d1004002010b09603540d804c1440521000d01030000102110348034100c00503615000007074424010071014200c104540140c1054100c2c0c1500540300d03600440c1c0100b00004000029900d40c4001400041100031490406c03480b040480c00c250303038290f80b0001d0951000d10054100400481e81550308000e215800c0d802102181c0f400401d02a0700d8020b600454000c00c401d1417121401400200300448040c80111a14034040040c1011906007501d0a544922403801c9281698046426140b08070205a00603404044030001c4a0060087e03000c0d07a016030076610200701e4030880c100c002c1c0c0215a00e40c0c0342c0c00d0113035640800300c50899000d410b00051002091203181a90010171000d0014044141410200000ba150043c030340c03400715445104590101d14592445403200c0c103144250345901c0c4c240a42e417405c01407207400441d040310741000100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 293008111 1250 293006861 293006863
    0xc0a050f0102100f0e0607080f07080114010c1b0f0807050d020102030f0c0f0a061d011b0f0212030c0903060f0c040e04020f0d110112112505160e060103020c 69
    0xf98003050400911040039050000003000480f8000039640704102c1040f410640207151580100548480c081d0030380e54000007203981030000d000301c0101250580c01c0b0070301035000d0300345031072105c0c410151080f4034000e1260401e5243c1c041c0d44801400382400c40c00300035007041405030030701030b050540b4200380c50032040e00040c0d44c0e80304100c01405260720009001c0b1100c4c0c420300211584101a01c1903ea110101c3d0a00201400c6058400d08072000c0d901807640c201d460501c1080301c41c6500e544038042d1a40d015400366070024103480d4813400d6026107058504420810b1000b184603440e000074180e01c072800c142c1070514020740104104610b92080e018004090300a00c00c0d2003c40e0812a801c01b074513a0742c1c0c408211107134a000d01045d040142d180010301000b40171000044000c00c280d80b1105904a003611180c140c540d00000f41c1c103080b40030450304001e8079240701d002004031001c61f0400341d00c90b810303900d6500d4003c0000800200c24100038041c000494900321554000000f4a415818094646810f0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 293009361 1250 293008111 293008123
    0xf060406050c12070b06040b01030507232206030b01052d0c1605040506030c0a15090b0d0209010201060b07080a301d011506030b04060e04050c0a050f0102 68
    0x1014000d001c60240480d44003009208007683d01d4005a80e1a40440d01c1c041c48450030984030360b40710700d05009015000c2d5109206003449495241d44000c002c0e0307080061a00f0785a0308041d4a090f2000412100c0c109090b610081940925a50100c4003558500030b8010101c41842c4042410820b04002c030060b0f40d41e02c100c13020014030881980000c5900b044044d50001e200e03500805c007460084996045800701303400031a01c01c0322001e8400b488543d48400c201070300c2d241c01c000111303809507101c2c0c8184000303940d851050041c2d483d0b034101035002e01c0d101c400907101a0044c07003100d040b8580001e88000156420b020b0a402002103100a50521103190341d4103045000d602d4095041001038200540780c1321404450000c00e0b02008082030000e01c6100580006e800380c1c00300242600102d16805014000502c189105103c0011800c2d250a0402100b1409841c00e00340007548651202404643d586407042c4090260348600d00520055403041c05110030b440860307018034416000030101000d980d07008100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 293010611 1250 293009361 293009369
    0x2060c040915030b130c060905130e010603080f030a06090501300c0b0706050108030306060a0f120507110c032a0a0810020c060c130311010302071a150f0604 69
    0x404909448004244924a003090f40050440d225540a016400c180c901c1e401610340c0c06880d075a403145444250a481000d060710034150450959000071600c84a194009400004440004907850f56a500e0344801074000c1b4050890000d800000d011030302e0518442d44004165400c001c0c0b003907616141d4039040784401c00480c0c428141010704d054091011514204041940c01030301d041c0560380f04d0716601c0a40d0820745040710100d18050021620740d400000b81c900c60a00101081c1c80c010780ca0404845884800b8008030502c80004000c2d071680c1d09600440344281030595a0030307252008641c50902d4000c19003550382c02608004035912603d00e4005d480804583c002c12003143e900340100200345001255070260002e4014803071380c1e04074201d5a4008115000320342049499a464250100120b8400d900c68440950108001040058140f128203d550481410018140483d58982c0c0b54100000c001c031402e4440520200444001c10140b00340030890151040c000e42c20020b400308180341300d1809 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 293011861 1250 293010611 293010629
    0x8070801050906130b040603080a02012315120105070509100816030b0a0b0d0203100e010b04030f02130509010b010909020f040e0411030703080a1d0f0405040804120b01050a0602060c04 81
    0x410b00302006003170f00503000195024004011203a500c0c02e00056540107099140010750a00340010441284200e9805010001ca100410161241070f5040c1c09508180e00c010741201c51a42c41c0d081c0c1c04002e10481c0c1c800c9200e0307240e65681e11070300d03010084031060451302c09090001100c00d0080321002003040206901541c100001c07a101c00200044500d000d607030000c02101400100c40c00d40d110150061400341c68940003100c1e080d83c84070351541c40d00d07800740104402e2402c1800b080020a00e12044412841d0018000e064031202524000e402d403030040b00d144189a44580f500e25480d644544181c00500b900181103040581d84038041c003280c403440c030a00149401c44070200d402c0c0b00301c101c41170f0309a0ba4001c00321003643d42e40349030000080e003150040101203038410340e41e9070002c180804c01c1c0001103c0204401d0740c42c0200000c11008207009002504c0c202c80510004c9425500794074051007a81c012500020350750314000410180c61900d400c68421904000203200002c86140161030075101c0b001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 293013111 1250 293011861 293011879
    0x90907030e060f0601141309060603020306060d050c090a0308130605210c1908090f19080703121a0405060303040e060d03110d09080c150f07020604030b090d08070801050906 76
    0x7400403140c6d203204403180b80040c00000341012102c2c05e151030305022510b24000601015a8039a802d070101d010440b01030707800c030b0802c103d080688042c580c421a400030403c0c85003403c01800801041400d142500b08a801d04000035810003c450784820110081080d03103001858059191240340441392020041d070740403650000800c00c0d041044044d12040d4010903401c501d22481c00500401d505000d5651800a001d04032043d8078411002c0f8040d440034140005181040d219552a20159441400c5c02d804105610150340321019180c018441d4080d04800c588207105808802c0101301d0314094a030500c640c1c400c1008110300c843c0051000c3d41722404660904010b034480c1002d540e68030810554207440c1c01011300d504062a003008a07d0140c410090480710046030a0084c07040c44030180d111102e00b20002e0010400c81e4084000a0051300e20103800c0313608080e0303240d4813408820700503140407020782c016260f0750350b201c1d510180340344c3d11048071f2812580652411020544005014103824000c2c0c03264 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 293014361 1250 293013111 293013121
    0x2150130020607050c0a06140f0f09220c0305060f04050603190c1d0403020715030609060905010905160e040504080702100c03110f0c04022508090907030e060f 70
    0x103003080e40c50181c010780410b607650098500b440e00c894501d480940b09a150034008254a440340d010610580d1401450354175107e1044681c6c5c40c02d400011744042c40390020003075802580c40e050910342200e1081801e4007130480c40303d0804030549100c03d18550805190400300801940c80480e0020402e800f43d8000500d030302d845003c01e00307142c1c04145e1011404004030b507040c01c100840603400e085a0000c12120b0811784400300100f981035050758060700607072104600f40142800b50551454030b134072034140080c1490b51745031300710195001640b10391155551000100f0008a10740650b550160010b0580c10b0081c01c954405070681506260041c01142e444000900b005407002c100c0785182e400800141c1a20302100c0003c3c4461704802084002036011036108404060018030340020104080203030440721100b80900009410080c0d602c0081c03802d1101040742030403501403c02025020b0300040da82ca21210701400f80c1006d01500c80420185441714004041c80045180b0350414000303115001c0756199 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 293015611 1250 293014361 293014439
    0x10c0203091e0d0809150307050307081012050705090a090f0605130b0405031c0506011704051606020a1704030201140c070b0406030b0415080601060507060e01061401021501 76
    0x9258202d0341c0111032921494140071100000c1c00480e5021107660034000301c248840c04240c0010348851011a03420700c040b6402500422103d035000c110049240300d42580c0380c0b113143d19030120a40070348940c0c2006074280b00b1414907604090340804800f80c280708024243d41c408100c2d035480c09001d41810751383c40118000403144c0000b103810383d4000d08101d86905040c102a0389a81c06001c49403100c10700010030b0892090b0318001c4501c5848140c5507508104020350342c4011149004000326030034041e00304421202403a10380002c01a0a403913008141603015031400d0701c120400c040c00072000090a11003000141c1c1e1060310180c42a80c2200d00c2034036209000b81c17080c03400d006600203682d022000308003ca009607056100c542e078404102c2d01485030300c001c3c0e00c10400d0310285004490140d0400340c014082540224020b00c0d20300d100380000250340d0304060095003112000c1d0001c000b116907850002c0b545690405c03510107400d125016040b899450302c90020841d03c56801d4902185409a00c1b0703c080d004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 293016861 1250 293015611 293015659
    0x408030901061536063e0f0303100b090d0c061805090405101509050f0412020309090402040c1b06150803071101030f1d060a050108010c020309 63
    0x20b045100081c91440c0143c800504611030b04e40b01e214107a081c49100240f446982500c00941c41c83c01c9505003814000ca5140603901072040c1d140c802d0040001400c074149031040c02a009180f00f1004070000c0103840e43c20a0200d04002074245c0c014418042450711040011044603014000a41e03500c00c0d49001c503d4075903081070041e0a180101000003202034220132200c0043c1d03001c211003110a901e4208121038070b1410745001d4019840705400202c0c40c1c1241c0e102d11460303441d2800070840990384035001000c0d10411500700840c0c81e456020310007044440701c0008469010760014508000906000c10010500104003034881c50b1070b8001c40240600500350300f030501c08030200c2000e5401450a1001c05412015820340d85d142006100282c40f900210a82d85a55400070001c0170300030300b403401100501100e10800d83e030250340350b0341c550f9440e80e01c20780f1064544042c8041c1c121864008803036401c071501607008000c3d030307410031030a00550396011040f1804042e04071030602001c400a120580c1d851 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 293018111 1250 293016861 293016869
    0x3020604171207110108060a05040903080906060102070f090f0b03030703030e01110c0d120f020406020304080d0e01020303040b060a05041a01090906060504050d1515210c03061e050c130f0e040803090106 89
    0x750be402e00c0381c01416031000c0703050b01c29030850003140c0542d00c07044012a900d5441c0d02c1004041d420940052202007071a0708404500d242c120004a038801850380041e045600182044021a9403008043c50703055080c010b01324a08510241142013811080201ea1551105651281080401000020741c102d4942c401d01001c03500c000d045444948514002c0c1d41c0390302c5030092044912400312400751903481010000c0d40e03200107034043c600b1922190303642c10452101130034040d401001244003203140c1d10b4912810004e40b10600c1d01d0000504c400001501028242c0c00120300c0a0529005010a030740003c01c480440e4400e0765280c414010904191004480c0c0d0703c2405002c50400d0b0f05000329101403010b0800b543d20b0044140c8008035420701d03050400320000700090501a14220410100701c01d540700d846684444c16642003c02d00701d200c020304032541210038500c41e107804136400d06c03400d007015955809007062080c0c040c9698202510f07910b5488006100a000341c90000000310890f50a4000c40c0c018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 293019361 1250 293018111 293018119
    0x4030c061d06060d120c14100603031b03200102090d0b04030807050406140d0216061506020c0609060a0c0c090f0b011e030506030703020604171207110108060a05 71
    0x540d04015500034070460403072a480e901d104402c0401c8051511800c0d0103010317a841a9448040d1a0940d0b060b40d444182c018190f0760043c4205122000e0b02091090090075640103030002071312401c524001d8129000c20219854021070b400a050001e500880440c10b5204485002c10407042c1032004e4501900c96008101c0d045202e1075405010065610069800703a40300b81c545602c5580c541380211040d000718890b40000440d020102141703150800002c14450304001001340ca008040c0402c0403456000040440d22075a80d07407104000c40c0d031800c02c600060055840580b00d440c01410001c6d800c1d01a84c800d80d44a03290024010141602030101c401155a000c410494400d5131440900300510820410540e02030800c41c40b4040b03903228200401074084040740442020f64540411801040b00600c001e401d44503800000c401350f40e4202c00f400c01000c12132040c5040701200346e0942e0400c030486403c1c2c100920b0511003100011b0309009012140d401c00c0c60002c0071669090b00295003080d060b4801500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 293020611 1250 293019361 293019371
    0x318051002030106031113141f0f180503030403150204080f0a331a060d09060c020a0c0e07140c030c010c05191d0301060611060a02070c0504020304030c06 68
    0xc85000341e0040c60403a072503034404001403508074109903407603c83d11683c2c0052901d41c000038405690101d03020701408201421180e2030703003d284001000c60300c142c00d4100100d0041890316007215401600c0590101c07511101410759841d003804290790303000d113000062209100320891030519101d035050714020882a07048a141c62455000301c1e444e40710b54070080d03e013400680340e016044120500303800c81c040d0040442210a4106288010003011103184000c007598665080079050b0360f58001400c541e101c11100020703416400e01e0300004440c0440040001c0d034003e50f400f4400300d1807403040381c01110110041c112041e03440700c10880d000f40620407904004180410060308006000015003811101c4030020848440c2d081000d41c1c1d00d000c0c082d6107041d40c80c0002555003916100703000300c2d2146400d5846c0360303412403c5040080e003925155006800015410080521a158100301c800c2d0031101c0440c0443c82d002d0f0036202e00e80051450300030580240c0d00040805d08052061008048041e04404100307d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 293021861 1250 293020611 293020633
    0xa02040b0913231905060f0d02130c02030a091e12080708040b0405031509030910020708030304050a0515090c040203130b090607030f0513110a0315020a09090912031805 74
    0x50f640c0c001d0781c0924003800c030240d2490700041284912030007040000d200a800815038000c120620303058000c01c0342c10400d10181806038080500508041d50080c0c1c000d0360322001c21200051400c0c078903501034586440a440c1040302070080180c2c903400da40328400407040354011810119110b1240b080c0040a581d0f00040003d607a04042001d00242c2c2c4040782a951029041500d07921001c605880c207000a400801c003000a600d040341040b501310303401340159140150341c0e807080d6013550401c80c3d095860b44c100310301480402005100150044650644240c128244049441d54036076a02d8803890085034008045042507402c008074410300c42c3c2c0700030801100c2c58900c02403610b9240a580740c3c07002c64104900d2001c0813000740540e030b01c9041502d0f0002e003410403503100e48000300c4110303210342d40040540d0300110104051480010110f4038211000d651060041d9004083c00440c2d404646800c6c90045100300080444104000d07080c035901e00800c01100820701942140c401980c010840d118070086c02e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 293023111 1250 293021861 293021921
    0x316090b1509010e01030b0301110c0105070807020d0206070513051003060512120304080904060b0c070321080f0702031b061509010b1b0a080304060b03060a02040b0913 74
    0x3503400c1510070140c0c9000030005140c45014102100303002c100084240e61441d4803070350000365103001c0100007056200c01c0303680b0054141e107c004540001d9441c3c00c1080011608054403941144151004000d00c07180864004d403130742d102400c00300800c04002510404c0a4210342000003820006040082700340400101600500c024402d0a006184240b03103841d00b0308000c9100240402140340040c61039036550343d007186030f9210300c0c00e00da80140d6130340b00070030fa40a00b5009401d0b9940d007000200000350071400c0c1070881c92101074500c100511222408441e10fa84898540c3d0001c3c20081c00501c5ca841d510000e03401d41c06640302030480d03042c01488d2600e01b5100019003501400c500d0b41c0360902966841e091000e040030074000c040600400b00300380940d0f070b54079064074080d4000310001d80e00b03940090ba48c2c1340001c2d4001d032402da4001d0b07180c140040c0546428401d09400092544c3d08500d814900800400d450184402c0603220740310001c1820201842500031a015680c0280e085074000b04000403e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 293024361 1250 293023111 293023121
    0x51b03070302060f150415081906050604181b0305060703060e01092007170301090501090b030c010801051009050301090b100902040b12070e130221060906010509031609 74
    0x240c1c0184150f5010402018000352124000c541a8280b050740880305418000a801c408001000c003440204000480300c1c2c06000024420f04000554560900c90741401820b0b40c6010303010610643c81d1a041042c03084900029600d00340d44406c0c203010042030780c030480200107641d0340b002c2d0280c01040c0130044181da042d800320f004d440008404100590f290040c84085407070740d5a030b441e28001020296148030415a01805005110b5030410f48038200c00c8202816030b80007a40000f41240d12100184110020350055040d803c60a50050a44000240c0005d003464418441c1900400c0c0d01e80c43e00032002e108102c40c8010f000060000d20802e00700380b90079200d00c0e0007140d108200602c000004542d510580c02110b0171510980d07411030070306050038000707000d039074001e03151000384240003903007420030380721402c0e0400c05580c07035500140c0302d0710381121605e1185020b40310700d2032886201040111954441010981280081c68003d407284a14008a45024924542d001d4480b81c01c0c000020103280799004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 293025611 1250 293024361 293024363
    0x908090a0801021908010503070501080c1902030a0f0219110a05030609030711060f0d0b0406080115290d02180a0f141e190f0b0904050c0316030b01051b0307 69
    0x70119411150300b40c1151078420a00892342e15810181c0c08200a40c440c0b0181504170380b00f19407103480c001d80c401010400c1a4405e2031600580c001042c0e0440441d0000c130760110b06007490018001c0c010403006a01c03800449032000601481c1252a1400380f5150b0320034038070240901604035001400c08100c01c80d5241c0040504a0350f50541c0842030545013000c009446800c244c07043c4036420401d042e2445d9020b00b40000b841c0750080e60310840041c0c3e0082c00d000d070a050509000140048600f004400c4002e0354031410300400c10080802907080d09c0782c101b4112403000c4240b003801625110320f020001a290700d00d211040c3c3c41406100c0105c0c50841d080c249000320f41d00034240000c0d0076281d1003444840340654500d04075010b4150742c14403c2e401c04403444400790b01c0d110a840d50355626143d8502c0520746a406c18040c0d50f002140d46e003014207141c800e171600040c1640610b8158a000c2000f840c004280d0701052082546440340e01c0c1003640540199080741b0600100c3c051002042505a5520340142c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 293026861 1250 293025611 293025637
    0x60905090309130207051603060914070b040e0a11040e220305160c15050c12070c03081c020403061407180506311502060601020303010302040908090a080102 69
    0x404200500340c0001141c0d03400ca0042c20529185404092980081d0000c44080d2140c0c090340030051684249410344001942c070031400054160aa81403991011121541d1010f440d0b10424090000401d014240c2d4116080403000c41100d0389c4820b241406408100b070703088a207a60120340400c41201c3e032018076102d6015100030018640f0501d0f114600701c059210041c010030030400a0490384c0041402140680b13028460038444103645040301020601c540040100281010544208510703050121900000100340d60500b4a441f540303410486961610004140541c0090102403981c1c2900f02030400c800d009204540721540c0e0708100f400303004048075000070404102c3c005002d6901414070b44001032125041c1c41d507020300341414402c880d400005804038192403980c1011458080c00700301c1d0043c1380d511040c4601a840e01a0041c00700003500d0480003590492410016141da0001c2501c0c1140d404580100d201c640b181441c80c2c0342d00c601e20703c45801044660003c61400815001007111420340c00b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 293028111 1250 293026861 293026871
    0xc020309090108240403080c0a050705060c0a090e0105060a080612100906050c07050d05030c0d050412020c03151302011704050a02010905060a020c040b0301020921120412151503060609 81
    0x1300d88050341c280403100100450068404181c84940280c05850829080e00b882c40c60034400303071541403a203079048580c074044010016400c90b010398400c0d000c60080194103001410f43d4100400200301d80140c1c1c400030b04200710140050a5130341d4050890860b10708410648059000c080381260160440b004192202e82c20b00010a1450500c1c00450328010b8104000c1c0c01294016001126180d0010b84034070161003040c0000100d01d0120300c60940554031950942200e00c0c1c420001900748000604518441e80081070050412907a00da1510340c030082e409075003c4220020310043c0d90795801c421001100310011303c03c01040140c0050340e4141c0314000d0f01e4846010383d44d4020802c4500c144206d81005030406004403d41c1c3c00c0035003101018000080001d810326081d48046a070164450504903005951803014505140c014048000c81c0d01804048a1a00d0b013000042c01c83e442403804c008040e1881c002881d520590194441110840541d0059150716a80d0030100c02400040c0510b840e00b034605 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 293029361 1250 293028111 293028163
    0x80304080720030307320a060c0302120114030709021c06080106050a0b090a050301090503031f0614160506101e1a03130501050115020609070305030d0c020309090108 73
    0x1250074801c10a00103005502e0074000340d4034000441c2c014071035a80c1702880a1440300340c54116443c03200c8501b41702c1d0010300d036a82d09810907038117a81401d6001028944104518680f042caa44c0e503140c1911408040b80100c006014042403510035558000a00daa01c0455840d001251844629405045900c81400b034940c41c0c0b10407a00701c1d0074030700c19603502c4440740c1020410001041d0140010080007800d0604099448000c079080d14544801210320390000004c01c02d195400350071000c0d0340304d81d001c1121400c900b401c80252590a91801d1981805d03004a03540d5488680c1c820304800c0b141e40441034615905203d13001520340c205a006100d40e07801803001c04000c40303800c00c1c003801c1103810000001c080101c260f0b048201c1580003030800b1005640044035440860400d008413400bc03c03040c038800d42c40c0e84043c80000d0800b900500041d81030341001d141080810000002d8a880c18807a020000314020b40460aa103184140d80103503400280d03100000540c0c0402150384c4184888c007a440790500141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 293030611 1250 293029361 293029403
    0x4031b06030c02062503021e0c06100e0c070f020a0816120b0c0901050d0e1605100e090c07050f06181f0906090206030f1f03021e030106030803040807 66
    0x1103c80260440d41700742000030707014064030311003880002402c2c01403815911125108000d0012411001001c20009003150700f04010405140d0181d189550810311609000a1528951000d8441c040342c5a020400000344036081140e244081d1b0f00402c12150796039101051030301d801030092040c03e02c900303500e8001007000c0e40564240e1148ea01c010061031a5590f130180c0f05d42500025440c6041007001e00042252603440d1040d61030095110005042d02c1c607140880250042e1281c1001d4001d83d08900451101a001100d40034101402c542d980055074440e002c8007003e00681340c0107050391260101a035036107a0301044a80c012081580400c203681d00b100720640e078514155103415010a01407040380455070065000c0501d00744180c1e80419846201d0300051003030b4005032144641e032004401440907150003003420403540d00c0c800b00446c1050b0314680000b07240e400d1044111032030103600e800d1061591744c02e5220308003035540700500a40320b040500303008030305801030300d001c03500b002e4840355240303000340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 293031861 1250 293030611 293030623
    0x6050108010c05090415030206070b010e0c0903100f0b03190b07020a0c0e040602041a090109050306010f03080702180c0a0807080118090302010b0a06030c080a1109100504031b06030c02 81
    0x15440d2115464013941e0f806020082000c0c905035200d0954500000c00165952002440300718029101c032049035052500d001c4600c00c0251200302e4040040000c002140c44c00719002e2030f01c620080740042d01059515212000c1c2001e44d4146625004152010139149403902c10500c0c840c1c0a840d0880d0195680c0d00144d0755190015005440c000c00c80008001c10341c0c40c070b008240e00510424015003055603540d100136140e080514080790740071001c03403102810751340040c0440c02070104400400340ca500d8a50040010781e0580005400300d600043c600c020f5440d40a403041c02c0342e03007604244a180c0313400c6080d00d901c1d03000103503007c1c00580b8003070104c0c0300b41d441150168180d44817050709001e25030580407244018205100d0440955480e2072401d4202c0d501e560b40075006207896100803841d84030386500103000c0d100c0100b80c1d035285071401c0e1080341168550015a04061010343d40080c2c6d590107040166110f0090ba480207180701044049070050340d498a41b020300f00d45480d00c0500c0308400780d04040e07031030320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 293033111 1250 293031861 293031881
    0x120203061f0f08010b090603011505210108060a11040504020703030b0a0326070c05010804110d140d03060f170f0304090906050105120a1b05030a0f030e120c0402030c040b160605010801 81
    0x747d0244014031185400d5191039820700352038200545030850a140b05010310003020348140c500f030321080c0104002c03841400085c3d8082c00220040044d01d800d090405000e0280d40900ba0189901144140401d80079038040300c0d4a950052481c1400d5940b0314040442051917070701182c91a04107055401501060816101040c0d409941621401c3c10480115070082d00103106844d507003401c02c0c6512050302c5401c5440d10140c024a00000c41c005d803d0035042c40d1440e60ba80030001c0502c1c0c000100020300014065030181c1301011320304440304440510062508602440704030070360000080c0020780402e43d502000401d480f41c041441140e903190b003001505500700c3e24041c51904107001480c0001c24150a5948044031100f40d6080c06803a0800710b1700e02243e441d422079000c803070305680d0b06c2450b0300a000260420340444526031528560304a05466015580036280565004004164482003250696014065040314243c403880e2203003083e80d40f800c04450940340b0310b180400104560a06019044e100c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 293034361 1250 293033111 293033119
    0xa1208070f022b050613050c060f131415030402030a0303050a02270f03070b040312050d020d020a080702060c070b09190c091a01120203061f0f08010b09 67
    0xd41503880794600d4000041d0103ea0040c01c1114103030031031180e0f68000000e4420420601224001c9140180c0380c1040900900c001e0088003005100244000a00d5400c0880980c1e010f9118802840410701d107000d00d82119004010390900401d800c50003450b043c445600840d102c0c00f00002541c9551418072090b00c01a42541008a52102080c00ba401540c0c014541c003000628200c07030030040c08c03412041d00341e07510201404080315190707901c4e0072241c28600d400c084001c0c2240a161022000c00f91133248002404d5104100138400014010b0040c1e80760090103010955440c404000810000d41c41031550f0000324010101242c101031001400c24807401e08034000c00d00d043d009845043c5242001052010705103d00503c003004540c50014840c603803842004140d41090a00c0920410f43e40c1041131071244003204080c200d210380e80110700d0000d46d02c80c40e10040c0d1306d440e040042442000d140c1c1c0d80e105004004070361083c0581e445210301812600540e26140d080c1d807540c03110803192058007120350348 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 293035611 1250 293034361 293034367
    0x603060608011e090e0a02040515010507150b0d08070212060c03061302040302040609020c1005060904030c030309020d050601090e0604021003240906030213020313030e030309090a05060a1208 84
    0x904a40b040c203c5603a8625245400f0440e40da80503110660300c0c6401a1507040d00241c620608604240c0038003a04001030b204141000e031602c0c0b000a11034010460017a2940290551080000a07a54014110124082c001c500012401d00300601c0941c4505c9080f03001e2414090a420008404101030307008004505505185481d1902000002e04405a10b000055404c01c0000f0040e0f03034512548008040a0002685544265030b07032034108105600c40380301e041d0030b00303041115aa840b2500103500562508001c8900f0b030030390804a0080c41d04400c020341100242c3e41d000203104001034014100c0b11019424440e03910f981e00095110141524002d400c040342082640300346019800096142c00c004084a484143c20000e90300c041c0c100d94060b000301c50b41d43c6424000d50a06000303010030b41941403000c2d881d508141146401f149903581c0c0250811003040c0e071858455805204807040002e000741201c55500703007442079400500c001d0b14400e00c0f03803006002c0028002100014881c444e9080165282 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 293036861 1250 293035611 293035619
    0xb15010507050a051e012f0d1505120a0b0118061d090c010309030c0b09032505071a030610020f0109060209091302031203060d02041805060c040503281a040309060306060801 76
    0xd40001c0b81d40f040b11464084c48a40c404241c1841509c659520800d4520445440c29081c0b1144110100891400c1e4006818503000309040034081411603818400400003d02d0101e08a001064640c205258090030b0710b949036515940050b5081c02481d01c403040e1940c1c03a07030403001036040b1059550014041403c0e58000000300c1d00729921107500081150603245440040c080300344801c203d40820340c40c440a00c0300c2c40300600c00c0c20003000707014101c20f8100d000c00c12020624007095000043c149031141c0c1740342c103940103030368800d000001131346000000a004021103440d00340c01a41101901ba805075408a002850303039950050000010b07a0080c0c0500301c28071000351560344039400207015582001c0c0000000700141c0300c07885074900d0490110041c245418241c500b80c0c2c02d085010703120220b018001d00c424889a5800310ba4405800780f07609000e041d0310f06500c500464514491406000345140f100c0b05192080c224000034403861181c4d552000c0f4a445030800e03420ad9405014880020303a0180040c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 293038111 1250 293036861 293036921
    0xa020307021905150103050609010e0c060702130b04020a030f0b030712030f020f060106030603030f020604150c020c06070b10090c0804020904050a050f0d0e0d0b15010507050a051e01 80
    0xc0d00c902c1c003e400740c4800036100281040c03588030a07031044506500040c01c05c104004c003803082138408110b070805070042444520009000c2e00410030083e2084202c0c107000b140301c1d0079a13031041c1c85442c8003030800c1d5160b620340704002d0700901120300070500c1d42e414011411450300d00442c40d00140c41d2501850304105c0c4807900d084440c003030441d098030150b2190b4cd6500500b00c3d020031840d4003c08441d1342c040b5171070b8118034000b04280c0102c211103066501c52001c4c000002c49034003400f00c1008002000080100503842d08070318092111007400d40145c3d000406006200700040240c1c442c0c0035910b0b160069598034400003085960b1083c8080c00030b6010740c0802c00602e4002221074202c1d015400f11010100d0b191104c07401c2c0200349018107116448200c11003115038010013090041d060446000c1490b40d07103900c910101000040604208042c44842c01460341e000b5030545544c076403c502141c241c900c0c24a021917907241a41000341e15801030b23100300c0d0b03081c06c014050f60041462a07003031039031a02c103502c50751 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 293039361 1250 293038111 293038153
    0x7032d060e1b090a0305010623030a02090105060d02040506040f1d130b041514070801080c0102030712020a12030e0601050d02100807030f0e010b0909010e0d0f09030c0b0a03050a02030702 82
    0x1544d025950f04070000204209000b05409806d02c582c161f0030201c02110031781c0007801d000100310700a82004550303e02503920341d0300a40c1144d0042e580c040e5500f5140310280028840d9811103907111b50302082c00b040c2c8100da10599001c2e104010303000c800728043e451020f00d5043c0b0440d5910400030380800208001a91541c1040e00148907141c4094001c0d120a41c440030b46000f0500d4040c0241d00c48200030043c0d900c644040d00415008001d401440c612900003501c910800401824207443c030705400014034400c0200045264116000304000c80060b240107000d48100c102d890b0b2239205100001c20030349450b4940d0036049900070051100b40d01128000d0760101401080072040c1940e691500302082200c1c01503a8074124503900000c0c24480c1081001013281e00a44076520980c54080350082d0740d00c0024400c60103c0c071500f0020205407407141c04486460a03500000c0c0707080113241c80040e007404504040d16100403151021302c415a11020b142c42280030032248030380140e2101070541040404001a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 293040611 1250 293039361 293039377
    0xc080f010b161e0b0612030703030b0d080304080406030f060b0d0e2a0102060a1a010815040f0b130b060301140109050a0b03070809010b09060907032d060e1b 69
    0x499003020b41c0d032503003a401d0500104801010107411030081c108108680100da10100c04c0b07840040382a180c0c5000c170354034081c0903001030616582e280030007480e580e070102074803d140c4c0c040d01807503030f03403030149803034a410b404c184aa500170900340301203a1412140b40c02400300b56013109000c0d60a012000d001350340a055460100c00c5607010b03a0042210744800d00702a00120701e10700c1140944e0100078800245072103001080f1920542c174000410b490300f06108900700c00700100b4604078031107444a210260768103c6c441ca0300f41d4024540040c2201d410003641054545c0c10040300d100c159101c08403404029114461300260340040104010b1001c10700b0500905003028042c941011031a4030f03080031403d1301d001500615501b62000c81004550b03a480303011240d1042c1c40e5002401002c5501c4081007402c0302c0584840c0c400c12075600000c090701d211360300c460f105540704020751183e40d0101c507180840c842c00c90b00c14489541008404205100708116103401260080704000040c44580030030000c4c0d801c0301390 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 293041861 1250 293040611 293040637
    0x10f0b1801142205100617190b2209061a180c040902070804030606050a150509120313060e0d0510020703020a0813060806090403051c200309010c080f010b 68
    0x100e443c0c00d404034415140300d409001c184025a500785480501801070328444003402000300420041805600721894204004030350001c91107080820000c5d04a0b000700c030040c990020030080baa540c03401c1c2c50304444040c50250204100520f1070500e0542039039600c070221904803084510119080405ca400340341d01c010003085003410151902c9070401a80d011540a8644c1100410700744240403080c8203285c02443c00312103185000740f4042c601079111101029000a0000200b0380c842541c99030401e103940c2c46110800d0b29901c100d101e0044030b500c0181d020310b00009195080c141c036a410040b180400342c0b90020002c21101141300c040002960101c1421801c50080d00c400d007001902c04030180480034805814004a103080c113034000e000c1400103100790701c81e000d82024000866007200403691613020115a800180600d03c0a0300c004d860700b043d0f403904400b044a2800d09800f05a000b45004841c030f80000d0003181e507462400c071550300e0251600d441c4581031000410004072450b000340300d8880010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 293043111 1250 293041861 293041909
    0x61d0406050a12150e1c030f0203010308030411030c13180f0c080606040204030f060c0309140d08150906060a172502010606051803070503010f0b180114 67
    0xd00442d600c10007a620011100c01e88090220411030710841c841d03400d44000404010220340107260315a102d411112284030300c6507824010b090b0314404e401c9020405c2c1904025541c950f504c0c9440c00c030960040b24250f482d00da1020440c501490007060780401803100400030a1410401d00040c0014070a20001e80100031203034180300300280c114a171200c0d110703004110f2141e10ba460701c0c004031300b4141d004150751300c00c5104010900001e007074110702001c0c20360400700005200f00300348015001424a07410107070085070b060301407030021200007506042142041c0d82c0d5282607242c1080380c1c100314041052041e4003141d034500058181c01c040024001c00c0c4904d1801c0c910003200f400f010f2888100940b400d821420100f0402144240812118903070001c1d42e1000300075492800074020320700d0040c0710040350742068078100030007070740c1e070401080024245c028000c100c204e448401c40c0004201d11181d06010b880c0c244d21071006000c4502074141214080c603110b6010200d08410400300c601c401c5040f40301d01d01e4031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 293044361 1250 293043111 293043119
    0x207080114010806010b0a09151209060b0f01321605011d030c10150b03010803040303080105030a1205030604060e0403021f021c090821060910061d0406 67
    0x340610040061481d0a0300c07401d50510f09102d09125058201c11500d00040208400311540560203c0440341000f54030002d0410b041411106141c90780e403555186ca0a140001c8148411361b80a251002421507159000e442a60010b540500701c00d0800c41c02c07041c50503a0841180360700340d01004125103861401386442290038184c29600350300602a5000d0b9500c4481e00cbe0009145580040700e00d204500542c2405a0080925a51218400c06020703054403598140241c50550042c03002a12540301c00f5512980c681191643e03d8001d8441900010942c0000143e9800e02040f0b0301d021036040300381320360640340e403010070745940d400035084540059494100140f8035041c80c10080c0114441d038091312030321403404801080d4170304031501c611115104000300050223420340000710181e0186140070400054a05000a030350003610805030b4441388ac5905050b584419401240c829801154405040d1700d51079645e45198015000e040013003001c100148241d58150070b0301c42014240100045a59511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 293045611 1250 293044361 293044363
    0x2070e090c060c0607020c0108090309100203040503030711031b030d050306010c0210030507080a02190809070f0e010602071203050d020d0e030a0f022a01080a020c010204030c21080d0c020708 84
    0x10f002803400d513070802414086031076410b01c00c1d2886a8024a849001800c00c904410348a01c0303040c82c194444c02b00b412801600c3c9000340192002000000c040d6920744074582040c803003200b16003046038828015036800090907589085407502d8248050014440140444010354544d40040e0400f414010741e4144400140d65031000c0e2000d4210a81c3e02103003505080401504e080c1000d0035500e0603600502c101816025800301c4d0005040032032400c1c20a5840d0042e11034107014090700030b65001c80c40444041703005181000304504070382c2c0b1031b4200c0c0c2d051552a020548515603008000f0002802005142c451403419000340c402c1c0d451051000945520401189255500c00312152000c00c2940071020b00640e010702ca0301501041c04411403200e208211508000700805040b0759042c89400300204030708040e643d0603640c4110910000f195115141d09000c1e2200d05944541100e61107000e060001540d051803441f801c00790311148480c2000207281c4c45102410f49502d0800841c410300c00c0005050304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 293046861 1250 293045611 293045617
    0x110307030306090f05160c030309020303030106020607090801020c12031503012c010603050c0907021005010f030210110d0f1202130306060503060702032203050d020f0c010e0102070e090c06 83
    0xc82610000341c91460708007603a0548600d9a21825490318110030004200382c0905070a6000d000c80c900348481c004146001c0c2c00170030800d1806509403001200200780c0cad54000402a000301a80e444081c0f129030b4820b440c030f00740c0c4a1102d684031281c0101d000c1e10410b110a43c0035513040505034201c4810141c40c000400d007158004c02843c0302040c046900c00114000c06050b0101040c84075000788000b80c11502e0301659000214a058002e8030200002010749100b0301c07410100381c500640500c200e5a5405905200c81124002a4490845410070008541c060709005507480ca42d07401030030400400c99816504078514003030020900c520b284945100c888a031000b001d0100c0d485186850850071418980102c80c0d25410850007603100d007090103085a00041a03e508104411003d22503204030790039140c00e0f5009500050440c440c03000110030b41600800c5400c80b01c410301045520244480d40112088180d100c0d80d039016070080c003014400d6810203094140d1018503c000c4400b14440440840c06a038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 293048111 1250 293046861 293046863
    0x307030501050f180103020f06070203030a030c08070827072711070c0b0903150103140c04110a0809190c031203140a0f0605030f030706110a0f0f110307 67
    0x40e9885005000c40c0c036241c2c0b00c00c00c9414080d01c403500c16150780d0341c880c040000c040c0000f81c407a00c0c82d4000141c0907900c20045a59555000e401d13203403507040f0203001030040c2802e10f0901c00411405c0000554843c41400700314858040200c14044d4583d501c1001482280080c2e15485540180c03940481ca9002d0686a00382c25032200080c01c900c2c0200c043c256085905101c6403032244042000203038007141c0040352400a40300c80d02203040d40c4208840010f4034000b400050044404000e500000c1407084008120341c207c00c040d002e403610324030301904000442c0c3e000503d4945201081c40b040c4007492040b450380d6484421102200c215100038071445505411400c02200e403080400820301c00c100110b10302800d19680e50034144400c640064407427400400041040e031901e61346031842c244840f00c64105100801c4081e05441d24120004500c42c0c03240e00c01c680c150b43c218140049034014440000858046140b241c1c1e4081d45280f200604a8a015101d9401c00421008144101500c03400b40001c0140c0d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 293049361 1250 293048111 293048117
    0xa03020c01091209060909060e01180603050d0305011409060a09021c05100303020d020312150415030b0615090f011b0b0f010f060f090306020a2d080c3a020307 70
    0x6203141880080170000f1035040403000c08e0428000700300d4a040c0600d41c5064401c40341c921814001c42c045610010000d5900c0a0200d2260580b46070042c0c0d00750b40181d040e0307a01001d03c6410f0030101014020041030664919411080320301d001c00c4000700680c060254018000c25030903171040b2000404098420585102a120310f07111810400c042c1c0400031240c01c084140003440c00d002d407040640501460041c2064640c00c5035043c10f0b4031580e1340340c2c044401c2248505519a015480382030820884400b00c4250340110004c000e0801142c0420003550100e0b00000c2c9180c1c101400342004680c0940144400555072554607098000a05a0454a0701c6000b0003c825045503160491008401d2096400801803000e0140c2d00c840c01940045a0016030b070f08520f0150f07451030f04110444100c100503488500640038800c03240b10000304007034000a003c1c044e0b922140113440c1c104060303c0e940318848021070301c500b0000710781800140703890a415100b030340303440546428903c0b03050000590780201c1d024000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 293050611 1250 293049361 293049377
    0x819110a081305130209101b0b0601050408011d0d030614060d090b090303060301050109060608130305041a040503010e0313090509030904050412030c1b1401060308190f0c080a03020c010912 83
    0x70387e0805078403060178581c6510340840d8102c500c1c00b248091891003400900710144540001c0d956900610840f07008010304402042809d075000104c0400c643c054408104a0089006000c1c02d07910a0003282c00361a2052105441030744c080301040010f0340450411485d1945481d5220003192102ca0850300c24640c18015503568a8820704250071104140c00c140041403038180c0922082c0c0d4801e07107003540007003000b9041e4055116800d09490318000e95204a145040c26844440c02d8081c00c070181044031010b400910480c410500b0702c9459000d00024205c0c0d5807880d5004200d1304160750429504550608207503468040d0540105045d80d0085805440032080104650641340c0c1c14030594450200b10702c0d101282203081c140c481074105014801038482c50f0b4600c031641e030102d400c0d40404021903024032030342e540301c018400710360103920300c0b46546010660700c0544400c03413400b8400a50b003d40d0300558184c5440b40f109001c1d4002e401080f241903071590384010f00c0e030005049401c44010750845880c0c1141c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 293051861 1250 293050611 293050627
    0xf010e150411091f0e0f070e03010e120a02011104050f010507032c03060702012a0905130c08090609030a030e010b13020c0d0201020c060a0b011106040819110a0813051302 75
    0x71a021a175440101a5442c4000700303d0395541c0441525000101403601e480f441c564040000d015010034201029107020705004003107040b020790024900f00415030003d00c400c1901040001d48c1d070190348602a04080102b1241007103600c00c00080c021244203062408410a404114031140b0741c035004410f00001c0443d015509500e0100a2a40d1003213a9100a001441d44020594140745101d5001c2001401c0c00200c000c65a001c1c244400241501800f029a0310b0044243c10000d483d40c046c0c268003003419400442c180300c1004c5031244c411111040114a44040000c04400130400c09039030502c555600e0040119a540d100704040148801e80005612804003290040c00c01103008036030070640e8810845402c821034045000c591190020b20700054081158005079030140c410360100b00c450250000b007100b0803841da00a040d0b1001c602c480c00150140d012400d681e203d0740ca5148281e20f5002e0000c4c6070000d00003c008002074048001d403038101ca566000410b02030000c855400c41c00d00d80100f100301c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 293053111 1250 293051861 293051911
    0x1030c031b2f0127020a0302061606051e070c2a0b18040c020106050d0f060209030303040303060305010c0807020604060507091805040515430807020f010e15041109 72
    0x1084441e8010340c84844c04594001000ca1030148002800f030540805d2841e030710740d4466000301000f50440004d01552a0903a100f82c1c131810340300301040c6189080804a4801c0e48200e5100c28960303072204240c41d00076002d00c1c250b04440180400c241c407510703c008011072000d8134140905a090301c603034600c285031112a01004140c07100c0300000c9085a160174410001c50740d4849115646c1500820000302c101201d0400c0c3c7c001e4800d4088864042c0310010510003055803590001d0700316400707a002048410046041240c4010058415200503400000403030082202a0f110f1500079041d0304110044960700c00e6038400401d07815044103180f950791010841401828022041015040710012180d440d00303800c0c0c0c02c0d610485450030914021a1982c0842440b8160f46203104c0d041c1d00c4001c01039840fa0341400400103141202e07444018040c04181f85450001406401404051030028000c0e010074030050f0021a0b100905c162607120f60841c46000688800c0811401154142108615000f22610305 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 293054361 1250 293053111 293053151
    0x90e0606010909050621030d050c0c151311040b1020010203161110021b0f0d020304050f06120405030406020706020a020f04050705130e0601030c031b2f01 68
    0x2c04842c3d401c1c941040752a540320f000d602a84014800502c52181d50103038400e1560080f0b0301d840d000d040c0350a0078001c100c21072902502811040386d084031112407180d41c06c218400c00980d0300d0f002c5c0d0926203407910006604403240c10382105020308009051225603000520180300001072001007160801c40e400d26a000031038000700f440680000f036107582068615850442c43c1d4602060800c00200521359603441c0c180a54240401c2c1c040055480e20054031001e910b42c00b941082200602c030300b60055030010004900764100ba0f16a401031410301c1d14081c180304190002020259002c042042600f105042c039010190185005600940c0c032182030010280c5044900c4c0c20100943d80441c0c81000180d841c41d0707030a00c1d446820342d808201c0c0c0c0c4a80000380e445008004d0500c2040c4000407001c17540e0f1004000c01481200c099070140100b16031102e0a504079402000c1d0700702600d00ca6404141c030307503000c0d0b543c00c2d1041d0100300c0440346050030001c5911031a004404500c0c8140d45424040d05098050703011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 293055611 1250 293054361 293054369
    0xb04060218030a050d180f030501020a0e0f0f04020a020c090a020301032904170702060a0c0507060c0b011505210103030e06040803090d0c1203020102131a0403080d06090e06060109 79
    0x40403c9012074448a40e00c03041414480b040021b038100152103244107042c0b800040641c410030400c55901d80c03820b075010750488c6009400041c20202003400350f20706000d02005105001d044150031100c0401448080e512034980402503105840002055451307440c51948540304000340180c49504600e00194100207502403000038a810302c5911f551803100c0c0e56910780007540303c004801c9800388440c101c2c0090142c400060343c00400841d405041540061081c40090301c00c000380e0701d15686600c0240e6042106c918082c210305010300050020904981c41c4604040761410700c581001a03280d06840c4444407100d0b110158002c0d840108205500b00b03100503240c1400710740f80b031706040c203000c4d8a0741c0d280141c1104a118001ca540d600d41440b452011440c06094600107081100c00c0a0134007a020358000003403c03900105c43c0100007003280c21601822080609007c6441c40c003071860721750103082d4010a00c409409a43c6000c00280309525229031015041400040d02640c501030001428108440d0700c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 293056861 1250 293055611 293055613
    0x60f0e0405010c020c130504020d02061207080a021e160602031006080c0f070f020a03231b0607030c030509060a0906030e0f120d02120106020729030613090b0406021803 74
    0x26042c000ea071b481d0310340e2040f902407210000641d42d69170300024880320500d035000394101c04c00186d640b20001d80740074903034850740140c0c842d40c1c480c0d201d02480c103040f4810f2940e000074001080a01281d03803203650300140030305030ba6030201c4440c0004030707120a8121380c400e46a60111404040040103882d4002d044143d10002c540c0390242825082d1b84550414894030000609044d9003400c1c1d80110341d2001d03803080203907801210180300c0880034245044d9071111110034040398030400301e10321884481210200000a4050096400c3c1112a03a05507103610191a040f81442030620041007030b521194058403800d540c81d0780b02425249404c42c060b01300e030120000143d940e0062000401c000000003484400d03046261450340c1d41d6a18031100c50020702650702d15010f6134500d0000050881c0d0b002440c134043c1c84520320410b41782030700e02541c030100c0b000e013445c0d1420220341440003640034070f056602d802000103000740108481185a07601c65449204030303022654a40c0c042810315180c030000c20415841d00c4190 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 293058111 1250 293056861 293056873
    0x190509070903150c0c0b070c050604061d0705031c020a14100b0103091205030a0e0102070501150605040e070509010314040f061109130f0b120307020112020405060901030f060f0e0405010c02 83
    0x800700170420b0903079510107060f02c90315001007020948655615085640c0000a80b14281824030b007000c0944643c04400803040c040c28401c40d24044007044c0202110001402070011140c034401c83c1240304001d4030b584003940505c0c800800807825049041007141c80c210094002d00481000345400ca9451680c4181014030b00040040080e070100031128203076005042040c1c5030b90b214200301000e4141d90042442550012031124100041508145502d20b84a144200d090381c44443c111401c1c00365100c0e01c503112440c80042158a4001c100424000c1d1040c54045481a411455554081c1003541c0848075030040500000a1016070700c0b07904507545d20841e19514182035003002989402544200c4410182c0d1070601d030310214545c0c0d00510701c03010003900c0801044901c200c1242ca9802000c42039000c0390007450202e03208012417080b20b00756940140094100400c1c500110010601140200c2c40b0039a2400b001c10b150701c0c50312841c402004180903c100f1460a441c00c1800e4070700841c0d21100390750000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 293059361 1250 293058111 293058131
    0xf060f03100f0f091109190612022e0e0303121807150c0201031a04060f090e011b0c0f050708160902040f050d0c09050f04020103050f060f19050907090315 68
    0x5c42c03072080c000380129000d6015455904205443d0303044081c1c7c03801260310f401800550200c1080c0c60000f41030003241c0c0340c0403c2108900c1d0640c0c01e2001104050911304031480404010700840b04030100c4940501141c0c02c003003900030003003201d45003502c4010301c080302e0f40351011054000b0040d20b006050111040f41188068400181100301400c7c4007d041c0350311000c080c2603010304401c4103810f0400041080c04499030312a03074500d00e40c2050040c141c0c41c0c0e003802d500ca0000c16050140c1000031036a207400d150f00354541e04045508a103070a0b411984c681d030500041e8007081080041c4c3d009400c1140140c40742203c50107924110081c40d51096003403a005103c1008440c010302070200440e0004c0d540744100e1485c0d841c2c11008100b0903044840313174500d40030600008013546641c89119034400c1c3c808100c280ca07a00c0450214003000c903240ca80c00300b40e102040b0b9090900c0303c0f8a007031242d01d0081402180c0d88401c00a440d01004581c1d0400141c551101002400b0054451031a07072074846008100010351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 293060611 1250 293059361 293059373
    0x90e0403030f090639110a0c0e0405070e010b12041406010305010b0a0f18090201050c03040e01030b011202100e040b1206070801061806140d09060902030705060405090f060f03100f0f09 81
    0x14150305d035000e00c5100700c054002c902d418080001c503603500c01041a02e542d1103603016641c105040d00c051f6020300c940c0001003452891100d03c20f040e0380901c41c04070f00340746e140c10074a059000d00038800c5400410383c2440f1301104604020440c041c6200d140080b408040010922403d0f14895200180720903c0480402c0491800c4944c69503600c488400440e1b504400d00040c1d419100c0c0441034107907440009400140391840c170031050b060342d22401d100043c40e641c45000c40b44481030a103019510003124040804140d0140307151040c105000f510115201825000051b00c3c101d1101c842281c0307801140030018030540c41804540506103d04000f41004014aa48403c0e00b06030300802b018020203660070790086420301b0903120420903402d404e000c1c06a01d4940603000d80031105041340640700e4181c02007603c1c0ba05405980070340d18054811080d030b80d02d517034803040702c40d00c040e101642000f01441c50404a442c18400700c0c0e950110041d001c1085600721680300c00702d50b401c8503860b4906180800380000160 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 293061861 1250 293060611 293060711
    0x13091a0f040c05090915120c091308090f12010c020f160317070204110301090f0b0105190e040902060307020f07060e090f040501060e01140f0907090e0403030f0906 72
    0x41903030001c420b0b59071b4052454070140c030076407180d80c0310030b0800052095401c0020818480041556140700503102d2142c1e070541e01000c0d40d030007001c03003006010050407414069514211498024040c2210341c5000d0050743c21140084150001a0081185d5400030b140400042000050135401803180b20300e5511840b00c0e035800c0c0c1e0b51504a8001c000307503220170f642c2ea03034120001c08109046034559a5940303c1701e040003080c0729909025020304064200c0829805101602d00c10920018080b81c000f900741c1c0b0443e081d43c0c1e070491b0280e203e640e031086400907899a0010350b118058a030000c0c008092000300c1c113031500310b569000c0e00420a042180c0030f41600d4401d2490f4000c24043d28601854580b407a24501404e201d0b0007032407038000d104000180716800c14501c1c3d42400415602402c441c80c105051000441c4101c0c0e00e44041a44d1103010000c070203220580e258400e001c2d1500003030080c0d10b1200441510f0320300b4410354406845544062902d51844402c45070041040707003044d001000c501225403420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 293063111 1250 293061861 293061877
    0x307050309030702061602010206060103110301050d020102030d020a091e050607020625080901143c2109061308030703060b04080102030108010513051213091a0f040c05 74
    0x50200c0810125072041040d80c901d6030340281004d0b11054020110344c403002c3c150703d0690051040c0f0f000b01303841754007a20400380340d42d0300c81c61400d2841c3e0030807052202440c1e0b503001c100c9c1140300030894200f40550314070140c40500c00585d5045c0f113503481d10008101d0340d80001c070481c803000c00d5100200070680e03469080360403160341a03424540382c40c1050060201c11754003984100071800d90000e15020040000006c0440d4a4240c881d0170320751032052420111401890325a5550802c0d60664a000344507030014400c1d001000070003401007030844c1e090080306d40c000c000202215007180b41c50185114078422080c2c0d0003d03181d0000c001d0791034202d510f01c150f0212440c2c06841d0500010118000c9032180c1c0241000e00030120301c06036110364640e1020b000354024801c0d410725502e054089843e21207110214041d558000c0300901281c01d250b5000c135040c0d88801c4100315421002040041c0800c180d008544240d00c03410054407445403104203025070340f010007a52611489c581039103801d90035045070980e8041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 293064361 1250 293063111 293063117
    0x70f050a08010e07171801110903070b0c031e040602010f0506030c010e04060b16020a170607030e010228020705062505030909130606050a180507090902040803071a06060307 76
    0x940c84002c4150b1706409840782da0001040da401c1045080e4010f0703d814800e820742d0000801c10400304503142d0605020340703181e50358182c02001b010040717042420040c0c000b504503842900c2ca00070b03207240c2030540c59501c0300e815644444041410046590203218681640d2050b200501c42850302d400001e442d000b0b1143d845041c816403d41881c0261959407016020b05402c00c4600d90303890030b4a040e0342d5081c880501c201e2161802041c080f43c407040d4214401a103511140040c84540c51f1540d040d0003500110488030380c0c565003440a0103e50080b581d0f02800c8100c1009900c44003428003000900700f13500382e0080da00546082041100480c0385e854a40340c1e4000307250841c2d651100602c0c0c224203510565900a074042c00d003d0a11010362100070202c07103402d200c1c40081003880e9440003480b144c510725100700780c1940091000c41048440c95005164440c0072440c0c00d0840750780f2139204d0070898000390002c1d41c0782e51000c02c600c020414005109180100c40400e518218078119002480610000b0444410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 293065611 1250 293064361 293064389
    0x405040203090a020a08010603110a0f03021309020a0f051f0e040c02010e01020d0b03190807062408071d040c0311030307150c08010b12070813051203070f050a0801 72
    0xa2190500c5100f002c0c5500604031340130b2603960700f0b40358060b014500080d20202c07001803d113803052510551074030440d1022030001c042540346800b00300c40409543d0382c42c600f19850344400700042e59243c0c00034014040c44401103008074202401d005044940e500c026050a4041000d42411f1303422001c00c140211007100c1c040340c1c1081846c4101d000d42043c0b1580c280c19070000c42c0d844204401900301d9030000c3c10a601720b481d002c199400070b840c240c407014400380c00c0c0038042101102050f07042e0000f00c1500d60003020609540e100020492034110240d202c2c101e03541000006000c501c0510031a0310385003600603071070031241c00e00e42c440300c010782e0f110b1000611003258007400341a15102407060742c8405402ca00c0720101200b2901a54002d0144035030400d00003003043d0008158110707000160783d00072920245140107a92094402e50350000060700c0000c01802c0b60060b01c001803c100203580d500060072217410b4a0b81807010380070705101d4200b514202402000d100b5098000c2d0b2100f10306046618582035203207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 293066861 1250 293065611 293065621
    0x702030a0b0703090b090a26300f090c04090b130606230102011b0509040506061e0909070804170306060912030c1515060906160302070e06030105010b0405040203 71
    0xc001c0880c00d6000304101312179420000c001101052007011540902c01954011125500b92034038441c1c00b070300c1d00007007010500c00d03c0c000c00c207425205483d25042a005402441e000c006202e00c050040700d06501074446001003243c21403042c41680c070000802da40500c005003050791180c8103407000809668800c940d0589050512086800480041441c075224210480c0281b00055070b40100b880114059801c0c050810080003240050138000c40c208e40d500c0d400c200e190010000034003406041680e01100920070b0070342038140d9040b462020f604420f005641c0b007404030188a4900002040c003c20f01542a08201c00b01e00c1d614000e0303481020107003009907a5954440041d60a002d0309580c00c0d04100c03a00303030103041110004002d21035603109104039005170441c0d00904040300401c545940030701c0060500000749080502c007510210f00c00400c020b0410302e41d01c1d806054800e0100e03040d0010b0b03000000400450b181c89d2211900640150020322080d070404103051100d00c41c9104440c0240e500000041e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 293068111 1250 293066861 293066867
    0x30a0f05100b210c12091923160914070206070503090708070f0608100305030f07030203070213020702090106020a0f1101020f0d09300b061809030706050c0702030a0b07 74
    0x710725100e8020204929081408407413146400207981d01e0020040c2c1000b2580340d11001030001c812002e20314021842e08100c1e41e81c583c1e890514800350084407000c480d20200d0850a0012016441c0400d0b0f18594032840d21045000341c03560081d50306960b14408050004655020078139652018040c102b4565030780b03d0000b41860300d9250392006105004104011520224441500b800c4500e907a503009070545804144890601591100030010780c001c00030280c050001c10041c10015020340141c07030900180b03801040e075890f090412524003a0b400a00e030320452070590785d01d40c0940641d01c000e1005c0f140c10b541e816000030340f1010140203e009180c80149030780c820880b2880d04800d40040d16140340d402c007005040c0340388501413600d1080301e220140302402d658001d00d0610616884a041c40179000b44c0303919914480180c4069000100001e41040034000350742100c3c060742c0450015580d810107418908121031001e440710b907042c0400c00c944001741c0e03400074030004070580150600d219510342d00416 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 293069361 1250 293068111 293068147
    0x20d02010b0a03122304030602070309051002070306050709091a040c090311040203061512010503070611031909030c03080406020601090b0f0f03100606030504020a06050a080a18080708030a0f05100b 87
    0xd45c030b40010700030081004c20b4010f030040c10300c2511000e824544400070840300d5001c0005d07440040e40f2203401040820030940201e6089156030900c0b80c82281c80e6140801030740c03000f90001c000358502c03818451070380c203280c8507030b00c021403c62030600909411079548005c412219140303d0b201c0d54021010480554584400300d00984031402c1403076440524501200c100c1d00c09100d11440303030282d110002640c41c01000108a0a51160040d51a150120300190080045540580e0810105100100010f0103000e41c920185002d800707600d488503d0304100a00e0300c1416000b0300031540c184043ea40c401e44943c4e4042d510200215101010800b0702d00100e0b180c0560051600040d50903c00c00040b0190143e200c00d01403802a104040c0680e121481a43c0310300c1104984400a16013170001100d4084503444039116001d00c43c0d0180c600c00b815141c4448d1a008501c00380d4002c40c000003070001440c407074401d03090170004500080c02149841d102a0b0700b080c00e00e00c81c3c030b45c900600080c0e6070102500c0310303c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 293070611 1250 293069361 293069417
    0x9010608030a1d10030f0507050414062d0c010515060a0507060b090a0605090105030307050303060d15050f180106030201050904110408070e1b0c060403050c03070c06020d02010b0a0312 81
    0x806001e0703414104d0001c3c00703000b4403138900b50b6081c03611000c42c1b0454865811541a100080142071a90450314140f00403a070001a286540750100101c0b0b103030b00014403059600c40c0c0b2a030070003070381c441c00c9040000742154000b42c10010f000640340607007580740e00c0d080140c41401e855420043e0b1100898100031024003250258943d1200071442082140c5901e540318000f512425551102a603072114149a500d20500b80e001d8420350003813000641d42d2802151501500f4031032946075985014050341181942c4080da043d2a0540c50381040120f00556650010b032035001441c0280b02051540d0006415441381021140c011510b494104e148200940d084800400400c1c003140c2a042d45c400c100b41882c081a01c0700740604c0c03070050b520942100000e05032132800300c05101a10340da40b40c1c0c0e9025200b9034442000081240001e015080100380d680800d48000e15080d0050101c150305114028211024000c1c0d241c80f83c24140e0090020501c02d0314111070380c80550a2000c4540034003c0b55050007031420f40c5d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 293071861 1250 293070611 293070619
    0x20102071211030a0309210c0e0910020721020d14030a090203071e1e180902060c0c090c0a0e12070e09010b1507020d030f23070b09010608030a1d 64
    0x4c183d010154404418011110840f00e0191151003210700112600880b14014011034085101804070941c0d141d8a141c0041e144000c44000b9034944001c00700ba41c1150800352050f9404408071f4000080403419031921034107920103003820b01c00d04030300540b10151141030705a0100d004000502c810b1403d5200da40c200e42c008045801d4150fa40b008030012070580802031030500794000001400204541040001c1c0c2c072880c3c0b15040072420101140e85800414010b8032401e40c0322103102d005600e481c4010041021048d0141c6140c8000f4001e0240020018001c800e00700001c0161008095211680701c40f4a041280c22031540b806140105150410b150051243c0584407403e1240d1034005501c2081074000c1901d0050b003407100b510164030f5a008e210006034018245295080000c2d01c9460450603040c03250510810484001095000112001d01c0b5501c85560004400c828440c01e100c21341d5200500000912160b410114030644a02426880c0da0502180e002120491050041032402010010b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 293073111 1250 293071861 293071873
    0x70e011103071412041d0907030c120308010501050c0c1507050d051e12040206160c0b072d0b090307080d0b12010b010801170102040906090e06010e0402010207121103 73
    0x401d0041e400680c0c028505001e104404d25599105090426102183c40725a61400c14503100d020034008140010130750803080c0500c0310040001005240c5400141c40403200b4890f80070301c41d29020f495403030b060704400e06110061100c5420703004001002c061010040e035507281c441e02645e030031058a000316030004046001e002c04801d40b00b0752100c040c6c1400c0c02c1b404910b030009010151240400d00ca00f181a9110300420b500007030241c14071074001c0a04800c00213110703009000356280c200d9501020b820003840b228000400c801030107912417002801d002682c683e15110010718134002c013040c0d100100207100582410004d5001c680c14829164819000a01541c0e41c00c00e80b040300000308002c5903410302c99104a209070b840400f052060001e10401a11144050b03428040c507941c000918880c081220364007084045480605809480020aa00c3c035010441e00b2121090350300340f40d0142c00412016219104210141c0e07070020344031007101d1001070000d00340c480c1d904010f03004044040216806200300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 293074361 1250 293073111 293073113
    0x12060b0d0917030c07030215240607021908150f04020f01050705060403020c090106180b090a03020d050703060e03120f06120607120c0e030307060c1b03030e0106050109060206070e01110307 83
    0xc1004000c40d03031187c0d0035181c0c1006c5291000031015815074089802c000c0301001c0c9800021140d4412242400041030981010243d41c00140d42c4026590344801070110784804014180c000c028005d1008400c82014100f45410508070075005401400613103e05180c944c4000b49074066012101899085820344015203441d040183d43d82c0d400361000ca02071074058000255061203404888080c0030b9441c0fa440c00e480c580348007940030b42c0080c004590b00008000000005036160680408030b0f610030b0001c0e00c0220b2a60400781c0450780d407046c3c0300c0b01d2038108000982c2c60040303101c980c80d44003c464503a08403a031a06004604038802d01100d0384444c0c400d4500340000d0039048119914460103030003051009965105048549040185c0d4158040d03009001040001e110342e0444035039001c00d45402c1e1ba05807809400201c4500760040d05078082a40c806d80603002c104280600005800c0c01c0c203050144a18100c030013540e40c040100700000300805010300c1c402907031081d4030740380311f910b11841104c1c1c4a030b80e1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 293075611 1250 293074361 293074381
    0x140405060907060e060d0507020c03010606030e0601060e0607080a26040b150109180f1d1606050a03091502180a050904020108040f0309080a060c12060b0d091703 71
    0xc1d41c00c80035622a0746000505140b241045030700300d42c000740480c0e04248044440601810029017010158020701e002412151024403030100246555500401c0d2000c1c030740700503410481d0680000041140c40d480001b4103442c0c000071a10b0442d440540325a440310410740480f2542183c60913104545d0f140707088255000c003100c6680f03006900412000328141c40312002d0311441c2c000e5100f41404110f001c4020081c10003181c00d50b949450b4034a8002c100f00400c3d10143d0110303641591070381c5c4203484882e94945925003c000305042c0c014044110000e5074200b800141c00c41c080c40b42103a0805884180810070031881e128100b003400b0b0f000206644580c0c403140500440c800890602e4010f0b080113100090b1440e05454031801540c040e1070358083c644540d181c40c2c4200d015800207505100411200141c00c04081102c295010b0180400094180e81040d00500b80220f1886440a1504010003071040c4440c25040b5449082c442d0030000d0700e142c09281058211918111aa101500120030425460a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 293076861 1250 293075611 293075623
    0x1903180809091008070909060207060f050702120a1b080903120a0e0402040e220b090309040e010506130225080306150a0c02040b0d0b070f090911071203140405 70
    0x8044910180698902d50b5910340b40f10603201e02c0c1e9281c0d119050400611440f580603c5000340a18009494050241c4941c410369016203061110b080da1001000920f07a0f0520500007190560b01d07440f480c240d42e10074000c0028201d42a480d4841e0466040320041203a807a00b1110079010260540c1c1c1418000054406150031600030031001c03a0a580800c006803829108940039281d40a0b6038144c180c50b002c1900d441c000301c00c10942c480d4010002c04d940810724038010315204504003401941da40c03c1c3c40c130a00c42035601000f0580a1a07062000703101480c1d840d080300000c00b0b29a00d9005840340151000b044040801c0760002c1545005042e54005000c00c4400030341c840c08041da03250b40c60301e4001104041621440480344000740108010100510703264000e090460030040c040030234003107140ca90241c403040030344544020903109200c41140700d4102501c82c0c000e021006040000400a4001509611136084010800003512106c41c10700303070003544880b81c01c07041d02d200403850f46041d18200b0750f121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 293078111 1250 293076861 293076877
    0x1404030b0907150f140f1b0f0c0103020423010306151d0a0806070e03070510020307050f0c01120f11040305101407120b012106230619031808 62
    0x2008885400343c00a000e0340c50140301e0039981d690b180e200c0901740303404078003034000080e4002c005c10100048a0340442c88844c22100030f480c1d901500507892243d030440d160451902d90306040c180140b004000304071075070040300e182c0303181006a500c0500b5401c0c0101c004101d65040307100c64440e00c030b4074458105d501442d43c868909030260f01e1080717221100c0400422000c07505c15040c0c254445000501a94410f0100018400005d81143c0d00c042e210340c0003c0701e403c00f41c4a50b0005a101051074010f0000400a88981084d508050081c3e0045400020480c0b017920400c450220384a035052011000ca5501249078900c00c1800980c80b00c0e03c919020ba100c1300324400400c4458200f8031070703115480080b11036a02039034054950848245411a00101921310a11914180321607801a00d420321002c000c0740203c0c1082d40720004195003401e10150360403158540800c04840c1c001e258040e103484030400c4480203a03a100b15640c0da4404132078100c0c05000c01c510404004078401c10900c08014000000e49507403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 293079361 1250 293078111 293078129
    0x12060109090b01091a01110f030720040903020304050f0d0c0312080a020301050901140f03010507080a0c0c020d020628020a0c05030f0d03110405060c06041103120a1404030b0907 78
    0x80e6a540e00704d90981d0740240c084401e10403882d009404c20360150601901d1064003c0035100001403401c986400c0d5000480180c6103810304002030491126131a80400c0c44aa003107074200142d00c0d0b25100255a402580038141c0515505e410034440e40d6101c02c07a50f01080c2d8400a4081c0854903403500e40d000142180c1c20301d000c1101e40c00816081c10507402500e042e22000307807201c0c220307a10382000d42410101216603d500030000c2d200c0f20301c20342c038203024082c03103170195495588070390600d0003952044a0f000100318003040580c903890030069482c0003100d44100d030116825078a40c44111440c4050341d4100c1d041070382001800705420141500070074150350785c0d40907480e06200d41c0d0360354042c90b4480050480300e070106d40184400d80030040c003da018042c00000c2c419400d04007602c0b100030501a07441040f081200d988680d08100400c08550080340002c10242c0c06010340854440c00720704e40340210b00355038003407010502d00d4111013401e050990b001581c01c10000401c6090070382000b511002d19004591030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 293080611 1250 293079361 293079383
    0x13051209090f090d05030c0c100b010f020f07091d0f0a061404020d0f03020c030d02282d0f06090204050f07090b0f04030c3804141206010909 62
    0x51282d00507207074810041007004d4013101c001241c0031104c40e8070080c0031a50070380043c4690302004100f00003000203c5013203d0300199540c03800b000035040b040301920a0b021980180056448240080f645108855144002045810644805401c1816200d100d482180302d140c500c0e4850f03660001e8502d00c464003600c410805208006604200c44000b12000380d08881c9448400000581c143d4001941601910643e0132484528000a00f05101180c40c100103911040e0800380141201d2850310030450030703000709603c0148558a0720590684400d24080304000e01c3c22101c1451405c0828200482d840390401d80c01e404285000001080c0c1998140d008600d46000100102940311800d8000c03507081c0c0b58003d001d46444120421030380306411030a03501e8400c1c0701c00000034440718007002c09400402401601c100d00c1481c0103002295038120301c2c1000340c402d5a0000322a10300401c0710b0035a07030024440040c9903106408106100941e9044000910400b0300010303c0303224690144500343e10418078059 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 293081861 1250 293080611 293080621
    0x50a060c02070f091a010e0f09011202091f03080f0d02030f040b090a05101d100507020f030f0a0c0609020910050a050402030c0417120429120402091305120909 70
    0xb124002045d440010003a203d0743d405030343c0a410710090305a401840814002c846002141e060002a40410310074200c52a50508520709694a50381c00f24605201c000540602140482004514407010781b10210000d12040c09283c250300300c40c004c0c005404290743d0b0741060138a15844403801c49080d0b81110203040030501d08030011601d0381106800c41d00034009150340f202c00e10028801c0d40f0107c42d401c00c0441401c080c40106000090007103100c4d42d800100c40c500600d0190a100d480035400c0001c0e0010484000681e0703900b01a181d4500c680c0c50001000001c1c0c1c500540201000b8034082c0d40400e0b0b10701004112082a03001905403641a148007818683da82e003400142c0c0010740300005d440798284410302000d41c9401b40a200f000074a812900c03102203400602c400e551141e0040d40e0340e60780340c44940c010b581c42c1e51200c0c0c8130000040e50301c03807814a226250342e0401101070b00003482004c0500c0402c20110104402100c01a0000c00b6609460640640c0124940c45000030341d01503c11000062 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 293083111 1250 293081861 293081879
    0x6100608060a24120b01020d030b06070c121208070927151a1c050703110307030b09010e060d030f02070807090516110a06050a140708040c0e1b07050a060c02070f 71
    0x45c0b0a0302c41038000341030b8134880c000c080c3c0145c00c100c51125000801440100081381448081100402d010200540001c0c1c15080410b403102c0b4a181403411b00c42004148055164803031000307800c81300c5c1ca2a24548103666440020f4850522184a070881e03030800714404400c0c5028a0000e04a50580c070b03094903500d40c01f01d014003050260b44090130900b2140b10010600306440d030002a4001030624000880c1100c04030403030380310341081e29140002555051880401c3c00c100038060b0241500c0424030241e850110002012880d903554010200603c0d149001513044c001c110f134801500c04201903482154030350b42120002d08048400f428000c1d00036810681c4a40070b40129a01040014043d0a80340c0300e54440802518014140e000007564030440b0045a500f0901d00c2c0d80980c0350782c1d0716282070782881d04085120030301c84e4100002c0d0381d52070030510100d808182c3c82c585040d060345c0540341c2c44c0c0e211400e05900b040b105203c003824540c20407446c402c1c45540400d902c416a1038101d0001c0d107160302e4400c42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 293084361 1250 293083111 293083121
    0xa170f19030e0604080304030f060f02030114130e061905060f01020a030f0e0402070b07021005100504090302070302060c030a080c04140918010c050306030d0206100608060a2412 78
    0x2045030110205044004280726210001c2c10080c080c0820f450075695030502d03881c0d0b07401640141c59500310391003138000b00030150003000c0c04486c1060f402e6013594107008580f070545072110101031141040c0785161059180e1500052134400249044d203000b40303010748441c407440112800c904d41261a1200240c00b0b45420036000000140c10f900811440c00c9590301074800c88034500d07401c028089070280c200000d03540c03400100034091180798144050b04003440040d240101c0301c041140c5250503c4100084e00103141c180030101c907011100440c00f4802420b040e8100302d0a40c2001c0e41046000503c0480c081c400002814520340c507a90721341d0f02d5510980710007418001d41c0942d65607544502d5004440385080321032213030000460b46c440e98982c00445003450848124650150101e980881001114501800642e0044042c0c0c0094030152038410018a40202136002c0c0c2c01c14000c3c514040340803516480c505c9005460700e4441226204100115007441c0c1949200c4080001e6822003050100e04c840e002e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 293085611 1250 293084361 293084383
    0xf0b06010e121c02100509150108030a2a0203010203160e060313080a030f0c080708070507020f040507110a050a021c081801021606030b13020307020613060204050a170f 74
    0xa00070044101d03c04403822803150040300110700c1008a50302c09000288691401080010010045091180901039200d2416400380c0100e4009000d20307a12103410401e941204600f003005000c9680709241d0310100810030810180d00f641c404802c100d02c0c41418403d10441c1d003003a44408420310701c03180401c030052008a5914502000e8055448009011040609050112400c000c9503030700e4801402c0d0111418810712000107401102407151141d080070312950010403d03e4030900d00381d00c580110320741028540d0910b00640c1e642c0002000f0500c1148111115078011054036244500c038141580e9501304914161712891a011454066200c01101c504846600800040c101403014803c00d010000f0100201e0550044040d0303940d41d25407003941b51010f450591000035080300c00380140241e0702c0d2000761000d0303010b104009110342d0b95000030340720b648880f580c00400d0200d081e6141220103409582d200f1900603c1e0b030100400c80002020094100e480c010301102c1c440e820007030103180c0e103400c0c4600d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 293086861 1250 293085611 293085613
    0x3061409010b0d0905011107030513060315061413080f0f0109150b0a0b04090f050a06120b04061b05030117010504030f0c050f07080c10081e0a090f0b06010e12 70
    0x1240e00c1203102d40204d050280150000199100015a4581d20b544100c208074005400003401e011804c04240c0310030041e00d030350305c0c0801042c422460406100b095a0013602c0c281700003900e00c0204040c00c0b40031207105000550060940d41c0d5602e07800340c1d0361b40340001c18540c2801003403954000a1014403e00350b4180c0c0002000d4a58401c100360741e00103050384240031f60406400080403070072403120401400144188100001d00d40c02c9503282c4400c6a07006010031440d98182041000f103400c2e0384002d20101d40d0446075040705a110740c6440740c0241641d030100742010b81000c041d0740fa00f54000c00514100c03001c40d107201010b084100710403402c0342c900722402000314901c00709800319140704e004c841805034448c0f81100c0804e8455140c040c034004465101e41e002e0742c00f211440d841ca00b04140507500015490a02684d607003840c0c8001076140003030420840b40c80384824001540007078240c0102c400720390001c00c011104000e45c24031300000081180c0c0d4a0100d214401c440403503003043c009000c800b0300a10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 293088111 1250 293086861 293086867
    0x51009050a09050f0c09010519020726070b13030c030309033011030c0102070b04050f070e010b0901050d050712110f03130807290a02040608130c120303061409010b 72
    0x21700c204d481380c1002607145c1c104942804038080901c9108400e402c100c0c459002010400d1501134192140060300d003070300b2440e60700ca02c0c2c9050083c0002402c282a80d4081e03402ca6103c6507201101114003446038409484401644400003d054002021340d040d2400b03868000c115100441c1104c080d40c00c07852100b2181008102131840b0035200c0c25101c0b0b481044202034034508480c0e00c0d603070307400d90300a245c1c00d07540c0465140501041002c1084030000101641000e051103514040b22101c0c0c40405102d0403c00c1c600001c2d290000740c3c443c400b00c544520500408000138201800300408800c0b80d2120f010f02c8600d0000042013081c074280c10f65030307079043c030701421031840da40d00f203075007908802d082c0c03089902140c14001e40c0d0020354a82240d0800340c00341180c0804400e8010768559100c180589042000b910410051000707a0303000c0c031600e80c0116800800d02940c5a240350040c00343c1031070f5202100d41d61000c2604c00401d0ba040d00501e04550720b00b140784112511440400070b40364001c0c0700d1383d0702c055010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 293089361 1250 293088111 293088121
    0x6080705071506090e0303010512010e0303220b07020318040b10050f04080a080a2a080a0915020304080f06130b09011404080901080a0b03030a0c0c051009050a09050f 73
    0x19034104039446402c0b0001151040d611148401a40d0b501404030020b6000400107009a06002d6030800ca0642410001d03c5081e050030403517501ca10004d0180018150000c000c112644440a14028900e51145140c0c00300c0c909400e0094076500881c02c9035880b00e02481d000320140c6031901609802c80401842510a0104403030207468503400403203042a00e12051200141505080c810542c007980162042640e0f036800030801800414410906400700c62031100d0003010044207030720542601c2d8041c922560340c9204640560b204c0c00d581d44104c071049810900707504a95800300103030007203c824104880f4a180e5450109445000c11110008d040c1a518140c1c000300701400320503900402d4000000655100d1600314900c40e4008072400c0e196003c0020740540556403000020f9445031030030100300003220110001031b440c3e00c00c140c92842040743c48403519080c0421718054800402c002440c029400300c140c0c10107420b5a0851080900c1041d20030341c0010340340854000e551080d842005440002d54070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 293090611 1250 293089361 293089373
    0x4060f020a0309090c0c020310020301061b0f02010c0602070204050a2403050d051c05160801090911010e01050409060e010302030717030706020d0b04150806070903020d0b070e0d1401060608070507 86
    0x1003909005c04104540c81c02c0c1025031024483c64108641d507030005a82e9605208024151011200461084014818075080400d18081806144d0395091034408070185103070a01ca00070b4010707114003035401403519040c080703490000d03031040e101111445d61074607451903442400182c00c052840050b0040c0c004800c0400a14480d2000b8078446603191505103613518224140710840e1400c0728a1a041e802092090310300c035810034281401408211010b00039040c081d078030644d1040404642d103050020802401e591a07004406403006854419070070042c1a03030314941d0348040e070400e1200764041c0c0920400800c0000031b910384109600b101e0f42c002c601e407981e107681d00c50080d8890856421003550b01d10746254035030340f5400741d80d015440b45010450f0301400e09400509112000d0329102c10300410003001c0005031201002058016041541d80b0001d5441c050b082c1c544820014005500506010001c800c100640003045040740d4082e0080200c1c40d01d600c41555444026100b03600860401c2c0301c04000a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 293091861 1250 293090611 293090621
    0x8010e0102090609210706020705090c0a020a031812060b040b0301090215030402011211190f0f030504060204090203090d0e0315060618120d0e030a081207021f0204060f020a030909 79
    0x50703084916000e0085ea40100c03400c12515401c0080140c2081004110714506180c6190b0042d0050f807026241c40c41d8050081d5030b41c80120341c0101449a44c45610b910f1000b0283c1400c020030f0356000c42da0314403031140780000086c080d4120302485189000d4a04009042c14891603a209502030062480d400e50348850704c0240c4c0000300201d040101c61212112114001d0081d191210044880386440e0011800d1024160102254040400c69002e110b00d10303185c0d0203504034181d12045d082c00116030b100c40c1807000c0644109e800c5804410300000a002071800000303800e0250604581d59851500e400000701030325010281c0c806503410115901280181ca0081c006002c1c24481c1241890032200c0b5401040b02d0122511441d0507039040014101107103508038000c0844541c00b00d003d007800d070340c2c15644c0414074010040355001c140c040c440011aa070b4001c01905411030490884403103184014001074020703500a00440700001c904201c03050116000080081215903d9220384004500744492140102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 293093111 1250 293091861 293091889
    0xa0204110a0909050c0403030804140a0f0510150b0702060d020a080615030f0606220602030903151909140a0602030103140105090d0f0c0c0801061a0c0c01030f0b0405090708010e0102090609 83
    0x2f403107081880165002c200c54100c06200d41c41c241c489a1840c03c0a43c2021401d0300118002d0703003400c511040e085c00800d414425210101515903c2d1106400031440740e000e44002840a103100003540c89140f504070044a1044008842e01e51250340c611402c060b181c001a40c0781da0b10400988080b514610342800544038641104400051504503019802c441c03010562082e0056000040c0340e00181c2402c2c0301d2204445c080112151260502c2207502c903012402c0070074146010b945052040400510380042d0340812103440480700d824080b414460000d620038801242c40d020462000000c0104c1801124451072610000e4850448502d009541c00030b0010141c004006c4280040000100c6003110708015102c42000001c1c600c0c103200394040c0b149541540c07581120420b0000c250010000034105000c030b5020310300850034488c008019000740c04d03201c1f07055501900300410000144400604c40c4103c510502c000e0001d4031a2032442400c03486150b200036040b10701040904200d080c1001110050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 293094361 1250 293093111 293093123
    0x30f060a030c0311040f0c0306050f01022a0303120f160c030203070314090402071b1a0a031116051507030506010e061809040302101a01200a0204110a0909050c0403030804 75
    0x30b010b0310860b4002c80f0603d040710004030303542750710a0000b41003801400050741e800b0f00003041902011700740c0424503a00d03400c60341000c03a40c03c80b82c18050785007801030742d8040e90b440e0b122140d603061038803d2072120310080760000003803115040c031003180b184581c0c90311060030b801d84c015610780030050700c1c21a01844003071401c007401c0d0000c01000740c4075203551009220b120b01604680d00961803038511024201e5040c2d01220b10401c01c0030320030000041c03940803121901200d0800141d0b1090240c074448c4130340202000501040c1c0642020818800003084a0355400720005080c0c0e090343d6494400e40803a1801d450060004802500310851410048000c2007100c10715816000b000233020700007030030310108850441c01600300d031402182c6c21f140c90243c14002005400038081030f81440340000c2c10b910f1060a06c4181148810052410708410312509801d15005482440203c0f01d03407010b510103a10801140001481005000032003040d0351080a000711816840c192500d455618111503804015005441d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 293095611 1250 293094361 293094371
    0x3080d0e0f2406060f040605130302090c07050105100f0b0a05070206040603090203100203091f1b11070902040b040e1f03050106050109080a030c0308070212040803030f060a030c031104 81
    0x155030800001c03064038041002c2030340944503807506644004024064038080d8905000b024034210000781a141510283d2400b540c80c0c0d20f058800084001041c1e0010350031001100c24444c880b00307103800400d110380c041c40007400f054a47d0703c20031030801f403d0320034180c51000c42e00052081d400342400505801c1b00916045040c5034442d0001003540d4495802039000c82e559085100450a0510848620600300181181545000d4080310b07294050440340400c3d258104041941002a0b5031150035540300c0030b005480d0400280c030b0b0140403440d03801080d0f541482001000a580402c0c1d00071102601d1210404c41e00b42407420b881e0441007000541640030303106080544e8225500000ba61500a50103140046255490480007416101d2150800c440301d40060341e40b8070103c2d402c0140e200006515161050b965aa000d504030b04201034913500607001000040d00280a01c0d000010354003801703500245007115203c904c10810700180500c0000c0940c8541c40b400c0011582030098030044070b1024201180c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 293096861 1250 293095611 293095633
    0xf060c1209011709030a090f0b120402041d0105070801080109020f210a080702100903081614150906011410111018150e07090b04090c0609080607050403080d0e 70
    0x20810f101102c4000e255800031841c0c0081503449a402401043c402248403030a50070030a0251552242c0c0075510381041942d00401c086407034550088840c4a0050b1010210355003080003103000e0324040c1e518000042c0c6200c00420044818495205c02c5640280011081c0c01c1d0380e028840402291000c1241d078205030a1042c07180310043c007640300780da44182c0d00295101c0b03451040240b001152800c600800400250a2001500150881301061b28580c03540c507140c07016161006600d1503d43d0314010502840302c4180703840842d407401743c3c025031208054840340e17030302d03160307184c4021516809050340000d1900e107103020300340251120380940201909a581303114508400300180c5001586d0100682184c0c6d01d140d05100300c0784030001824000d45402c1c032141060200286d981c80c400d00401c4440390340c4040c403990030b030b440e07600035041c981d4409100d0304819601c0b00f0140100c0118895140d540c0078180c00118020310410845081c1ea42c000c95a50170701001200800042002a4900c01ca80c4510f10400c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 293098111 1250 293096861 293096897
    0x60f090c0d150e090d080705090a05030d03020c19050a140c10090e07020d120e03042408011205060406110c060a050907080f07030305031003060207030309020f060c120901 75
    0x100060400b001c0100e541c6103040c500312100c040041a50040340c1200301107684407030740241d560f42c0095040c580161203d01800009400002540c405a0305d445024440018181c150300500400c0503940152113540701d2040c0c4101071102180310040203070300b11489140026480e00d0070003505a985104486440d07040001081d8254423000074031010030b00c044820001104e4260346990700c032106202034100b070500958098114041290320050b11610f500d6003a0088030100309941c018151850405c1000c1e0154040d80540d0040d9111100007903003030f1002007500c2d880342540806040c0d01000030080341e074031a00c1e08402485c1c000341d466003040e4100010189184100501c0d8054584c0030b600041c1814808000c0c0d152a1541e0301c03001680c2c114079110380c01c07000041000012280c060030210f50344c0c1e542d4008030840404642004045500c08525942416070690012a1952090344d280900c00905002c100c2280110100204141d10005900007944102d001805002d070703041c140701e411528018045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293099361 1250 293098111 293098121
    0x90c070503130602011d16091e021908100b0306090c070b090106060801060f050706051f060e090f040530070605100e191a060a0309020a050306060f090c0d 68
    0xba9006039107500b40ca000c0c03030221348090386c0d01d2003042c4014541e000da05680214030310710501c100c49090b6543c54142811180d2800344c0301046c4000503003151f440c0700a1008ca00c16000341c0680c10000b1b1030582c0007803030002c0380799100c205458402580078155510b602c104007404500a04401c41c1c64004e100c520001005004800c1c0102e11304400440c680d81050320003002928142e10550800c015240e607034901907000812640b40981103040802d0a50f100d244080d0414003504d580c90f0303c0c038a244d000040f003e500410302100b095048416210b0b5458003103c0c4142e01d2070035500035003207411082180b0010303601410000145040303050052000007000000c040d15400c41c10341600c401d5141d030200101d0000340b40c0704201400034901880c80900f40008401006510307004900344d80303580d035242104e0080d6550b04c0b0600c0707108000d203001d94501300128010084c0c120604201e02903200c1c3e9201186510740840c50904c501405018004103103102c1080003018000901101c1c0f0002082004003118480d50080c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 293100611 1250 293099361 293099369
    0x40b0a0509180105010c030e04061a03010812070c0e040c090204080a050118080301050d17030a0c0e03010e0607030f09080a0e030609010203070e010806012d09080a02090c07050313 79
    0x2545803034540e980c0c00d0220000b034016280000c1c4002100600690780c100b805250030310f03010b2804520350b03000c04010800030718032a0000010314042c1c10003041c3c020721754002503040c1d0b4269001c0c0c0c0c96038072191551000c0303030192150040070103490b11002c1c04007004010040b54046d0040c400703030700129a1380c1d50308001c030703030094214000f1a000b082401003480000d00807a103c0001054080c51010400e171100c051501060081c0b520030411409854140880200d0114003c1c0d2122400d685e203041c01e00c1e24800510100700260007003444d110b103180907807034184540307a000e40b5150068a001d0f582e80b5000c1b4001c203143d040d100106661945d120001c212810040c08106a003a01e80c400c4199034601090f182c06002002141640c1c01002045111036110081d03d183c42c0007820402c5117503e8035401601c11a07072602d422250210606207005401d1a840b4070f540070802251240c0130000e482d0012140c44201c0b80b040030350084100720110741d04070000801000964010400d4a082810741102c420000c401644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 293101861 1250 293100611 293100617
    0x206031e1005040c090f0b1c05071d0904260d02210105060301120204090311101e020c03120907030f0305030f060f0f010305180706320d0908040b0a 65
    0x140b0090500e80300f1382144282c682000d500342480e0841e07811501c1054064111103610100d041aa4000603070042c2e8660401000301b800145004d003001000030541c41001d135040c1d980c0c110100240d0520000c0755000781d405c40c0898080c812580f110744007841540400c4a04030800b0085035a00c070000344094201b011096186400e40701e04650004070200c1f040e0001c81c0b240c5010001000441d500c55880c404d5250305440224030b07900c6070308064441e8003900041e060580a1804031500c00c3c1c202d0b6001d030303030507118812100b81d00321040f0f030320f0380700728001c107404042c2c16402084490000f505110000e42e000b64203d0071100402c0c0c4070f0f07451620b4440f00500407001b141010040c0101554140895648043c050b41c0d007041d0710076200002000036180042c028181503440002c10031003145500d00880e142c061600300e8800c1542c13103070700030080b0740ca4106074207c150023000c1c20360070303600c1038808400c21070100c1904a003494184c03a1100300074452005c0440c0c03410300421000591598a50240c050034500c0e803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 293103111 1250 293101861 293101891
    0x3031210050307080d0e030c060f1218030403030804150e06070e0102030909010501030203100506030c0901110102030f041203020c1603030e010309030f030209030c0402040b071218030206031e 84
    0x10a03100500c03201500001e21035000f40e50148141d240006081c058506035250203c25085450b0220381010320802100360080d4000070042032280380000248016400c0e00302d40b010542d0b4070901c56040c03c80342c1c9440b20315500200700c2000840c0c4550001a0071034010b081d081141d1000c0c035000002c550012140401640000c0b0400800503013000416458010a00180d0b01d030070b080f10005840c6440500466047c16030101c0031a448208003482c1c04098200a000103a07039050080403d003061b007103090b0a90000d40202c5a5811030300d010300a40e4025552164504447e89030f0742c0d18101000b4904594008150b030074090302051a0041240c1c040741d00b90340c1490710b0943d046044c0201001110305c1054149400c1075410303400a5802a8416900e68071460011386841c071010011342084030320041107602500108000c02c1c000c2c080001041458030520740c00080c01104001512080740e0600d514103d00c100020800150600d50001c5500074101134510b00c0700ca041c640300361203c0c10306032422416030510b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 293104361 1250 293103111 293103121
    0x270609052b21020a02030706110c030d0801050f180601201c17070e062d09010813050606090c07052e020903100e0c03060c0d060f0501050a031a030312 66
    0x2801d0702ca984410303500c0a4440300b459038011a035105100d00c182410094030b8128114030740303800d202c0783d21103c100030141d9440e00701000c0003c3c203d40c4280a640c0c400c10800c2c1e5505030a10b055505400001c480c0d0740804200da49120040d0388034100c0c02c9442601200503201504aa40144010302840102038156600c490800800600c00404107540c42940a050420700c000307140c0004e002e115a034011100555103510604201400506c80b8000e415895503503020702414602e003501030090303034500703030b03520780d0166200b1078101c90121024002515030b800400124400d4100582003e5001410359111441c0a01351b5031418a08131b007004000e591609030404086101c11036070150b0a408012540542c1880000700002e500c030811240100304150750344641801400c1c1c28440070400ca00f0050544150385401e0700c2411082d40010701d04031480f407910070b0116042d140c61100c90151801a9101c81c1800d00c02c0a00b03a00809031349001c0c4c040c01006401c016401d0350304000400c40c04800002d50350460402c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 293105611 1250 293104361 293104403
    0x1104180b07030b040c0e0405060f04020a03020d050c070c0e040f08040605091203130b1c182a050405040212010623040b150715020a270609052b 63
    0x950241132080341040b9150301180c2c2e00606520401008440008580d110366002403840195515200c3d00140045000c1e51200d4155000e044c04c5004d15005000d2682d61040c0028540301d00a0010452008048107000c482400e01401d03620074400c85184070018256102c00350180c00c03d501c0000007c8000036156960b08203103000d044402c0d070750380c000c3d42003c9403072621200580d610f014883c407200c400301c0c1400a00c51004030004c5400d800d504104003095101d008004481349044059a24400324101c811080f10b8410456580c102c0a036000400d103804d2030108006000007802c01c0e6441400e0304c00d5800c202e070082c440e0030020105501405a030001e80800700300b0f120380d4414644d101e40e1400c2c0403403201c1d4a59004054a1104807401c0030380e02d00044c6000800156909070105100348041400140140c1110944803103521a0303019005d490020b0500c007251428500a040001d02071030000c02580c2003140018191500000004403000d036059a03040541c04c2c0c0b07001c1601c4607007246d555800c010907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 293106861 1250 293105611 293105621
    0x7081b04090612021c050303070c110603160810080601150e1008150f090a0b060c060709030309141e040b06031f0512030a0c140d02010e010e010c0c1104180b0703 71
    0x250303d4200303c405c005e16444460301e0303000c020b05450030b10580003034030b60801c403011003d51a0306038000c2405860382005452002c80c011021000d0000c5114031000c154624540c00d0010222800c0d40002d20340e0360700744504000d00c00342c0719038440140104001d01e90050355805604810b94003540d658100c1c28984103503c0501c840c1d48640d00307030150103030f02080b48154071140d984035801032200c40045801d202c401c0100700e2a1140c5140c0050707a0084000740a6456880341c40c0b0710803a80250b8441c41b45039111000c10590303008219003103034030154000083c0200c0214200c1c0c690402002040010403002c21004500b055208890b1003420340012902c0550300300e24072807000060700003540c040034121000f0900d02d669204d440d4820041c40f500b450704a00f08000e00243d50a10018001a650480320f24103010303002c0c00c0c507200d003440c1c6542003550041c1c501d5814072440c104815a49c1e07849842c42050b0311600380030541c21008507000b603150311080012400c02c502050250340704d51140c1c0c51078504404002e0480b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 293108111 1250 293106861 293106889
    0xb0c010f1506020309041d0703050d2d0f090f090608010f020c100e01020904020d2c0705010503041511070b01060801060c110a03140304080c0907081b0409061202 71
    0x2000d40704148001030780042560100304050790009000081e08a00b465503031054070a4002c90710412802104000002c260490b4030889a102e0b1008160841c02c1c44c1581c04000e92a44083c81c1420100c601e071030310070265003491030b0550820019803901c036214640d800b0401e8000c1080252146030802c0250f00074851a00c95011243d002c5082c8641c0b00501500c0710700c1140d18202c0c540d100c81001c070304520290304039009448000c1085507a0b041400d081c401601107403008a242c4190040c4031b110055162800c40344400c1460003038040a805c00005450030340000e0026281400660700301a44500d16110741c0c498540425207141e1034030340c0d51500001508050b0411000c200300034004204c469000108030848690040605c4403034070b102ca010031180c14450344090058201c61031031009a00f001b1004005030703500e04003a82c00800c0381d8000d20081260640d01e91000840b01e00c00924800203d00054000b115807440551030584c0e0307600c0c18000d0351103a4200100168441d17000c10300314508078200180710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 293109361 1250 293108111 293108141
    0xf0a09150614060a050405150c06040b0a0b0f1507032003120c0a020a12031506090f080303010b07060e16080601062a14030d140106020618030a180b0c010f 68
    0x301d071305100000c00310f01491140501030400307000c040303404c5021401580c0c4590812001c6900d2490316040c0b00300c030082e041d038003690300c145070141c0150542403441d115030b6140009030807100d050f11500100f9a9641c0b00340740603410409001100f0010b0011049121001100780000f1925800168221048900043d1071022080c6003002400750040e0080742e80a001c540004000d0b082407503146094024205003815004000841a00811456084040c06054501e41e400901c8250348802c03110340c1e07a00c42030003002ca2141051004200056582c0c21281140301120190360718000010310485204242e40c100751038503000b00d40140007884e13002e01c0324500b400b0074185058500c0c1441407195054034001c0030162030b1004100c511540c2120400071a4455110454204064550048482d000340341c00e00034038005003d0540420000080b0407101c0380c1d0b60500e18040c1d4a0308030b2101d011f503403d007140c40704440101500900090388400d143c0180c03200840f60000420b0081d4141c4002c4112002c0000800300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 293110611 1250 293109361 293109367
    0x90209180906060603072715020102040803090603130b13020f0406060f18180204080d02030a0801120201140307020a06050c1c0e1c0f020606090105090f0a0915061406 73
    0x8003800604580c0260081e00c6141d5a5140c44c01d0448580c02140911420460708052a0401c60201c1010600311008c3c0001d419130b02c00099070403401e030f01c214801c0703440b90380c001c0c0540c20b003503e070000085d80c120081a00748030302074409540e8410244000c41d00e4072150382207190b80f10150f0400c454119400c5500b102c0c2001510309214000d4a81500f0052100400c50380e80000f400746038840020f0400b9110800710414400bd452402c0400780d80980100c80140c0224101813800314000000e03201c1540d40764407140d60580c203004840c5400241024142e04116800c1403048081c0c0310f060046004818030b41c0034000044e01410700c83c00b660005441d4280d0714004209098102c048801100040303480d200c004503003005101b0405180c144c00c40748041101400001c2e84100139004400741e105d280440e001e50f0301c540d0729041000400d410034030800c0d0b000280740340000c900584441000b54803c04840300040c0c0103005490700365500311010f07520361585540340028048440e800002c101c813807104850143ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 293111861 1250 293110611 293110621
    0x403111c03270b0c0708120405060a090909060605030d0c0b2d010e16050406051606020d0e060117010b1c0f0f061a032b0309080409020918 61
    0x9500030124800340c20040645a14864158421039801180c0c4004241c2505a0303102c000c0031a09a1100c101c1d04081c2c030441d1000541d1060125000040c4148208840d0500d40381909011459001d2300d01d010400c4484000070600004a10828040500503900007410504260901d03140000c00d45080f010b00c01c2440903a0005980b01d000c41e039004003021161626000388007203c50314110b4030f419a00010000c8030001c80e40080803491940b10361440c00d203030000c000c0d5006090701d00c0d10403401001c00150341002460140a030700e0040c4034141d880742000515180e03021002c04225007950b007250000f41c024000400c10300c0c1e03444101e200c076035000000800c00c030b00000b80007401628000680c0044280e0101202003440300219080140503000340c0300e074000e010203152540c0104980821542c0032140c850781d1035504e05001134030b2040003060000d840e1507202d800001801040c0a010356004151719021820002000711010340028450ba21000d0303110341c08001007191200002008459051200302004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 293113111 1250 293111861 293111899
    0x4060501030b0325030209043002030a2003180a14181503031c0c05090918030d02040303080a0506060906030408070816030c05070b04080c120f12040311 67
    0x40783d40601303400441011200c5910142075055400658401c00002c02c12051011a452191082240b0046c10135100c80c60304003140f168076034050750301c01a0303c00c0c40070b00c2c0128001c40c03c540110601a0310380d03005000c05190546540e01910401c01c0b070940b102c42600c52414802c240c0000341800c5a074403050b540828010440315003c3d00d18030591528440007040192440500041c00da150190581b562a800b8200703510a1107808111840141d24201200b102e01c0c0c0321b14250b0302e042d400140b8217045504e0b1681e24182000c0e0f481682e5041f4041080000035080c1c903131004000940c442d480d9a01c4034503003020030000301c40000303049900401c820807a840352640d0340030803030764855408103599403102803d0030001c500740200001c0076a001044110074040c5500803101c5d04449226000301c40c00035403500d030128202c3c010340c42101c14a52100b0b20b81142e81c50324015218408030580300700e03145900781081080c500082c8030320308105064000360600c284902003c0007a0b440d00300342c400b0402c9200c0c40081ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 293114361 1250 293113111 293113123
    0x803210112060b0d0206040b0414040b01050a0c1713061404030807020d060908030c071101021b0f01050d0203070906140405010504060c080d0507021b0306010e01030201110a1b0504060501030b03 85
    0x420340c0343d9801460340c1543c0c440c9258414a600038215a407101c1d00e4543d0840240c1c8203000700601c080c001c4142005c0ea00d018001c298848006944aa0620f80c0320241600c20080e4100c0460350074240301c03205e200c2100260302900b0f144100d910100d903a14034107003015281d1070442c0705860301c50104000900c0030407d4002140c0c8500d60540e00070180d0646030078a800203200744030008111403000014080c45406c10405400240e000d00c12850881601c2c60059035600000481804440c12903158649140307801c0383d00780301e51503041c10007914000d402d03414038049a100b25001008580e4040d424445240d2048030160421854045145060306060000c2c0240c020352040b1000c021b145445142003101a40c15111404c0e1204801d20060a10031b8001c3c2d11100d07201c02030074003818a85805c8145203000106c4504032480c40c00140020303421500110346800c0d5051104034075105a021682c0081e000104030000c00ca0b00d8542070040c60f080c042000180c0b08281d100b0b504260800200e0090b0b0398010400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 293115611 1250 293114361 293114363
    0x180510140c07080a090f091e1a04020904140f090d1b1106160501051909020d110607120e130603030e10030b030109080310090513031107050a0803210112 67
    0xd64440d51803810840341548036811140d9100030b01c80000907540260f41043c8029810800494070801d1502351440c2150400c02c2c40b8000034401000c844141c2c00c10381d000b400944001707800860004042982c0c0d0401000541d5003070840c8510348100414610107000343e00c481d0070149401d6600307611102d082d5480c2c3d2600c01c0064030301c90480c000230071195101c400321100341060303901154500c105810703d140205002c032150322104800403e2041013405900c60080d03c40e6004200713220110554450702c550007909009075401c100100f1900700030a108c00382800f0b4010076981c40300b9149082509004500003d0030191501d241030020500c002600001542c0c42d4207019241c900d455071854204802800f01010004d07015442c04804500303110b03820004603c5101d4006d2004001e82e40d5502c40d000b1a00102c034002c846003414031452000901c24202c006400c3d410300d048900071901e410018000b071a00c0e60100c01664030000b034010b42040d00e80584011516a0885a601036260008941002c000c81c44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 293116861 1250 293115611 293115623
    0x60d0305031012030f0306080c1c0204110c0715030213050f0d02040f0e1207032304090606050304050c09091903120f020309070e06150904180510140c07 67
    0x142c46039000c0c0d40703000c01004900d00c5440c200b0b030542005001030012612400005e81000c402190303808002a14201c124000380462002244103d0f2b03546480c1480d500807680b10351500e003407a1808001c14041d04013284100c02402c28103241181e0300046a8584101c202858014424203400c0303440822810701701c40301960410030100300c0c04006842502c030030741e00035842454050280e8a100c803c3c1e004244c201c0910341140c9220010707040e251114094844010000788e00300b00e40d843c04800d40750424041c00c550135000e0342410b0701c94646906a401c9a00f02d1f1000410100801052000400141c0100722040d106d80b000e504182e6915600c682c9589444446140c00403034203000c240c491003151030100014034007000a280042104030103580292a20b52851040c604042a68408286424001c030340040c0b0b002510303c100801c6500315007110f500c040e1b0060b0313a0040055000c402004c00c2c40540d200d00c000d070484100c1e00e42118100d418000025100c01002800c000642840c40c045540080d0458 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 293118111 1250 293116861 293116867
    0x6020111030c16150c110304030506280903051306111203090c03070e04120815090606090319030809070f33020f0d05030c03040210350a05060d0305 65
    0xc540c0300c0010508000700940c1c40071400155006136644921201c980694a420078240d100241996034040c40c08060400e0700f119020900f60320795004402540194841080d01901521003107508451a4000c141c000c5000004d00b00003000d004034030140585000d080c02000d40c0f10141080b42d5800442600c02c0c1e0780080000130a419980400100003034610007822640c2c01c40e2565079446039005c00780c07803c89205651003040030060f4020310fa02ca1041441908181e00c2c0000401040f1000002800d41d5400940402c581300494506002e000c01c40c410020841540e80a07a00c1c0047c0035443c010110259134220540500694000d2046103089500021000d81c1c0c007541c8080c10b055101549050307104140140d8841c4500d035801040104185420005035070780d0051800c420340c3c1c0c2c0d100449040b0f410140400026005240600803401c0e17100a525060301c07100810004284840900e40d844a000900f0202503100200ca004010340c0c05610179209101c00c0c101704010070410703c1c4600380102840004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 293119361 1250 293118111 293118127
    0x50d05060a050a080a020a080114071b0b01031406060a06090618090c09091107031e0c0803240d02031f181a240d06110a0906020706020111030c 63
    0x300c0940409440c008002041280d660421385903034030b00700a0308074069403607040d002501d42c006100b8640e400200100e0908a03549002084801c0c00262154104400c0014400c00c00700d01442c43c02c0c3d001e54466003100204042009000d450010000c1216200d007403080014484a83c0c0109004100e076281d04011904c040c000b0200c12654055412919030f0500d0200019185548000c14008440c82d0640400a0011420302041035101d00c441c080c0206100056000322035204000c03040c06402c461806031903071105c55a990400350f00944440c0c0d62000d21030400c0802d10f500d00b4400c022641d0480701c80300c1045055010039210091051a00501802d0622000001c11290440000320700c3d4031300085400903680c40c10300d50711038102e405540019041000520000000c0126207140300102c04494510b010b000208800d0490405040300c1d1162502952884000004080d042c00c00e010340300c8402c00750401c10000d2030b149036a4000001c681c10001074100140d030542c110703600700ca4180b4205540d4906 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 293120611 1250 293119361 293119369
    0x10e0c0307090b0a24090605090306060f01030b040f060f062109020315070309031403041709030106050301050c04090509031305010507140d03050105090106050721030905070306020c070510050d0506 87
    0x990740c0540300c514001c4444d0b101c0c078580305208003800006038071b55041d01a21040304030380720700070101d900390940c4c48140428100d243c210880700360000705250104002010001040596608501d800322807a00c5501c140060301c0403a40303900160401d40340c02c0804001c040301700000e0082482c89a072a65030b48408610075506c00740003041012503406248062810030080003801441c52a00543c0010410700504800c2d503101d9003140d01481e0420080b1065034014481c04503d81d1102d1000340d81513603034100c0029203403230a006451156981c80300558855142440410135110001c02c1208507400c2048952160844040303203000740c07030080c600540c807002c81e0310300030240c0c000320100c1c503499219621542e1903156054002c903068440682d4000c0305a40e95083c1502e250080c0303a0000c1504141c0307602c060410440300d501c003860880321f260119803003695440d800c1c11f0118580081d11401d800044000703554400700a40001080241c42c001040c141d0444010614000c0e0400e804149403030f100412415a5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 293121861 1250 293120611 293120629
    0x1203040302060a0503010e0a0902102f01091202010209010c1e080d0f060e010503031c0216030c051b0603060103150911040f0e2e030501140108010e0c0307090b 70
    0x81d000d85202e6076500080c03030181442d0030034400c90340ba9201d00d10000d415071006000c0e81101540c040d118950485040c4000d03a5154060485400c0e50a0181105148211055840c4900c600d04800000d00240303181007440d124148a0b0422066a0040003603035044e1740d10204c110704641c0c1110b0810094603007050045600c900300480682894000300d09081d2040240e4450040341d2800001003200d250354820150248209119a580c10340083c04190040c1b955601000b0000782d03144001480c14910484415109440920660002d00340d03c18400421004102411202c04400c021609107522440042d240d0301c80108003d04243d04c2d000710b82c1d40c1032034042000380945011101400008801902e405140d0864401c3c2c03c40c0350000040010300090b0301d0509409001480c4c05110549000c4001e100c2d010711220803034040000c100c0001020440a208500c400f0000514041582d4906840706082da11000804140b60b08040003c90065800041d0301045503111000414000c41c844009030440d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 293123111 1250 293121861 293121863
    0x60e0615070305072003060603070b04060302090301021312151103060d02010e0904150c0306141c0f21020c030d081008060c120115140f071a0f0105010512040212030403 74
    0x840428170a600f66072a40701c08240520030380407070f480ca903201000c2540d42d440ba0711440041c0d400822080c803450f88260014828200e0140016260003815035029900c0c800c20b40c4268828202c1d049a0380c00c000030700b9100b00c0d0107000c81c0c20912540c00e005035020601c1c4400742c082881141601000d104690003001e5003055100000c16032102d919103801d200302e100700c0c0007820f5403029240c400c0c0041d903240244601004d4841c0b10003101203030440c030700c2400901134100491001041e4108089000100b44040b5920898455030301c95200d968000d103c2d50344086901862015900424101001520009403040303030400035143c614452345440c0d480d040d40b1000364010480745d004d100c2c10011b103401054010125812010b20501182e80e88038542941c450300501408009203030415100143c41c100e5002c0c2c1003000350080d4442c640301141c0d0360402088040901c1206006032081000403841510380060300400003030921528095035541c0c59120540f00520080c031807010036402440100080060710059 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 293124361 1250 293123111 293123123
    0x3200f13060603111317150711070f080307060b0a050d050c1f02060f04060b0607030314090c0a0302061b12030109050601140f0307030e190501060e061507030507 71
    0x30211104501424190103068042420280403c10340000b1070122a035240303030004034480c2139042000d8004000c203900300d003902500c1130407020b01c4424099043e0600486640d201c80c4200285080c01d42d081c400b140c0d100c03480c800b51001041003000b4021045814056002800042e02035400c0f002410001480d0005908203804241c88410801c001403c03407030700b0b441110202c079041e4103201015450841a03d610340117070404d0010a45001462100c260001d02c01d08010a00446190102e00709030001172058002949074081000000d81044006400c20301131405041510b0200020030000401c0d88002801031200003408030f4000880701503d41d000b80e200003600e409040d40784120344590030038020b00f10154074000c0403500c0380d802030303a0340c0c803405449551f0103041c1190711401c3c1d4080d801c020454818540c50310507100c1c8440c02400513a0320302800c06640c1c0b40d0382540d810410308650107908400d60f00011501402031a6854003103031150500d510603d1961540c90345005c803840c7c0195a4001d1070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 293125611 1250 293124361 293124379
    0x10908030109091b06020a080706020d150915050a2102030d080415020a0206041e1403030a1401030203030f0f0d05040804060311181005090a091b050403200f 69
    0x80c2d542c2e00254030b101c0c001c80754290418144510909584050300c0703074102592201c100c200008448002800000c1e0040200606045e00420702109503405c801940e0086518800c050100140d503100d180e4401b050602410001410700d00400d42195640c019600003400c004100020100e002c462001e0307240d40a401d81e5200d0f00c000b40007501c41c0d07000307440c225420f1400e664404161115442600d149070700c26801403205848544a00300004c0c8141511007030000c10310740c8840420720300800c45e1501412880210f03502d1810340ea0080403601d0102140c035504c4094070040026130350010035149040310100303150f0b90320f9908250f80405c81c42460404c502c52401d0500700420301160314060700c1160178030340382840158400700b00707000c191044041080c944a0740109440960410280c40b15019800d400c0861400e911013002495141c400c3d40100811500d40280303001d191070403001410200c596080141c1024103556a044801b04413901d040c01e00541f40c0b00500b007645e40c4881c224000f44018040e100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 293126861 1250 293125611 293125619
    0x70b0f04030c0816050f13020c1e070e010506030901060f060207061202031e06032a040c080c07080f0403021003020d110f0702011103070b180c012f0109080301 70
    0x2600303821038402a90120807042d00014400d0703002c1142c038601450403401da01c40360708190411451403040714001d5082110080080e00b0082c0620040100d600004000d040c840080a440d140c0348100c500d1001c60f64102c00c00410002c035485081c0d41c15980103c440301d4980c4d4443c0b034414010052580000d814102c080380000704a41c0114041043e50f0141c0e846201100d000042e1405a11081d01d00c4450741484164807610404481606504150300070282c404106281c81c80d001c03861041c00fa4003080f007d4400d58440240f41500c0f54032000c50b41810121600d250250010f241c1d402400e5028062800010740a41310801d50302c1110040e680c014203030010f8520310000180290803c8070540707052403a2551100f8800d03584000d9984101880e01c11515100ca581e00440d0b900036919071610362441305000d8100000d0300013010b030748940c0880120810304982c3d070310950300e080310301c1450a050201c00810f01407030a408001c400266081100c1d00000241e0804d9000e004015001016010910202c0041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 293128111 1250 293126861 293126887
    0xf01090c030b090d08070e01090905010609080705040b03030901120605030d030516020705060a030b0a0e04050a03140a120506030307050a03201c031e02030c04170a1211070b 76
    0x80d00380c0e401410300c0945503032012501c5036952490403050011402e900001401a4420085460030390018074203100d840b40d80c1d405c02400d450702030b040079010460500060007603500c2081410300400c4102c9040c410080c003440400e0301d0388110760080b8100182005d00c0c2188a103980c01a00c0100405811104000e1140740028000d240039601b03022001681c203544942607100044240c20303540000c02c400c0c0b8151441c01c060740106030031608282c111154140c00245817440f484003510445c02080a04003c0c911450018030608404401c09040c00c0d05005601ca00e552040c882c40348034191400005450321a50300003441d5000f0f03880002e0182c820612202c0c10554400303c81c2412185059805080e8200a584252619500c0c0b041c1c7d013820309017601034102c0c540b10b90840181c21941c1c03108404401d01143c00e5000f0f81e80102d428960b1030030300080822003a10b00003851403203920003002030004001d09948800204075200d4088040044801044441c14014081440242120f000881c2e550400c01d2100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 293129361 1250 293128111 293128133
    0x207020d021c080a03092003070501030e070b0706060305010c18030f03030605030102190f0c050619091202060714030402030318040f02040303020f0c0a0602071208040302060406050702150901020a140f0109 90
    0x111f40c400c101d00c2000030303009005104110b90700c0c07004021700b11450030400110014400340441c6042e80c803806c2d200141c00010b03503008100361401050081034131821405c4c03984c25600004419420081115804048040380341006015a5880400c0c000c1d2200c0c0c5080440103484280c01c000c0d49540700103961400450010340c150030358481c6071104080ca2044000c25101400d448130003811503000500000c54003131110402186040980c4000160340c1c44549807003c101c0c003a1841580035074044000d1007500c43d0800c1c03e0a00c110003000055166113031030ba0209840b0f000e074110011385201c01c1c21b0959a503a8840d048501442c0c2100c2d8215101c0b9903c1c10000e5031002100703011170050040303614081c05414800d44070781c00d5607e83e0300100084d9103000440c00c4201007480342581c200794140030200c01070307135220000c000411089e5542500c075881070041000c3c1030f001458005100008011214940e40c000c01c907000ca040c0c010001c0410440da10710740e18200048202007809551a048528003000300c403c00c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 293130611 1250 293129361 293129363
    0x31603030c21050a0f0c0203070f06110c0a05010e070f030803130813090f0b1c050c04060e0916032a2c09070303090311030a061b030b03010207020d021c080a0309 71
    0x2d00040050f0b0717000504031101d04510100507001005060045000d232000b6018245c411600001d60284070b41c210072480d003019200c954207070007042048041c40400d0003000403030035080000e800072034640300b044004160540b100800d69100400050041c00302004441083c43e042101690350703c1d640c40150305009002e009083c03015103042a200000351440c81313155007000003c1c00c908030100c56202804079801015008461a2003841c01450301e90302c450007241c0081c030270715100410078100100000d00300903103610000d600f080c003c2001c20100f030305503031887c0c006880b13030a03070f089c4941201039a039454842641182e41c1341c0c01030440d000c007841c402406d80369400c039041c030000849403a442c50440e00d80b40548005800500219410f1000c103458520341100c054004044940d045220703070750710003600c0360b0b10200c0d8102001482150801c50305806030a121400480c02185044241d0b8001030308421415030103800342c203895031031080711a41c20b0700c0c0031107094001c0c10854031042c041c40010301800300d00c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 293131861 1250 293130611 293130631
    0x11011a1201091502070206070f12030c0509010207090c03022104030905061809070c02030d0206040201020c15031f08060a060f0e060303120603010209101808031603030c2105 76
    0x10300c00010581072050301c000590024024030108180500000030790031505050703901c5181040814000b546a0602c14140c44c42008802400c2850b82400750031265010440f20900904124131103040c0c0e404a100c8c01600c255200000d501d00103c80200d000303008183e101c003104610110101a0b02a1240f40540702c3c9200c2d0740d60144042c0c90b20284802402011554a420404414081054502588071640c04002407818010401c0303d030300042e00d480162511400942c020300140015940d040c0184408008241d0302c00808901e186461201c40c80700600055035800b0a000180045101c000400c0007030408808a500c10f0404080a000070510380c4a000309281c240c9a001400703040a501d92071081c80d0040c060750408610721601c85803030000510413589558200983c0100f9030b1407842100b02850540d407000ca01d049141401840096603400c5080260300034000481e121400c1c01c40f540800b0792600e00401d50a11640702511440201040c0e0ba401072441a280400b042141c0c0c400c92045184030307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 293133111 1250 293131861 293131879
    0x913060b0d0609050705040209011421040b0702060f1618170f0105070306030803061e0a0b04060810080d0c0f12030e011a0603010909150504060b1801060905040c11011a 74
    0x1001f0001240705520b41e4030301040c10000d03029082440395003e0030740d01c03070162010580d9050301203910f0603e0a040b035044880030110070a00c12030700e5040100070350290400e01021000d08100350148140c51910380208108000781308070f04800002c03403010100078801c042042d200c2c00480c03c070103034440e816100c002400c0d618080006509510038000c81040300c0e009002c2514680700c2030184485000300444242e00d01c40c1d20700141c0d030140c03a2012603800828240d41083d440e982032100040ca101000703400c4840c0c001428500740040380001c0740c40980c1010f5401c0c9412000d00030320f03010300898812100a4090300c0030201d0021b4594040d0006c0c04980b4504008012950100011540e40034003502c0c0507030085400e100502c03401c10b00f6400303a401140140b51703030b09410203818030386da0554504840881d04251141d40c4c2c2e4101d414040001d00d03d0328180070a2842a6040c1b25004044144a2040a00c00c503222008140d10f00e025404112040280400034003820840c4076007c01800303440603840d07025850031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 293134361 1250 293133111 293133119
    0x50907080402060307111f06080d0e030c0609010210060312080610021b0609090901060f0b0403120810120309031202010c0804020402130e01120b06010c020913060b0d06090507 77
    0x3459999100399801008942180c4650104803060310391548580e2181c41640c040100d00c606001c28420402c005800100c0d055003021102424a1100d4082006002003102140240d54002c00c5130a02c007903041e2045601c8819500040703182075804900205507a181c042d000c070502c990540b0381058441c998070f42c0406074852400f0b11140c14844403180f00180c004410541c45040b40c03440a4045000c010070341803c01c03c54200141b88050169009509a9904c41d010031080c000a80b58800900284805904081c5141c1b207440f101554400c04100300600f4900089040c50b100300e408000d05401c0c02054920580341ca005403400b280d5003c10388030404510003005065205008018a07641c03e81d0f5900b4558885509100281d08503203a00310411103224804600e80100729020382c002c1100c401030004071a041d00b00980f52210190005041125240142e00035840b030340350302500074000c0350110038940c0031414900010a0300300c0f0826842005190000180800d9402040c4130340d00840c29100e0075030755 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 293135611 1250 293134361 293134367
    0x8040e0109020322230f010614040b0604050303250606080c01031116030c0503070605131401050705071103070302060a050d05090105090a0311010e010603030c0b0601030501050105030c13080a0c050907 88
    0x20078500200f211101c503903411416178105081c603214000160441d648161004210346c25100590461000303030003c0100c0c081c4c10300e07160003000301080c41544c07414071301810302c030109899200311030042180c400c0006054003001000e00031300c009203400c848204075042d180da17002620313044600c4501c0e00007414801204640c280b55022070b0340180c00e008079184c0140b002c1e45d040e01c141c682e2000940d030320701003884048040f958074019580f0821006a280001f12110f142c04a841c0d0704078035840310b841c0e242c4000c0021513034100003183c8880340c00c4202800c2042c40c0c80002490862a5080207400c0751000c544907034560340003005030240c0056000240101d989150103582210411a4000740980c007604015000c00d0040c0b00040710f2100c503c00205180600f55041c03400e6402c00d0b44118009009400741d0810321003e401040c0d00030400340303000e025a52400300020014040644000340c1c50700000340c0c0c254118154000d010003410070109481024001d4104000004028401c182c0201204030006100500c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 293136861 1250 293135611 293135671
    0xb0901081011070f03021e12030117010f06090209011b05060601030c090e0f4305070209010b0306040501151b2301050405010e0a081608040e01090203 66
    0xc0e8680284007400010100754058624515010421042008180042403051164000f62800b0350000c110840c20405050340094400c1c44c584881c3c2c00054000b00d81005080c1168112010207105480241c0d00c021070f0390041c49100480c1c82c00740e141c040d0018589020341c020300f4600c0d01c2601e8141340022008207a0242c110b50860041290300b0110001d086580a907001c0400708220b4580808016100c004401380c1000039244203410072040d00030440e00c07800c0841091080300d502805406040007601d11071001c00368102e185090002c0f1409031401151107a8140c600e05900104011001d583d035002c01c103116031055610500450408002140c040011040f80c0c908804a1b0343d0038a1001c2044003801c050b08102904036009002c10050100d803a20a40706090403403014400002c2500b498a44982180d4800b08001c640d80c0120440101003500c6100341c5074000303d5541e40080800079864070340260b00c104d420107031001e0074000020640b1351003640514030400070f88403005a540305502c26000d080da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 293138111 1250 293136861 293136869
    0x5030c0103060608130807080310082b08040203010f0f0204031101030501030305070b0a021606050f1014240703020d0e03071a1b010c0315051522080a0605010303030b0901 75
    0x84e0f1004c040f45408010b0889000c40d14007542d206401c0c00a0b0341e403802c04690007030b24030440481c102038082c0044e00003485810140c0440080740c1d100c201030a0401d03c2d1900180c802c00052044000005040d03460070341101d421058102403c02c90715414402100c001d40140c0410b40d000107014100f800b0319400381c45003034180c0b501612801d00b17044083d6900816410000c3c4060181074080c0050720009005041038002e66200301d202140500e002e005800c641e01e00100000300700d8426880802400b244184113030518001030341c295a004900f80c048940380c03400380c0d14050041ca800250034043c10b5001c00d41c403154082030fa6942c01000c0b00304081507620a100d0244862001c0d91502803015501840001d10355500000e44082d080d20704e0142003400c40c1c422055140101e031300d44845000040c250104000540412252241003600342c111030000d41c084c3d40c02c07410742000305100900101201c1500c0800410350032040314a220704a02c1c012014090a10048000c2400e040c0f4400ca5803820b84025411b072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 293139361 1250 293138111 293138117
    0x50f0a03020303130f0f39150201020408060f010303020708010c0e040905010e0714040c050f090f150f0a0f0c111003090b040602030103172d040509090705030c01030606 74
    0x561076000c0c0001d0342110042c801c50717258030315580340702c0010a400307058000c0c2c9014082d503840c913403e602841c0075500080510320f10300ea1213083d880c038214094a9584401c0d2580440c9448a2117011a4144c0c02403040e40c000f034200740300d14001c11802105815a4030f040e203111741d0a0f5038804e984d85070f015003a10003000000010801300c1407417a103581810303440103030003c1c002d0002041c4480c0c012412418000f15410020700c10141e07400c0d9291790700305030040702070361040b92070624681584103600003000d0041540300c9214109000d0119065075440214054440e1031f40e03e180e5031452051400b11243c2e00041701100418030850305910040d00070700c140c0c0000e03030f0058641e4500480030010860321401442c110b405060b034900c200004540300e56003440c4921f114240059495040d414840d00060000184504160041041c44248400003002086104006580c0c04500d030b04003045a916015a80000740c004802e281008000e240c000b9481045403816016101c81d80106001101a50414007500d004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 293140611 1250 293139361 293139367
    0x14040506060607032f0c030d0206010504020f21090106090606171b0a09050a050904080d0c09090e031201050907092105030708040f0e01030b040209070e040f09050f0a030203 76
    0x728100301000f042c40d40c0c42490f14600d200e030303242601d010b1180d0000107843e01650000b1400e5070307808104082c80c15000e080340101030540360311300000d68400c0140036060040f5004250380701c0c0c045201055580280440310f284080c10001070079402142c0b0100d840407003542c207201000940c0300c0984100010b55180c0d40d501003680b0748450691981c1040030b80500c1c1700c03008d0155501c4000501102805100c2c0180e55032142092600b010806e110515402070317441030f5142c00c14880000c0c82c20080391074441420001191203815070740c5c00c0c0e03843d210a900805c40507040054241c00014080014540401802d02001042e45ca4100f48410070404071b0b045400f1801601040c880e14404a9002c80403080601d01207509a910b40e039450308540112400319001e06000c5000d100440c840b0411901514162001c401035615685900e625290003601c003074054132019000c244107030711960035a105201c02400900010180c80c1d910b600400c403100b0180c400d8026190302c02d510210220303000c1000d58040e8001c0d41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 293141861 1250 293140611 293140621
    0x412020907020a050615091f1707030b04030c2303032202060d0507080c0c0706030c02032701030e06060d02010e1f2c090106080606040b0f03010302010314040506 71
    0xa039a20281100c800d520850b18042c000620400242c1d210b00007008140d020303400440d00384691580e01924a1103548401d0020340540c1ca81c0844407000c903003a890f103034545014650096410b210042d0000b40c810301840e400c01c070074181c100e00104c0c1002d1146c2d26070f102240085081c1c204403c1c1500c0109072640003000031404140c1a815056401c8080080d50b0303100307030707801e07800540302d80d1165030600702454032001084007440c2c000440c240e001c207030803001c280713828041c941d1035440361054002d010500d6511482801d10328406c00a0303c2c4401c1d5a4488004036400716480c142c00340c001602500c2c006070925610203071003071020851078000d07540030348201d0018803a9401980c51945c07600c00e06410038807900d041070034010341126030914a00f0782c2d1140406030b04000c452407401d100e03010281d4100681001c04088540326640318074111109441c107142251503e90010705144120b0344000d1210744082074a0100c0c004507002181224401d8130104000c0381035031280800c64902b11400f81c00c5411240000c0c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 293143111 1250 293141861 293141869
    0x1002190302163c1b080604020d080f2a03180d031707050901030501062f01060803040308031005010801050306070e010507080301090509162102030c270606041202 71
    0x1039450141d191580001c841007080c2c0020104001c52804900c91500814240100e48401d80c134225142080c1c20011800e11039441e030b48034000b40009008110f6007440006010300b81c0140e444540c4030308800c41c0e48100152104003580085500801c64190540c0030300c0b1050000002c5502000c40100c40d6045d1264600402500d40c0b0b07104019400c0c0114000500e501c80300d012059403103130840d0b444198179141404001422520141c01c404148a42c41d02840c01039030704193309564028030030212166002c51416000d02405a0342d100303a459202c01316002c020003082001175403091442403240c0c048559901d0046495032820f11a8982540090000c13543c60382c0b044501000191060500380d15283d401d60b29801e4a07482603009008003541d603028017250990038031005036407540082c0740a28450a01e49040d8003050b03d1508990034409840380c2a045440500034007017844001000d242c4440c011500c0c4280504112200c4104820420002005d500d441410b59065039510321a100001c810780d8280 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 293144361 1250 293143111 293143133
    0x90316020f03030c07170d080705030a02090325080610030321180807151b0e0d120233061513030507051507050607140c100219030216 59
    0x100c0e4043c0010001c4107030280701002000c00514080d030045108090301c24816081c80c85009022040042d0b25043c800c1159010050f6508100d00242c0144d85000400009242c14580801d00110507820b03152502c002a01040b15401c032144002913401998541020001d03030321440c00001c0106115150090350841c180c13880e00000302ca012400120b01007410120800e0034103500301200c65101c0081e6600c10060092401c0c204400d954009000d1510240d09280201111032194010071045209400f819a24500040341c000d0b002100009070800640c8c001f07445590b1f00703c12200c803e6113180507103d0f14030101c000e0a0100091318811940d500c60408100c4110501740c4501069030301400a104d507194101450300c0111301c240020301e1114500380c00d000342c412540326183c0d250b43c03040c000030b000f285011031159806241417810540b00e9441040011450090940d413260501c9144031101411900e94000c3c00c40d40ea03401c1c045880c0e50840c00c81141030344100b601700300215010b1040040028101805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 293145611 1250 293144361 293144389
    0x1f0f09081218100b1c020916020a060906150503030310061d28090b060909070215040b010311040504030509040b01030e0111120906010807030b0a15060e01020609031602 74
    0x4500b1000011490315490001c0da4000c01c001160703500e850900514102402000c8000101401d1a840150360001b07105000020310108009205003800c00c11075200307000c0c0c03c40741a844441000341c0c40e82c6081c00350081c41d2a00c03124640740a2110003241620340001a648161600401503c0540c20100e003100c607800b1803405a05400300440186d81c580e075034410103125511000d007480100d40d607010100c00600310154020380685140c55904130081e252141240c0c07020006442c1100c1503210461708038502045017030a0b04404c01c0c0d250a20040010a800041c12039008002051a08443d03404000442e41c0c107031030003030120701c1c10400d03100141401c0d044200c2c0c029050500040852011a8946c252112000c014100440001c1e040d001e800c00e005120b501310b2300007002090650305062496a403062180800380502518400203007000c100c0b500014910800c0742c4504001c26920035001c0c0c0200c0160b06164050301955002520b112000402d0340c80c0c014a80c07203601900686c5400348240303240c107450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 293146861 1250 293145611 293145631
    0x90d0308040c300614010303030212010e01060f080613022101060e01080109150e090c0301181e080903120a08060d17130b040b03040c0602010203010f1403010e1f0f090812 75
    0x1a80514821011740c68000c41c0070781c4002da6a80700b40040f07070b1100001600702d030703000281039401800074561080c1706050222441c201048161580800145030985032006908030600001e41040000000410082d044215443d101c420782d0301d9090546c4d2003004044081d00065400c40108401183d03a000402c001004101b004070040e1030b02d103a02c1d810321b0200c5108540303500070707000b80d00c16007424400d524101e510090307524040400c982d140402010500580a8403901a641410510070303040c0c2124050740c1e0007403c8034a92038541030b8120070b42c0c02c8107200c4d40110708540001000c3c3c1c28031040041c1135a03808907400700d4500b1610200d4440d50804004013000300c601c04c01c0418451442002000508004078a158903440c02d813a00e5a40c0344010707009202164010300c0100100110300c004001980d11a00c5080c065050090201c2c1c012300300c1d461820038911440300d084043e69650b010a03003074004404014004e00c900c0041e0300003643d102800090040d481007002440c8841c4564001e90810b025031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 293148111 1250 293146861 293146871
    0x6130f060b13140702300f1908010609050118091d0105090c150a050f090f040203040b0f0604110d02090604120302030a021b060d0e03090d0308040c3006 67
    0x5840c00e0304884110b88980c0004080d01c3c10701c41d1258040160341020201c1d054034800103034043d100d100d001c81902c0603e4550920100700840c18162800c00d4980740d500701c00030b542d0340205000c0c0050428100380f24060100e4410a07020449500c900030b8000c0d9a403000c60024003041c9880101001010801c151704841052030f10b510600003000e01900d030040e0800341c0148403114809040107802d0040e1003084000510030050404284d4100b0141c0700c4003a00d641080c1e44031207a62002c01c004040b03515480e0b9119100104000410401c04081800b41304003042c401d800d65103c900740000c6445004240070b02107020701544200c100e040d0000c0014400142050741010380d65000213200303000e074000440261300003040103644140e0402c0490400c5844820b00309140e0040c2011035140d04c140b034007590710280c840c80c1101c507580080085072000315001e410401407502a00f401029245c00390350441d9003034134440c0300003100c0703003240180b56080d002000c101c0120b00d855a032516050061010407034446441d6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 293149361 1250 293148111 293148139
    0xe060d121121040f12020102060703230403030f06080120030406060302030a0c091b09060c02150316090806040206040506030919150c020a0320010f050c0a0206130f060b 74
    0x1006054900c030004002e80d2250700b412040344140e04180c001011240500e00c0c40e1000d81e0b03002070040d4002146050020700306a41c0542e4881d4000400c0554990180341020310040540c0356005080b02c10a100c002c10910381c90350460707402c0e2001002a42c900400c214000c44090b0f821000643d0058070442000980d55644d9010a05051506c1000d82e80c00d41c01e0303017082140b0070180c000d0803000d940100d401c1040340040b200103081941280203180401900969034411500c8180405100900b54a102d584a01d00000c0b03600701d00c2c0e081d404200020310070510024a4890001e41c4c41d00a5500401d0503090074144406c0c0103c0d600002c1150358030384100000000405c0b000085000d0742c600880404081e0065004820300303880c0800d0140342150b1021041c00e000c01d0340883c2003086d40d01c1544030300d800300c1030450105014108050840031064601014001442111070041100801c180c0940d081d47c1c1d60b103030a05c42202e1140c2400380400801525420014000382e01801074200001d010881c000c7c21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 293150611 1250 293149361 293149393
    0x2307020604030503180a051902100c05060408030901092a1d2a0418060e06030a020f0402130f0512070b031605070b0708060a1514030703110c070e060d1211 68
    0x2204000625001c070230400029070400c0c190030f00e190540b50404056000c4603654055403550001d0025141010120124034a44000c0d042035003e150059100d141221020340e40568101c2065601c5480b0410240b00041030501c0d0b40c110040103840c4004610540e0766820702c03401507800d1961107031301c600601c610140315160850240028099030503007203c1160410103150304a4160741c01c003801e20900c03a4104400c6542c0041d81a000c00da040d201ea88812a500300800d02130700612604030304031031041a010032140c8904051300c5c11103e0803100500901c100c00600d0352254064011030180da041003000400d149200920500d40309030038030f4444e103451425240e240a86800ba1204000144158180f1003149040020003001e0007203515461442011488050504006002618200800800040c2215000340c1c0591152a65130f00d55a030f640308000c98854840c0054010f404018103e1400314100381001250398600a501017130689000200302c00580d251508403207819903910407480d000e44401c1c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 293151861 1250 293150611 293150623
    0x31209080a120e011d0d020f15030405010f0204050a060c0305040306020412020f040c051204080d05010e0a050f010b1209011e09020306011a0912030705012307020604030503180a05 79
    0x40580054181081c0c003040090148049a000030304100c5c490074178580707a4400b00080d804098003190040280140d910100d800c5543c44100142d001104984508448100d50025031089118070020856000400c0d0440220b000d18002c0c103800480902c41406840d0164400c0700c0018082d041480c05c0a03504da0b1404283c2c1d0164103e03d22540b007004202e42141403031640310103002400c035030501c522404198003c09901030010300110a403104408107080c00402d00c2294035900c0114400d21680da1520703480d5103200010340383c8818103840d040000d800c40001c0107095040c2c4039003c61852070700d10000f4002e00e09071000340480d54207542c1c8043d8004202c1c5045405041d00d0301000700400e4011580c0109402c001c01680305107a05c495440c090b06000399008115400c0b01030483c0c1d0544084c024620a07441e600800318014802c3d03280003075420b48605085002e0400d80780105420940390f90b000d0f0101d803502000c1e600100411414400701d031030b4050540654424404110460f5102541a101d2500d484 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 293153111 1250 293151861 293151863
    0x241b0f0f2203030f030615031d0d0c0308160e01030c031b02070602151027020d1a01110d031a0306040c0e01050913030e06040308030f070225031209080a 67
    0x800c041c20104101500b05203c101d81c03c2c1d4a09040001500d8001084c49006596420404056607800802d80342e444402030b00c49000355500c00c498098480700005884403003001421780100340700f0000508200e09120f0b0004c207220b280d41e980f03105c021070103005401070000c0000103001c0c544c49000d026240785498403542e081c640706900078540c036480c04001a04140d0b04c0c1003440d140b05035840400070b00b11075121a0104031032611800010500d2050902c2e00209504007402c061a400040d41c074005c5001604060b032506490400003030000f0b80e550041d80c02c180c212101c82000d41245412a681740c0c00390713100c200d040c3c030052503402ca4825580d00103402e104003103508850007003e608042c88801094400c250141c0400c0e07801043e00d080c181c090009600c01c0311002410010b00b42c60301c840c2a200d010590f001154003484003030b100d0406445868114900f11a050010700c240c0354440e0064a0200090001c0d18014a00600d07a40c00c64072641007131920000300d01c0034081507500006180808100b100515 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 293154361 1250 293153111 293153167
    0x2031815070806030f060c09040e0d050403020f1804030809030d090602130e011a0c10020d021903020301060c060b060c060f1f15051b241b0f0f 63
    0x41e1405007405442c60b58060030942c0664410f20001c0c00d0510000f40f26074104094060580c1c483c0c105e2000940600407101d0509807038000c40c20040d0a040d0000b02034016244211541c06c00700110300f06001601403c11540ba400b10304d150081000329020f0302002e038100004e00c090700d244c8500120310100b501c03000101100d14070707030001c1d0b07406105503142c42c0e003405000016084e00095241100302a0041c0b158140d00443d90700c00180040c203100304010507440720010f0382040d91070745a070300780c410029000122400c030542602c0d1601070040d8420310880741033340d0107500c0d01c041e508a15294503005201e4008201d030845801c00c0707298500070301003042c1403280b14a4070341c4040a07d0403291604000000c81101c100895102d0824065280760550f14080120b46240803034403460141d14441d01d850181982c84041c1c059659450107244013071000c40214840c1000c1c0007030549400001c581000503c0c00440318451091180c41c180f4410f40c0d0040203c0c100c1030107104c0c20510303924040303521600c07031101c10760388 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 293155611 1250 293154361 293154403
    0x6070c0504020f0a090b0901020304030b1515091e090a0209041814070b030411130b130c20030f160c120201030b06030f01090e1f0b0f030f0709020318 66
    0xa0142d211031464050110b1921040c1030110080009c1d540e40194040144205511030001c0d0038808011b0710001c0c08640100103c001410800040b00d00b43d11045002d401030610104508181c181114184440c1d44043d010079203681c1c4202c074950094100e001000e0344540c0310304010301107028055403040c45078010b13407038441423900300364110b407504036150b1090440040600412021980d5541005121001502c68a0762400a8840c0100804490440d641d0050f84545411504071456104114104003034850030b65861100d4010852010085403460b0030358070400102d400704a490001d40b490000207015403804140507620609002020f0f0088200c00c4200540d9805540c0d0501401c1c0e5003a03016100c0c02d00e58100007003c80f00d000414010308400b90f858094401c07868000300400d80aa000c08008c0a040c1d6481000b600c011b01400300106224128040410040e46008079800408168500041c0340c2d15150803000400782d00003c0c080800407150f44002d8120080600c50845101c400e0b0030b81400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 293156861 1250 293155611 293155627
    0x3011502160e27061e09030306090a090602030411120703020f1203090a08010212060a1202041d10050906010f0b072d0501090209010b040f122d03080906040308010506070c0504020f 79
    0x3e205911010021721003200e40d420320480000c0402203a03040074040d5003c000c03d0b605c098140020b8041c640c40105190710000030001800094100b20700c1001c811149100190071440c02240e83d45034601005c0d40c0507990604940a602c0c1c40c0d9a81081548900203580c00c010084000580b00d0b103c680c0071060701e94002880c3d4068040c248611684800201e80100304d283c01c105012a0007514070b03000a000315517030700e02a180c0815450320480d1014000e802c07141d4414043c5008c40180c076080d5030102d003901c103d0f40041125000782001d00262281001914149441620340e908200703e120021000c42420040c2e680398003801518415005025000205480000b4414003090070816444040019400e00c82072002001c000b088078125a8460b2050368500805e0415030492000121220910052100e500e40840c40082d1583c031801d00030b440301c10143e070b14030448503241c1000311002070001e0941700042c000c600d801c0024181450080c54a002a02d0711000840d049a00c0308014942c0c9042c0460f03a10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 293158111 1250 293156861 293156881
    0x105161217011d041401060306180c0503010501030f02011d090c030f1303120f0f050f07080c030403050403030804291f08030306041e06030803011502160e2706 70
    0xd004090314a04002c60380c45105140c0001140038000170110b46842042050b60705094010030091504140d00704407019107000d9042900454210480f410712005000065918040c0308540c1202e03001161940d00d0b01c142e44c01145c2d00088055210500710080c010a455a160a03d501e841421110342e1540daa04102d1191100c01400403d40d00700580209400400079510050010740d4406107100440c190380f003201c0709000342500d1407a1382200f40c03800c41085130b00e8090018150041c48591a86007454031002c000e41e546101c1120080c021840c20041040080d00c03948030f6035401400307541140010f0120741c613802c40100b00d5002c1c00307020202c41014406030000c0d16100100b8040107055a500c1c0629007100b483c4c60b4040202003902c15a034403c49000c800c41000c2201da040100d07518204074854507442c103d00e25810a0050041d1070100454034032030540001038a84030b0750b1020003004042440c0051400d09240028119000045c1140a075004040110040138086442e14060001c44c40c02030b00f00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 293159361 1250 293158111 293158157
    0xf040c14010e010302181c020f09150d1a0a0914150c0903030c10060329130201030e010f05040b06010512160504050a0308070201032901051612 63
    0xc0140041103004100103680c000e0455041d00400782005611070301140c2c00b400e089160301d00d040390000351000c81c142c4055000c18038220040c0c170888000f035281c1c581d4802d20410780e0049910303a02c0380c1c0c012140d246031490300e0b4420f2212903205100401d0641ca80c00344684603101c060320101e4403a51690728007010084900d0382da003071502400009004100c03503104100824040500051381200c80000c00e414a03403402d00881b000c0c0d000c040100c409031545000f0070b0000780711a03c03046d80c5601c1c003c00c1c0c44802c1510702401c0b400446501000000c0e58480106c0182c2004a13501c0403814140d880b84a807601d0310080c0030b03039030390130b03c135104005024505801e1003040366000905160411004200c0e90894034004200182c101d52150003a0f1552038000d4400d840500c2140c0003540d0013401100004200b141d8080103104d0b99200303a9050020102403d41d07041c9482c3c514050318a80903003100c50300950b5200e40c002c0c04220b448170380600e50000d480c1c3c44105503100303031a100c01d0000c2c1c101050040008940401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 293160611 1250 293159361 293159369
    0x80405010c020309010e040e0f1e010c030c14090406050a090204090e01050402030d0c081315120b01020309040f02040b03090c01021e0c060f12091c051c05130b0f040c 73
    0x610b01c3c0c0313100c0c880000c3c0141408410944505c1d5035083c402d070600b034100f0024180b038400d40100d0701c12203107450003d00d120308841c03a1501030358207160400100354805d014a01401441c2d4480e00340290100117400041c1d0001c0d81d1b0242c02c030740c3e079500005d050340c0ca02d0641c90007446106001641c990500c9a140b0075215902e40f20001603040c04107000040c0c80000301c02138184580e01e400c48442000c0d01d486030345032084c08102c040120940d403010401044100400d0025508e0392680717243d030035a0f887c1c0300301a0740c0400c1d00d140c05a0414042070b851410290884103440d41041c03001407030540c03902d24030b02c107680058960031401e50003103c0f80150365804000d611154210f030f240e2295207060301d00001b69500b102c2c407a11401000041428168015104169a151001340c05541801d2604900d810742d51280b60f007481040000c0642c648940314080d03412110f02080c10340d07007150442e03400354001c0d01802024003840112007102c10f002010405064802d40680e41d51034401c2e0050500c0d06100d42c664610f40c02c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 293161861 1250 293160611 293160613
    0x2506050f21190b03160e0c07060e030322050a060506010908011515082202130914070b0a0203040b07020a03080406020c0109090c0c0308090120220e0c1315080405010c02 74
    0x1744442d4070841106400440c5e412219001290b07503400d00c026140c0c014418018074050612054144844001c00518455480c2c039400c54040d402501e480c00075103000d90409016a00174148031b030007003142034014030382c00981810a1030226554016441c01c448a00c0450480c68911601c184003204260290640c107002508e81040ba0741040910040c80700070201c1d00e0301f03982411240610454482d1042141003107070f01d640400030480c050130620381c018111600a400c0e400307003000c04a0303540c50f0842a14612480c0d64025803d190070604a60600d0b40f0950050364000d04081d80040003403079420050019041d0b943c050300400000790009807030a801c0c0d800240841d4180399a4213507183e4030043d402400d58041c40e249500703072180888076005002900d40900007103000600c81c42103103580c80042c2401468240c000250058400d0402d800720001d0103020200c02c0e81c44080b400d6012100040e00350414099140e00013550b541c05200005580144e95034081a0000104801c1c49028400c500031000c541c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 293163111 1250 293161861 293161873
    0x40b0a1d0c0415030b0312120702060f1003030305060a09050103120305070905102001060f0302090c0c0606060c030c0304060c020f030a020907111606022506050f21190b03 75
    0x38072501070a43d40c65001000301540c0b030031a16125502040541c04c0c0a400301c212666074000311b0090311f2280000c651110151003948041080101c94411243c41101c8d41c802c07004c18503040da0b9044010b00f40250019511000314400841d141c00b085c80b43d18029482001c01641143d880c20b00038081d01c02c020070007028406121000c0140d6101d500113a07518403c0e51400e111006d035200d41c140c50101102d030208000e03629041011508101c002c840f5015280201d80008080d03840d04401c40c924071888a4008a9800200c0440c14504054014040740e0811f841070fa41000c2d4025106413854125520900021390701421001c1941429070380c0480d40312050380030f4840e032501600400ca040901030324060802c10904914070080c00140545142466886590480b090f0740d440000d643e41c10000c00405115040078401c4034081c450038980c02258815200c260815072258403c100b1900b200a05455240e040000348054070303280c1c0056031007400c144c002d030f032401000b8404200c1201c043c8160303036011750710074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 293164361 1250 293163111 293163119
    0x60801050d080d020c120d1104051311220501200c10020c04020c01050403030e19110111011506020d09051f0306050330090906010c02040b0a1d0c04 65
    0x6101c019034496040002c0940c0c502d0509501c100900c00d0454440d910300901c20850203049014000b81000b5041800c14464448440300e81b141a20407817149a03444028000d013020341604507080040181c500d869038900303181c480c003c076242d1070783c90071111408000144030902245d07030004113884548011079030140f045807100c4800c40d42e600c20b004009100c1e90042e0800c0241c0f80c400c00c0480700c610009070041d074540601c11a142d01070002610100d01080c10426205184240002d0030050461003441001c6800780d1600c0300c100c880e50130b403a00c90400c0110680011640000d0085074000f04105030109100b502d00030000341098900010b0008200f0001c1041115944407445140500300b6100141d05480b507104041e001071405070f200700e4150240407a41c3c410b045d1500421200d407090044060075200c810000c00341c661054404035035011b6110404181c1e294450300710305050620117480024081505030010705400000e030700400292034440c2c0d00241070343c071003003c180c0c00010840c1014140343c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 293165467 1106 293164361 293164369
    0x140108010b010f021b0402040f031a180a0b131b033003050603100509010b130c0509010c051501030311010e06070912030207150503060a06080105 64
    0x107055240d40c22540208082403030100e8541c044c1c414808005c103c0b00f5503184080405420070307800c0c0408245807295049440103507010b14030005018425900100034400d004100324544540312031598000540020480c805603401201003420b87e841107a010945680c032040545207910700e0319220105a0207040c10320959025039082189840e1054010070802c01644804440380b46201d0703200b2038281b081c0d10440d0005001400d0311304080e25580e014003075450560700e42401d0f942d502010001450000800b001c440c401c21030520064100c40c1c0c1c060881d026000c40c450501651140e0141000010301c010b07501e100004d00008119612410001e1204050110009681d8038110014030321407030005000344180307080d0f038a000c2000e0511000c2d405d41d0042c250100d0641c0729410001c80e07004094164811400300075a159922882e205040010310441a03000c2c0050016400040c441c5480d = true := by decide +kernel

theorem cover : BRFrame.Cov 292985611 293165467 := by
  have h0 := BRFrame.cov_init 292985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 292985611 ≤ n) (h2 : n < 293165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
