-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1478
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:10:40.398271+00:00
-- url     : https://prove2.me/submissions/15806525-a565-4845-80e3-fe77266fb139

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 265647482 ≤ n < 265827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 265648732 1250 265647482 265647517
    0x609060f030906090d02030d020a03060504060602010b0316120305030613060312090506040f0b0a0e3a030e010507140607080115020601060203040504020904020d020a0908070801020703020d0806040e0d05 89
    0x82d0050b02240b0016040380c83c0d0000c6081232042408040030f034115002036010075035140000511035445018443c020300707164000042034001c14051600f4156404982190b40340c541e0010029a014031128601c0150076213442511b9485100009282d6485068010751103800c0007404014001000d004c1401c047c1a41c8801034120307134440c01d04c035140c0510300c610303507500a429604000c08a43e0000810f994130143c0b4018103100c07251800501c0324100941e013080c84891751185100e980b2001401011010503d1a142107101074958004101c00b418007003403410440089620420001c00ca8000940e0300400d0098510390301e0081001420490f003403243c48500042080918041d1b400807440358141e4106a0286280505080600000c3d500040416820075401c03c50550710985a03c064402021f090b40c80490343c0c3e181440492610681d45c004c45800d0344108140c00c0060f80010b21000000d0950400c41511790720140018010510010b074404940144d00703000c80b10580c450010004034450704103022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 265649982 1250 265648732 265648741
    0x4031406090f06070806011b02090408031609030209060f130c02030307080c07020306041101050f0f0310060203041409040f0f03030b030609070f09150b04030501061d240609060f030906 81
    0x29a90001564104040717824100030680e194070800c00307011200b8500c0c101800e12803055000c01c0c030a900403901501c20020100074040d00041111005002c0390706450254502415500095003c40c4040d000da48205c03000c01d04960325480d031001d0280c0d52815460200080101d1080281d12940304032030490014840c0c800145d0b10150800c191015150040c0051031320b69280c0d6104051626110300107414004140449110318820500420b070401c02c1d0390341d0b86d0312800c04c0941404003c07611740100003550070501061114602d0741c0020421100100e5121501e46c6650811560400113400040c1080214000241c24141c140c2c01411040005800b200c0b070517500e00d0059522404d1500038800a500140400c0040f02c515410140170064494100d120855a0f00b070480041d07030184d8001c40702651141020020311051000000c2c8000220030300c00402d28181c2001d40000c401080d505c1032a040210340701c1680d44849065a50203000641100c1d99030b284c2040310403040d00111010001d5100e803d0006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 265651232 1250 265649982 265650013
    0x40906030b07050f09010806030f030c0703020f010801060f05030a09021e0f120c0d022710090203152e0c1403070203031911031215010e01120c03020403140609 70
    0x22009000013134a4076081c0206600115402c0c3c00141400e03906114141448881840c10320081918204e82002003851a01c0c0d441170003485009400280d043c03000b03060040050700d0300403240d100103c1e0240781843ea01e82c2c5414446009000c0c0c1364010b0741100142030705484000310075841c00075100c4211605401d040300c51042100d40100542e84000c10b410805a141d010b0a001200700500c81c4002d003800c0951a5801900032914074410620801c4a1401c017440710200b01c0300c1e049000b6020301c2c501540745140091014480707104640c80c06004200d410b030707421250a5220010145082500d458041069041000030200400628240e80c1c4190001d0b1116060340008111014154007502460401b200c5c113542240341003040c0e841d03005002c0c401400440b4600b0500c0148000300c52092290050b06005516000c0d00500c040d105040c0994966038207000ea820161059004405003c0801c5180d02d1580c2200a80120790005141000e400704c42c01c05210b000c10107a104901754030441340c100a648404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 265652482 1250 265651232 265651237
    0x906061e0509060a0e041515030218060d1b0f0e0a030f020114070606081f090b0f09010605120c01170403050301140117150f0a0b030f100b040906030b0705 68
    0x2090216604021544180c1800e202410044d0b0040c203009190011210102e02600d018400c0c0d5225080c03000003d20103070950010840803117085240441c141485022140c0e2921040c010360b51080e0f0000c103801042980303036009003601e40000e01c0c00d4514803840ca400608421017000810000c1a00b40c4104040c50601ca10340500300d03038120f0301e1140900455001515400450382202c0042941040341201045480c05580010000386c8002d100040d1003810350708005001b0400b0b1081d850400d40240c000c5521101c5507600604034540d41120398480711101070040101c1e50140350004010300806042041c0030541a91202c002c1e21594401c40c10200c01c0c12400b4004c5030000c011840500c014400c203041e416912400b6003041c1012803100790104544149150308403000344040c04980001c0c002404c200149071071141041d14028030040c144ac03418202408010001089540c1810000d10603400d880c601d000200104044984d982d40c88040b80300151100d8001541c07a0b0400d680852801c5100c0c504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 265653732 1250 265652482 265652537
    0x10309031b0305070c140103050105040e030d0c031d070f06050c0601090c03020f1614014a0607030b06040b070f060b061804110306030a2307090606 65
    0x503922805404009010a2088080307019020002c05001c510005188161010702402c01d05581c8501000f1a01c0010306403034058100500890510305801c0c0340076070010035102000074404021404040b45a0120003d0a01d502f840540d0360000c0038402d4000b10204070581581c0c2c04010f202180c58990f41c081d0b41610500388601c12035482400100300c2000e05038480018210310b80b03009458985c1c0c0001c2c03155607400c84501e442c40c1040e80d40705d100c00c000020807003c000c10041402888090030201d544081da0740d8800c01c04126640325402043d603030100f650b9101503920403441e42c03000d903c94440741a84c3c030741003281c0c010003007480d00c1c140b50103a1401c1010340b07040395000d20411b850b1407810381e2581322904480c901110f815460712080b803126904d0707001906c0308400b00d200400100c1c14080401c01031b81c01030441d45000307100c20414002e80f900c0104500c801c2070340103409002482e62981c0c50940d444017005080c02603001d541c0001c01c41131483d41003402155950340c2c44c403400960010b0302c5458101c0f00d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 265654982 1250 265653732 265653737
    0x80a09030e150708040e010501110a11060d0e030406031506140702060a02010b031b030c190e04030908030f04150809060f0603120d02030604060f1a07020f10080105030c01030903 78
    0x2510025a00d040800000003580d030080d414240185a03513003401982268000c1c540c2849580c0050240e035070700040070650968441d00918407130200307480300040403a240600c540a06c1c000a0341c1c01e080091a00b00c80c82c18081e0301d040703039903440c0d5906008000700030041c1045420b0092078030010301780c1d2050255280240785000300900c0d046040d801c01c00c003944144166400d5540b1030842d403890399030501c8180fa1b4030701000300704140000900700b01810004410103036807150006003107800e400701c4080008e0090318240301400c0078584035800c0584030002c00c1c1d80303c88a0780c4000185400d40780f1040c0702800848040c003100c04171560003e4020760b40350780121100340660b0300c01400114080070113494a44c0043c8082c5c1030302c0140280403c003803055403040e1340702468541c0020500c0743ca07080910403800180060954050801c0c14a1400c1c2e464848845480c400904042003c6080d903031003050046850000524141c201c4000d000b0281c40d5481c02d110f60341c805e006508280d4220350003800380c1d804a40e03159 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 265656232 1250 265654982 265654997
    0xc0a05041202120f0a0b090102161407050306070e130c0c0209040c12030201021306020d02150a1413330e070b07080c012a260a060303080a0903 63
    0x300301c0001255850700c1aa44000018003c142254007800b4168030390a28038050110700210b418005801d000151040000380e1041010707624003900005000130580d889580c0300507503440c0c01125860041a038000c10f030305001e08400c2c86a91034100441c09452002510303c003460300c012030300d080304403880821210040780e20140341c00014900408200d9015201c1c0190030002600e61601011000591000710050303035000407050480140d450100340100a10310007010000624a07000791030304000c0e0700d081541a4960046109000990071002112481113898060740c58004041c044c00c10700040c3c1078030124101300c000c24400c28986100200320340403001e24a5480c0c440c1c15083c00401ca0b00c1140f50b518080c0c4103000c59140f03500c070000d2000c2d600800c42503850742640140703d421240070031004503148807588094441d120000c00240c0c2c2c1103185050020012526540e0f00e8a031b9036030007014a68030a9800300700110004c2c1c035405801600e0082d034507001c8958030301500d01c1c2240d009201c06030205050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 265657482 1250 265656232 265656239
    0xa0903060b040e030c0c01090801060f050907030b0904080912070303140703020309090a05180a0f06020a020102090a090203011d100504050618151305100501030f06080a1104050c0a0504 81
    0xe40d0407800100101810000e0128100100103045401208840039140c0015102205960b408580076000d00b1105e4020800710b49052100080c102d1503101c0c15010740c00d2034001901031030082c1d004030108840649890082d16242c80c01e8585580442041403080d0700c103560f20b1001c000300050368820780e54180c42d890502100f00d03107281c0064100ca20110210b21007001100115202d003440b40d80a03104492000c074480c1400004107442076036202e611001a40440804c1001c100c501d0005d04815401c08801665001c3e0034070100d0191043d4120306821080121001800c5805030780114101c0700c400701c8240014420000703451007105c3c29a0340b2001460070340b07418421864194403250304010010901e044101c1098003400c1e07407000449045010071030307602c3c01c4c526500700310280164040a80c002080f86d4a454140300d25800200d00949040560700c10004003c100164130070401707040b401c03044800d0818103190502a1942d0300c04598007490414021443d0030008805540042c12151200d9080606 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 265658732 1250 265657482 265657493
    0x3052e0518272802040c0f020a02010e04111c0c0207080307080c0106030c0905090607110a0f05070b07060e0d05040f0b0d0609050f070f090602070501111212070e04020a0903 76
    0x760101c0700026030140010071801500724000c3d458030301d00d56510800200b000380c01008102c460207042d074018086428406141725a01099030800c1d1340c0d090802010354402440481c0050261000c140c1d000000000d003009040125042d000c10302581c144288617115000c14103d0321515030b0b01c2240806e51051165400003001c1c0c4014000f081a288000104213a0b2074540a83c030051076800702c03c2150f6200e0a008103840180483c41d400069070529040302840c894046a90710502200607100899800b03e040170000d040c80103030000c1910941080e296a0b46040c068001c0410f088561482c0c410f41900407034080c01242a5411030340212100452285041301324000c507800080c100203500da91744404604560b0314072840e8024840120010381c180f90600c0041c0012591a105a041c800d5204040100c0740d400100301c1c00b550400c0c0ba00309a0034048003070952901d8042c0e41050b89010001c240075000c018004001445540c695549080c10400030090004030b01c42d090b10000003d079a100c0920102d80e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 265659982 1250 265658732 265658791
    0xf190303080406020f0a09081b0a090506150d0b0906030c090123030a0b0403080601030504080405130e03030403030b0a2408040f020a060801181103040303052e0518 72
    0xd0003000054544112400f140c5c1c4942e021031124004079188070300030b20151504119101d841103014040d8070103142000002046c604032441810069074a50000500545441d010000303004880000152a0b150742c2100310003404480e03015a000e404a0000101a45800109c0384c1c003000e4003a100a115074244203611000c2c0c0f1008800807401d10380380c100f0200c0c43c0c0301000303003d20b05800b0300110398060810385801042004040c0000b8101810001070002282011088900311101103401d5a402500d05540c000038101c840c030399201074000032041006154068000c86049242110135242c0c607500ca29070201d0103c025100e204541510761164101136009426854010b0b01582c460180c03030f04103500103504100e460308003000058006004000105050003812079210641505014156040d04c205c33a46000003440a410591541c01180720b0560501500000301442d84d9206101e007100701034100503400d24404c0500800506c540c00e51100115458540200c1c8581004459455940000000003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 265661232 1250 265659982 265659991
    0x20d020913050a1a070302034006020903070b0703050d1a030d02100501050103020a1b1b080102030601140c1f061e032108070804080403060c0c020f19030308 69
    0x40e199901c51001080d42044a01071240c0702d000400e03008521540385041045001e001801403500610034000e4030313030000c425900c840190112551440c80c02e00c80030354020b11010406451a2401c030484001d2144940041c076219005604440c41c43d81e940c6942c29541c841c00d0310140005406201d50750180480350041520700d0003504006d99044080c0300003d00300200c000014002d40e11454030403041341d0700740c007e15004110900b02142814141c00001c0c011401a080030907011800d8081e030030810800f4000300c0002480c507282c40ba02580c4030740500303000303500a030b940e6030200b8000001040078059140c211340c00000c0d958054120841001e20701005508002030402d056a1144c0300401c80e010f85030509130391364000e062580b281903d1800c4c8040f0042c01c1c050f20103250f030a0548a044926009081503030454458540100266a14144103c150150307820061010341030200841c00140d00c00d4044102c2d50027111102c0e100b03910355041010501e010144014800403074201080400c0c0241d0606512 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 265662482 1250 265661232 265661251
    0x7080c180a020904021809061c170d0905060403080f0115030b0d0b13020a150e01080702120a0503070806090f0601050c07210c0f06080c070f0f0b06120102030103020d0209 75
    0x2001e92600008041c1d1b00040c91031900701401803079043e020314090505c0d035017207070080d122011140902854100381702c40d92080030b40502e40c07440c00080380d100317030808840055441c540d04004544480ca0035a481d40d000b0745055000a0401c404910404d40b003800d40c1e412034112a0b440312200b000184290090584076150f154490550216003000c200c0d4004d403d44910183d840440e2400301d0b074410071100d0b08168001c00020383d9074011045c44960040c1c8410720b4031201342001c804035235400000700d10b001c030142480442c607074020030200303c0030790010045e50190300c1581310b24406903160800c0c403c840e14121003081c4000c1c6c0a40200d04994011030082c6010a000c4050301c14840d01c40d0003c8107001040741c0d11481c400348401d000418081e041070010f003d00325800ca10074602e0f20f0030070010312004020b0513000440d00700081e08000c00a045200e440c009612410402c2d603018075040850019400316500e9000b140180011040c0349018400c130380c10303a0390080c5001d007c901541c0a02c40e0024000b0800e040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 265663732 1250 265662482 265662487
    0x130e040f1b05010f0806061e0c0a060c03060503011e15080303010312140c0d0807030e060a05010f14060f0d180f0c12030c0b330307080c180a02 63
    0xca51a034070a0826005400c0c007451020745400001012030280702d40360010854130340203200c004c2d6103000c225002004482500c00c0d084000021078106441910200802c41c811050100c00300440ba4000c0d03210910b0307030303101040b229682d0030605080c0d582101d00c0e040020454035200350302c5d2503103500015604046c8403403520420348640b50103145603c00e0700103851004d440c0c0381c940000ca034007606584080e444224024209405101c101d80e80e042110b824405000d2428001203015100f0303800841200200700454010f414401d00385001002c0c01c0c01804248150b40c0300109000c0d100550b0300005c280c016268502c0c0501d9040144042d410052071800302c0354807640c072244100c40b18808603030000d00030900c0d51048170003881c0040c40301c082c1c0c0d40905c0311000481d40c3e444c0400d030045c2c400c2050702c1e008040b40b6000d41d900205400f11040c1810121402c0c4141d580c20040000c5007616400c1003841501103400c041d8855180e260380712140680076910860261680f480b1500d6090250382050940b203000d070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 265664982 1250 265663732 265663763
    0xa1202030d09030905130207021c0213020403140c06031b0f040b040803040f09060b030109020a030e060903040513110a0c061e0f0b0a21050a0c0623130e04 68
    0xa040e1800303028207070001200782c80180038629203000700c81070718046801b003103140a40e5030703000c80d480c5041e00020b41c074a450014010030035510b0304c0504020140f080e0108654498030f901d05a1540e41520003903811600c66080305050078101401100c0c01030416018451042c102c04030b9102c403a034000010144221400c2c8000a5000c04010140c009880040040c5450b1420400c0381d00038000143c0c00044a142450004c1200080341821607043d5103074008003584e9407907900d0b000c0d000340007030f00311071890b43c4203540821440c0d040c04401341040c4d40044034220a528841d0701403070150f85466004041038030040000c1559540101083d2040328030604000c92000141100c143c01311040d201e503095515142c000c3d00d0f208034494440d4912000301110503442590820140c403100344a4201d801c150700d001031400106109042055802542e407055140030300d940c80300300040408102c0e24100388000b03500300b8000110b01d0b1510590307420f0314280b1703a40100c80d0f1401200402e0040040c00581e08080644c0c00786 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 265666232 1250 265664982 265665007
    0x4020a090b030f0d05031b04030809010503040201200d0225060c03120509010b01140a090303030b03010f0504050307060615020a06111c060501020f0106120b250914120a120203 77
    0x100f0340a511181d443e41fa04d01c4d01c26500708000750041030440403c020900004200000b40c4803049000e04c1c0242d145ea03294801656030394103524900e1007030303000c98000b180f107028001440100d0038041ea0079140d91040400f039401d1b00c600000001001d1012026003404403a03c509000d280180c02860899142035074a83c14800715402940d200300941d4491024000550b0450702500a80c80e1285400e868080c041800921a00075800b0044c10140c50318401f0741076550035041071401070380141c41004107003054030b04140d5a6100c11f100b1901c4a080030340000f2007a1421160540c0c401558020300081007503592040001c080560368014404000d0009800c100480e102c0c911150002d000006030103070a150019107081c91150700c450f440da044c1603091045440349910b07484500d603c4103103404941c80b6044c164120f00c8403040e2026620035960100d000250f400181079080351140c070601c1450015440502c020b218564144039202d034000015100001c1700800950308208541c415603081c2940482e45 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 265667482 1250 265666232 265666243
    0x30209060c060f07090b0d0504060204151d09040f0f02130e0a05010515033003040309030c05010311180307180204080705030f0a02060307030b0d0609031704020a090b030f 75
    0x48805641c404410003c100304000da83e0b42c0c0180c0c403410900b003030b20703c1d000b000c5099104035248028082e465401003070800009030151006054004052000032100e0440241100d002da036030100c0b40e0340c07035003001c1c500340c2000d52590b4040c3c0c0e005030b940361504c451611881540240c0560898021038020b808801c2d003100c900c140d0744c07141d1110f005041500c2d090708219081d584040e004c41e6406032541d10b40811964006642d1912681ca11451503941c0c0c4040760742010108100c50440e8081e000108220030954000d11410a60b485911001d101c0f9031103038011003c46410100e0446001002c2001c00071416910b1200940250000c1c201c80a40d0f465007008a20182e017140701481c00394011905001d440400c0c0000f9010740b01c258024418140040b4885a0700c44810340007074003d610010114400d24030942140c0051a0003405042d102031007842d141d030040220200030341c0001c48250200745a50004440d090140d43c00a00d03846405052000c0c4000070983d1a0030f542e418414001c6581a180e0140070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 265668732 1250 265667482 265667497
    0x140708040e040c140103151413050702010c0212030903030711010b0d0b0a0605030c18041a0103200f130e030d050c130807030f030813020d120e0d050a060c03020906 72
    0x440f040c8a9103480c0d11400144400c2840078141401c1c4001a800c0c1800003000000321481e484c0d01d158115040000f04082150040b044110541040100054190150001c0204240b903500f200e03c0404080f0040c80140810b450000c8150000c07c0031840c1c0c2c43c840c00d4407540c03c1e40054000285000e080001890721000c2314421103100c0000020040c0031001841030306c008003012350244c80b940880780300140e2600c100c242500f210704031600c003003424010f10070078501005074010008540d5585034100007410441c50600400c5404034816090194100250840b000350405408405402c1800660708050442000d202d0960b00c410311480811036154010b150180200204e02c0d0f130303a802012807145440d4090703085207015902080703080000840300c02c0070011041d01881c1c0701c406602e03406900349541e4240100039500c103c883c0c003030300d00b0701c1082d9105418560380b80e160742c0c100201030014458103413642500030304a500300e101c114010401640010201c40402d2a0040c0b0381189a00040c100790000c0e0f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 265669982 1250 265668732 265668743
    0x504030807030608031c0c0e090705040f1505030a0905101103040506010503070b0d0e0a020a030312050a0b1005090f0a0b0703030612080a030b0d0b011d16140708040e04 74
    0x409108507650540301c1c00f0b01034215003010358900340203283c441c442c04100401403034a0313075034a440da81c1031184200d503420b1642000a180c0c400354140588010300700e81082c0210314030411f400c00f0024480340d01c440e0000980c8000d480d002e043d50780b00c0b844000204920705055549000e811144c1f00421124801d86c1c489500f40c5042907200e00b030034200b8519003441600403078002d43c048201030003024080010707103c1e03116a01c54041418040401160f0a0100d403a40094101c103034806c01004064210841c2d112200300d4082c108a03a80c3d5518900b420303208956140d03500010b1840c02c50b00c020b4131800040400400c042c2c08800d80c4802c41010400c81181c41c2d100444015000c1101c0b010035616001d603200808110508600c4121035842d200701c9440780003804400d03d41e42e610740718466141c290300b5158a541011035802d456030f50f1580e450455916025210f07110450100203041d5403081d040a42080d07030f440d908d2010060085032000707119031105200303417070025082c440050b0442000780354038071452248 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 265671232 1250 265669982 265669997
    0x4030309140d11010212010b070602041a03160905091303021e0106060215040b0c0c0c100e040e0303010f06051e0a0e0f06090d0b0a020d050f04050c010c08090103020306010e0301050403 81
    0x8420043c112400c0480703142540e401005005243c001e1001c0c03e40c1501c00901c0350a41d43da8040c505803000b4480c0e540165201244c0c1200c810609000c5005580300340300702c6c1000f80c0314400c40704040302d00120b540101644980750001140741d07034983e2011111510300c81d00440d0300a443d0340410500345e0884512196040c1c0d116135013031100d05da06011188602604115442c6039051551320320300000001421100b0741107020400019043c001c00c09801040005807044075400000c85004120500c0b00c00342d54050781c00c00c41c040d48800c4002089904035900015815890307400d10404581903031040026030340252000c1002c12052090f80300500c2c0410720390300e80c0c01a100c081c60502503054040d41105100310401c0c4a0602d9680303070000203032122a0301c03100c40c410f6995003107001002030140c445404080e900d000200040640b106c81014080e5009104480404004000465501103d01c0004013507000512044026500a4002c1c50b000201414001c00040c28103011a08603442240e05034001080d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 265672482 1250 265671232 265671253
    0x402030f0601140d0206210a050105060c030f0306010c0b0115020d0804030c0311011512020a09050702070909240c0f02070f181404030804140a02090c030403030914 72
    0x8000c4010010401409000c0c82c0d8500720310050390184040100e4001c40a0703030040011541c4010840d80e02840544030080300400074101c03100c0399502160061442490071002052074603250090383c900b11100c20042d0710b00f45000b044e0451b15040a41024103200b4004218800101c0303a4503041e000c0c00c1d010410340c0c085850444000d203459a0380300350768284000f810074031010903400341c000f06280390523080040d60f10310643c0c6c00b0350052845182d05590302c503007050040b07240740c003981810102a000721a41b612440e11402c020044500c16220000940d01c40c00080210869070380000c0c0e400d60041d89605002c03c0301540d1301c0c40f00712802a56211099407034030041100d64105080d69081503c034401880001d041c122600b07a03007400d601130f0f1141c0c24501c0f1a00344003405150441c3e10764100010042017503003041d141c00b030324421003618203e8101200c988040058240001e280a0f829002041c800f1039440b980c0c40c40c076541c1d0001d003055040549804801d00400c4d0011340c8034160100103001441da0070304c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 265673732 1250 265672482 265672489
    0x70f0b0105090c09060c25051914210a1406130b0a020d09062f16030f020c04060f0513090c060e1c0605010e13170a0c06090b0402 57
    0x140c010301d10802c0c200c000d20000340d00c0d120503a814004161007450303490303100c04003c0e46007030308a1a80b9000710034002255240d9160610107642202c10544000032100c0201e022010140510b02444603001c1c0801d100d40301918068840ca8403c104582d54807100358000d0b2441030a001c0d41e80802c0c0ca030022201c600304440c8401b013040f1644940700c80310b143c00e400115951440034040190007a0030031a00401e424140c88002d502030340035280d01c40000c0051071480d5a281b40d074103400c03907404140e03200e080e400420012003403011180d201901c4240c07001c00e91034a9a0036980040140700d0002117100350140340085894500c240005014088904182a0b242c601003094002100201844881c20080b5820004001c00924002d0b2040707420199100c03607010004c2240c248401c0d07100c18211107000c01c21010f22400390710440c16500c049402044c07a60f40d80000008600c90140c0007000005c401c800304040903840310250940310524a8241907009260716410191051003500340c0d07080103000140421481c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 265674982 1250 265673732 265673753
    0x70e0411011b02060c010617060103030f09062a060f0504050705030a0804140d12030c0e0d0515040303060f0807090518060112020102071701091403030603030409020c0f03070f 77
    0x5001d281100c0c000305810b908050311111481c0c000d00078640071542410203d820b4000001030014960700913252158021a07039581c010a01c0103030301040808850003a0903228041040948045440710030003046921050904551507070b000c5d96900d4060081940015124060000000c4145c0e40200d100e05240c00c003a404e10034181d00051007036110702c451000142101c01a2000c4400f29417100c0b101d508503c0218501c29141e1100030308206000480100690705603002c0741101480b55600070306214400e090000b8104a84409003da0348401a02d0302607103030003544290311a00c0b82c6000708203e65212002c4041003000d800076046600121024000c1040920450fa070200800c41c0002d9001030b0401810340360403040c01a0001000100810410342e4001c0211000a160368541c84640c40d0504001d240203100680003191101044001c5800c4c0c807400106890007010014007862820b840d00c41410000d502109801010303005600403940c2480e001e102620909000350000c13400c481e054a010f03111031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 265676232 1250 265674982 265675013
    0x5150c0616120506030106030f080c0d0804080f091f0c15021e0309030c100605010809120315030c030303041a0a0203040f06020a0e090114040c03060e0610050705070e04 74
    0x32149000e1103001da0350b00640c95208003010800010f055110003004c2409004642c1010348443c0d11aa204001c0103510002440000c50100984420101a400403141d540382542c024014043c144508490355082c1801404110002015840030340a815048880c41c2070403640e07503012840044407007041c024400481d81c1208030f0f242c004c6142c480303003403410030003111540c561022611000c400a1201d640c02c000300d0715041500d10413141410410141180581080e0207018001020303800400d0301c82c1c50000d2a82075903070b100c65107a800c5030760f207810f6800d4861700d02c94440e034580301d01920161241c0b400e00007907014900a6105402c036003624042842c40c1c100250582075454410030402c000316030814242160b159100d000075a4032044407008403060342525001c9039025042c80000508203950b5080b01a01031003e40f001d00409603190429801c6031201d01c100c441d40045000025801e10b031220701002e10346594101b1a0502c540d80e00c80900d8070b8000c0d00030030142000c0d04180000d1216006190110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 265677482 1250 265676232 265676251
    0x20a0c1221020c150c0f1909080d0906080709050613170a0b010303030507050d1e05100e060f03011b05030103051e191e050a0b0a05040503030c070c05150c06 69
    0x805600c5040b040ea28880d80310105000c0441e10046091912140c0446d0307481e080020a41e6114550442503924000f0041f0080000c0740e40d50100182205001c81c80221100310741c2c50ba03010030f904d0721307205603612a0010041e2080140348000400c0071743d140406040c0c0080541105c040340340c00c00d0806c02400003402e00380341c141c4c1d1012425a0002d15a1802c95055944c9440e010506403130b030b0340d01a6110b0003070540f039000701401c0c44000c01d0208221011003850079101d180c00d1003581c4441100c2049420329000f441b0203119218001801820904414009444041d000240603840c0185641c0e01308074034000500010700002c010028020200001c203501401c6503003c0c0d141c0030248907195a01d1060700014900c00403006040401c0c01450110b05180c01c0500980800c21091481c02c241c45030407103070040700c8040c0342c14040b030302d50907191159502c9550b021005603d1b64039042c8913407410b80c0044404580c18509044041440d4803800340d00d2200746482a403450725200404043d604006000340721454 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 265678732 1250 265677482 265677487
    0xf0b030108030f0a0c0c030503070605070801080a0308060d0212150c0a0504270507020d031a18090a060903090501031d100905071a09090f130303020a0c122102 70
    0x5841008022503c1c0740c0204092a503031405003070030944100c4810b10010f885441001c00000503c030001c001840700c40c1c0302e2082005a903492900c00d480760142805003890a5001c070040900080c0500c4485400034002014040484402e600207842102a9858600c00d40c21031002402003000b41f129031600303d1010401035080c0300d82801c00518501941c414020b00d07480000b42c0000900c0e0b000001561440740700b80a001c1840c1007040a56184250032400d8006490000700015007440f020300d4060030700e4014190a8260070042a40c3d041d4138024001c80401d0061410034000180e0521510140364403139194211094645400035044071f5110603005418403540304811201e003008110791802003140c5900180364030250900c98a0642c00e0f40003039900021000c132a850080f443c00240c07005401c201c5252441d55544000c0d240404002e4a00140290540810400190181c0c01400c1c080b04145085801103000b91140c91a041c0001702100105100d41005120a40360161950b03000300070303a00039403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 265679982 1250 265678732 265678739
    0x3080c030723090a06080619050d020f120106080c01113705010e03040f0f06080c0313051f0507030e0c10030b210705090402011d060f070506010f0b0301 67
    0xe01d1001d1602e18840d00b6054480c2559140314110180c48039800040c15989640d40c0310b803c003500d100b000340c403110703c03841e0401c0038040a282c0e04030120050b18000381416250900690900801142c19520254403010605001014540c02d208010040c0341400c020512048a00009820b00e0302e00000c141160700001d0f80444412030b005001c0302d14810b42c00310b125005ea114001424121250788000300594200395661100c1e28001014000f070320014910010004c0e6540011145032405116142c0441c0009000030305616500c0c01869000005240310291580341e075072540c0c20309c440c2c030703c0f4036540341404842d41c19040b01900c1032030b50103102410108004403452130229a940307500780341c562296802d81804034440d44a41c1140c180800090043c0b0b106540b00c1d4403803c002c0604d401003003924481e0440c000798603e031113079005002d160103855410700e150300310741c20fa60070f01d020f050384942200c0d0800500e104520b014004104181c0100050305441d4100035510721505100d61007400e00349014401072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 265681232 1250 265679982 265679987
    0x50303130f060915110c0307090506130c080106180b0f0307090f05031e010e01060e090d02030306100518090a060302130501140111010b0a0b04080c0415140d1e03080c0307 75
    0x1ca1311622681007400c00305051581207480d12520120441d058000d11000044103c681d41041e80904e0b42180d100d5038520060400c2e400b1100c201d1550740010380e803800100400307805403081c50140c040a000c04818140c64890f026a158451759641003032190000401411552184c0780c00060195024a2a271103803808002907590380d20f41c00c40910075040200760081c0f000c400d5119a00004c0100000d2080b655a060010024036044a10410354000e0400c461021840401164414240103000f81c242040c0d96104075041c0c4c11070914440c00d0002400a42041da440c107694600c00e81d45400c0c00314206003580305104c1c0f109045c003070700b90405003810014801c5101c080314144200d6828a842060504c4450031107002d00b451540c0d0b40c2c1c01524190b80414404c242d50001c0c8150b4110b941100c0c44c106044007440229680002c2888a20b41580014040e03041441c00e808842c600040c141c0d5036801d81a245e00244900710610412034040c11a0791200b0182c100b80c515520142c20202542036281640c0003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 265682482 1250 265681232 265681259
    0x60303090b0f04122a051c05151602010605090103080f070213020d0209010e031b21120a09060f1b0f0b070e0420070809010504050303130f0609 63
    0x246031800801007000781220355800e0a0310010084d500e64201e0001103810440d00e040014415801c840d2501480d0f006504401030140c02240c0c4060050107498031243d00c0d9840c640032070340b8100c0f10b40c00780c601c040017420540b10345039000300d1010300c80001c040b80400d806421a20320780d2082e400354170324100420119034041c095540e0f100300124003035501d007151710000e50308140420701a1a0b0303034400326900c40004c12366400340500c07030820380301c403100d44640004156070340180f00c80c000c140710100301d655020307410640200d00b24698000184002409941105801c4c90141820140a0040400c50740c80070380d80244503800401c1c170750030924407519070762200a14030b006c5800c6200d00d0f03942c0c0243c0d400400c0060200000d50036007080a440181c200100002c188502d040f1005104904049226802c2c2d4006c4040c8002d045283c05854030f0b00c4003551703c00205411900325030381030060034040069907450a100400d03964002c5001451036500f41041e0480b01aa990801400c10100700e1042c4a0121f10840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 265683732 1250 265682482 265682489
    0x602061602070b0906070b0c04030303140439060e04050a02040e04060213031719020708032a0706020f010c0c1101210f0e060117030301050d051c111006030309 70
    0x21607031354828500020401500c54900002d0860701b6601c10000c40024500c0504142da00c81e907014015229400d035403406400f81a50041c1c00925401e6549904010705040311200d503800c4004145004090350616550341065071100000c40d201074020784481c80e01e485683e07400300d0100005c5081605124060360200401400203120341c2c1d00080030105610640030700401950700ca03444000586040004ca400d5801c0000c15491350f2060541030300015002007414020f4611200003503080031345200102c2003400c0491498203607543e242c482d800d041d001c1444408003070501e54008040b0024071012060840b0b1700c484200f030030042c1124100d40016140b001340d40d0303130005c00d04e0005c070003021104410300c4140000c0f107140c82c0c0603d014100050784584d5045083c2112036030007922840d070b076200148504400040004441da8100b00010720562622514050500f8010400c50300c407100144030060744110a48103070404565032190340039105100300020040001c1c15041440014034581c1c0c06000c0424500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 265684982 1250 265683732 265683749
    0x3170115080c070501020f0c010f0c050f0d0e0303010303030c1b020108060409080c100b03010c021b040507020304090f0209040e0a0308180f0a1119030b01030305070f0501090b01060206160207 84
    0x700818a00c00d1020140d0b609141c00c00000c654500302d2802641040e407007050300c1e42c5c0395424030001141c000020700c1103c4d0001d483e1346680d07150040044800016500c0700c000a20865070b00c2d1144042440104080c1d0302079031090324001b4107201d000310082c1c0b00364250b20440ba4201301081c030490050740c0c00104990032150544002c03501558038034089400d0b0140d0380a0305003030f12461080c1b04240741203820854140c0c0003a0000c009a034080c12007242c89180e1259407800d610080001d43c040ca09050744a140d10255a105070b9080c0358035004000141d50044141c8038010380c001c00c001403c0c3c5024880c003148000b612000b08440c901541d0003904001c4000c20a81403a09002c85a0a54110900c811031001d40800c00303450758802585040c400c02550480e510707014810f0700020345809401007204000382d031b0308800e0103021a86182d90445140e8403591080b500c0c44035041503080003c4c0b00b4024518002c0c0b040714003200541c104a0005d2800750700901c2c845050285450301c003642078000c41c00100303440303c13032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 265686232 1250 265684982 265684997
    0x52b0512060d020904050a0c14010206010b0a090807060e040c0306060f0305181f0f0207021f0302040f0803120c030712110408070e0702161d07030b041803170115 71
    0x40002e0242c000c0706801030b4011011404000420501081d04080710b4401c010842c0056105d00e0b0494074250000d00690143c3c1c172400051081400d60700103800c00650504d000c1100603211a038242c1428425440f04000ca0312a8500c5000381c41c180c000e1000034902880c0810410b032402800404a40880d00e00342d0a160381c0360081352500110303000c040f402034080d0303044a0074080b4580042e11035170341d40f4031040c103118074040c1483ca28042c24000c03250f006400805c0c1c1340400a81030000d244007181d94681d81c0916600300000641400420030a82c02044000c010f15121000c4501c0c0c00040c8600512001c01100c0c1081048200d42c2c11402c0c60740c00c00a600000240340740801c403000c5951299412140a500c02c07144005031004401d485948924a26070948048060b50643ea03007800a40303004095400328442c070840344010300c2603203041e8000000d00d408568100310101081c125480300c0c0202040b0200c103000c40e800e01d90026248a50841c010b44030101941c540040480070114003070603107007000550b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 265687482 1250 265686232 265686241
    0xb040902060403061a04020c16080609030306060c0705030615040b01090308030109020c120c0105160e03100209130e07140d0825120201090b0a02031612020f07052b0512 74
    0x340c4003901440d1001410440d61001408c0c901503841c00404116000023883d420041340303601c400314000d030260001500442c103503203e01d020085030b9008014443e000313106030341000803559000c102c3e56024566401c0750b00c2030341c0454020702080e524100c01300303070500081c0c3c03108100080404080301d04542c200c1c100141c5544102d0041810b01144105500e808100410040c40002066000d03500400c48451800d00e51a5280e405441e0f404101c070901d94580c20030890280180c906070000d0512490080958402c01c00c1d0061308400c031141408001003e42c8a80014001c144654074201d80700f04007160301e2484100c150ba9203810602c1131000028011007040401003110100e01010b8401552244502c40d9a103034a5000074024031003014159465040c5002040c0c2d011120300c2268040c6500109200c14040c140c80140e40c0d0b01910340440d59810fa0030010598070a46c10f4020740003880c4036074058940d00c040751120520010521131101c89c201c1a42d00c103101070726004812140f6151800c0c403800842d55a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 265688732 1250 265687482 265687511
    0x3090c100e03011505091b0708031e07031509180f08040f090507090909120e0619050c010b0609010c12030615020f0f03041202010c0f120908010b04090206040306 71
    0x14540c0440c2d4066003010342c402c005891820514064403810344c0d24020580e07490801071403207105c41d640545901400c01c0218081456130b4001d5a00c001114400d42e007010001001003000c4200301c4844000950303441014201601081d12100180103002c418400000d00407695265a2150700008051007400302125080003000c1050b01c0007001c840300c8134503a407640c4d1480c00020300303001c1760300c5030005000040200d0b00207100d1003a9410513400c0349070a154a8614a42682c8505124110380d50080c1d040c8082c100b203809405000001140341d550307282c0c4400740582e41b28251813044482920425003405000c3c0c05991000c602411542c201c1100c8407442c440c80401c1d401840c1c030341c00070396455141c01504030314070386c0020b140030a40942d54101d0300d260a83d5a21903072a80242d0282244210461031500007540c416110780302c9950107007400800800d869a902c40b01402c0c0b0285850204030319440410000000b8802c8175107c1106940a100c245101d41c00640107108900000b800700342e82e40b0241c40040e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 265689982 1250 265688732 265688747
    0x18011a010906030e0c03060108031308070e04020915041811090603060c0d02040b04060504080c010e03070909031b031e0f02060a1a03100f0e010e0304120f06140708090303090c10 78
    0x1740190645030315503180c0c81c2143c4c5030ba0004080d1000800040400541100c0000b1a40110340c0a10009016511207a00b00101508080c1134446203060041c0056544c4c1e4443c0b291000a510322100c0f210380401919020088014801403244070300d00203020005c1a89010078419400000002d10650f5040d40300d60407402409550810b41c46e4820104000c503506c0d070031600404c00d40d0111021a4507240c00507004552440c140264141c042c1c1000c001004031804a401101c4a00c1c40307400c1281411034002859094a052a4070940024022500e0018035124150700820001080d103002012a2080400a507070748034003074a40081981d5901d14680c05102c05031842075030010003010303070784104012029040a010340140400d40c041c07800014241c00107051103507030f0480c0080405075082501c2d05c0b110081c00304105600307669000103d003c140c0003555520510f10000e4800911629a06110740018258240140420400e52080041c0001e10000043d6070083c20401c5030404081c1030480b1041301c802 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 265691232 1250 265689982 265690003
    0x4050a0f051c02010603030e0919050709091404210804030804020109030f0308010501141e090411040305100506012d120614031b0603040303200318011a010906030e 72
    0x82d00540d080800030707030341900041c080304e00a0f503a541004519a081007402c09054031109490b2004101200540d03016802250303200724941070440605590381c0f651010380d003102150200441d0410b00700001c2000010641201d013142d002002c039401c4505502408888000c2c00203018082c1c2e030350008003107a01c202d100001869115044000d44155072038041d01201080c0070f101d02042c84001c16500107248001690500f40796003510210000e24070b00d10040c0c0341c1c004480700741c029803504007160034603c141c40180001d601c03c4e4001d00c42d2410038410701c0122a405020f0904004184100301003030490781d1040b4000403510300030139071404c102800a030766880314909031807001801e0810026001c4501d4480e110130440c01d505031150601059060703001440f449103103660019040c80845c3c0031070301c43d600402d0b85440d0202900d100c0d500000003210290401c0307604001403c0b0000000e85200c4080c060b03040c5201d00d20341440000c511450028001000600400307040550300c0441c428a0070081045840c0d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 265692482 1250 265691232 265691263
    0x90509010504202704050105012103231c060609030209060f122505100516030903051504110d08091201090209010605040e010b03071d0102010f050c09150304050a0f05 73
    0x90301c4440c40084840c04503019506c5510f004000504200003840d01040da00e000240750f8404100d07a0380076991801003182e144401100c40c1c100044c90608003005101c106a103400740c8032001194051581552001d40001041141381c130400c10058488540203078000170120381c1000c100c1145030114030701003ca1403e5080602c101032054480c83c60010502004445441d0a04403860f114824000e4a83c04604000c0c00604c082210b580711078001d00d0301a0340c051003850000d010700e0380e81d12243d107071810000d46030103c0015101404108040320885020014042d100702440f0406929500b1060295140e80ca015801d40d440c030201824003036011083c02640241200030958444130010415003182c01407080d4900c0810011070402c0d458070a4034800c0800340e0310103a200482c2905802c0c00500a41d81c9415503485040540542611b40600c6100300d82c60008140c545040d07100700403914a0f101c4034068888010002c2c0030110f00e000c02c0342e1014a400048402c10800d0f2454120325002c549030b86082d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 265693732 1250 265692482 265692529
    0xc02030d0b01021005100515090a0603230405030a030608010b0d0b0a0e070308030f0609010f121518021302041d090f0607020c040609050f0610050c0a080409050901050420 75
    0x41b0400e440215809032141074901d002d03103201843c184605841907482c42688102d403242c1c1004041e1003070700303c50390b10160206601146c0c096441c03800c90001095500f1039030764002041d1540400e5042c41210000c085000c000d005104a000116080295542c1701400d00e40c112000601c0c100380c150048800425510200d5100e542d603400d04617025041941d00c3c0614410043c01307d0034500d001d50405048c0c0b2512561031b4001c070315090800141c90140744003186c640104484928000384184500d880d035000031061564071000314810440c4504580c458840307100d106010620036110400c0d03540e4980a10000f40728840e403101c038851460010f4554602e0428802c020411070080d5000c1400000c2d248180c6090081c241c03201148400c0c1c0ea8110b42d00040034501800003009850004070f40f4844240300c2c1482803070441c011400609180e42400b0030f0707401c0180020104041d40103031080c1980050858006c00280c10300d41c1d0340380100d00b0050803840030100c801c1003003101580c803520f000c0441840302100c0d48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 265694982 1250 265693732 265693741
    0x8130b0a110f07050601121509030c0c0905060a0e150f150c10290f0d05010c171008030301050d05030f040303120b0f01080a020a030908030f090706030c02030d0b01021005 75
    0x1951030b400b150084a0a005410002401c45015443c7c24102a4401020300540f0031604c000001483c00c3d03481502001502680c01c0041041d8001c0400035000d00350000c9003d103084418850031828036800300f9000d44a00c410010541d40061761070361140c504461010342100880c000a042d808c08041000590340009000240144000762080040300c1103031040c80701401c1074800d06541d4110907101310b21110b06401c511b40901e442180318412000080084005a9440e110907003100c1040b800d10020811710038012200141c41c000b025070000100380803211039410011200d07203900041c41454000c5041450306003c2090500030750303141c003600c50840c0391182c2d0303241801000712800407461596549072541108160619840a020640043c0c452108544070002500c00951100e8895801c040e95811400c1c00190074030003c0d070003004480c03084240c034142003010900708030702a401081407624000d8a66040f980100a80d0754044d034800c00007819800140060b801c0884c11030305000c0c03040c078040400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 265696232 1250 265694982 265695007
    0xb0111031809070f0801090b0d05060708090c0405251e050a1b0209042307140127030b0a0b061911030a0e1c0503190e0108130b0a11 58
    0x80007a1202200e203106262285502540e0141d216441d00001402200c0148448003140d005143d4036840908080345515058940c581041810780e0040001540ca40a0050600b010807400c140080129402c2059084c0129081d640c00c050b82c40515081035140840c03400c05015054251030340c5541203540c8040403204000500316840b0880c07100c046000440c1c00100c1140781e0040d50003542d40a04145d08507150782d11044441d03c15500c1d161b81800e400a0114020101072148000400034640100d6440413004001b41030b00040034254120516140078081415100c02c1031401200d4000400385c000b5140d0900c0f900c0a425003008450704920000b070204000450501036071908011541e80800311a80c0c51010344c1c9074800c660000d8000303241c520302d004003864203030060b407c103030b5500d410301590f0b0920b565182d00f940c22022080e4014891b0322288051181c00207480c00e4114002d20b007503401c0d40b61804080415400000c1d015050f86402c5000440d40c00450380215138641903141115258512070425 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 265697482 1250 265696232 265696267
    0xe190e07031410030c060801031e080405060408010501051e09010608071b080a020f0c0307061808060c18060f0304080a031e0914060411060d02130f151707030b011103 73
    0x2101c5c07941d194240007540394400c610450690b40d211090514420020380510a52118288260340c111010070000625568500c001c2009003020400071030250b141c10104407100e01d9020000d1441d0800312000006941c0b000a102c3c1900d000e410a050180c41e040b10444484070400221180a921034100c4018031035038070050702c0c1054040e802c94040f81400307100243c07262110f2200581590101c00180310f454050140c580d030780703941d2001c2015200e903150319403850808245c5651090440004403403141441520340c42d42803e405446040ca0074a0a4442101501c80140f019000030008a001c900880c80f9800940c0805040b0000d1030700b03201840380c590024488140110b0b6071900305030039441c00e4171020414070b01c996000004402d142c295801404010381c80ba00751100115420092070284245040d0b850024003807442840303810394245200102503691007400082800301e00c04200307038076582202c012a8084c44030718020540c80419030050380e200c1c02450b685160703408042190710800184040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 265698732 1250 265697482 265697489
    0x20a0306030b09161202150a0504051008101a0c0a0302010c0e0901030c0b0f0f0a020115060503040b0c0c030403050604050606040c090f0e27060402010e190e07031410 73
    0x1c080e142c540b50218120f03a90448410595100303420510100025080840c064a059001404461041c0000f8400a046030b000c0001c1001044012070b0600c40d0f0304003141004003241a0f8205542c1508040128130034401007481780c90b00c00541803503082480c240079000d40c1c201072079000440d400500b540c03401070b000e0403552403100e0000d21500710b8a481071401c03003101d904998100c00025403842c18600340e100b440c0c2c0300800401e8030307078002c0008414481060009054800059000044503071108040e241203018641c000e1013040006d1050001140002c1074a90300070710120700036030742d032502c2466060442c001c661020704103002d60000c000030b0200104600e40700d600304680401c1410b0140c0780c295040c0200780500d201e4070010140510442c44c1d000101c2d504140343d200e100703110340c40d401c01081440c80c4000c000200c0d83c000005002c11540c0003100f0b0301c5500401c039220302140d042d8410703a884040b2144a98900741c1064800305440d10b001c1ea0018014113a071452003c1580f5101c0031041c83d4030329510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 265699982 1250 265698732 265698743
    0xf05060406050a0c0c060b03010608071508070503090c040b04060f0617060909300a03090c05120a1707170a080604020909070e121605090615070305070c09020a030603 73
    0x2d43c1c601d80c02d105200c0003140d02c1d05d030300c00d12000070384560004200346481d4541541d6070f0000880c0c1c3d08804c01c494002040f00240c1c0c0700c1010303140382000b0500c0502a09100510034203000b44200020041030150b08208140d50015203203016600090240c07006921180c0020340661011882540c0000d8842840b10641c0c0c4294540d2241710034841c840908982c00d0010f6002407000c5d40040031242810f048142120038003010481241900e5034a80e4404c1d420100801e540d001c1400c02c025100d0181001000c0860380842180003803075407079803142c3c1c0321000200f11460421900c0c510400410a4854007900581d603828090901211828660301c85440741c0d0120b03000000180d0303103180c14001c0710014500030300301e10160b4990b0300041d81c0da010080d0110b41c2c042420741116104440800585807010401001da60005103080b060200527440900600d00641c50b001004038503401d60310884800642c1464802e50300c0c14103040c5001c0904a40c0c008085050000519084090780364005900366070094 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 265701232 1250 265699982 265699991
    0x2310f0609151208030c040b0301060503070f0804210212040b07170f1804020c01050f10080f0d051e0705030a170f0a0b180414120f0904020a03090f05060406 69
    0x82004061500c540c41111407008946aa2000283c03010003e176402031141c44906040035140e40c0310800c9500709801c584001840070003041000d0b035001100e86c40700c0c00e03903042c20f40c03260826444049880300000c1c0b01148800c03041d814000982c0c800c1200d80d4054a0440161380c41c2c0e5200c10020403e584011025a80813004104040c3d000e072100040303078561086540440d1404e07288405065080301c00f90040340d8000d5003440a20221102805280e1182040025100c1c1602d849409074403c0f4006400c0003001c0d510070740342c3c9280948001902c10225215013007150310b44c089207000d007100100c1d10008600c207640c003103406420408008040d206042c0940c079202e03124812800081404002110031448225503180855449203a5038003444075034001804101020112400011a00d6402d98044880180c2006017030741c07442052003d19012422a0992817030040107206030403942c042d900e000c900c101d60010314000054080d50100d2002584599017905a101504040d40c0700d08040720190f4005040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 265702482 1250 265701232 265701251
    0x12070e07050328020c0307060609110c0309060c0c10032009031b0f0d0b090106090b06070b060f040e060906060105040602070b0319050c0403061802310f0609 69
    0x500190b9124200400c00319203d5580d0355190a803450500b0f00014401d607080214800c000300510003441da80b0300a074070200b41c19280021030021103422540707030100907105004d9040140808821504526000c03103045846840302128070f801c002880c0d00ca140e211208501c1f01c020b003034060b0040500b0b00940f01641600c00034155a0701ca00b80f003400c2002d641070f0810700d25030098030820740342140c418038040c0030000c028502c10042542060141000d07601040c40394104a0f680000340520000303800c9200b42400070b040d206001c41c501d4000ea4400400a020302800582c8640301c1203056070140c40300520512070b9003201c880031621524103480340b11081c011140061010b5000300215002c0b1000783d4010400c0c241782110100d03094001902c844050a0100703120445000b25000d014003441c0008a9a550f039443c40c034009084400c15419403401c0c0010014840242c2d88103c42620548054000521821800c05039050780c000034840c0b01c03240900d042550808404150711201c01d894102078100700a001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 265703732 1250 265702482 265702487
    0xf020d0c0206030105011107090509031209010c050909070e0d060629041e05060f19030501030c0504050403030e060a052d0a090503040902041d0c03100b0a05040512070e07 75
    0x851003001e034001804000401065120300c80c240303581444001980e1811703031100c01050540b14151101143c80e803001c9040b54100091030511500001406c00030041c2052210010340035005202c1070702d20032288880001e40807406501c1c0925058401410042c6100a40c9030850041c60b1501a00103071800b031801306100c600154110400310820203510380e0600345420300124420b41800a6103032440000e81c00005e45482c1c0d4806491043c4040700700d140c60f0b040c2901c211100d14074069030481094204801000440c0c44011071606503101a54003064a699506041d0081e0001d405040054455102045554103032a0f000ba8011000c0600e0742038600d09403035102c0f03415145016144001d440b5000440d480080070b034040c50340315208200b40e03400c0030b030354038a41c0c5e08036003041d4460b090900310a403810b09040d0034050f03896441260f20a0203421401c0101125120311214026609114000500344031744900540684006140040154000d0090f50003219111043d0740f00312100d001c203520208020b0360 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 265704982 1250 265703732 265703747
    0xb0102011e0b03150907080c030a0c35070f060c080409150302030312010e0705040605092101021c0c020a0506070c0218150a060f0e09040c05100f020d 66
    0x8404681c0c030302035509403210031001460029640c0c1d52610034003001842d181305030701c106807054907024050100d180c90015000d040008526029109400840001e00003c0480026030143c1f81600c003054a031418401c81c43c02c0c03005080c8401000e0740441419000c00c54000901035051343c1c041c018151609a55080640e018a02418010310a503001d010600c020366075540001ca1100e401c0c40c104501581e01d401003400c65110090f10b50030b014030000180010800e40c1141c1d0f800070840e14065145c039113803e000074500d0241180180c41410313005102036208007000d15005000c0396410086603508602d112700c21540c80125087c0c0c41d83c03810815041c8000c0d00104140c55000d0b00040644015a601d010888100306060360407680b18105940703681000c0c0600080d58810110400000c81c0240e1100c20404140341560101c4104040354605001c0d05a005040c04101c0d141903c00c06155100c0703103404004800e05400490300f2128207100008950b41c00f0a002c40103882603004d5030046c40704e00000300c4011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 265706232 1250 265704982 265705001
    0x4020406090e1e0f09060c030f1611072c0c040308030403021c0906020613030e150c030f090109090204030b06060702030f011d070b03010e1f080d050d0b010201 70
    0x1403400008000c2042e100e92019485088000762003070103806100541d800040986920004464520402c03080b28800c010140c2c202c034100204604602d4031404690b05c1c0032008005140411002c56554629030150141c1c2c0b00c01c098003c1540e050545030314682c181d000350691840e0340c0c020400340034212a0440703642c0e24001e6241203080361800c1e043da11225401e0344050011802c51107099074808090007960300109000006544000015152040092070320700301615070740011120840441c0003070340103001010700c440c0584580e0321200300c3e000c5001241c003c00811201c54000011390501001d04c5d00010500f4003030980383e0102554840400c4000c0340101d000c001d0002201c9408180a441c191029041c0248004d0845100301107000702d9a003550b21448040804070114152114241d130280003190142c03450801d02415989000220400c1800103400140c041c5624010307292920740c0c04160001801c4420100c4401040c131800080a6078044500040b645162132007401c1c03d98410301a04000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 265707482 1250 265706232 265706237
    0x11a06071101180305061006111e07030f0503091207030b0402010309080d0f0c0f0c0302120702041b020a030906030908090f0307090f140f04020a090203071b0f0302010b04020406 78
    0x409680341d58940d100c000d040c400c10305100c1c43d103890400720425030107110b0145200e0006800b06040c81201a18911034a81001080c0411106407109a50000801c4805200362a800981c043c00800541c3d0038140c00c5c0c0c10242142500200407410700400000900090b00255038003802c02600501103515400a8000140301c0b03071001000c280590310a40000307040a0160304c0e02841c000030b03071005030100e0ba10600c3d0143d6041c0c4450070200c034150001c29a083c80691401c10203442d00d400d542c025140d00134520302d0804207002140705419501c80c2d520088055540500102600390281c1003c0d540d0409120118005442101d020500070302c2401044c501d158010b40c0c55040250403410040c000b1400b004943d018480d8281c00505284540034840c6420500303500000c074008800300c1c071102040014609041c2c2100141404016200e64910030301700c41c50124010f0304d948070b03d003084400b14503d0307042015144807140942d091103080d80541071002c0c801c0d002000505900018001030b4000c030300c0391001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 265708732 1250 265707482 265707487
    0x130f0b0a0c03050c1e01050a0b09060a0e150a080a0b0a020a05030c0a1701150e03010605010512070908060f0603100b01120b0d15050603060f130206090d050d03020a02011a06 76
    0x240a031000d80381c6044500107075555505e81c0201001101c500c031144444a039110320030b1001d00c00d968400e0705608038007640c5090591600030702040030800c091040e2040f0302207540c009425100042118801c14000500e90203c469030f44d290300760fa030885070350b040d65980350b1100401c0c80866984215034400c1501d4603a03a003180d6a501440055810814950080c084c1c505c13454803502c0c1c02a000d190103015a04441ca0500110701e800401c46895080b03036501aa01d00310003442160b800a0030b641c07902585941030411030b074941300c00b2110010140c2c0101d1851041c01d0a0155030790400804904c2000d00350115500806400344000a880c0d00d407910310701003403045501d9446a0801d400022043c4c1d0050b10a0108049544d00c40341e0f50b1070503c0c140c040c0c00e40d443c403d0110a00e42805102d0308107aa10348450190300b02480c51218010344203034020322409002582c1c120320345954001d400b1041e00308094550309649402c0107070180d48092480340065103016400d20040b814515603403e00349025001ca070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 265709982 1250 265708732 265708757
    0x604050c0d030e04110406090602070e1518040b0403030f05040308070f02010e030f07020f061e07020a091407030b01180e0a0b190303022107200303130f0b0a 69
    0x80552416015420007a90143c0071645440358000c917095280c1c850f590307590392850b0000091104605400003401c40d001050100300c540300a03404540c01000d5680000040071300640015640140741030b1440360600b01e64108014000c4103044144940d00075201804491120b100d030130201e49040382c0060101d6500800b0034071952240d400c00000e48524000003440c0ca0041c511071745075403c6000241594280000c0003411800c01401c005a00202034642506041c121858100d42e0910b80c0e90b800744552021a112065540d581d440c107005040c1407504100309282112000d036070000803548100400c0c204801030110303511800d5520040100c103403040c00c9040c14002d4804113000c016103007404094844d500403003030341e81d000d034521803072030a451641d0103c3d0704d140b81c0a03060200700040d000100140c2c131514030440301d010007101c1c1d0f1640c1c0300c9142d840442d1045900800001c80740c240507058440444e91070100001183c0d24401d691342c0d02d03854001e035903851040c900c05119000090000584956455 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 265711232 1250 265709982 265709989
    0xa20040c111c0e03030d05040203070801020304210c02090106020a0219300209010608071701060f0e0111011e180807080d111620010e0f0301020706090b01080706020604050c 76
    0x6603144490f142005103141c1c0000001d1450b0050100d0110295640d0144021032408000c510007c1028070000c2d0705601c0d040d2103160b11044500542c1c1c08401000000c0c00455129203e018001c0b5402030400c02c41d543c489100030750305c00705045e04900803000090340c2c0703c0210710425410100d0383c4040d01001c00f507111940300c6056068070980c0842d500000130b00200160780c1d500d4014083c000c5595400d080d4545180300070700b0807130707240600901142c948005214103540140e83c10a002100d050000d03542405000489400e4500da4504803154a000100c10110010782650744110005060034401001180724880762424000303c001c020030401c1000034001303100070f400350004813120900000e16507a542d12a00460780300690381e0510b400000300c00410058080a0210180c502c0440350780502c0c150b0001a005003010b42080f0311070b1411050b50103080d58250101c035812540321200b40b002080711301e441c4204038420f000340c2501e07000f1100041140c610004009210342d030420001c0c60350001300c4050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 265712482 1250 265711232 265711273
    0x30b1f0c0807060c030903020d090602060c09030f010f0c020c04111204050304180f0c180504021309060b040e0f130602070f0506130b070c03080a05090a20040c11 71
    0x880d801d400901203031011460320b10a520341c06456440c042a030418903d0000c1c1070000110f82c00040c00a081d105002d400e9001889a500c042a5061503607104501c0000903e80b030301c0304811290b01c0d820200782000740c10442e0041aa0215280c0840e012a4003000401c401d4800b0001038807030502062082458101c1402440c94006003c1ca05581c078080d03d581d8800e00c00d185910b80312401c283c0341d40d141380e14240e05108149144400e490907075801101c00c4000c000080c260300c503c074807640d0003140d40c1e070a8443c070403040c100816001808103d5940c0c2e030311442c00e26030050f1051013442c040400006103094803c00406110f547e00b4031581c1c078031002d181d540c3c4009400200060f03031160b401e00c0f83d1100060301085064012021020190300c6008103141a40c1c510000410348420442140c221800080c0c00c42c40681e08450744410100d0107548410885140030155140501003900f21058440c1200004180955000c026601406241600002659440c00706c03040c00c0847e51044054148000d814183c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 265713732 1250 265712482 265712507
    0xd1107090623040b030607020106030c050909060727080a0213060b07140703080703211a04020d0b10090305060106030219110c0604090b0418030c030c050c030a0b0601030b1f 76
    0x3c00240303030400001080c5070000469950700542c1d901c0341c3c140309000b12407840c4070080c103049a9004152800c0c040c01d9032510406000d98051002c002c80007100e204001e42d4101601c0f07002d0403052030345942c440c5200d0307440c207010500740e00440c0007042d400130b090f10728061942070790081950b0a2030500c082e91000c0400e42d40d46145e200340e0048480200000b801703040140b48030f82c0282d840b2118101008107481200f042d141441c06443d10f02607240c50000098815a4120b0400b1580140c903025148900390142c4070030007421354808401e0b0f00c68610075400c500c0900c02d6900450072903000e80c2e220394043d012031041c10040030103100340c8000d40302003a00c03542034002c4070032240045d034400c0040721780802d405402c1034005010050b142c01044155041510801d0800c0307540b00d80c103501c4040396450107001201c0c1b0703c401508000f440c0c4440402c0c040108658195014060222000613005003441403200d031040d03503501d0001e410894607d007141350201049600d4070380c3c0b404101001000d10303400c1d51400c4410710b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 265714982 1250 265713732 265713739
    0x3120302121918051e01060b030c0c100e03120705130305011a040908120907030b04030207030605060f1302130503010e010501030c0f0305060703090807050d1107090623 74
    0x412480c481080c0952401101081c0201d081803100c5660075054407154000782e441c46890f0a00c41c03011913000901d000c072141144103001c1e034032a41420484c0c058070b8079400000940000009204002403030341c005018007200982500c2c00010b641c500b14080d54102c0302c3c9103840341d006001c814084901d40203080d4000e0b0340307810302030301e0f02066103228031408a180e4019201030359070704445504402c0122001d800100b088a042040d040c1e00c0d41c41840700c1c0101c40c3d001c00d00f0b02c82e9170b00080302e0840c1048540051900005141e685207803a2400942d1030a50340003ca8045082102007111414444510828002e00a1007604c400741c1c0021544000e4100c0c4d031002100707840d280700008031a18203100e44800e8426010010542d90b055003002c060603801c950184030202e074203460030000f0603400700d1040d401101c03a250100b003801090a001d92540615200a8035600824146012480d0094004082044044280e40721590781d07128800460719a446a60b02010010700021151500140454219540107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 265716232 1250 265714982 265714987
    0x1503010e1b070b090a021905011b0543060e040c0e12060405150903040603090606170a0b06031b0906130c091707050105070204020d091217060a0f03120302 68
    0x503150f15202040030356140c1e43c01c0c0c22450b9004158249191135001006051130300030b128a1501000034004076640200c01004c00c4009200710401400340032040d1707840c01215031805c4080201807000c180240300c40842c00d10b082c00c40704260f20300300815407400c01c54290b0b4440700c81d070141d640c2c240300c054a0804240003c020028143d240c21399644011140700d04d01203c0148038610700b91805d1850a0344254280c0000d5403103404000102800108036000e0322034a00d40402d02d1030840c900703180981030f51f807c127440c4501c06020f803140015000a2010a00c0d0140d0340c0c843d160b03107400c418142c40703d0710803d841111070000d440400190030502e42071501700102601c83c040745407403200c440b803c403850b03244448001440188100010510003894604151615001d0b03d9500d10740300c0007a00e14441c08400074042c0b500031404c0c1000010303d0340052441c0c0d82001301e4414001d22500020089440782c1d18080c115007001001c29081d042030b903440b6080d09c0f440100898218155260404444400c0403003404140d000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 265717482 1250 265716232 265716247
    0x3080c1308030c25080715022b12140105190e041b24030b06190918050c0708070203030f0403061409030705070b030a020c0708060103021503010e1b 65
    0x4100408021100c88051316491140f10204180c0403100c540c1401080940348080c000314801140c414101c81c2641200b02d9601000e440681c10200461090340b100300b4100100c01801c100003040360009643c5640d041c06c40b803449074809048684001842c80c4c00c0014200610550038221a40c080d02d90340c0314034901d0f400d03030b40d0a440404800d044400712660b02e80411690030890300c002080001d0310390240603811200041e0b0821115107078008101d000c064560b40c226805407500c04c1100c25018011102154107196004040d24400d45481380c48081d45000f040545800d501e40302d1302d400741d20580d85081c17524800e9140c9040da900a00416130b4103020807c030444126414030010401035101d25004502807070f2841200b402100010300c0341485800070844140056404910b160030344203e00c0340a9102d44941d810000207000c0c0c901520328070722a04001003030301003000078950704a80c07085804100c03112011300466003900080c0305451010030b000000c40c003026102c070218841088400c00441c01d2608 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 265718732 1250 265717482 265717499
    0x6060114070c0f0302040605090c07030507110d0308100803040b04031209120501091502030f04020d21120e1c0807050f040b03040201030b010f0c020904230d0f090303080c13 76
    0xb40f07a10448241e914800d04004509050107040f0041204036111b584501c0c040b0b02e106128840d1100040030048000b40c45410484031007407000d9004006000d0614800c034601d030140000c00103030341d0003a044114800020703031890004200c0d0191980d0954490609180d640e9484411240d401c081c000d000e4544170201c1d00701c00c81a5034210260091001294a8000742890741c3c140c403030340c0c240d009501d004208005130034203071480890704194141c03010900c2c440e060500080d850100b42a8154080c00322001c80d184990094000c1e15052100354100f103018924075100b81d0f1207807100102c14802e41d600f05401d8805000d039000503448070150400b14a0004400c2607680d1301e5019070004954901c002c0140801d550741407040700c050f03001c02c0c280300d45580e803042c0000d000b20041d000c009101d001e02c0c1c0d001404001c507008040014000004044060301d610450700f40d10342d1543c010f0340c5d0000c4c024070000f00d0310030302c9200744004a0303401d80c985070703402e80790000b850545600500c020000300c1d0212a0010300c802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 265719982 1250 265718732 265718753
    0x50309120d08010b090d080c1015080f03090a0308180d2108010b040510050d05070801030b090102040e061215040308061c02060306120a06110304020109090e0606011407 74
    0x38459005089541c9070303580c0c0503104001c181c020718102581031054806503200c8031003c480407600a01c07426282c1d000c440c005440c2400800481001e00d0070714401005a807618400320f01601c4560f41a038410800a0f2042c90b540c1c01481140b561181e50488200701081800d8010071402000c654001440610180812000c0340326030400c407849112804044070440c0606610a8400501d14120a440d45009040f240500944c02020712400e00c2003400405640960304407030050403960f00034405440c00c000e0181407890248020780e242c07201e000c0021980c690600c2210107070743c1d03d5000c0306103e8031000309025440011107000a002c3c400c4008450006540340d031050b210740d20a07929611945480018024805220841e000fa010790010240006035119000c0e02d9100c3c03c259a80c2500c400c01d400315916100c00c0108c081c0c19940b81c4074096090408d500c0086107c1c4d8004c1c1c0301c41d016075940f24149000c07200c0021044d54180c000e00c0c045000c540c41003000a5054038108485400c0480384e40b01c007541e0301d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 265721232 1250 265719982 265720009
    0x18070c080408070906050607051f0f1104240804170d050a15080c0307050409020f0604122904120329030d2109060204030803150316050109060309050309 67
    0xf640080740c100441003090040c0809064142c0e0302a0412040343e0715942d03180160222401b805494035021004200c00b94040e070502132070700809200c48419240092080c1e4041c0c0256540144002c64048131070b00350500241c0140c246540b50300381a81d8584880101404080b071068005004111540b0070b00a2802014000c88090100040c400751701001969002800c5e03004440d40c0d0040b00d000220340e540420100202c40c001d45010034103039820300c00610724500345100660b02c003030007042c045108110a140241040d22442c400d00d00c138a0580c2c00c3c044c0440b4440840048014941300140c0001c400001800a203074850a0210700b03100c00b07600e1030041410001d004d007901d140300b0300425a5807800708004e0629100c03a0800012400981c1411110700030014040c18296031107000000400c0400e9040714015a0032510392900c0c0c1c10300d01026400c800201b1500c45c428170901c0103010001070050314000031103005850b024900d900c3e00d90154007822070a1002c1d0b0f030902050006458948cc0e40c0c18a4024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 265722482 1250 265721232 265721249
    0x7090f0213150c0308150607150b0406030809010c0201120c0f02060c190503100e0f07110706021f0615080601090e061c08070501090b0604140618070c0804 68
    0x2100e00345006000c51000661200c0c02140b0002c024500c026008000c4070707603c2e601071901050555580c1907140d14240e104d24031a402c00c13000500c8005010750244400d00d0010125010f01030f00e5072003800c00050340c0340f50001030400b03042004080c1c5290301540100b120780e481810101c00b03903ca00d000300c0341103d20648543e0040f4050000c84c0c031600d54140803056000162007120350400044044541e00388440c240c0d01003e22500001244168035802c110000030302e1400342000052900c4503511007040c8040c1c424402050710104040803264020440905942c50b68ac020035125001e4002408a5203450004414840d41c5003008143c1e80790040600d0b02074141c9031107900c0380303027001400140441902d070f220000404c81c10007442445c2d5070b40081c184100384090704200500716a13043c030106d1031160080c0140107610341a5401c00304401406031a120345c4040b5020003901c0c18041142c514510202c904540c0041000c40d03003031500301c4002802d80c0040940c03503c0078180c0c016580b90b510541c00754008111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 265723732 1250 265722482 265722487
    0x12030c2001090909110103050c0c030301140109060c02030606090c090604080321070f050717120603160812160b0f310303052a040f0824060307090f02 66
    0x556507003107282e01d401401821400c01c82010191102111190721540711170406454401180381507601e84162010036a403113040d284d503542d6489001a62140c22901d0f51f0204d0b1010300001075640c0070b41c07802514181c02402510309036a6000c01c01202040c0280700d0224914244410310300d5880d00340c00f030405880428010341c2e8072251400e03054030300d48e40c07030503035103140b02c4c581c4204200361740e108481c4004048541403c44d1114038a1030540000b0310146020141d100740451084d4100b15040b81082c0100415020307a030550f103000c103a403c4111076502411100781d20241212000042c2c05000f090400c48040038400700300e0301641c50324820b1809507241425490070209100a80305400500c010940f1070665070240b08000c44112030f03c0a8404001a05050780d030030004103949842200030442c85c4074010301e490108000c00c03030005160880e000b03000204946e0000030583b0003002410b0200c10001d0f9510204155101040080c3c101009040340c0e050701900d40c0003e42c007981801755541d40200e0800140c3c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 265724982 1250 265723732 265723793
    0x30c051303110a0b0906070f0201052502191401051804060605030406050603030307091404240e0c0c030403080a0e040501030c0302090a1b030b010c0b0f0906090a0201050412030c 78
    0xa0f00d2009802091140070200b12000183d0356500494482079401601c20180111070700060318240100784484906080c140c0207001070188a02c5200d811303920031202421100c01d1b0720064046100903008a4a0180c1605001d82c0c41d5030041c009010041b4188080d803d25601c2c1d0004107080c0e9003141d000d00b0115a005c42840100240381c020701d0750021040e801141185401d070001090800c10784036041901150640581c0680c1703031900320940d11240e5400d15031281d040050107039550010b5108241000c29079070041000f072076801c0100c2e4018200341000b142890300715120b40505521070880f9405004240c803d1150607111402024001c6004640010704170785140140700100000a002100c5107182005011000728494200380340c0e20000e01c0c002030302a420b4001a0303034103d860303d03000e008042c0510800130405180d000e12441403002c8001e8407000e88030110015500c120308000203000c0b40f01800144803e25401c00c85903101c2d4040d00e0000c1051a1580b20298421a01103840311203003044004407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 265726232 1250 265724982 265724989
    0x402012a1202010b011d030714010309170417061b0f0d05070503060a240302030a0609050a15061419090909050c0306070203070209060d03031b0302040807060e010f030c05130311 78
    0x84c06d0034a041c0280d100c00846540010351a010711b40240c03100447d903807600c621710342d1003980407803546075100c1d0700c1460410140414103410b411a03c55880d0101140001c41001d4601180c520b008402560066010002d01c54101e0740e1034011080324038141409000204001c401405030a000351200d03241c1540d00d0901000f840307103520f8560040d8143c07042001c4207118503180000d82e0203980c3c0152a00503141c3d10f0f0610300b000038008950201c0d00c0141804c0c18440400c0e082e6020124401c4000e24004e02c16940307410a9070b420314050381564200c20248840c00c0301581c095504a2030690a00c0e2100b03c56031644107880481d103803408241c401d50300141d000000b504003040490b4200b20240029030401e1940c1d400151098001001076004180c00c03840042014004d41008c1d40c0001840d0b90035405081e4140b00900941180c49200c0103407040f20b500055050051040d0030129038183e6078900300e40700c10700003034029200220fa610308000c030402c0908041e145805058025500c04d000b60b11043d00307240d080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 265727482 1250 265726232 265726247
    0xc010b0d0f0c050603040b0a09030e060403080409060e100b070302010b1c0507230f04020f030c071b150503150a06020706030506030f070e070203070f0f020909060402012a1202010b01 80
    0x10134040c1c1c20030070500c0045600b641141c3d0380480903e20202d00c0015500c1d048480324041315072141c000b42c0c0030802108005c5c00a001c0c0040d51101d2100300314060352040e4040e172401c03003039400310034000000300d003802280c0510009243c401d00900022440403100c4012409029441403400000522195a42c1c1045010f108001c02000d1849591503c1c1100d07100f2032641301034034111180716030450620000c85840b1501500c0f407280c14490603d1300c9181c0440b100c40303140e01a01c6d00301c0355000300c01400d9220000c100c2003e0180c40d80c2007841a6a012002000c0d02d00c3e600103003410b0504169203680c03c000396500203039100601025400b800d400c0f80b901801030161007000e882c0612a41080030750042030080080e035282242c1901c00710700c00390784864400340d04511910380301825012900d00c6d00818050724009450116100b038504040c00d903078028146440e001c040c1c40c02800500e03c403180d40038542c02c03120f09145118800c5516940f1070100e50f104000e802c1180c10140160f5140c03031081d0003030740e0400760 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 265728732 1250 265727482 265727489
    0x3020309010f0507020717010f050f10090219030f0b03120d060e04020f0d080c070f03410304170a0606060804080720060d0b030c0a1206020c010b0d0f0c 67
    0xb8288818100f44a01944651007401100035883c04182a060092801d4006036070f0285d50300000c100c1814523140c6003030000011035641c403420b241c4110010703d1050070302c21500440c001043d4103659400d480000c5000d40b0024403201042512030030b18529560f424003404c807482200040fa40d0351466218206403da443c03640c8139010080540c03042101503101c4554104546c10104d9514481d84070902d4414001e003c7c5444500040c45001c40102c0c01380d07411400d101c1920300540600c000260b446003480b11307072040e00740d80e2040680e5078800c2000305400180d1040d54041c4031005d580c101516502c2e11418003084c43e40110166020902c403000344180f03803141202401c8546086030f11854903880d21100380c854280c000b00552001110701c0c420310f0301000c0c80d00c00118001d008607902c000303c40c40070000e0480010018401e00464900d83c4980c40c00f8400002120768500c084045c1201c182c0b15030000790070000078180306548404400082d507440b400c000c10128032591a4184c40340b05070030b10b401c40d03064a40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 265729982 1250 265728732 265728761
    0x918061712070f020d1a01090f0b0303340615050d0503030705130e090604050c10090302120c120d02010c080f010302120c0303030106110105130305072a060302030901 73
    0x1401e5090038012044415041e0040008546181c00c1c1c0b002c60090320341001c01410411952900e004154000d00c40b96040b01c8401d0740610070400c010041004075400314040c0c50b85a80208501407a4002c4c4c094865292080d12034100c482c401070001d913441c0d9803c0018202d900d00d0f994080c200c40f2101010040010300400e071018100c8454950703515540b4480a440c0506000002c81e0344800212035010000c003400a801000000d0300b0b007181c3d00360b0b4030281528100d0703040c040d01502c1140380c1891040304980c2c0e02e95a5540003030700d1840e020302411015411102106018560b0155003948590b22031000d2940c0920083c0881d001d410002801c465140f140801004604410b008648100f294040d0550703404403403038440009002c148625009d0210f0880350180004400010002c0c0c00040414400c100d060090203a07996002d40015400710b041c00040101e0010720484003c5640b00f2040800e07205080448401c04d441521842146061580700c3c3e00001c0d000410800d045000780184c078030950110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 265731232 1250 265729982 265729993
    0xb13050601060c0215120f0a090c030f200603061216060c0c06090617070e150903190b040809031e164104090b040b070819020a09180617 60
    0x2410080d1004102807d00003c805494010400708145507012982c11a4002c05a4030501c2c1d9918089d406d40c0755084060b039004a00d110070f40813007030140321482c2401100074070082c82c3d42d0781c10041022000302c0d10504502032180c80c2c4262940211400404083e120300e8440c010034040524042580384c0440e003251041014102c1c040102d01d421400402000c0160040040644e851442c02c0700c0c60048140d070a51311000c1482c1d1020415800c1008080100341901582d041e202051040700c0402c0900800414018507100000c0110300e400019003a58480102a40d800041c01e11141074a203503102c01c050500d801003e1003c6c000f650314105036000307003640c40c00c403005039000410384143c49020750b0300304d5940c0303000c0000c801da9040600d032a18a0710034003c00070031410070b081c206031030300e1038044400b125003071019804210310030f02440c5058428606030044000303448446a500c0c0103500700d15070180030311103c1c06021a102404602071a6464061b5400159191802800c01100b11300c0400403072031500007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 265732482 1250 265731232 265731247
    0x6010906051809151f0507060b041e0504051608030d0e0106080303010305061005010306061704030207350105060603070c0c09050a1514030325081306030e0c0a030b13050601060c0215 80
    0x1041d6141550006400154583c4840100780640001c041d805008014080cbd5110405100d500c007138040c6000c0c500300d418680b651200c44541c3c40c0700340105001507205118079003540300550000350126220b200082a041ea6940398245150003c1c0c00c12a0150449000c12083c0c140d01c06000c0300406013443c05100c02c1745000e00191882544070050007d051240d40044c2c1850b0003002014014003154411262602d81441c2c2a0510314040401d42035190020101d400424414020706005440003028280b564a6045040d200040c0300541210742d502e400a0000d0030b524148141845041526004160680142c00102c40c07070048d50403c50701c40ca190070480d0442d8400109a54084c0840705620807100c8500440c41c1c1e1280c01d034040100007450016007140d06c1841265070b14202d81690b00d040c4220340c156041c182d00d03503885040040e00070760409000c20100b0800e804541d0800e010409400d800c24103034407141c2c02d203c000d0704070401180c0c10110001c11420480c207003076000007404020a090500c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 265733732 1250 265732482 265732487
    0xa03050307020d020d0509040507020c030d021f090812090715110d090b0f0904090c090b190e04060b011e09080717070e090f0109120801080606010906051809151f 71
    0x50200d03254000c0f51b89c2d20011340164000c100803181001c0040c1200d40f880b24500d0300940d114000d1860008410801c078001400030064001c11081d01d51281c00d030303410440c00c44041c031501000180224114411a080000d650110061706040f040081d52175011002007241141d2800f0f040410071400c110204004102c0081104190340ea4180c150800c265901c08510001d4044d205030b8101400c1d41c280070200007908038141e0711080c41420103803105885201e00c2e07020036002d94190320403815500c8007800054002480c82d07102045142050402c0a01d010303904020801002480c4610000f10701c0c0c3d00820300c02d1000c00c001c80c4004001100100590081e00b40000380c0310545485021490189100415000c0d1b90a0080c190041c648074001c120000107820300c2c544400f40003100c3d0022404020010948000115101c0d10502040e1211804249440ca0441c0c0550001c920030070503442c2c190003050f580c0d461140c964000c03120221003d0740c00c025801001000041d000c1c62411a0440360000701c1100d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 265734982 1250 265733732 265733737
    0x90914041106031503100c02280308101d0a05162019030e041503050d0e060c0304060309120503060108160309080301090c020106080303070923030a03050307020d020d05 74
    0x5009450301d988030b8840d580d0081c08130101580f542c0c0d042c0140b4081007409409039129059a01903030f802c0320140110300c4070003083e0303501741c01144640baa254803a410100e80240c15168022a6044141c40041e90f900803041214011310440d014402c0c00324140003805a59000e40da80048c0c40681e101801300c000d4002505009042c10304821102c000c0e4508400c0010034030400040c0101402c0c0e002c88201c592034010014000042e04522882c035149a02d0403c0c50400340300400c1e42d03400700050180c4070f001c44090302e5540c2504d403515400b18041100720500202400907000421480e00c0c08541d0000e0351400d010040c040242080c01c11a00f031040002a80c1c1c004801500034070b0041c03070880c035159058012000b030110380d407000c0c0c040040080005050307100e030b902143c0d5198441c3e00030801c2688551200d0385030301c801d0341d4150005403011030501403078082101101c501b800d031903002c0f00010341603000300707050001c2c95900340c0104030b01008100e5031030b40501c2042c6040c90b240c40501699150303c84050280e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 265736232 1250 265734982 265735013
    0xc03050a05060a1437080a0b0a2d020901030b18220f0c150201050412110a05010f0b15090a0612020912030307090f050f01180b0a09091404 61
    0x44c0659070499080d1510fa10b11800001408014031083d03000842d818096080588031210644600130009031613080416103019155009032408240d403603098081d0702030000380580110440114035030400c400c101e008000550040644003503104c801034400582200e040080e07442c041c6002641c960400503460a045510280c0f005100b40d111a1403c10109600c2d8500d10082180036480d100105112035840c140040703601c10b0703c00000c41705c60b0803012803c0c0e80043d140140604c66513030034150110f0180e064000720721143d4041710780f401e40c10b0700c540742035424816181c02d4035a541d90500f042c0e0b040c01c043c01d90f00660040305007843c2685003004203100d80703014400c00c000c010f1042c49040318445030b90100c40c9034250052064013010416070030703c0c0c0c9a038001d85040e8007199480600041e4041c2030b200c000c044600c02010000e091652200554a11600b2030700d1002a02885c1000b049240c09030020740082001ca607910b034034050414012408071a1515100d90140710144200000100b58081c002040b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 265737482 1250 265736232 265736249
    0x90501050f0103150306090803040b07050a1d01020a061d0f1603020105090d0204020d050a0c030e07030b070203070b0a060f0f03050303130203030c0102071b05040510030f080d09060c03050a05060a 86
    0x7525114405044d110054000803c841d0811018a0610194002842c0190301680d515602038803007a0307054419100c1ca841c20170120714000e5100502c402205031030344103040103006403a81d04a0300c4d510b6204581d07110400041210300e00703061004500042004d034800350800c6e002071400c0000c03902010a5850f00e480700a04104000801b00380da9180c1c186001070071076000e401951100010750022020780717000c490820020340740c1a40d450880b8464083c805101307074010082c103e96030954480300d950040082815082d44010005200042c1c100194079200e90181d030740010704c4600f020b4110710030880aa01c0307000310201082c820b1010460110840b0f810039880c41808640204920120341140a0481d50040c9544041500002e12240e28001506040015aa2440f06d034498003040103c510588010046400c0f403041803002451640603610400c0c026284542021449200b080564107440320031a20192252003481e01c884d014040c070340e000b41c21100b09000d2071400901003843d200e818450442d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 265738732 1250 265737482 265737491
    0xe060712050c1b030702010f03051608130b0403020a110907090605090d0507080c0f100207030305030406060e0c0a02010c020609120a11030307030605030723092e0609090501050f0103 80
    0x3000000081100c460408144a03460440700340418142c40e6040704500b85d001c81c680c8123117010882d00c6485142e11400300343c01c283c0c503104850a000c80c0e480c0b0f0000d01042002018818410102c0d2400c2c26a5100d54486c0d401029102c3d082c0c80d01d60b6007020040c1046020300105000c2c80a0942c01c80c0e03c1c10181c0d800e5250550b03e545800000a40300802800040c040d4001d40d9004581010041024001808207070390381c1c7c04491a070340c1031241500804140c02d006070404c110a1002030302c103d00454000740100ba01003190f0ba00e5410540b105d00b07060760607090700400000c1d4802c0040d028042c102013003140e400a4800d07407402c04290b079180c006003014070318001000501c00040324041c1640010030f400c858212510380c604a600600180402c0c0141842480b0f0810001506521003030710240e00c0100a0401c994007480c5001d000010740d0180242500780e039441c81000386003665502c1e500c00c840d01d0b9030046090524110018003c141103070014590f0390306080061107035454100440c69034400a280009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 265739982 1250 265738732 265738741
    0x100507121d040e01050604060617070e012006041103160311040603170a0e0307030c062312100503010908090607030908031804060b16060b0103020903011e0e06071205 73
    0x14007501503000c00759005280003060340401c44154800c522030f132015101009010349402d800e55002d032594102c0c9a13508050b800040d1341c0d51240e068060419010304100c440001420420f003543e61002264004660058041009000c04640e429078040800e4010380019500c00b2002d00c8a0045030002410041e03140043c84007903162984200011360f00410700513a061210b1281010316803155170303e41c00048005010071594900800c07011b0869900c00c80c0d00d241140303070100c1a190724103c006001c0d8102c484d01d500e201d421440b08002c11140c090641e190301c907032030803101e102082031307036904964000c0c0e15204031000046c03820740c11129070900444525850f61078518041300e25208681003640c0a000c00300d43c00d1049083c4c0b101d45070b40b181040343e09124190722001d915405020309a415281d000813060900c01003252a032001800d81410b25015141c601d264011a080d6040c032041180054042c075107000030481ca0f4442c01e40201d002c10041c00035800c00045c020006d42d0131080c4000056640e0f00400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 265741232 1250 265739982 265740017
    0x11070b06090429060a0b03010f0e15060d0f05010806010b0f090a0510050301031505071d0411130503070b122707060903031206053a06060510050712 65
    0x240030324296202c842101c1840d4458818050030303121217018495080c000706030b1219030f40949059903440302101e00140d140800031248050050b00c0350542c080e44600010103a01c03134000806008072044030206048009000721412104160312115440d00300c9401403000c02d25185c01c4480e8802c00c07500058903490040006141c01c61154442c0e86c0c0300801704820101c2d15000320145049a014180303000100c0c900100550984508840b030100040c100500195951084020150501c1001e07000107505040750300f80b84019400803032212201d100c031741e8040025140400c03451000c1c0255030220303414012070013840050124050107983e0b81494903150b0091403c103020004e00301c000e405084410b2241c0d01c00300940300849900007940001c0c1110b50f150a0400ca07402007201310381c2c014180500041e00c8100000c41080c0385c4070061074041c0030f2544600ea240c0b08040c01241680204000900940741c04100b04250006400002c03e00c2018841c203404152026040d00300c11065003440058040301ca46d03070703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 265742482 1250 265741232 265741253
    0x80c0711040204091b02010e07150c050f06190b0a060323070c061a01080c0d0e03030103050715140405041802130e01050c091f111c0311070b060904 65
    0x100e90030078804240020980a01e40090186880800080320309041c2e50b4422402c1e0303a203421140b00705500502d410400310048a0140006510502e4406643d43d800e0342c0305810440803004012081d881301003440b58034000a60300540700c00c403541d400c0112420620214a004681e48526010b240d40c2c2c6d00740c0700c0d9040408000100900c00e400030096103150407500a041410825025100b040c82c141e0a80034103d5071a40e104800c140503121120305643d0318421243d954041b11141026035181d8441c17070390400042018501951085002c2d04821b030408940040e200d61520003203041025441860080002840071181641c0e000c0d140030072810502d06003581c008811000080d04164a440c00303410480e82e50b4080d100c0d90f1403c0000b0b001c00d44410500340d03100c3c0580c03040585d101480c91042d00c4c030a04080544035200d1a00d00346004003502d64840103050106001032801c4d00364100c06510074141d890b100f103807126100c40241900f010059128610040c00091200380140c003007901003428841d0681c5c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 265743732 1250 265742482 265742513
    0x110d03020114070206040c0506030402031e07120c091b0815150403081209070614030414060403021e0601180e0c0a0b091c2112050a05010509070f080c07 67
    0x302142c85041143d002951040d0450301a00c0e02031030804041a54500402124020358004000303080c245006000030f096803501003050749540c03003548000140c1d803203540c10035154103000d0150b0840840c0780500300d0701500d00c4404050b02100c003c6041440c007a400c89070007604041c1c40071900b1210038511020840150240701000c0403500c0106000080069100042c406000880142d90054560116043da641d099000d018041a0b140d60081802c48403003020b503500902920380c0901550320580803070700708107040e5801d40040c0c0100e1711400301c6d00c01e0001140c0d86a9000b0004150941c58a100c04000d4640704080c0c3e40300c5c546070840354503109401c0110301d01c6144020041c9050583d50803058450354001074115020796100c0150342c0d460b00c65a0f1048918540000045510780718040741c0700341a6118007000c005001c03d55904c1070803414203210703c6214061003280050030394140400c0102000d4010080c1c0100b0070f1071500b0810b040e41c401e030b01d540c00001000d03e09449520910301b42840322413070350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 265744982 1250 265743732 265743761
    0x621030c01110a1e1d0303070f050109020102060115090302041d010c02030d0b030a1e020a0801110d05090a24060504020c030a032a0e061603080403021009110d030201 73
    0x4115952071045400420b4800f5041d10b9003200007950031501030044180d010b20a0104003942190030140b001069003c03d80f135002419246800c170b050742c0760303109410b03090707000d50b8141c0d5079a4403c001c65804200003409000d03924042502103864a900030443c0b00c840c00002d000d1a200e800c05007808a850360208011000340e002401510403041d40255242c04c0145045112400c003010100e10b400d0100390401442c0d0800e24041010740d00340c15204202d05d900790102c1e0048030582000a002c0400c0c81585800300352804442e5903411001000d8003521400b41610f1031075005401c0d0140000d044225200a501c0c182d031400342e00c0364802486c4002421558030080d0024000034203030303c010001000030002d50440b83c804000c10026803d51084c4007045c0d071468000000740b074000c400b08034051181c5440030003005004601e041c0d110380c1c0e101e00541c5011400c801141c9a00140300c00c268044c40000000041c0040030054504d59071614813070a2000031a4038042c0c003009440c0401c0c0751003900702c42c4080e0b0402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 265746232 1250 265744982 265744991
    0x11010504031e0b1b09190e0a021809010806040308040302010e030a0c141906020702030c120a05010b0105090a1a040806071d0103110304110f130c0201140621030c01 72
    0x1503401d8141c944485000b15900303524000090200300002218004c80c0c0b11210505007055941410701103050303604807a401410b0300140f000100100c1c000e031110b200304102e500158507041e10182d0360307640284010f00d80303224802d80303001403044d5400000c2590384203070903240c12805515070f0305007a40103003ca00c134444440d0100080311418941c1244000031000c1c842c03907910b90501202846d5544501030507855035008003544100d440072403800d130007401301d02c0d000605403500d49003814001941000c00c0340503514650025803186080c41028414005844001c0c20054a019030580001380d503102d5034000d02c05500507001e0301d0030030b1956940c03d95002d0440d840417255a81403001d4050700755601e0300101c0303040c9503181c0490101544240602040007080382d03406400c54940e940d64030000c55400c481c1c1900301031002603111803590780d240c41642d0910140c10001d2440b0710a10001c0c00c1d11095014000c0200300c8400740080b6846401c881d50700c02c24000828080780c190301c80d0450842c407414040242c0340d800c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 265747482 1250 265746232 265746263
    0x80105070302120901090c1503020903191109040816030c02060307080f071403071d0411090a050a0302030a2604030b18060f06100309050601081e060c071101050403 72
    0x50350040c2004404040c03e00c42980e60460414261031541900800c00030000100704211560040018083c01042c107003d41800c41403004240341072202da4412054900510300d0f1400d00c0030000b40d40504010135a601a010f24042c0c5034280617100c3c0207000b201c5c00c40940020001e16101e900c8010b049640144a1581d030b0030700f13403801029140e040d60307844928210200400e0381c1c203000d04074115254280c04206825991402d2060300e004015000c0390b0385000c04190214501c0d03689220300c04515100c4603815444182c6207081c040c0c0b03004283c0101c1d015164051007030015940029000f115560321a44d10a0446040d03001404c000f0180140d041640c1800b16001c010400003903400c611404200150405c01451920859503070030040d01e071a400440c46101140140c100048410003002c030905001c145e090f4140e54041c98074000342c6c4107a1080e045801c95024048007400121007070700340c8000402e0700d814204055580c0b803140ba200100341410302c41e606145030340140c003554004d40c0c0150505408426 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 265748732 1250 265747482 265747487
    0x24060c060415050c0313020618121516020c041a09040b07120b010e1011070801020d0c020102131418010e0601030c08010f050f060d060803070c08010c050307031508010507 75
    0x3042d00ca603203606040c0400500110000000d1704c1c40f40d2490740d0062004040c0c1c1d000d000003035000c054511450720364202080c0785500c400014280100d07210300203007030324090310040c00310080f0702070005070240039040c44c0080f0341a800260303001109011540001c001c000401d2001d98020071010f500c3e0448110000c00c41401000260a440390b8115100c00c0b0304c0f0002c0000d2102202c00c2040f030580494041e55000d010350801010128803202c0c982094450644079408062400703a0941c0300508503900029a070024600c2800380920081840c0000d50400035507008450040340180070704600907950b00c800754542d90710030700d822540302c0c450074a220055031160544181c6a000315825800f0a06104244183d03910030001d0318122a068a06441894105010049101c44070303d1100e034056810301240701040b15a1241c040100b4484004549e02c0b062803801c681080c0c0c042c1c2c030600d4140d140c8420110350503007010450358400b4080c5000074442000045195084a02e60030040c0c00c0c1d0710300400c00250a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 265749982 1250 265748732 265748753
    0x120218040c090f0b030606030415061a04031a010510110109081606380102011b0819091703090307050a060c030e1c050318060f0613020324060c0604 65
    0x510b009001500c0d40c0c1c80c4c4241142c0c0d03103c01d5442c10f030440402c20015012403800d100c0041408200ca001051083d43c9030340d6880000e8880f03c0200510703400090400400a512101c00100780200b6094103603903161100051068168001e020180035042c0d558251030079003035000e103500c5a40080f10548134890b01e101c1c1d00322441c2d5928111203862030325a00041011032005078014036141040d984010640070088480406442141c59041d5900c42c0b000d180034001552041c40840981d58840c1c6d440e00c1e1030381459075080910a1122401480d000c081000700b170100c1d081050f80794002206903525241c40382520f1461140d500040e0807809000e014004000c5250861010000329590501903008103e101903154200360700302d00ca40307000340c8011440d41c82c014400b03194029081e984008800c003040101a00344402111801d41071442a030421819103070400841404084880c0114154039100c4c2804994204841c0180c0144070034200c502c1c3d00d55242c00856000f04a500d00f43da02c103051901c1d000c200701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 265751232 1250 265749982 265749989
    0xb040f140115210201032003130227010e07110f010e2112040201090f0b0409110a0c15060801020f1305010e062b0207030e03010b03060601120218040c09 67
    0x1842d54100080200082c00900d41c51000444551803401031070b80190000c1c202885150243c034a41a0350040004018020b14442d0030201211100d807080c610410180c8030125420401a03402030401048800c0c0d80301c8800c1c1540c40d0f1202c541c0391911002d0050701c0f40c1b4210321f9071007141d200c0c103840c183c08860190040c10030b90701e0f220203c0f14120a811020414981c420485240d2280f040c01000800310089040d03681080c0107044c102d0300181c4a080320002a007198009010049000404010842c858030504020403c41644070703040090a01004190035032140c0040e0002c01404001449099160f00800040c08040c008650316a1a01440d0ba0150003120090b43e0500320b441e40016294040c0511183d2080c00400d00c915090040e030a02c07560421002c52407550340c01e400020f00181b00303188018030086003ea03c0f07040f41241a0b204041c2501d000c3c0c80b00364085c0d003144043c000c071642c00408042140c101130340c02507102c0c401014403156840c160100709030b1140c04c00180c40c5800d500002540e0a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 265752482 1250 265751232 265751261
    0xb010206011514030a06030c0e0f01090618023108060907081c0302130b0912011a06090f0d0b0105150f0f09030319110d08090303040b040f1401 63
    0xc0c1ea0b1030703868a8100c11441d8480002c0f0fa8035a000003902c40e602d80007140c1c881a003120001700c49131603454000301140315800104803000321b002807001180881343e029005250410050015030300384144500508044d05030389454580108401c0900680034181c03806481e40c044000e82c254211088054004000303205991440c01000081480e4400c0895540300ba203842c0c000503c43d50905003807c950078541d5400d4801019421705c400d000031041c5000b9800107140503020551504d0604042040c201e14104003640c15031724001803150040030500300710700c2041d81118403903141c0100341d0111b08000701200d4400c0d4441b00840d2000204601480d82905891081d143c84c01101102401540c0701c1c07140e00440411300c8010700000b859802200c0040a254a0140c2560b003071800c0c52695198046040120303c0c08518001c0c0034000e02d039810805040c6c4100301f8a0442190305100c64820707200d21002e000a0541101800020280000340c040d5000c400e41c000784500e055040700703e080f4001c01600070250314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 265753732 1250 265752482 265752493
    0x303090f01051216030c110303011e0909030e010305070f0f030c090902030c0d14040506040206070204091b090b03010614040f09080a030f0b090606030718080f030403020306010b0a091401031404060b0102 89
    0xc00507c100c604c6440c1d6508900298030f141d00340035258ae004010765009446e898050035020482400a0240c41c0031148251201c6a44071402c10000d42a10300060555040140709500302907071a5100d600540103120606001401c46100002240d803108103800c81c914140c0000140320903502424018540c40d042c0100822040301003142c080d0040c0800d507006032a5501c41000b083c00740c6810070040800b02d100603c001084141da903210b200d80d41c01401c084060300c099410400864045004601122004400070040903042016030900440405200c500559480c42c148142c101c83da0b1014525541200e10543c54030110384009010304401106801e00900b1f10184c1d8100782000d094150040c04003e000c1ea04507075541c0301c201e954a0141c2600401540e210000142c818401e019154601e160750002d90b513a9401c40c0180351400794181d0125050720000c02070214440d501c09800002c0d50035260303810040800d1400101e01400b00b0520005880c4005000e00c810400aa80000300003203080e02910b1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 265754982 1250 265753732 265753751
    0x51c0213091a09030d0c020f060109061505030a060b030f0711120403030c02010201060302152206020a02060d140a0b120c1c06090c0605030702061003020303090f0105121603 76
    0x1420380340c01400040420841480c40b800c204a54111580d0046400c1c003102c0c20188404801e6060310101100038015030007202c140c0607013983c20b01c590341c051325503000180003072498120b01901d071620401025041010200c0842c3c0c20507104e4110400818401110070349038188612031203c03441d002c0c3d41e500c0201d44034a0818548c91f00200f80d0700d01111480c400942000d1940d1019100c550324004200d0455603100c00100050361294a61b210110304694010b80b03c12102c030fa02c88060081c840010300c43e0341110410003149a0000349103444a506503079050701c41c01d0244440014101c000108154444170504100c0400746aa002d03050522040790941031b04002c00a8440c1c4a0f030f102220650441809403481580c3c2da03103c0d051911951040070001a0403407681c540c02038203c6075400c0100024400410700102a50400c40300b0341108075450b103601064038584c0041d90f00d11580009501410f515950b110403030780901d060f146652074881c0742135540e01d0612290680c0c188101c0030304c00461314010040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 265756232 1250 265754982 265755019
    0x7050d0f120c020303040303020f1215011412062e05030402040f02091518030a0602120f090706230c010f05010909020603040b1b070606050103060509090a030f0207051c02 75
    0x5034042c04241d0043c1d86183c41e1614102d0103075001402070368400408021085041c05a51501481038120720340780c0e0700040282c0700040c80c1d40004140b00d259aa010310041d6001c0c01c1000f01355411410484008030361036075814691403940c1040c00d101c0d100341800300d4034503805038004004601c02e0307100711010400011191201c000700d01540810540100c01d4905545030050400010a0031006101c00e0500e0b101c4031070300103464aa80c540b800c454841d00481c8003401030240500310b5030010810a01c09091785452004203540d103060b84622000c10880d5101903680001114109012503c070048040d680e1446410700c070702810003d6101c2c0700052600b00000342c428042d120710880e0035402001d444c595200c5881e404001100a0100c045181e00751220f41d03002805000140f800074454079001c681c0c903150800150803128150b100f05c4c004c280e6401040201e1001180099449600d810030f0750312203084100c120300d8642550000c42d0445842c007045103c6000c459178044101d4402c503a40300c0c0050414806 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 265757482 1250 265756232 265756241
    0x91119030216050f0c0a1a030f040201020a0f0614010506041d2502101406060f0315040c0f0906020106050112110405091003060c0203030103020d260d02070501060503010207030c1214030406050108010e060c030112030507050d0f12 100
    0x502e40c0081641d020071851740c0303115015b00e400020303441030240000003152003840f4224050000340301581c0000880c9506540601034106032085271003c0c40d140703142c00300202d42d0901c03078844180c048400010001c0d65050703041d9024640d007071025008004e402c0e0180b0703010307060103031038805007011851542300041c94901c14000c1c0341c2941d00603520700c1c0c0110320308945000030341001a400c58881c00e0030302004c940d81d00d900c40c14034841c02a00140c014000d01d03501303240003103500d244000c02c1190010030041c4090384030760404103030341680524150040e646042c4903040300341c9403041460440400140301001400746802604483d40908005c0003e50350300c60406080f0302c20000300802060b00c0e880800b003c03500000164800003590700f424107410456144014040d8411a4100c9100d9900c800500c01e01000748501f503800300c0c81500411941c2000000d02810340414450641c414850b18401c01c1018030400035240c503254010708a9005030b20803800901405200110400000c0750128600c4440081d400b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 265758732 1250 265757482 265757489
    0xc0c1d10031e0503040e0a05011502010212040311010b0405010311030d0201060305071707080109050d1d0108010509090c040e0304091119030216050f0c0a1a030f040201020a0f061401050604 83
    0x6030481402020001c103000310714005001d9443e07000501000580104180509109003c0088005030a40c14084a00c8164060301a84000c580c818001c051006215078003c54000d070f01400c0007000040071940243c09491403410450304607043c1030001003001254104038400725811819211104071040049088030304074480640654417400e0200008241c10042c000c031001090161884036885052990030342d440e008081701c060b0b104d214403001c0c2551144c0d84202062860b044010410109400204000010f001d4984140d68003008600840410007030b40e44a900c0c003070024000c04515200890716a0800c1c03080c0c1200d02d08080c56241c280290034200c502580c2c00c0440703a03c4006403038000b10004e41000d4004010890844502c00102d00d040000c036140900601c02022180c1d904014800d14a4060340407541d0040301c0c40c19480312045080550354842044c1c0f014905076616400100c5c5401606200540b0314030301803180f101400515080b900c0d00f40081c10700700e2103e99850041c400240314510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 265759982 1250 265758732 265758743
    0xf0207020a05040513050609032116030b03030c1e070b0307080f04060b060f13050609030717011113140316090c021c02031206040911100c0c1d1003 65
    0x2007080c08a0b00c0c103984032030b0300048a81251103504c1e0301a5100d41c80c0a20039070360050660300114507640816616415005c140e403000e64440000c1c142844810f032447d209405500c285501d9400510309600c080090700c2c002c8004408071045800c51441d40c01c6544004100072110b8011600c0100d1810251012070b0b000c0c4140f50b0324000c0c0ca5607500400542e032540588100d030b035203440e04145145640c400018107a21180d8000883c0d8402c042001c40360202500ea03c090f001c0c601c03c0c07041e0450340c0e13070208981040781c104200e4140113202151602d80186201005122000c501080714046071609a03080740c01d441c02c0364007000502c2c2c078000415a444040501542da810b01c18902881030381d1080d000a51135040d1030040b12130751001114240c001000b000c0365500140d00116a01001216a4940d980c0109080d04d08101c03140c95074407890494135800c0c0102e4052201001031106143c807c64010a100f80c0160401740380a455041c1448030030041e60314001e0840705207002c02c0c03144801c544010100da0707110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 265761232 1250 265759982 265759999
    0x405060c03100302040606030c0815130c0909020403081902072105030d050403121409120903070801230117070302100c05151b0304030f0e0f190303030f020702 70
    0x1418100d1550320040000e8144011a0000401078a4900640e8050150342e207010800c0100384800604417a401803200141c0802c0e100c1c1c11711039841351007044651900560f80803031090032000040e29007489590040b48482d100017000420f00031008041c0c0f0643c80d03585400041ca1901c0304c8201d9a984080c0107180114500c03c60b1450300780312042003003100030303c00c805590600c0380802644080b40c1080340c050b0701151141d03100c211482d1091050000c10f94460074203407101d08000f4411a59010800c1d110039005000003541c90003a0b400700481802850110020301103803142c1d40390444203030b00c0c040d00d86142c0104917001041e0000e03035581c6003401a03005030041c082149180c0802c12480c40c0d0600c088148582082e2880100c2c4041c0074021414080d41c04825880c01d060222402c1c510311401043c20350072090007031000107540072010b0071000190345002d1500d2400c400009417003142101a19510411116020342c0c4030207003511401c104c1e4002d40301003218582241c41007060344103c20009500042c1c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 265762482 1250 265761232 265761241
    0xc0a080c090111030a03051906080a1b030209010801060e0606160201121512050601060c0b0414071d0601090501020c0a03080714010e06090d051602010c0201110d050c0f010203040506 80
    0x2a001d0094a10145490702c0e1004405550764207680c045136000002a4403081000284504801c104411005902c020017400c0c0c03400310070715290300c06644010211580c1d480c2187d110201d20407441c0265800030945055540d58140e1140201864420304d056115500001a80c9107000320aa409a40d440215800d02240c2c03980112454110b2201100c01d9680c1c5d80203865104000020700009009242e031a08842d0000d420000d26092050340f0420030014174950000c0014440d500664020782d20017080040f03002c9281100f414000c694000034401d0340012807080804c506035a100340035050a03210341c007426840b031004a0302e5550500130b50383c01002019040002a01d19401020320398068000210007651134610b05081d01d0303540000450a610000c188407070302e10140501079907000541019450020b03008aa20303c410305000000e410300036507003401820369005211800c400c21008054a01c260319081016020750042e0764144202e11600050020280b4148201c0b030069400c880103111540c0d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 265763732 1250 265762482 265762501
    0x30411150a0c03091502070f23130f05100e07021c11011104031101080f0f180a020a06110d030509430306050f040b0f070203130806010e0c0a08 63
    0x90300782c224104040c0c0c0c100001d4094043c60385000300b14660f40035007444c3d4a80701400c55203000980000b01e0844c40c0c45411034030410180d09008107484240c41d00240900104540401030074035140302180b05051000304001d0b030394044060016115a41411101900c3d100c0c0d003260340306882d28031903800510481490302107500500042d040800c0e5900041620712140100c0d20703071500154000c4490707041d88000a4420340c1c03c4540e07142c0c0300d80c80d80c82402040c5016841041c035840003030f02c480c030a14600524145506000e0080c0c00038183c010740207140443c0e480100402908003504484094014402140440c40c8680116405101d004000700444c403e0200d010108226410a24100c510122031407010501030240e5404852807281a1500283c55030030008283d480003850001c000c0c85100411002410700c1160f00e0704802e80c0620082155500b240582c41c6104091211410007000080011f5040000624030f0503102c2c085061342d244d46070329104403180c3c01014492350100e952000020701d08403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 265764982 1250 265763732 265763747
    0x1804020309070803040b0a020708030a1b1a090a030909020f03150a0807080601081b0102031c060506070f050f060f1807032109080c010509060c0120030411150a 70
    0x21281d07030903545101d546454803482c581c0654030a41d4260780c0400c421034940d4042c00480020301d1040e020354a01041054000c240b50207210b45e41804400e0800014240003451248100301000c6200ca05207600388400280e0b2741d9142c00b40210000780401e58080b4031008030703009a03001c040c131104003503080d900d40042000b04158100007042c1c03ca03460f031100280387c1004000c80c100814040c1c025011b01c4d414600034500704003158440406030111440c122203140d03400803c4503540c00c5011040302c6072401c8818800007802603a03002d41d40c0b050000c1400f1040c04440d12500c0003952181040b1070300d411600215540b85c2504495007424002c41600103880e0400201101ca0070400510640303034a1a1245d50b01140120f80440c054055230070f0b101e0503031450b07400200c8030000d4030f00ca4000f4200401c40d040001c1052040ca04201d0080300e004c600d03613000300802d4024a046155800708442c403900300d484080d5043d081210195002100316402060038245030b21031650781802e80714484d04d06400003d0036642d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 265766232 1250 265764982 265764991
    0x4200f01170a0908120117070b030f060310020d02040e011a1603050904061401020c120c060903190b040201080c0702010c0201030c020f060423070506091203040308220b18040203 78
    0x490b211005400050004c8004000150006116500550402c0c0c4c0300705840084103601d55465110020510002a024007a031f40d100450580102d00f0740d80d02c0f00800d0800c8601c0000110713003400410740001940c0c1c26005002561809241143e0326a640c0c00d17801c0140070500c04c58617000000300240f00d06589021554115036000e800d00a1401002d01c0100b0100d0385950b1100c407808903e4140c004a960b030620103030541e101c040340c00107104858044503a8480e580004600d21410000030744501c103440a102201c0748022401c40c92180c0045d07820541d04200c07003258124000740c1d2140000d1031074100c031000e0703614058060f07440c121540340c258010340040c004100c2d00c000b544540310507244d9501301005a144124800e41c0710b00344071124004410a1440d450011820a4200f0b036010311003502ea440035145285000c50340f042c050180c107140c0710708610942c0c1014000340d8000030f5290000e20908414a01810407a501c90b03e815920300c03456026004d10325074048100c20307200c80d44035a45820380195800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 265767482 1250 265766232 265766251
    0x140d0207020a03082212050c012001050406020904051b0403021507080c1506040b0d080a03090803070c1e0519021912120206011a2104200f0117 63
    0x703190f03c0b5102c5800a8100d508031101100c440402c0000d0008902e00400090088003014000c080403a92065119415480780b24104054041080b01030755680305440c816222410017000142000e040c11401ba620004140c0c1c040c0d0306010108036130b185080f24403941c003a0b0280441d810b190460f404c11220341c85041725841111004d0101101242492004120751107482004200b20a94070f50b040040381ea00800710b901c154506262503036152030700160056856405954140e440e203010000354018140b014000e001d40501204000031300e500900019412401250614180c0900c0c20942d40f01010b5038100610750b4015000180b07144194a00701800144020f005404c44100751043c1c2c0d80d815029403008a5206828540f80188076600d80c650443c2e180a101400d0b031981000f9012410381a280d80c001030658000400340000d0040d00008861200182c5100205040c9401e19400e1200c03000740d00c0310b40c06010102d42d444c52814001d445104503040c0c43e00d00344503000101c0030718280381c01007201d0340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 265768732 1250 265767482 265767499
    0x3060103060513141014011401030f020d09141507050412020406030506160801090204080c06070609021903060c0e0a0b1810081006050702010509040504050c0307080616140d020702 79
    0x1a00c0040c0804c40024684001c1c0580c1c3d600c40c101030300343e600d10f180c0005040d0405005210312038a091003860718a4081c00c0110315140800252030080c0f045010144880389003150b40020060807a910850306501c1d40c044070300c9180e4262210b000303c502a0389030750105100304030400c0717024210958420745900040c00052400d0f0f4075201c040c20402c007200c0502d582c2c001011500310454018560a016145607501141418204494030b6036902801154a114050109141c0c0400c4656004881e00300e5000c1e114503030001e80100c440030f0450030780c00f044030031500b8100000284c0e031041f090283c54820092004252502d03101181119902041b64040c41810700404000280c039a811040f084a18aa0f070b9058140340041d4110100662030300700313004008041000b400540c0e4000182c45981c80200c40006268683d0f181a074a000c040b0386045030540101240003400d40004a8502c2c03240321100e00c02c03d10f40072120700031142108002842032008000740244d12280c611640030f4a500b0f4409041c110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 265769982 1250 265768732 265768771
    0x60b010e1003050a06141813050706050319050708010302060a0c0512030a110a050304020402091f0f081308030a0905030424030c0c020f0415180603110906030601030605 74
    0x28a12095218070002103515076003400000160341c401c0000a1454046803280c902a0b000055041400603009404a400c12408100020094180940c407154444101d507a000e030344a1020344140c0044903200320340e00c1d9900b01d02402c3d00803809000e20608081c0d82d052181d80c259070800015070070114040041180300c0c103c01c0000340041000030f80440003007103034980301d207410049041541c0c04444490101003007880700049581c0c126040d00d030000d0b0704403409138440c54140c0c0826040000344040850b08040c800050301c14607084003840340d0300d10303140d614118140d2316501c440116010b034100003070100c841040010304c2180b456004002007440740d800e41e45015520f20082e0185001504003030010721881d60550101505445110303a6400c0900f003081a0030116000076091812081100d80910317247e6510b80070401c003940d180409000842d100c010001c052304050001803486020480741030440c46078003006483d01410140c41510000c00421140e8210750390328018050191a16124015281412 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 265771232 1250 265769982 265769989
    0x1120b0c0d0e01060510090303140f120a0f0f020c0d080402041416020706170406090f020a1206060e090d0f020f060f040605070c05030d02130504021902120306030a060b010e 76
    0x20b11010219200200c1d05030308080402c410761101e500d00c0b200b40b00780c0203010070019402c40c10300b40111941c45102e42d1a06400c00e842040d912400900300140e44041c01082044003899110800044030380c01d0400c15880c45614060481c0708403240007880b980413007000310300948260078061340716201030404541c0181e29031030000c0e944829183e454914104003414031840e581005810010030240c074002d000441b65074101c14181e1409003001e0308a5498002107420b100e030745c07503005400a90240c00300314025a617108160000c0c1000c003007241e40b0f13400e00760001018802e00d81200d00500c2e50102403d0260035180041d40c1890841d42088103601800198a405180c01d216a62290445061ba4010b5203020b180504c01c40308010208020f00c607101040130040345002085d243c1b040c00c2143c005a80c0d0040200016203441c01d07900039944107000103032008403c030b688071801e03140321140c2e0202c40c0002c3c06e0391f50b000c80d10300080340c0d03a07600b59015410041c0824131170b4000d1071214406040845452480301d020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 265772482 1250 265771232 265771241
    0x27070201020403020909150c0d1b05031f050a0e091005150109090c0816031806020703080601080f2d07020a0c051005040b1e0a0c06050a020301120b0c0d 67
    0x1000140c0d41c08a000c00540c200002d110f80e204c8644000760120505410325130440d448058030034151201e001ca140c0400d18842d43c003020f083d510b0504051908000e00100400329401111103c405551010381401003502204500c810743e1001003604100c1410030b14110350b4030130010103032100d500c00c0c46d0002c2c040100c103108050040c0c4007084d800c0c3c42c103002d410000d4010000c5503c5200c280c0e142100b5031210b59030089a254010281080c40b1b103954943d2103045000d004100c40c43c04c1004807480140081014586c002d1054034401e45a2107000d5850900540e10810100d07408004012804000b90044004100c09058a02c0801d10000a01907040400350329400c00c4076041c0c0580c1c01001c03c07006000e960100740d001044d040360007032007076000524020030b00d00a9206000241c9070100b26021741c2011002c00000000e0400d54140d1100001107000300301c0c0781006002e0341e03c2843d00c004100014024000c41c2d0581c0c48c0840c024100200903035900043d000c00034805c8006660a1140c01070320049400f5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 265773732 1250 265772482 265772491
    0x20304030c090b0a0b040b0d0b01030605040c0c0512041a07020312180906040203190207020a17030a0801080303070e1c0209011203020606030105090d080c041a0a0216030201020c27 79
    0x14029800c0014030030900805d811000004000b84020846601c40e1001c4510001601e40c02040b80014007005074007400303958100580c01402c0205800e16140d101c004c10300c585010703000301d07029420007441100e09031003240140000756609161034102c0711079001c010040c407840502102c2c105640c8851110b0385030045002000c0c0c0c441215800006440c00c050501d4001d034040340d045146080c2084113409010030040404605500030030f0100070365442c1500b080c010000030b1400c15110010031031040d12517006640c4000440c000b034001060501000050340d00c00c3e05240c540000307502c860360030420444082c40c21440f0301a49440808010f8503000300c3c2c0d80c0240018943c1c900014103034030b4040d0800d07500400e040d000340c2c0351204000e1650b00000f105c2c41d00440906041408c0c2d03d8400031070042d44902e8000d0072a03600e40e859820011408000242842100d070740c250f84c0401c115101444044c8071520008c0c1c0183d2240081040030301c0c088132203449038808441c910035580428000c1c402105070855 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 265774982 1250 265773732 265773749
    0x607050714070e09010e0c060a03090501060512060f1608070c0809120d030c03020f070f080c011401050f0d02240d09060609141b0a0311030412090b18040507020304030c 74
    0x8041c89039420090261b11501c20001016043c4030110303401054040c09a81c1001e81010b071255801c2c3e003404000e50010001e8030018094000100301d4654036559514151071404465144100091150700c0f110b0b1001c0002c01c441e42d80c5400c030b803100c0104640100c0b039524141c034111010005502c07103640d14849040c1003190360016104410b0140c4018048416040c40e640c181130040000342c03200520101215915030f485480c412200240d4100700d4a980a0700144000a600e0b2041b513448400900f11550b04880007207541e012406558000e103ea56030a4400094005040c010882c41482400c201c0b5070000e02c500400310304191041101c0740643d1400b4038107841241d0307a41c105010040d007900034800085400a181c0040d82132408280c051102c2003190311140744e1b408240f030701c50a4829002080e800220030044c030f45a00b09401d00f1203226014410203c08100483d40010b41d041008064951500080d05164a0911818107100c06410018051011404200070110019290368410006800d410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 265776232 1250 265774982 265775009
    0xb1009080d05090906060a02070807030605010503061e0f07030b0325060504060f0c0309030614060901140105040509090a080a021c0c0b01090902120706022d060705071407 75
    0x81c0c00d200740c00c4040000c0080c200403040e40c0d5200d00d140303107030426402c5d42c82c69907900141201300e0400c0d5103034010300301c580030b44100001448042d82145e8181c0d00f04500740d88907500c50a80c00c034050100105c0c2115001c2242c000200100b9506540550155031810b000c904e801500d0002414050003c40d45292604d0401e0f44041c0c0501c140c04400c0649910f00307180d8070303003814000084d2040141d4074902c8100035070020200f08262043e0741000c01503610000c180040e00c03010081c0c1201d91400c8074214010401d00300001104504035007800e08140041c1c440e1440c00e42040d051050f003160040c2000141c2c4a842c54a0700041c00c4003005005c00306641d8094011003054148200400082d0090700c0104410b0613002d40204100c00320050464500e420005800c804038800701c0c0307518141d0482a84540a40300000030116004600c550002c01d15054400b044001c0700c00014804441c12054290b652100740001c0c907103409400181015402500c0e24021501c15031109803800501ba0001030b01d08042 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 265777482 1250 265776232 265776239
    0x912020a051b03030913020c0106060903050105060d020120120a05031b0306130b01020109051e07050d08041203050c0106080a0b0a023105090c181012050a0b1009 71
    0x140840c0702e0300030742c80d00c0c0410030740b444a0003c1c1e074901a050b14984030380402550800d43c0f0600381d0450300c401d410000280b00d2140d40c0c00c005028440e052109071450350070710000030541e04e0400c00348014142d050f12060300b000310702404070a001c4100f0500c90068820f860070030031003100e00c601500d25041035580701582d81c5441c02048464824114100c40c6641050007402503681d20101d0029125005072400200c01c440c0f880100c2c00741c0b04000000e0528000c2801103c00d5288090020100a01c20b10859040e075981720103010359402e10301c40291400303a0901081c04007180c0210a282028001d1078940d0400000407107003400c44210f9446607500f40c3c0904204000c216811042035440041c00e0070450070242d00002d07495076513803158116500d416100400d418a2100c1362900c2002c1c05019000c0403042c50b0498112000d070344a03450407540030030800c0000002c0d2a020003c0c1001e43c01079640c90603000000b003000c0b4054000507082c8008151110710445140d141c1d0403a0803410942580c43d0f401c40c0e4a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 265778732 1250 265777482 265777493
    0x80f070618060e0f150406090b0708040311033f0f0f0a02070201050a0e061b060114040b030a03031e02030403050a03050709080c010e03010e03040b0409061e1403010912020a 76
    0x80c03412018250004049000b07144d0003c41d401c04013094074502000c1658852070070b80010a44490018075004541c020b0122180d80700e2000f5210714401c1c0c03219000080107480f00c0d81d80b401801c80d448104801078480c0d160170309030131450002a4600c941c442c446d14543e01c26501d0900c02c03c0702c0f1a00b000166804015040c3d503050349080c2c20840a0b03000310318017142034000070010301c902051075052104000c00ba1003251501c2044403800715920004418000c2d6680070151554070a125209c6c0200c410340104540d450580320b08480c095004000300781c0405995802c1d005071617419048030800010342124a400040d9000451080d8841d0340d80a590701801c01018003260006000c0300104284101d00348400e460004103050440000d08000410465280000740544501c034850949800003143c002041034158010b40159901c120041c012141c07207082d00142c2054540c01401c9492502d24204144c46501c1c0542074101d070064000325001c1c1980c0c90764403d800e521202403005a108220340402c1c0071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 265779982 1250 265778732 265778741
    0xf050c0105070b010905040203100533100f02070305030d02070302060709030c05013006030b01120803060405090f0105010e102306030916030305031602011503080f07061806 76
    0x9600742022410045241c0341c240d0a03035014014400744a9542011609540c1c0030001070f141e4000b00c9005025600d00001c42c100741c2c211a078034013020300444c018138000e9800040c8418070381a1300941820031402110104481d41c60900c801c0c802980182a17000c00460f00034001842141071104000da52030316030303140c0285410b00042c541020006842c005100052488003902c04440302407030480055522a0320075104416000f40c2495149030754941d01c6201042c03a0890300460703008001240c0180e1340c130748503065030019070f01004210400400000e1410701e0140d000c0746d04012400110342c14160ba0580b25400c46200b031b0031844000c45844c04200c010200c01034002e010345088400c120051a4501c807000c0106002000c20b4404c0d407000c00000e0b4002010008035142c240c16450040c800c50baa41005483e5030300641d030320500d20262802c4a11454014000c80c00380b40158940384890524507140e0880640100001121040c010086007000c03441c98054103010000050100c5801d035110700e02241180d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 265781232 1250 265779982 265780003
    0x90619030c15080a0c020a15060506070501050105091639151508150c120a051506091c05100c0908010b0d020a060c060b040e030307030e06090a06090813030f05 70
    0x29042203a114086580803807d0420070313034400c081d100f100b40180c00c0031000d804140c01c0203070806400728182d418040c05401640c120b4400381c0d010080d540b20403242000b4006d4030b544a0010801c1100070407040200403240403504041070501286c00d511603d1080045201c120003504c0c00c848072100c03441141002e210354448955031202c030704402454075411a072101d2051032200b00c210300e50000540d4140140044034070341001e0715991002807924255000040000f520b00101520790281000601d0400c042110130b903110003080352862241c003441503d02d840809000310390500a00c02000400380300f038000c4030490308060301d40d484442d0802c038509003143c03906101980f01e06025621a005601e80180c0c000a40e200c0340b0b0000002d9440d0304118002e0107499005540041c5400440740703034094048007940c01886640e41c184640080a51025910071003542d401015800c168140800580399500c03128500d48030700d4000e4200b050303140c0b080308500c3c025841a1003078031400818104000b82404941c100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 265782482 1250 265781232 265781251
    0x90307020907180b0f1b1605010e0604051309020301021602090f0424091e060e070b030601050c010e0706051e13210f2001030b090619030c1508 63
    0x40c000312500f15294211107100d4800ea5820000d01211285032000880312038910754016440303000400c3c0d0016980740c0f402c001b6040b034074207a0729001c03e00c5d41c402c0e804041c0d00d400040c070311820300741024100050000351008414800340d07070348403800041c0c41c203001a12440c0c0a2541180a03c20300c1d00600444207001820310b10b0076204c01c010803000812120200d10310106055801c02c0091104030480001e08010201038104030081a040b0f480380841d000542000f8800c0c00c06100003c0703401010741d5a108030b802101c0380c0c90000e000080545d485000076110704003030b0000126020018030705541c141a82030300044001140041c0d800b116210b0b8115441e50318101d0100586005002e0b80080d0a402070341c024500441c00c03040960b0003881d5684940907089400c103400c0300d00503505140c960f80c845602008882500d040100441301580240b0844c41e1006004d4450251955810101328000114590080c40c0d0701342c40c100400400d8590521601600c160340c00c004018460400c06040386100828080c0c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 265783732 1250 265782482 265782497
    0x30901090501031b08090a0c08031e0a08040303110d06090603170403030f0e04020705010e070513060b040504050c040e0103030206060307090614010c030201022b0e06070c12090b03090307020907 85
    0x4c90b61103501990340107100d24070b4045625241c910740c09040c2031000401901c4401c041c00c010079040c4010004005241c2c0c100c0340950310203074803c0c006441d4003a0401000120b41643c00140129010350400030003a40c205c600389242c40d001040c075204890315030708085e0f040c640d2020188100b00d0b84155140c03410b90103e249504152560303500070310340b03504440201b0401904402240742600d40703806482480b680030000f40180c141d40011140d48840c10310450303103d909200c850309000c46503071142000343c449001da400d1800c0e04040504c4041d11000d030032105a040c04100002e0401c06011109002c0d41c4264090506401c0040406283c03c40c290001010245441402c12400070701e88026118a9020b090840c0e0044007810180e00901030310100e0750540318103851007640780034908400850250038090070400611310041166aa407011110791010031281400c0c0301c0400c40b6101c1180d41600c5628044c01041c1c0c51f1030720210075420030740d1400e07401c0c0c1c4081061760071442c003218040d900801c05c1c9404103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 265784982 1250 265783732 265783751
    0x131a01091206090203010b060a0c020f010f050412020604120b07080108060601090303120615120624050d020405060d05010e1303020c0d113a020f01030c02011d03090109050103 77
    0x4000020301280200510f0380c0300e81c040f045441c29080746080910040403107484a21828001e003100c2c0760810102d10940e15088501c1c40380d0b00800c60170a400c2c030039588050030141170921000042e00447c8060b68001c2c02448000349200a0090841001d48500004400c0e800c010901614010040e04014102c0c0c02580c100015039910000440403660589013150a004038545010020001e0382c0111403803600011001d00c40e142c0011144800c011860707010000c0305c1d0f85d4000e20380c114650410f05428080c262808400d424031510180c00c80c04e14250005140c140d841d0006111079003c0724901c00b41d15181c400401030b02000400036070b8800c101c100c1c035007005203003a0740c020744400045006030b100c0d0254124400502c210103400c46078408014040c840c00420b2001c000e1032007060b000b0401030702ca800c8030003103600c207888000c03038107199602a0038080700b8540c460064020b42260b0310914111341d6120000401815400184d403070071034803a0040c4d80d0310780d00c0c840010040030054001c14103041c14900d10780d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 265786232 1250 265784982 265784999
    0x306010602010b0303070b0711010f0c020c0f0904080304031107081606020a0201080f0a02040806040f02030d1b030302030414010924060513020f0f0c030307030b092403030405131a0109 81
    0x206d009035800b03600f0705460381d29048207407240300807116030460a40c41d01e4186c03808841c0720b5205165980140d021038005100340810410b8409030202c1d842e800202041c049000200507501841c0c0051213402c10080c09141070510303901e03181142e4441d000550081200d40c20303c13070b10700361044003801c0c82e48040e20185550340c00213064207601508400d11032101d40005000e010344e690586000d4007044041d40c0f6242840c2c20701c1801d08601040030703486405421030700402c0350301502850001460010842c0100781c0181ca040e0001d40004000f5141c20040b0f4034161100c043c00c0c891240104d1066130325040c8921150b2207060710320403800d0031445051420205203c03681e5a00754010241c4c1ea00d280240e9a41035003441d038400740c0641d20a0b8030030b001002c5400442c0f460040055407003007332070350b50410036101000100200550252414034050482030138542d1a1000031800d58020540541221328099840e40882c8043c80d0440c001558560b071100316200e4000130303080b01480b90009280002c003e500b071a01f403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 265787482 1250 265786232 265786237
    0x80a1a01110309040e011a19060f0c0609080a12020405030304170a0b07090806072303060414070c151a01050304110409060f140c1b2a0306010602010b0303 68
    0x2118140851a50600c5200d08100300720f4a803e18041c0050040413003440c1d180740a8032003514511100c0d0140700c1c1110710303400c2c1001c0d4030482c0111951034400c1d031858503c0569030308c407068822000b000b0406111a004c50000d000704101c05101702101565603240f10801401c0c406010504034500f401000f00b001140d0740007090303406075104034840c101034004030a6464903003c000c0200500303103c4450108403c040e0801c0d8081d0171142503201b035034225591000116180040008825080318404050804036088070b005141e124001410000c3c0f908503440054440c503000711010700000b83d8407000d501c10032201d200d4250b0011004807050104001900d0b410001c180c140c243e03a41000300c0400084e00380070a1081034040840003401c00c0129443d10b04040c4050400206905503050408285a8141c1100c034502d40c46410184d102c02d013080200c000038241c1000310207000e240c901c80c446040070030554500c800b2048815030040c2440301144002450704001050741300c0400d59140070401d0075952004000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 265788732 1250 265787482 265787531
    0x31c0f06080607180e180f010e1902060c1e0c0909060f041b0306060603110909010314010603080f0d0b0619030203180d020c0f060412080903030c100c080a 68
    0x409400c0000664260b0207207a540313500c05ca025a90450034804185080c00c214040000d41c83c0680e2010904d14664a003a2908508000401c0c1c0c0a0039001c045c005a154480102510040550785011110f05001d881c0540020602d28982021910030030b01813010007070546a5101a82c541400340381c8146495140c03100105882c071004c44d910f001501f00030302200700184a5044940c00180b00351642440c4008002c14041c0e036003c28a44a91015100921415540c015200a017420703056030844d03885028903000100780062945d221000400040d1514010303002000e0b0410b02c032a2560300c5001a0001d440c891021680620010032020710f0741341d6138000071f0800d900103080140e0b481e1146a0440070021510038410460301071003510000c1a640400c0f00341008000701d600f0b403081036803902048018810742c40350f444490340d400014000a0a0f080c00340c29222401002d49040100d0440c1482c101030f099503070050a5551090701041c400d8000242540100c02c2010400c901f03841c0d000c11540384400c018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 265789982 1250 265788732 265788737
    0x5040b0a140d0302030403050a0507080d110307030c0c08070303120614010c0605100b0a0305070f0305090309010c230a0309060f171005190611011505190503031c0f06080607 76
    0x2c0819042c0750080084500440c0d000301140c00021041c20000d80351484e601640c1a03502502c092460b061380700306038003000c00c2805005146448642da505a40c85007a8007001c40303492003d80000102010300340f00d850011030017038071110005165603241d10700701da90071742007068900184d040c2101c2d240d9200c0e822142041e07201000113080e4845481d01d0360028038642c0100d0400030009203c00075903038160003080c0102940c0d00da05100e000040ca003038064441c200d03041b40e11540b052006418540c03198071081c00b0b00c0d018078240c9000c1c0c0f02400034600e01510a10f0b00c5401d60344080507803810140c1c0300c81000010003803803510030240c048081c4d0003404541c2500c031040e00543e508000ca13142000c00e0740400010a030092400100380060201d039418400300703225540c0803800d40300384240c078030340107004d442c106d01e200340c0340c3c103014500b044100100c0740c407030030b04035054140032550110f984d485c100004c05c52005844050214039183e50b071058241c0c0d0001003c0c04855041500800000307000003900e603007080d400d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 265791232 1250 265789982 265789999
    0x606050616021c0807030c0201080a0614060708090d05010c02070905010f09020f0c0615191a1e0a0302070204050a1515020102070803040609050609061005040209130e010605040b0a14 80
    0x10302c1d1042c0881c0f0740f02000d80390324000140c030400c0640000080150f640b003a284c07000e151b0b650300341c4d44084541a200b848900010350403103600d5481c0403c0205038040c80703454100d0a0038400008030b0040c0103598800c0364142c0d0348000e841c008940410020006000d5030405100765814204070301210000b51080400194004c184141c035080810207858050354541c048404070b01e000106511107240d0440006e01a004400444000000c05074104040d544142c1e8090448454440d130f850f000d502c02032090f000d4140201280e810400400001e16540a280d40d0140e103840c82801000121200501f400950514102c00c05200e1803007182c20707100b103c0410720602e42903100d5000590291290b000c0003060103000008000c100701d43e56020a02003401003080f6601c80c0c0e6001c0b50180d0311103050f1039502200850300c00030842c500d041d800030189044007400c2400301c094028045400d03140d09030140b80880e51141000d00140c1018850b01c003914030120303a1500180e01d0207501084020043c0c0c440c40c0201c60b030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 265792482 1250 265791232 265791259
    0xb0f010e24101202030f0a0c02010b031c0903050f03041a0309150603010b06040306020705060601030c020312070e1206190b0f0409170406080f06010203250614090703060605061602 79
    0x3404010f06454044030250b60b00e1414110080c07134000d04071116800d90340381c40f4804040c036105110300c4030301640190080c00b50304c000000340c1c582180b134190701030104200803201000042041c131250044500e904029074aaa040c0460007000c1031450329000ea26050074002c01c50400c0f40042c60018034056004c114425880d9007001c6809424013040450f00280000740000400959500030311410f4000c40c00e8460a0301c400b0011000d8072182d40440b40168424090082058481c100c3e891f0403108504080c45400510401b05400001c8040324076455000901040802e00c220150a2300c0c10359408000c1000b84407100000300880300180d5403034040c4d030703440c4000381c02c01600398071084040c422503203500d46a40c0d40d100c2c001c0c00c44d40c048401d00320041c03014012a0369940000287c64840750000840f20460358145401981d16519540943c0ca081e1a00c04800b240c02145c0c0d1002e0281004001400e1140d00b9420040241d40242c0d21a40c000d040c2007005462403540d030b11060f000d45a04071143c07801d0b00603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 265793732 1250 265792482 265792487
    0x28020907030e0f01051009150509010e1302090a020c010507080402010915030906060311271b0d0c08090d080f070f052203060e0f0a080a05070b0f010e2410 68
    0x2100b00201250701c0d00007882802014000408104c5018160611401601c0b41c22300101c5802e0703102d016006107441d00140200c2041d402c5441d8440c8040c01c0301c8496000070b40010b40c12a5064580380340c002d80c00550080a004c081c02800d038417550f80c0c20300554030304151780020120801c0e0310407001c5200501000c9007100d03200f41c001c0c0d4195600b00b0400d004070f40d00c0341041001d80b60600002ca00c030740d90200b00014115201007003c0c100303046c902c2a0205a58800e03d810b0202d904440c075090410f2801c2001800306229407245c8601c2200d82e41d91505030349440d40a1b0f600e4001070300d61030b8041c8601c1008004e40c0e64920604203602c0012880e004a407014000e105940d540100c868081d01c80311118240a948400c0c414940d048a02a06060050900e0282c0c081d0b1142a02d044102d0a5042a600070020841d00c0006002401207450001d10b45801521241c01c0700e41c05448092100003281c00421080300d00c42c5c44a0740242281c40714480c070f103001c404103071088452104028040c4200e034400000380d60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 265794982 1250 265793732 265793743
    0xd120e070f080601211a151206090105011a070f05120d0b03010c0507030c0201080403090f0b041509050d030806040906020307030b1002010608030a030b03010908040828020907030e 79
    0x2054201c904519226402c40e07441c0d54090284051011400d26400c004800c407441040640c0c0e0041004560302604900c03401c0b00001c010072074610000c0080342c140542c1c4070700c2004403603030800101408060418040150039100d06030700c6102d4132541080c450003407058000403940000c0c3c0c40703202e0b40301001032454003a0a03c680c807404014800404070b920720b04640207400070100908110000c00065048100c00e40300d40c02070301c60240000d003200c10008015401170001c1134100b402070814500315a0340320103041034034040360002a802200414204203291842c0364000542c0e1f8541410080f40c6c2c01c5c0008a410704181e0500a030800030381001188c1107403903d41c02040000c0d00a0410342da8be1900b45005001790004174492030042c0f410900e040300d060f01c184900340503990580095450701a00e03038000c0300901010080e05615550350b914440000b003254004200424440010b041e100c0240c1102c0d0051540c1181c0000d880d01d11602c4020050b0390b4070034442d0313101e029428005850070381c2ca0003031481c1c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 265796232 1250 265794982 265794989
    0x271e0902040f0e06010608010b1c0b040e01020412060f09050312041e120e040504080f28031e0507120207080c0a0c091a03030901031e05040303050f0105030d120e07 72
    0x1c900e043c1c0c1c1c4807461800418514140e0f03184d0f440d4070043d40da80d54241c1855200300c80003640e103107021000c8001844042c3e0024201c1d400010404900c05405032074240c00c80e030240e0b201c071400e50070220b890010007849004012a04141d84c00800018103540c507016128452105010b034903901c0040000d041103040072903d540d030080d15000c54900c12442ca01410f1080041404501085610008001c94600b50060328403ea50001c400381c2800b48203141e09010303030401050103818070321020074a4041c151080a161280a42d40c1d404030b050310482144181c0c0e9500c1c603400c22085c904103006c0210b0719810900308030814840340341c01170b66160142050421400b1b01d50a01000d070041402c11802c3c00046c074030003000d4807284041000f0b94070030488896607100000d48603a80642050002c40c00703e6010740d00c400b1421100d820f541d45040d07a024100310842d00c04a404030042695031081c01410f403c0015240d016080030303401018a040040000761044211040ca4045c0e00d403102e0b1601a0000c00740b18580c000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 265797482 1250 265796232 265796261
    0x130c14070501050402090a05070e0415030501050c0d050601050406021504140a0506010503100c090b0a0c151b050a05180f0409050604060b04090c06050a020115271e090204 75
    0x540540d494424040c00003550140d120b8000d200c0459480c045901c2042d000d54030980712031340d0340b040090601c009003100380c1d101590344103901c10020209400380201c0c2c0c41844200300c000d503a429003034010004c0b0b400c05005141080703410701060107015000210031105c4480c0401510055482e0f00e80041e101a006a030544035001307800011080110005181d41a04d804a00795803c601040c1140340c11241da045882c00080c12100302013020030040401011491100d203413065100c503030358031601c48105039051601201592810502d80d0403040c070204108003881c13850003034a0903040000c010b0290041c0b03204150350304203d401840d2a640c0d5070089516101014200703000c0a41c9605085407940000c582c00d44a60341406881c1303065242c00e220343c8240b990702801002007030b42804000c903460b820480c0040190342d65030720f695441e02c207101d00c1c40c0c0060441d0640c040701e048500344194182a01d0300000c42d0040c2c00c003070300300650b0301e41e18480d401e9001480070001501611400003c0c017400001d8200400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 265798732 1250 265797482 265797487
    0xa0303051b1804060501082403100e060f07180e0a1b0507060f02040609030b0702010207021804050f0f0303060105071e0308010e09030702010e010e180a050a0f0b130c14 74
    0xba55065001c03459036520007100c040151036a6400107541400044030000c0e94000304034842c1d0240e01800c811001c8015003e41201d41c0a2003500c40f001c00c43d100c15031888a207902a004001488440440c032650000c005e240c0003c50424405c2d019151260078040e001c09807009900240320010154080706500c1c0921129139051107254401400340d900c181412b99a950506101031900c60440c004c80e0704840c01642c880c0209460b580f80d540c002c2602600410841d5003c1040b40056541c01940420304079481442d4540d60410340b4007549416440d0896082d5900080803100b9064070110030b0325440701081c20010358034840c42c41c0c0060400b038103200e54200c03440003034107203024107610034039850507240050000344450b1501907015960f4002c844000380080c80f13960042c005548030704012924040f004e854060040c1002d401080d80ca4011651412200c0da103074100300280031706005284150240b500d00300078045122000c2550017000c82004010f840d2110349005c0d07918400d072003150b009040740170317410b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 265799982 1250 265798732 265798747
    0xc0204050c19091409061201050a1a090f01050f0109030b09010507020d0801030507090b0f040c0e010201051f2303070311090c0a08040b181005010f12050a0303051b 72
    0x1601e904948211000750b00d0358925412a40d0240846100f550080c2a0310064a02d410082003802e0b500100303c19041401c0d620300f0074100030240035082c020309102c07401240c20880100c4607441194200e003241d02c10310700d080a2105040c183c00d480b40c19914203941941a06440c4001a100c1002543c00101114100d4040201c00316040d0f10040c010361655090700c078012001402101c00102c00e02000d003031504500c5041003040c0789a440b02c0741c250400b034040c11003c0490000102103440110703a80001c00c621842c9241c4645c0c1c20b00c50a03510030442d400d1120411111035903080d4012440c044c440d541c48118082e801c2c014101c108000300000c008046401d013507107a1502d0f8480e20502c403030036402090b0310804106003800035000d40e00f800d4015a60200c045d912074a80c049061806003480500b0861000038090780c10040c840010303802c900440103da2545002c1c00854290001c0d03015045604031448000006840443c480601ca038042c540452592110200451071028180801c03005c07100005491 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 265801232 1250 265799982 265800001
    0x20607060f3b03071a071407111327020a1a07150b090a0207141e060a0c0c030c0c050303030106080403030507110304051e151306030225030c020405 65
    0x207441c079440701c1c6120b0300d040900c82000d990320301441d41d00402c072101c1e43c101c0c8070b0010728010100341e0062036803034510101c07168041c0c08a07481c1d004850039162000a0050076a540c00d120400846401031100e04001308a02d81e0060441d0f41010010070000300c0e4460070000a6550300c001c0d079001b402e10501e0023441300b03800088149042e48007482c00c489900d24003402c803400100300d11030703880c4002001c1c14020b42070f610031044100039400210b04803820b00d2a80e0030480c885204129a280c1550008455a0700007400095203207001002008005040d0803c4030845c0c0042e80004e0040001c0d5140c03c06c094a12042c4c580140d011645400c15900351201200000700d83d0307030020361140600e0083d02c00300060340792214210342d541c0070001c1c40c1180d030703204000030000c600700800d020007a841100d417085401800800041c16028401d10a00200500400c401c0000c0d40c1a4004c0401040141002c514004603d007407240d181130b4114402049082601120003894000c2d01001c5103185d000380200040d10344800c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 265802482 1250 265801232 265801301
    0x3090201050f0c070e090a0c05010f110106062003090f04110f03040f06141b0f0904020412030e1c1e05100e0c0303120c0307021903020a020102150103020607060f 71
    0x10100f0300c0b1703030290114000c1840071030354001603500030000504141c01d000066500d91003220504080150f49219080d90701c02c20f101c0c1c1c0000d400c1a558022501141c140e2250b692421301e45141d40c250010400c481003940c03044904140003100f40d40210b02140f01c801070703100c3c6004101181414110000c00c02c010001340c80d1601d140c07248158000c20002e41e4500300001400703c2200c0012040038006440d03220b80f04048003500709032040207603c034a04981000800c0980c2c10951100c0b80c400d900300c0d1100c082603088460b40c001010141c642103104110b40010030038071000104094aa40021004003a42c000c4910081103856000320441d02d004906074015401040004003c1c0c0b040e002c0c400324580149008422036172510610584100244c50f580c8801d0702d1a0f1001c0c0c8600198418207070341c04032482110001140c3e06000e070300584610501c41c0006400e02e03502407410303080204580e0050005944601c150b4501036000000042c40181c0d11513410700030b1400103a0702c85100e48d40c0354000616010a000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 265803732 1250 265802482 265802489
    0x9050d0206040e04111e0105030609090f07030b060a0602010b010507110303040e0103240c050d0b240301060825030c090e15120606030309190905160f020d020d03090201050f0c07 78
    0xc6e1031680c0307070003003112136884c5a19a0b881800100100041002e0740342180341690044440c0b4161081c1544040e0309a01c0c1204941c812a0044051804c00c086858500e04c003600401c0240000d200d07081c54070000030000e00c41c0792030041003038207010501442901c3c02c0055070301130103001041405c1c41d40c581c14800504410408544600c925490300c80d60245001d00071110b0314501078442c0703401d120480f02001c0140206101090700494041c05404001a00c800c200050000d6501c106903654102640244144c8004114003010400c4082945448030b020703200310a4048289070015090f000d0080464180c0300310f500060f100155030b010b101c00c0d119180001c1c0081c1008851a049080d14040c0290712620f003161a00c0d40b54000b4892210242800ca803404100f1a0310b090152083d5180d05c10306003145c0b025a04198040100c603441c00b5900c0e0070803800750f0b00e5000344c0010a42e02030400e00095548049903540390030103807124051000c59014005807450050091f101342e03103039542c40703446945d150070714407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 265804982 1250 265803732 265803739
    0xa05010f0f0c02070501020c0d11040204120203060a0605030706111009080919050904061d010c030603060501050603100303120b04020f090405011205030403020d030e060c0c190609050d0206040e0411 87
    0x4104541d140c00044c0100031110180c01608280c0024810031080602072401070301c115907000d2052070070340c0d2103200510103044440c240020803506401454a4003c0003449032080700c1c5004804c1c0318544d0000342c07400885400703190100c109a00c5040c43d80c00c0603034100070254880d04183c0c83c1da080001c1740c1c001d0040c504003981c002e0000c90501c05407002904440c40349603040034441020501090b0113800050364003103150301d5206410407000c005030843d451003441000082c0d03560410b0082143d90b0041c80c0c0100021101c007415414000b00b0448407402b5403000606106a000d541407400401d600320b0b00440700d005004544501c4200e144000c66030184084034451450310b400403c00206010903a264190440c00840c105415a030a1081d0390715452800e405000c06c940d40e05016603204801010300c100380d4009403030865001c00910401a81031540f03082d0030398103038106015150b84056810116101203520b0410000680041001403049030070100303141140100300800c2c80902110b05140803802d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 265806232 1250 265804982 265804991
    0x9030a11040509010627021c09060506040c0e01080402191206150303050d0e03040e16020f0309101d03010203040b011e030201050403060507030608010c020c0f040e0c09090a05010f0f 80
    0x103c0c0e401e400c90740b49000300401300108002803d180580c440b56011010200d240040c0f600b801e07a40f00c0c211002e04203c1c450b11042e20b4121b0442044041e00650b60407480070758090061203034041c40903160b001d401203040e0421940744001020b550354007a0102001c601ca005c4040c49030345410b000b46450580441c10b1f28614140000c50a907092030300c2c05141207039050b0351010b080880e20410743c4090152000010400e220a1202085869000c00f80364090703510303081c0c0a101c000300352201034104569240e410040760018460305296407102011710403804410f02e4900b2201400000d05007000c00850649078041d0310107c2000f040140a00344141a182032619090303019082200804550751140030090001d50309000410000d40b240e0040c5800c9100c0b4103010900548400e00282110740c20181c810044c0e0000c801f45105040ca81c02d0f00030503200507281445841304048043d0742d182d1071401c2140c001e5100d240059200c1009124280354941e02a0090201c4074181c1042006000710245014185250 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 265807482 1250 265806232 265806241
    0x31d120d110c03030339040311030c0f0d03020109061103040c170a080c01181515030503030c0901020307050f07030b1e15030703080d330509070509030a110405 70
    0x240206000b0710050045203107540d4000a000e0601401c00610090f0071402e40e80000920f0003500e21608004004c1c00f240c5861450400c80b0240001c0b4000c5d034008d400018111285d601c8003140c2c01c0c1a040160b410b06031400461400b240100030039030010300701c0c504c0d040d550246032940100441c0100c1c020301c140468581c0358441988030190708e004a0665601071880040010080c00183c40c0c48651203000080d4805100030f8500d4070300080e90203c4a03817503000036403000c3d0b6180e44a8a08a5400c40301c0b480f0b16603046558184d680c4c4405044d89114400100750348a183e803081044030003555000003a6551600c9100d10b0b5961b41c680ca01040301c1c1c1c6002c0300005007011079607142611903070450000c0d05202e40ca0340c0441111803160010201d405005503c0c000c00490350210080448200c0c00b400014495958001d40c252070a00d80b2200e0002d000c1da0003111388403401c244040741510021a18909035440382541070f42c642c441c0541c010f81602480d1030510a100c62100b0020030f50805441c207120b2070b80c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 265808732 1250 265807482 265807517
    0x6030b0108060108030a2d080a11090102071707171005010b12040210110a05070806011d0f0601030b0409150b1906140403050601171018031d120d 64
    0xd0240021300c1d4820302965043e148180825000d0030003000a03105961900c1c09103240040c0050b4900b8042200d68060140c3c007209480b600120599080e03d880c01c2000140c0001e44400d0a07104040b162480e1640b1224120741c1401600020710a417803e2180300001544016103400c60780f490382c2112032408000141c100341c400d044400c51500844c01c040c0c1c0740d6950f401c0007080407123203040c80304111940512050811081242c0c2c02e44a0150005140461908502c1460200d050700300f00549000c8208508207050a079100c01d4021301c4182014046540307805c0100c000340072414a1135442810030240109000c0d03401c2c0154441c8a2012042c40480c21010900c000c14901c40012010644012020052103104e9043c0c03031001040c4010700c0307283c260b41e40c60b400c1c54110700782c0200074400c03000b040660045404110360310b0440448030f811f005448070448000215210384e140501881a640c61402e11603461401a246a1100a2034001005000c142031507a0303c01e440c4212000c40c2c034141c60000b9a14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 265809982 1250 265808732 265808743
    0xe07080c0706051008100e061602060103120302160b04050c120c0f010c080d0608150907060e041d0304050f03151308210a05010b03070f030222030606030b0108 70
    0x38080200c0ca141c854555140c100802c1c000b00b0032001c1003464400803810aa007404155101000c9400124000a0103160141003a10250101030496081c8440207800340e00450a54110fa8020a602c12180d8130000f054003c0c0c403074202d0540804801d40a61402c00c48400340c21801a070050086900302942c240601040d1410482c42001c1a0700c69a0100e0700b500c1c040b084250a45010315017142070f00f20310f64503440c290b0814842da911080e19040184900e441c1000200340491a10001c01d00381e0070403c46c0180c4a4010780074072020020002c0180000b91116048440f0f910404800300b00d144842c100d903d0303180d420078001c3d1881441d07100e408a8a62400003103520f1038039004051040315483c1c4080341240d0070301c411303c100d40c0780300b080c080c0040b61004090384c0781c1040845956680c0a02d40040032408039401600101e03000d000500034000310f00d034401803100f079800d464203005a5403c00c00c45c954041c6007842c00f0001014170008004030070803100760400ca0440e40700301045402070740c072114030740e07281e2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 265811232 1250 265809982 265809991
    0x1090207020102370605070f0503070507021905031c09080109021518060f0d0b0d111018080a020f09040b1f05090c03040506011a04270c02070e0708 65
    0x603446141c0c40302c1c000c01c3d040010702005095505200501d00010344198600004503819a00c5c56600d5080044140c3c210300100081d240302e1a14900d1403030703c0303440500706004881d400b07030081c210181e00f8218018000038a40152030010100e980710203800c0310b4020380c0c1e01d456000c40c0015114150001d030458050081480d0640d006260707030503003d0a202c0000651300000015000d031000c0616071180c0c0d03180c0c040200321850303809100b01e6484401c210400195880c085241d4014040558079001003925251a40c0b10600210b51078121b28849002c01c59981140c45100242091100700000d83d6036400203150310201d2098501c0e1a842500d8800c02c41f100c0030469014012a002100062074000092200c10204802100c44400c0c036071120045075003144121212225544008180000d1190403c110360061049202c0c401c0083c5603003191401900031446120410072405401410021899800c1c2d004094400d50070000b15020801c001c1d52080c4a100c0c0d580c8072020f031800316880038450301e00c49204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 265812482 1250 265811232 265811237
    0x30f100e010605180a150507120c0b0f06130e07081005010b1213170a08090703110f0a120b04120219150f05010b0c1605030607110f0303040303060608010902070201 72
    0x4040100ea04d00858200c080d610907404001844045420654052624001000741d603c1a450356005c1c03070040a02412640a0003d014444090301c0008400d1007401c0d40c01104680c00c0003146e00d440000c103100d41c1d090722200c8005030408404005100c000544c503001c40c3c049000310b45c0e03800c030410f610800700c074028020300e000c02c041049031030302c1c0701001441e140e08109281c02c0078107425060345030f841c031f13641a076050400360a0000070603904080d40002d000d80c2045548001e841c1d003a14540e0f9081c160501c480c415030041076440c100c0d40480c1d031540220801002109034510740214689401e090010040364200c1f03c22054901488907a480056500510410b00c22855240000ca44494441000121004d4181170300c4030780c140018070450191314002c0c01820103642c1c41e4031a80c09035500b02914ac803d241c42850903c181000343d0f960004807a03402040a00b45489002807200145060545424840c2e1340c91000201340000c1640c5540940204e81d06645c840155989604d000002e921550340041d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 265813732 1250 265812482 265812487
    0x3041104050705070503030408031501050913050a0605060c0d081609060513030813031e020901030209150a0308120649030e030105010605031b03040f08030f100e010605 74
    0x4160506a200726008656401c02c03c0c2002801d42d51185198070848080b0303078550020080c808880740d0300c0d03074000d1680d509003800d41c00c010450002c02d080201e14602058000d494070081a007010311540008050207003d80003d6682e110b04001a40e40d44211140320001030303a0100040002c100c1441a44040c52545d661040d040d00d0001c2c12140c42d0003040703960942000342c45000000402d100300814160860001c10354109265040418110101800b221502c11103c0384680041e80c400c810356054941c1168111101e8889050300702d1a010b858103002c0d000000d26001205010f820b0004c0c054180490386005000e030348440c1442044018029000304414080034840d44e4801da000c418181801c40076028140d5041c4401d270309214002262040d00440e800014a14181c1003e001e25409040c031414142d203142840c0d0000035800501c00b60346060400080003207410820301c0c05171f841c10340d90402086a02d0341083d18070405c00d0302060319080c24a4001c40000170703000d000309000ca4100c0d40315846050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 265814982 1250 265813732 265813763
    0x1050a0e04081605030f0703021f15050904050109050102031e150105070210030f060609030302120c060622060f0905070801031203150b0301080703120903020a03060f1401080f0705060304 82
    0x205440001c3d0b0701120240000d00000c8407a00291000d050194001c0c0d0007440074000d15581e83c40300d00b03003003030030200c44508000303401850070340307040b141001c549003594052011360740c0c1d042043c01850005002003080d4000020310012480b5900f616444c0c400b4009a2400c5484684c44903094007464217485000c80c0041c041e040251410113070600040040d4140403490705040c40f00d460440384190402804105030300001d01c28582c0c100115580c000d0304c0041e05250039603040040d981c1d104020302d043d20a000311144807205460001c1e6001441080090922403d41c6030000103540d0f182ca07000d80c240c2c81c1c0c50000040d21461082d5180c3d8122900510551507201c02c1c2402140030388500011000c0781d440003070303000494001380710085000b07220b0503010305041c0f81585040b405035414000c42c601008106401440542e44003402001100d62051b400142610382192000240c0481c03c007034162000c002c0c00026030040041102000d80345240142c4440c180c03075100704041070000b940c015020041c40081c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 265816232 1250 265814982 265815007
    0x7050c0405061c031115040f080901090308040e01051507150b0d0c0e0a0b09072c06030a0606020c01020102070804091107080a051207090b181f02030301050a0e0408 72
    0x407504080003400d0483c800e52a0f0241100c0c00c5401d0b5004c0f000644413405600880c00e06000c185214000602c4082c0103050503260b0040100c1c003440041c1c401000064203c245a0040d403c40b8021607103c10141c1d00c41d83c1c0d07440104c0144109210b518006c020000120051042d04000c95034002c0c1d02c219440c10303a2101e9a8080002e105010419802181100003003000c101c80d20818401045c43c1d42e800042454001005e1081d140e610b0308807400f03003803020f007448683e0790029038907083d103e03c07880042002920380f00d204c0084c48403840c5c800d4000f0742c00000d200d840e29450f0020340030394099400710f0380c2d1101c0d000700481c200d100d01d8a000e00303091030a001c2400b05c000590403480240102c6000e9500303200003511800b000b035101c000380e100030036800030342c01c55400c3c0107400d01039004800781842841d080c903180c041e454030312030301042c1e0041140b09041415140d90b58078241d1403058104c172400c24410701c5800d000c1d40ea13600a002c3c06205058002c0001140b411003000e0724820f686c0b02d6013080c10030050758000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 265817482 1250 265816232 265816241
    0xf04020a05150a360911040302060307030902011211030603120412060f0e01060f08011b0f0813080a0f08060f0d0807050304030204050f1510020304050f01090b040306020a0f020307050c04 82
    0x1600301502c0c0507a64044600c002864019486a1040e0131050340c5450882e4044031821905044400c0c824081000903a80b9807081d6503003c591400c01281d00c0c1038a1004940d0001c010800765551031921211050082410000d1841040c05800716418148003003503800c1c841c0a14444c00c0c02801003854854000b94043e0070415002c600c0c03031030228042d8100c24040d420346045801451420344001e401300990308013406401030551000700c1c05941c0c0341203140002c0c5001e60600060b0203024a64001c00c800d48880c0803e1a5800d4100403003507250010000b00030158409000b050700003c0c0100701044580c0307050824103001d800000c05001c0c040d400e80e601c20b045a00040c1042d80c2d01d000c01d000000250321039024482c4034402c1580307150142c2c58410343d82c00e0b03a0303101d4001c0b08c1d0081c1c02c804c46607080d2076000805c407015503030100c0351001c102c0010001200c0340070703451b000300342c42202c0420008108042d070380181c0569035a5884d68540c0d400988001c1340d6070702452002070026808100741c0342403401c19900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 265818732 1250 265817482 265817507
    0x17040c0b0a090906060804020a06090b09040b0d060504060f0e150105240d0207120206131e0203160501020d0203120a02030a020d0c080106020c06070f06020f09090f04020a05150a 78
    0x40c404500c0c3d40d205212800c5811581c86400401c00c08030400085280c5401800040d001d1410003800c3c09003820744400181c05803210306401a6030741e8001020542d500c10032941c019070700140c180042d20b41803400c0400313480d46c090340729091414001400c00200004c20350001120403801100704aa107000d082101c05d419001c141d500f08040b010f00180303903410100c01050040510310000d0390703d1042e0300d009440d03e5102030f020030454008406000300041072801c0e0015107600302410010b42000045180034080d800032000354503218200301c1594800d0710382d1016048600980a4980041c140541641c481c8a003d14042c0400880300008000c00d8481e40555000030341804c0041c100f00c281c03541e42040365600d0100b400031400500040080c281d042089094043c0140d9813a41020b14958443d0b211411000d002032585802181c10b0204000440a40710560002816101d09040c0184850b001050980302603001e031400341c00c0810107040445020b00551900c4240c1894000c00e118201e455425556 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 265819982 1250 265818732 265818737
    0x8120c042309010f05030d0e010e100c05191203050a061d04050609030f0706050405100504080403120e0f0f0315011d0924070306230117040c0b0a 64
    0x800d4a003081e816403003200007200d03109814a4550001c20840c00c4050b40031100300412800d09005648001c11101c41100701030070031f2514000150016500c13241c0500000e42c02c0051400104649680015480305450150094036050310b107039942060380c21000c3e54044c2c006100041d421000c1440382d4020782d44405681000581c094071040b0154829074080407124201e941c030700034441400410720901c0e82200c0b812004528142c000100d041b00d130300030842d019220706e6403100060207001d0103220360180c080c07482208200380c2c906444d1424564116010548001801c81d210030340c1d00d40940300149090310000c1145007003042c5641000100e005c02284a0b400d03010b5600840b007440084004a40070f000800f41c4031601903c1000e40031600540104419080e45c4403000d1844610390cd000c600305041518081e55502e981c07107d00039806000c0c00d6200d12404100c00350306544503641c4070310344490403030242d813400b81480e2a14800c0c082010140c3e0050301c0f601a515042140d112020000d00002d00b050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 265821232 1250 265819982 265819987
    0xc0209040c120b0403030e01060302010813061d030a020613110909030903150105040c020a080d0c09080a120909050f070f0e0307030c082e050c1219050a020708120c 72
    0x2d4040c0c0414400540046803035400799400d0108140d01406040c800d01d4541000700011851600020b0950201410600528000345120390078845160410b021202c100e82c2c110800e020f01490a6a80340d0102e020600140201c201003040404003c25240015400080e6146040c4000341081101403010700700402900c001c1004103403039202803046450009600001014a615000520080c1c40e20310040300219040500711600185038401600c034246069000003a400c0c03003080c0c0a844e208101c0d00035900a00c1040507030010000d94440200f120350341030356180002079640302c40405441043e50740350042039204e400114043e20417602c1ca90140c10a02d0300b40000710400c03010a05010081d04180d0b08503420840c18495141c0402032141000d0010a206d18101683d03424141400c85004440a0032620340c008a80040c00080c1a124040c003001058211030809080c0c2004200c218041441100c0c10407001601002c010f100341c401d03850300203541c640741400b04080c03c510054004c00c43e40d03130324006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 265822482 1250 265821232 265821239
    0x7082a13090f030e3604020103060302093102011709120711150a020703120c080307051e1309050a020c03030c040602121317070305030a090302010e0a060c0209040c 72
    0x4011040b1045402603c8281c06a4844418020003a40680304c05001084c0510103100443c03200343c071340c812032a1414058a0301e482e1440120302404040d44045e40c000748420600c400e80e42d0054001400c0050920045501d070120140c070100e201c04e6510180c00b1070b82c589003049400114440740c03984560070b0b0095542c4988122450401600441804c0d102c1180d0030b64809402d041510000003a9200398007190308040c08070000a55400050000901490f00e1141070030740f050151451840c3c4540c45010291245481a03008100d50443c1c000f020b1038104481100d50000d40240417940f9582c0e15402170b03406113084c2007415010f07000140c41c0184480e401c21210440c254140013441c040d40d014040c06170b680f86400c0009240c4161600030794000c1400f00402c04904652104410440301310b2214501c010010041d480c1c08c00344994809400360000013000e050003580540402d0a59201342c0390000d24414070020700c02c90701c50f030b405003001040c01c4e4011400035191501d94207500501c2040c0880c00c89d40c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 265823732 1250 265822482 265822493
    0x160e03010507030207050f1618110304061a01170a1e0213061202030f1603090501060306060f0b1e031012030207030209060306091e0a020a0807082a1309 67
    0x204072802d000084d408556070302044418400d00d00c08404140003090070b03d02e543c01c1c01e1040c000e14440da40e51454039481c0401c42203a0b40c2c2140680710400000f0a8492410342010006800d544a898800c52104043c100156008510719514640c2461041d030181d60b400c04510018010880904100800341000c0001c0340c0c01800205804d9500740340074502c0d04e10300702d400350011300808021142c0c40d0041c0100b07c0040c9452600310790200c114040120344042442098000300350429000d4140d500f01107002c070500c11150003030300c100c544900d0100713001076413500d1402e464042c5000f9440350500e1380945a80c02c4141030091504006108252101260b039100b0217007008032640700480150300405c00400641c5405885190300070001d402401c02c0f4580106401e449504401030f5040403601804110400d146c108404089036074040c042c440c880c0e8070703280e071540d81c0c0c100e80c8100165486098900d00d40788005e0200d6110000603124030100381242401000342c2002007090290074980d450784d083e4045070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 265824982 1250 265823732 265823741
    0xc0905030f0f01051003030c03080417070b0103020a050d0228080706020610230103091103010e030306090a020c060c0f0d0f02070212030306010c06090203010b030f1c020c09160e0301 80
    0x4801c00c0c02465007540c00b010007400e4900003000e0700300084400300c0401c040f07604500440c03441c2e6414a01520160b03214546451030410825000541e8a00803e5040410841d00b40c118181c034001c480454005070741c2c01c101b1241c000b06240007134211018102030000a2003414244400340503200b1200740441d241c045070fa1074011340d544040c0c0141c6c065001c0c4503103904140100e00207084400312141c180420b442325024083e5900c1d000d1070400d46d8410114091204494000c002900c0040003402521280b590f2640d07a40c2082c4c0e81244114117100104011040510840300941c400602034809039840d24034480081d0030170388084000d103408101c6030f049040c581c4690300c54100881d00050304c1d00b10900601150b079103080c944a00c10b84c8104140003060b03030801440c9000c10740c000004150000e261001c00c6c0940040d10311a03030148901d0103140d0700d01c000401e28080001480c0014000094810f0b01242c1e504000c60500350007070441400b01d407081340503880380c110100341800c107440385885850201742100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 265826232 1250 265824982 265825003
    0x403060c02061008070518060d080a03090308100509070804030513092a0801090b010302090a090c18050609060304061d0d0f08061309140105070c0618150c090503 71
    0x50b003004040002d07a1034040b0056024201030b0b00140005828500811540709500003084507100c101c1000541d150385003078030b03103a60b143c2c0325601c1e645407165008042c002d802c5241e41100882c1101e80050104440d080d500c07012510001c152071350715240c1440c02c1d5010b0b44050001d4041000820460200b90480300d01c801c001d04000700c0000329000c2d03050014050303840c4c280c2c4450426000c0740c0342108007540300c2001810b592040c1000a01d14041c807005800a21440c0303803890300003040c2c07140040c0e160503aa0010408110580342d2107038498400600220b040b80310702420360301920900c405a014100071000e164498031414000603170a09800541d142045d620054880c10340c0b200c080c5071081a4000c481003414460360422200c9130624070000380c142a00805c0d100c0c05141d4810090003402003000800782c62400c0e4100030002c1d824100c1c0001c08815105005503400c0e4240158403404c0c420701c0441d40e4034507404c60b414406000d8851942e4018101c5450020304101c80c15001040d260340c184036106c0c1c030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 265827338 1106 265826232 265826237
    0x302070509060f220b03030a0f201005070e030f070e0406150b130e13061e18020a05010c030206040b040c0f1d0a020f1605030403060c 59
    0x84590803c455214500706410700c02801c0b500340644608003526024002514260241a1703030744a48080700c0c0028070703824601026140308826140f0107020414260384441c82188500b440d00c140e114203c0706255403441804085600401220035480081d00500302e006035481c1811b44030b107003510504084124410001d42040040d6000200d910300304201141283d40b62000303440185c0004405562000000f0004203050488800d400d12500310341d02040540c0d40180e03a880c02400e03100014201008004858041c4502e4600950b0024101e502a0103220245801008522013140c0d01039410f0200321003d074008240d0119241d0b5001d90882e000c0c20f9261124641041e403418070f42e10000e941d0340100710219003800c01921085065003180e01c616031f1603c40084070400ca20070140100801101040340b21115030804042001003800346090324201035594598070305a848041d0b56400 = true := by decide +kernel

theorem cover : BRFrame.Cov 265647482 265827338 := by
  have h0 := BRFrame.cov_init 265647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 265647482 ≤ n) (h2 : n < 265827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
