-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2325
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:47.036789+00:00
-- url     : https://prove2.me/submissions/eb399e3d-9f25-4b35-939a-f5afa39a5d38

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 417985611 ≤ n < 418165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 417986861 1250 417985611 417985619
    0x305071508090a1b030b150109090207050a32010c0906090803090415090e010203060405071b150f050a1e0605010504180603290901110706051b0a0509040f1401 70
    0x140e44105504e011450f00301003000800700d00c80061542c000d00101101e9032425000c80001410980b803600480806801001020006000000d031041455000079000030304258440112501c0311a040617003649040007010702c040301c101988980d4000c4c0c10b60b2a281600c0d41e8903030050f200c01c0c0c990300c02c501d1701d078006001e040443e0078142c100e141220164201400c2e026124541002103a440404a01040c1c2d8007000f08600f5007010b20466402c0b0103242892020050904041c6030880c04821004003003c120340d079503403400b040580001214200d07000040c002d500d0040c1d802c1c3d008110000312101d40609910300e810111009120f5902981c1c810b0b03607442d10b0542003803d95214510725290650b40c640c1d403900c000000c51012155002e08506000c0f0400e080c0250017444186100080c08121051b450b00000c402c0d0000c1c101c0484e0080383d440100458650b4507002807205401405080d20210100062445030007640075000300000c110460b000c000302d6002c4400d070b03022201d14401c001c45080030180180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 417988111 1250 417986861 417986873
    0xc050a11070f06031a030f0f0c040b0a30030c15150b0c03040b0706060501080906060315151005090139170a03090b0c0a08040201180f0305071508090a 66
    0x125405c802c40e01008111007419001c82c0c540101000407d1107900000c018451075041805180e8407400c0481e000d02c034010b054000505448661311840780c03008121041c41c0c14655043c0280002030030403003101086164035003000381201d4615041203a503081e040136800d004001520603030440900d1840c0e1060403908168506201d030303000d020304040900c0280130000f400c2181c00000d00c2254030584002c0f171010f15101c00500404000383c40880d964002504106140d00c00254100008500074818140c60311110a0350015a030308550640d00110820090302c40150002c0c01441c849000303903501054000c2581c5901040e55440c00c06001c0035586804c1d40610a441c01d905d0200036020fa215404000400c904503003c1d82e00182e021300110b034a176a81041070112202d41d61394014071225285251440d9044000d10f82c03640100000c3c144907031000710051514283d0081006080c020082010707040d02d170b0925984d244550302c90703060a4840342591500161080d08102d0198a00710001e0840050682d610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 417989361 1250 417988111 417988121
    0x90405100507090b0301080c0a1d06010c0c05100206010501021204060e090406021c0b180106050a11010e1e010c020c0d12031107060c11120f030402030c040c050a11070f0603 76
    0xe501008098040880c4ca4001c4000442c001c08080f00104010003000c030500003119042d80c48040050f01d00500b00b511208190030385030784103809190140c044811498a82d0300c00c0c03040e4000982140c0503203004056140c002034601c0c166042602119600341408103c4601ca00c07503030062000050700948210401d080480b036030358200c0c1c0300e24405070906001c2d602950b450b01030301180d0403070b0350784980c81026142000d00642a031141100751020a960514034054840d02c035400254041101030441c4510050742940900404010302080d10000d100b003100340e14040000800c90400c80d464007071780030482c500004450690100160032070040f19000d8868503002100c1d035101d10281921000c40b051440180402809414415680082c0c0701c012850010b0102c2c101c030000c0c7e886944400064000454940c00303840c901e4489a801550700d55441c07000c6803e113029100d089400c5414940030210082d04a0301519244105545809142002076075075991007441d0b20446465200040703047c4030041c426004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 417990611 1250 417989361 417989371
    0xf09060708070f050601030b1608061e1c020a05030726031e0406020d030623060d09030302190c0201122703050406110a050d081b0301090203150904051005 68
    0x112810b11441d41c4411441011060040f119500044018800c100c4280410b980006210390180b07004510171700042c10700100a0407103485004000400e95003650442088d0070054405040900c980c0315440450f4003110700d641c0308031b114109145011a55007000220700c03045074064001c400c0c00caa0b1211640000c00711005110304a40070803c00c9107509441c0c206410003403600050040c0d603961a0500003410031002e0714550341003604001c1c0030051840403c600d0700a55885a00d40c10196044e10000b4960344940203501d0380d081c4c00c0000038010f0680582c0684801c621500c0c410f250305109040489880d54684402070100750064211211405550700004014803103501069011031510038008201c002c140e4110000f0380001410311100b0f601407241001d03414080010600348203243d07549500d034003045e5115403c00c05550300041303a0020038481404400390300710750700b6642c0d40c40d0701600010b1b40c03044600e281032440c10856449941007240d2014441d90704030000e40a20000d01d86100054507020340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 417991861 1250 417990611 417990623
    0xb0d0206160b010f050906010302090a0b0901020102071401050a0e060403020601120602041d091e070b130f0311011409011b02061e070c0e04080304060510030c0b0c120f090607 77
    0x10721000120310780d07030141c081c220005000000078a4642003045840c402401c02d0b04240c0144590035036170b296041e00c1ca0035100300c41d1401e522030540d100101e009004029025200115201c076010100d001984100d00412805005203c01c4120309002695030038203440c010016030000004004c0321b030a114104081e10301c108030142c9403070ba840c00e030125407500400809035103220890510440c10320400030f500340070301e012003120221a00000351540b40c40700741c41906400440040c128000e4601002c0400140540c903055100182d02c0b4200703181c1d180d090450380f1740800c030820b00902c100090401a91180c10050791140b4005940c2030040100302e041c003008980045c0103100391510190160640e6002c81171400b0140d842d01d500342811103034540300d41e2001c01c210181509000109260008899105e03070082008540c0b0303207503510310364007144a41e80040c00c0c4010801021900c048814020006845000203c0b034500d100051200428880c01d00300f0b802040040011242600b04080a8000f85008007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 417993111 1250 417991861 417991897
    0x207081e0a0f060b01120606091a070c06050d060e0105130c0c0816150e0c0d0314070c0e060a05030c0f0d021c12020f0601060305040f02030d0509040606030b0d0206 72
    0x642e0300003501403544001c0f190075440e04218000755038800c00084000c0c1c0400404d20400d03181020107800301400b070248802d6604918840d8140d4001c04c0b04544406611003100c5200c1e40e51000b0007411600001c03005810f031380c00c1640000310216a00c8280381a1100240011824518907596030003d1140c41801070030721500d9690704010840110150000c114a850729203083c4000740341ca0003940d1310b0400c203104000e00d0304545840c00b080000b100340000d1419150002c9a404609040c1c4005e0b51f0452500da01d4200081c9007800c1081040106e03080700c00551032001d242d100d403402c015008040340901505648500e4643d00c007031034104a07014449102030441500e0f01c0254012418618581f540c1650110780002920100600220300f650060218400303410b20100791303010a0380303c45041c82032908050b2550f021400340800846000d8400742e000b0304554404046000c050404d4010180403803044d03141020005401e030007070280380510340006250005000c110740c00c00c031aa400c08100c80000800c86 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 417994361 1250 417993111 417993113
    0xb090c19110a060609050a0e070b04030206030907090906021b011e0f0204051216050118050f130510170a02090103080a09050a080601030203190b040f0203010e03041d070207081e0a 79
    0x3c0e12940c03001c1d01c0984030100e41480c10704000400c0e81c02c2164405010707402140308010303180c03407101541c0c1925412600555a510707001444c2c1e2410307041c5d8101d1800380d847c0000d0501040411f40c02440805070703c0400d96403081c842c0780f101e0f00320742d046146c0890b461200145a0840d98055000302c0c00503012000040c1403607201e10209411030b18551180701c1c3c0b035120007100110851090210320041c0802d181051a4110701000d080d1401002d2103075a0042424800200e902d5a8015402d02c0300001c807001007020f031900380d0701c10701c0d6051103201e007008104040c41000c0101c000031174641d01c8103801400f510f070164a5540d41002c2580302c02d0318102001111800415582d603000e80501c010b0400000800403541107004150400d2030300304c440d285080c07205403210000780441c030b00340394803e0b0400d401300100d12a40c00400d014010400010a80e400009004500001440010055513a14042041c03007955030b0481680d603099640242c1c0d0b007940c03180400100e018100d1000704480720016050320100521 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 417995611 1250 417994361 417994373
    0x110406090c050c060f01080a03050a0201061a090a0e01080a080903070b0c0d03060803180d0303141602070e0c04030b070509090709090c18050105070602070c0305010b090c19110a 78
    0x1501c1a000021030000300143d0b010401c0015075004072040a074100c1c90351400001540d101c42824000b0107129020038214a01c50003035001100500e08484900c1c100e400c40361132001507034008154580b1030b40c4e0721500414814240c011080c1a00c1581c1c000307000d510083d4450400300d8008010096240c440c480300880c008621001502d502245100200300712148181c0203400c0c0d461903001a08560300500000840e000014842c0714040001da03181c8034000c0050604038050000c0810b0b4152411300d10003809800000d000c81403041c004150700340e03400b41c3d803503100070307403008400303489140d402c11051000b840031803003a070742d0550004490f0900340d2074540b0110100361810b008441403804141481c908120104440c024a008000c461410140300e20007506010300110b1180117481c100940880c1c0b550400c04036a049807407450b0032400780c40d10a6680d2505a000c2c0c802d5030302c40b50040c58000003140160040380180c900e800c003d8200103800d5a81110125140c2e000d6000711543c0313204882c210008104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 417996861 1250 417995611 417995621
    0x908011b0503070e040b061b0609060c090907030e0615190302091b2503090b09090a020a09050402070c080d09080303040f1e05010c091208031605040b0a0804030909051311040609 78
    0x1e084c1d06101c0c0b080583d09203a08008000f0b045c070401d0340000e002c10252006c20800c544c8903840853b610301d09038403a00011402003d5104214000f84540c4081c8108000c076005c13110038108044501401c1d441c00080c00f4040e819051100035045580400821001a5500c0c0c001c609102070a1003a402c00e211070805042005540b2040c0c030560313042c041854103155101e550003014100354144c091800c510400843c141380d6004080151803a804600700c82c0452184211038014040104159210900d03814004c0c0036620070302c80c1c1e000c01e01c0b03240106940107026400d038508889040000d14255611516410810b0132001e60840d0f600d541e81c012000c00c64491804035071014011000051424100e44d8081c0002c01c076600407a01c80c1c0344a88400c00001c110300100c81d0f22180d00c201d142e0880c0d9044505031a1401180c10000c40c031440850200780c919480f6070b8240c8114003030741c2c0d00100c141d079481056003191016101d1202114000c12104041a070b096103810b07411030081d20014015685031410703401c440c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 417998111 1250 417996861 417996877
    0xc0c0f030307030b0901140d03080411030708010e07060f0906080402030c041107110102010219030905070b0408060f06011d040b0d06021605160e040b0c12070908011b0503070e040b06 80
    0x2950359240081302e0524036030480c00341202c1c121032081003030040d00189007100881c40c000c0c208551000000c003080680e40c645800c0140240c1101c01280d02e8079142800b914070300041c410144982103001608030322640b046032448040c0c0d1201c460a60802200301d441c1000204142c0c0c16115140c01400d42d91260b00c43c99011100b0788a001e610b580342442d2001d4400c5e12218a1811a03005200e80d0740b6840140d50120048031590600042d803160798600380f03050620aa004000c1510041400283ca20700443c4180c0309401d1000091455a6030b4401501d61640c0000981e041603d151901d99a5080c1503100c8158060001d1190290115543d1802c00380e0384000c81040c101c1c100510703c8130410008100504044012200c0a20b00c1d03810401c9201250134010000342c10440c840011a028a465100300c1e410f1403100d0380d00102c3c0b4505940301811502c01031003070f426150719008854803108040244d00c0f294a40f20750755149961212402111841e0400d40d5165005943d100084071941d01c10700280461 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 417999361 1250 417998111 417998117
    0x9011817040e070c03230d090f080a03020301030b010803040803030a0b060c0a060c0906030b060723030703030b1305250e0405010306061406070309060c030e281d0c0c0f030307 77
    0x36040d10300d0004c12030075804040b0a51140805c8046c514204d002d403e030344403a02e60a40000d5100514286401030b410f50140107000303904001140155203506800641c166402803090006d103903a103940d82e80d034078461441959181d400500200300401e00c2030b0403d501d21500145418144403003040038a08049041d00b0440340243c0d2064100d20703807a0000740600003881982020008044c604011070310341e00c24008020085e51005941e200302180528039003020441d21403c481d107076105464003400510f000541c0c0d6104120071002e91042c200700c0e000e02841444005a0088820700c400e1505240c4100e20781040f05100c100300990990b40c60b94403031140218000d14012400e540390102104d40038251451050240f0400c101100100f500452298200c8217240781546134000c0c50b041c1142c11252015903140c1c80f0000f51400d5034a01c41403d4800300050000f4025020542c0e600700102001d445905c402402c240b080300020440c1a07020050b040400d10307101510070480354140410300310392040b0b890b6804 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 418000611 1250 417999361 417999377
    0xe160c320708100c02030d0f1d01020a140f160309121b09020901141c0504050a031205010f051309060e0303090c010201051905041401060b1209011817040e07 69
    0x3034648100811005002415410030207084c0e5207000946a105408409070081c1e12035130041807540c80c65204040305c030406050040c5d110f2500582c1c40c042d42c04100031500007101c2403502c4c800180300804486210100401c03a070703c2c24590400c49054242c80c244181c040c004501c070005520002524400800d902c60540c1c1100d918903403010586506258001035007152062168810030b98100c50580140f034186010961030700c45d5040d0140030010b03445401d4180509000c18032080190014240100038070a840d40d074070040405c42c81e801100d209101e11010703524000c40c1045a4200660b2861009a03560b00c0800e401e40903071110b0f01544c404424012043e03000004001015030140003101080700e091009010505051070860344107410343e80b4000e0800e81e0b5001040c10000d0810040414000700301c000c1c04000e82c0c48441041641002e05101d01d170110050000d921002d062142d5135040c00c4150440c040105507844140f0034181440c03603140301c04410800494003020034941244108540e51307070064 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 418001861 1250 418000611 418000619
    0x20d2402071403040e04032016030b0f040c061409061605071a09010e1207060201050105040b180414031b0c040c050a020a12030212010f0e160c3207 65
    0x40c5440050182e00260414401070044074140d001d026045505454080c20303611140d410460200c00903003014203540302e103420f2403030319800c001c07204011640103070341c500d43c2d96540e04410782450504540c024002d9910440a02803a4000d060b0681c00d00f813595030240c20000c0c3c04021030340c564010f4010400c1d1030356248280d02004002c1008001400d644041480c04140ca0300120910340a107503891414889a4003051005461f011100b24031140a0303000c803108690340e968003900809082c011f07103010b5401c040d0624001d003000000d80864030f1060381c14012560729500c8484245040c0782d000920760008103c40541007102c60300b80c0680c00060740260801c900710200700411645242c403440d003408418000840e8807500800c7d1086119040050380c159040144070031802842603507540350400c1c800fa0008902c002d12041030790155446200080841e0301c515480c90742d500f0840d822507002401c084001c1c00061b0f007003d856041c1001141c074407260054100000380e02701c042c4280f000303c02d03032081c50100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 418003111 1250 418001861 418001873
    0x20c03070b060303070b0a0b0f060a0f0905010e0d060504021503040501050a14090c0111030c030d020c16230d1401050402011d060702061b0105071d09070507020d240207 74
    0x42d0410000c0300151301d41051070391030000e036040c000e101c40d030080d984d1461040f09031200040c0d14200440140750356510b0540d510064441d081d081403040000d00c1c02207020629501501ea5100000c4005000004080c0640e6460f000741400030301c00c0342c01c200740c10ba014060010307000156000d5481600081001e05d8a07002e0f020480e6044c10005804200340001d116603401e0210f8158900182841e00b2500d140c0440301c020702c1c5120b40c119900039403200003603407241e42c42203901401c13850080c81d050701ca008048214074020750642d80544490301480049584071042000c045500e40e55010701075020032900c82d01d4038011641c6510692034981d46400400c4219a8000c900300104d41c80840301200740810f1002180550040341c0b0001c4c010303c000124014860004070f14507048003950002800140760404d401400c0500100240c410b00324003c44a21a500d00f070380e01588110f02d03607551182042c001d85c081061040945000752200e007022031000507003410a0807141800d024140380980d03074440901e404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 418004361 1250 418003111 418003133
    0x110307180b07020d03020c03161404050907170c0402030c030a150f0b1605070b1905030601020c06070201180b210f1602070e01030312110703020a140a06020c0307 71
    0x303112240c0c80e0502070005030200e01c00d880072590103035010700b40c1c0019460140c1c50189050103640d40b62240e001c00681020620251000b03803803940e07240c2c000c0d6010b800140819580c082d550701c040d58001620a010301c420581c1030050445000b000c0b102c1c1001c990300480c040340d2040d0341d8088500c0e000001c03c1002150341c015400c42c0502c918582c0303075003460301010445068090040b62004100001c2008030030f00c42061480d865074015003550745499070341099210640c00084c1800250342d154000070420745c080c030705480c890b44040e006031004449200c1005030550101e07500304d041c049540940e00442040509020113040589003881d920100501032200c40307001403800d5418a2148000c020b04c0d54a90311095411000081c0d441c44007030583d04050781005c0e5160004402000624000010305a00620340000c844104408100c0950011046803140c4554100a0090380c002074007140044c0c0410101600840c1c0c8405951044031195180f0302643c1c0709a141d10100e900218105060002610301 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 418005611 1250 418004361 418004387
    0xc120a060e1302010f030c031508010b01030506191206020f0c07050f04090305090415030218100501080f04420b030d09030602030604090f05010e1b01120e030706110307 74
    0x1000e482e1540683c0001c11980040c3e41a5041503228034106207401e0080c2c1040401280048140c0400d80d10b404105000b0422055194006400c0030003281042c148100010116001010078200007801e08515040c004440d460883c1c2c41d550802c1800c0c640c0c007941010b481d00240d0100a8444140f40070f0400000c101314900c25032040789400000c00019800c4021a2450034082d0760101d620720112603171540101c515480a50081c000310150312a4601308080035104100141801d403002c2d4a44004541600003141c1030064048010040380c0810309031264080141e000c5003a01000f5864008541d00105c40003404500740c8036002c0441c00e00b060755000c0d0200410054000741410500c21100800c400040d201c058661640000482c1e125240d41c1c202c411403540060003408209582c0c9400790007800040c00070505070150f021745002d0008034280b01d2403940016900c081b00313905604105002000c12220740001840100304080000c1d116010b845071039020498400e8580c5401032002d00044a4028 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 418006861 1250 418005611 418005631
    0x60c11040912140f12062403180c150d0617030a0305010801021201180b0301050f090d09150e010c02190315050903180d0c030c0602010e0f0304030b0c120a060e 70
    0xea40e0450100c80c20303030345c1e4180405400030450710b4a40114600c1003119102a100d051100c07094070342d0340414130046000f003480d00781110040402021090319040041c50107544014819520829015a80301903d0b541c0d54084d400101e0580d10200c25210030f05007a03542c01c2075000807070707061a4190144542070062100344007c2d481c1582c24070341a9002e1005005084c0b6030321000e440414200025400194503060140082109041940581c420004100d42c0e907100f600c81d1081800d51240310341a60b03001c58a070080000c08400c03002c80107440d1800380716611410814a1180c04c0e015070b8802c0c003510f0b00f520fa4030141c0321619040d030811180c5141401c641641c0e190034141800406240002121009403401c00143c1e280001c140007ea41d0094943c0d0192102c070b071002020080c04400c014641c01c90f40300d40c00030410403941000d004d03141c69501c221801c03250800e000800104080d03440c1194002c0003c04100c0c940100c019501d0000c403010b80d1001c03102940c0d28001e1000300b000c01152070b00700b51002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 418008111 1250 418006861 418006867
    0x150f080d110706050c0a060c0e130902010f050306040e07030b0f18030f03180d0e0910062f0d0f08010b0705060a2a0e0f04020c07060c1104091214 64
    0x10072960b846860b4803604041000000311240d50b00014840c096400d503200c070043c0140d400c441c90080c52650341541740f6102c1c204c410a1800180c1c901d1284402c0140d06840e41132204e20250000d803030541008207204d4000d038591007210b000c16010301401c8003451203140300c0c00710350402c10500c0000d001c00034819008030703c540714051081e4070004261039103911070340c3c2c4241d921f640c0c0030580703c203c0c080d00c03100341400d20881580e000150b80080703205c0c03c40c82c1e05503600d010b1350756908000c0e4a0900749124aa01096035018034031141e030b4542850009054004032026100168000500d207440c00801c1544e0000e0b070b0500301c200400e5844a138090040c04043d0307006090042d1503e51684030700300a004100da02e40d03075240c05102d19400e0100000c5080e4181c941c41c00100e07403008081c00500c69481564400d00f0000704504181ca05482500c0310040c05900414500b410700070280c43d104103200c820760780005001280700b00399a45004610f405442420082203000344d00030f0140150880c1512039000e21024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 418009361 1250 418008111 418008137
    0x50303161e02091b040312170708191a2d03060103030e060703020c06030112110306250e060d27080d0c0c0c030605090f070302060307030b04150f080d 66
    0x200c0c3c2495000740094071001560700d00b03020b19013030a00c199440200321400a034400da401c035410484680c2140e41101040006035076600c01141c02d41000c40f00c2c800c10082440804a07100400d41c410024a104001c4040d51244a40300203032491003410300092030801c2d11400c240350414043c43c948042002500200305550440d94050503141020443c1c1d0b00454010551724140340c800c0104000548001d020700340e60f540c4074060300310004240d060603101801c299013000c42c81d0a000581c2c5104409039a072b01800c1860503a010354400301411018001c0000303150b40702900750750b090010582c60074900340000e4240c11010424002040780c101074a40d81d1656160580810158801c84d295180341d5000010403c40321039040d945d041c960f22002d00b80c41c20440b00842000515404240503544807000c0740c08441c203c05005580c0d000500000750004011702c0815030300e03402a08400c1005e18014004558211010308850050f0410ba0108102c21102c000401660205200c500c210107518035005500e0204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 418010611 1250 418009361 418009369
    0xf0804030e09040f0f050d02010b03070b0f0304080c07091b0509010905040209030307060e060f06031212130204180201030c0c02031c0309152c0d0c060204050303161e02 74
    0x10151a507405041e8102c00a001c11030f03000011180291303c4421600020718900700950b8580040707030740303030050340c80d140c82c0130724518000032060216000c18513070500d01000c03040e8140990b040a40101da10f08800d002d80201844144801c03409040d260100161b0650546100528011800403901c18010100503c0030303603903480034a0005a4a040e100135130f50380400400b0905c2d500c14403d000d03000c0f601e00000c1d807546940c04540c0320b00605514214100c2915114209501c6070401c5025201680b01007110b0400c05204207900340d803040581c0b441000041c00394022905807419411040d44070060440740604660301481402ea444103a4902422400d2696000c280d454070201d0126401c5049001031140c0b0305d01c01d07007042c5803050740011001050602d10f051100070341402c0c9402424044105009410200c41c0565100308202c100000d00da420200c0c44195407419044d5415100c1c00d400704408241514100000c1c80d05082d08004110b881049051800000142081d035240c0001d02c50303840c074003580c2c1d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 418011861 1250 418010611 418010627
    0x20101103071403130b030f0c0a05030a24030b0718051305040809210d030b010512070e1906020f0106051f1b08090103051602070b0912120a0f080403 65
    0x42d12140c00c05100c42003049007032450107241044070034000102804a9003000782d502450092101c221032910079200c0001d0310191780100c034503900021b0000d01c0003650051444c2c111101900400703000d06441c440282800024010580056800f0701c0c500041c861750a0340301040364117000144040c1105242080001003400c45480105d41e07015860b42c0200302404625412a08112001842080d00303a00405035a40e03100695942c461050080e241500b003507a0003405084600c0605030340e00f51030301007104214880070301c02518400400034515090411a21602065500100e140c80780d280340b98a48203000b858401c0280a003034890341052000c00080c4c80f070702107008000540070b12080c465500e180080700c0c05004009000d01059454035041d09000651008004810302030f6401e00c9280d032162980800452010401c00042c2d120311400c025468980300a0840c460005011103a10011204032502d04035401c1c1c8154404440001c805e1805a0850202a041801414074158516080d00c0c003803d0f140d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 418013111 1250 418011861 418011863
    0x507061e14031b13060c0b010602030f07380604060f0f03030305091009030e011d0f01030506041409160816050d0303060b070302010606031d03090f0d2010110307 71
    0x2002c0340c40c0c0e50003400e0402041c4d4011070340c0d8000c40c030141951080001c003c0008540301303a071030b105080008111a4408070488004074080803030540b8140c15950307a40b10300841d0700c51440503102c16201c5880340003000d000d40d07414445c1c01010005075060076000c000c2164401e6100c01c1c6841c80001e030410040900f038001c00100d94042c1800030b82565146078290038804941d00c9030104500d064400c0041503001000440804401e80c1e880a664601d0440d034401d06500c1d400d905d91080081160705650340c429084950b100d82c0103440440d6800c840c59490707202d104191020620754101486034400c41740c540c019034001f0408000100ba0640280c81c0500708e03006240121801074404212040a260180d00301e5001031401c40c2203ea40c645050a00a00801c02400f6040000c0d04001c0ca201c0c0d026001d6220310403524806000c0c501d41000303403040021851020040d1904082c030000c07400b0104004541c0d811003010906035404500b0a01410400c603104904505018000c05000d01e00303441c0000401e5408032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 418014361 1250 418013111 418013131
    0x209030c06030a15090e070b0403080d20040828120822080d05071409010318060e2103070c12030905030c070f050405130803040602070507061e1403 65
    0x2038450940c0c1002402d1001c044d5500e80b1812200007407131100b00d038040c002c4017a11209070340d980c41e200c00c4a03840c527120318400a00031410511042450326200d50001d040848020b080c842c420072484100400c41d00f141d4000917090b0000c6200d588603001c00e4950494403240c2d9905001a14030f282e0b42c00c0b0003a000b5824900c104039079000052603001c903400b9081511041b400d0242c86002d101e29011078070303511140c44014854103200101d002d0700e010702c909000103403020b10b030682064000c000440060141103090104141410841c401040e00d0348259a10307075082c030010f417035503d5005002c3c4045604102c000c003031071300e030800c100301c51a68020014064590311202601c00d9200c450412000790040203000303001408002950003420310009440022030f810907200d03200d059a034030204012100103c40d180c8041500c100300d000080c0c2880011136001c0c0c850b942c01824010b40d40c0301c1600e4460307590403080c081030b01c2800b036911305104071540f1000d198203807a1031014041c0c00c001e01211400701130210801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 418015611 1250 418014361 418014367
    0xe0405090d0c120e1e040c080702120c030403080d090b07140307052a1b0d0b070c021c050604020906060a17070903061a011403070801050d0f0501090f0606090209030c06 74
    0x2140c2c2c03041d2684103403070000600c0c20b00d841c00d0240c0817107240180060818031482c0740511882c100c0703024840151068030540c01074024016503014a1545a0195003285e40d1030104001c0400020503a41c082c1211140c640c1001404000340d14101020710000307015041070007503800b8204080300c03070f003011070364000164504940c135001301c009614102080e0440c04540c0c2103402d202c10035481400030b424a0805181001061800e501d03d003404002d1203405c3c00940b8030b04c80c0500044032540a00307034801c2c0e03aa101a28000040c2c465204c055880345680c80100c2e040d400c100c1c01d0100398a81000c0321900311508072202450404404c00160200394880703002c0c80040d60307130000252203034050b01148006682001050000400c214909503904521180960100303440d00800100310329440c0540780315011035100c1030785690802c000c00010840100b42166070101120201d0001032084c0a42c4100d00d03c90351180310758000500e054019a9025040305242c45d1052082c0030b0039650029003890310520a403071841d9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 418016861 1250 418015611 418015643
    0x10c0206091e150f04090b010509030a0b070f0e0d0f030302040b0d20090312070501060f15020f0303070906030e0f031b010b0d0201080402010f0207150e0405090d0c 72
    0x30140119084690701031039110394207940c111460860001040211040150800956102c2e00c00340102c0c1140d41400e1404d0009100c400c0c0300f9480700420340d9050505a00b0300da02040020b280060031841105e01c18003c0c42806499600001c0465030b28451b810848000c07818100420103120607030f103000c0d210b100c5d600e03040340525000381d04450282076544100da0380d40b032028407110040d1401110000c48210564500301c424002c000960307590b0f520040107445803045081c10f00714140c00c0b500d8244c2e43c55503203820020b1a903030028860001442700c0701701c901410f0700350000a03041080c0c0d14400c4a59400030003c00916550004281c001d0300d0450400041f110400400a80f034600b107010320708110300c40010444015040109074070110403002c0024041c20100109001e042c401c1518001d010075030703480c04180190701402d07001c11a0482403046400403a561008540720005c5104000b0102d00d541083d0702590601e4081d43e83e11102d82e000502251014680c0104060103c54000d0301220110b25480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 418018111 1250 418016861 418016869
    0xd1205090c1516060c020d080f01030512070809060d0b12010608060613020f221710020c0c09010e07030e010608060703091b0b04090b030a03080a051e040c032609010c02 74
    0xf0071503900042c3c10030003d494071030040d5503052414400800304102ca400601c030341312104400c6043e02d90010140040303004032082500aa08890403c80324200140001c4d1915203c003030142246508550340803070415014800d103c0601c551248110482c3d0500d4400e0010100000b03a07941c0004e0b09884c0b01206c1c1c2c3e180401607000380100c181d021030100c0001100390983d0b820071100807680d4100c036000c0850075a40d814000da004021324850f00260081c0c0b6030386030400c0c102d034003038102c2c03c0384032040c2c0318000d42c6c450001d164107800b40c201c07109104442041c0728108c0c7e41880303518607032000d1340d00800655040c030300d01070703a81c04008000754101600c80c6140d80401203503640c410100072210049a07206a00e41e00c40f9006e5810030b01500c00c40610b40101c4103814034000982d00026900f50300d482000e0b032654083c00016010042c0085240c1540340d070780905c0c0010a01e4074501c0342e8043c041d040c40190452034107880e104a0700081010400740e008040034120075000440d640c160003401c00e20303880c04251003c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 418019361 1250 418018111 418018147
    0x30712081515090907090f030305070201051605011a120c0f0a0b040f031e03170a0e07030506060901090c0f051305330a120b030106080d1205090c15 65
    0x20036000001d080b040b1440003140d4015040401c001c13629441c0565a24604580c006282e11070340124403000da0301040400c2c001c1d001004030354010714181d8a0044035100d030034005c19922130116404d0303545603e056802c2e00b03500d80220080390115a100390384488000c0e015a601c00605070203119640e80c2070a4207055898461481c0200a01008551075503a03602d0107045682c01c5200965400c1421007101c100414003420792134441360305440305200220728030304000d0b100d03100400b2968041c1d03845504015248041041c0d0b0b0095110344020646860000148501d02e9410f0b800302c01902d062070100010103030000c8508410010500e041c1c0d8880f0200041c0d503d0b50015540610780004107541024003156641c014a1004001640b140c1c0001030a40103001182c071a4510880000d5106107640386040f2094111015154004001140080c1c0342c0d5100f90a0103440c00884020600e41070380d25001c0e05590041d140d0144080700900b000700448400b160b10b641c0300d08203460b03030f401001840e403810100707003182 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 418020611 1250 418019361 418019401
    0x301090b10080d0c120c020f03070b041409060303030103030c030309020a0312030c0e0108010b07060902030316021804120f020f06040c08010605030703051207170f180303071208 78
    0x440d40d050000784100c00c05060300030801140500480402c80d14000c451504a16602c004002040300c5100707403c58840c1d40780501244e0018030300140c104903503070812000001d8402051a07580d2580b40c4038019070403400c0340e001030380660040010012076682c003000340c81c11a50142000400078240d460224010215814020350008205801000788101046a1028810203031000c02030700c0b001c0c00c4281c2e0f014841044e500d002074200c40040c421001c10002801c006846190041f500f144541d000a0564010049150450710060586c0c0d003903240820307103d42a40c403441d10714069410581c03a60450003150565440c28003d541020121141c420024182d0f581290340030b80380d442c281403401c0d40c2441020b2003100700030740c24080c0100329854045066002c0340d03407042c010514003150b80c030656000e4100310b4003038605071010600303d07115071603100c02040902501c01c000307903903011941c00d081680784400055901039802408a6000545000c0ca03803421070116080480c800e0b5114441c040360b2100c800300e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 418021861 1250 418020611 418020623
    0x2091f03050609010c030c021c110a05031207180305031e07150c0e01110303010512120a0c0b070309031d03101401150507080301170102130e100e0c040e06030109 71
    0x1c110140764117501c0700c208040107030b07002d0000502012049075030b4820317101d0705600544141d03513a40c6114040e11a07107030a503140a040c1c071041c0003244c550f1401e46d000400314071079200000c000c21024613448080ca00000301e00c003070540b0a55095031170f100c0c1c0d03d01854110349500800d0b40000c0c107008591405a60401e68004800710244050b40a40406402d12007040004103105464a114560040e240c1c3c901a1620764000d40c1144c0ca490304204c940390058016100502810306000c885c01c0c0307000d000b004a42c021740c640420010680c40d0465038044010110002c05181c19118000070364801400d00a100400c031403880c1c029160800207003017600700000074600398a0200c0c1441460200f811007412100d500c00c40800004da600000d032102c0c0310740900103086031010801480540c00030502204000c140700c000504049601c0280c2d10700d840a038010045909081041140003117500303200170043e1030010420704be181800000c8600501440c064001e202c54031070300080c86510709622842001c0d4001c9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 418023111 1250 418021861 418021873
    0xa050d051b03160801020d110f0d0b04020c12190212040b2803090b0a06060c080d060b041d06100e150d05040f0201121e0c0c0c06030204080705010c02091f0305 70
    0x203c0c196000b9449210b03047c40071810b140c090006580c40d101920207001040c11400d10b400d041c420101c0c0100158010181d02503030900412503521400c00c00d6005541e10008003e503207012035402c1c0408040150710003030865024104184000746400b09540c2210741c516201c0752541c1441513807031441140d5460b051010b8000403044100150325400458003103020354145881500c40d14110b4007512194003880001c00c40d19150b14001441110041c4060b001c003010000f200d541f91036202d240d0340d0060344104945400b41c4c1440c0000c0700c1008480b900000100d0328141c0c40e80441c0303c0608200c407400e10031840360303a241c40e407481c084010000712038000f584901c3c20002c62401c0d29100c003107440f8032442a0300286a0240194281d5520721400c84204e484000c0354002083c451441c1c000307042600f0300c11081050711068003000030440c0420101801c07440d1005600d403410454201e24050311540100e0401c02d440680d06e0250321051507040c1c000020300c00c400360003600c07890380301c01184d46a40020040c5c440c0d9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 418024361 1250 418023111 418023119
    0xc1e0105070315050a030b061804081803060f04060c030f020c0a0b100605120403140a08160e0901140301060305120c01050a0e0d03050402011209110a050d051b0316 72
    0x65100ea03104001c1c54404103c1e400341c1d000c0484465203070b405559000780181d801400810f1003480000c5d8013440062680b2349180200311740d07407001c40082c2c070f044420070b002040013002d80c0200400034510980c00d80003810f0600d01004148000100940090440341c0e51702c0010014500ca83c10040303503022a0b850940d81e400c402641150740714501002a11000c04020128000c4038a0060200881d031007656101d0410b6a0000c0030010bc040c0504203c051059000310401040461005480e000400d40c450041e1490404001c101d40c540c4640750000700100302188030142da8400b10035606640b590070b034079850340c146035003c280186400c1c0c00190042c4110f40c0d804204901c00001023002c007094400034002900c940c011441034860402c803c1c0400d800140c0f03c1c00701e26209034007040c2d1040c0145001c080002d9025007600850720091016140340e51002101846030402c05810401004203035180700c008401605d640e5121561115a41e040300c1c2020026000c0d40e408000c000c0895400c1e690151305283e075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 418025611 1250 418024361 418024363
    0xe0309030f150c03061014090904062301050d2306010b0a0f03110f0a09050402030a06051206040b180a021503220201020d030c0c0830100302060c1e 65
    0x11103a40d65502e201c0107000490043d81001940e00a1502810400d89140052800d840e8a075002c5c0c401031142d030061003030400030798803e40114003031800380000044489420724662140c0b81e42850580e188520403004000c40d0320341650300c8140342e40003109001d180044801c0c1c40490310144541400600c500800842c0c0c03228100d000702545051a1211000381c20070400580680708140301c450601e040070f05c102c0c88080142c0d00100100708a074980858071544450000c1e00b2078206030390841045503140b03010b2200741484504c82900c03e03500c1002f000c9503d006e80e6040020a0020002954102c1054482d101100104048031559600078501010310015005400664004555440c0a60403410203900110041c40003042d075076406034080c1030340c8034199a0035400b0b0014075085c1401c21040d0342c414408a0620343c040d1a020440f035035802200c030300c68400c018400581e402c210b04440700c0402484000020313140304400300d0f0b50513200d03292a032020fa0300321170401a0006e1007098a4420250405000308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 418026861 1250 418025611 418025623
    0x504171006030b25080609040602091302092812050717011a0d0b01090e03041d09280b0a0902100207060f1701140402040b071b050904050a0201030e0309030f 69
    0x900100020300e074621000100307104c038101e41300e071404034118a0102d0290705140203d19401402403e02601d09040d920204102682c18445c110840f503010400010b185407444200103004000714103010138650f4003140c40340d41d0601d8400c415001c00340c040c1803400c000062042c44010a10780d54940111203da1012034040e25203040c420700d006226980c0101d4504d000f14110005079001a4449030300d0303083c02403c000800e00107500489500c0103000000741c011450340c42c0c06944903500780c5030155051221441b490815a00c0300003580640991020018054085030440840d400114010661300e41c458400c0042841c000302035084a000d07010684c059800250020444da03217a039502c110241b1841c0c0888042d141001d111560900c2c800c010040c0705600b241c3d082400c500100014075050b030790522041281e101103011502d46011002d10305007080c40c038100400900302920088554074007640d401d900e42000810003818140c4e107682622003014104240c924a0714041d0440f41e05071070405400366910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 418028111 1250 418026861 418026871
    0x70f12020a021f05100b0a0c020118170106080c090103030f0f0c080304050a12050c0a060b03191209090605090a1d060a14060402120c030405120f09041b0504171006030b 74
    0x50b5100002841915041200e5400450b0341e234a018407120340d4011621642c0c103910641c41c0440c02c20300484e05070580c8540d03030050300100c00000745031842c160030b050819400480c094400c80d4124010008650000181d070310b0303d9128505038000c4804443c09543c0c031510701e20064030003c800b108200802c0b03030000700300714158040d41a80d1022030342c0c9401150644122030000c980ca410a1403c01d0004500e50001c0f40a00c10080a645010166040c461400c10190000361000450b468400d145540c200b5013010283c001002c4c248801030070480070031a00302d40584819840d81e80c0341202510381c590314014040702042041610942c1c103110007080090401034409840c03150750003000c2242c0f03182520031208100b00041001c10941c4c1c5210400d070303d0b40c000920035201c6014a4152840c00d0300c20800810002d0507402a054881101c0e01c140000c9880134144208101490700d030008a640d00070303080d28210390400c0740840c0803144400f500c6042c0f100340352091000301d042010101c00c0021840000d8803507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 418029361 1250 418028111 418028131
    0xa0e0102060f04020f06090105211608060114090d02100807020d0305011202010e12010e06190c021f060302130617071d041406040b0a05070f12020a021f05 68
    0x545804207000ba0203070043d0790080d409416101e0782c070850b04102020300031011050428a05000844003c02000341d14417030060300000c040c808020000845042c141001255880d180e5010b20b07040c1e001a0180041d1403002418030300110780c64003642c1d24221120b0650358054240c003045541e60380081c146030700c161110f001500401c14150f0f6076601c21700c1480c1c1202c2910000700030700e0302c032900113441003140c081c94680c100080760705c03090181c0790900440085030007001c020107107403602000d51100c0e0702c034625107134041508204489186039400129000c4200700d0b003072200c4080b451394080078002d12440e03000030b4001255201440c0344812075409981102d0784800c2c42d0700d9203601068410386520403400340c1245a2482400d4107110f250b1074403403d40c42403042d281140c20b001648070561400104407000c82c1c0d080080c03403c0000d401c3c040c0c042d05401584c1c03820090300b500c42003507000d009081c144030b080b9002d55000c60244803d5108000d60710081c818100402c112942d228010006401d040b1034510312 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 418030611 1250 418029361 418029373
    0x6180c09080d14030604240305010501060c030815130905060a050603030424031112070e041808070c210501180b042004051e060a030b2a0a0e0102 64
    0xa96400410000850703259652283c2c0c05410000c0d500000b90030140941e9000b0b1760761403540000400c00d120401201c040c0800d0650240d245161460035030b10140c100c0c0041240308000980040d400164407500640c600182d000c1c030241003c0422584004620300461144c18441c0388010f000d0040f88143c0115168101405107641d80c07018140c1e244a14821900040014003061108055084508401650310b103804074400d2071070718081010360042420035210034205010700112542201c0d00d24185d81e030907542131000401200400b1807540360900003605c0e24400007100300c104002c0c02c61480c0a0189280110283d4109241080c1c6076600715908444c10341c41c0031012000700ba1400d2882c0f4030b188d400005540c0d40d0b035a40d590440c40359034843e103040c02e030960200703111640e988038001c50344101c808440c814400d102c00d9440103c40d03000680b4441c0100800300041c00032a06154600340e0186540d801c0f510005017a140d01c1400580400c9184001c25001c01c450303400591108110458030310903400c5842d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 418031861 1250 418030611 418030619
    0xe040f0f0c090302030115120b13170405010e0109050a15111c0212040e150103090215180f06040b030601051201080d1e09150302040e040b060301060b0c06060405040606180c09 77
    0x500b0307100e03000d23210000004405c0403000401e10000d05501c80040c8001c40e841200c295180402c420031000c01d14090300340032a05200c256072110000c4a495402d1801245581ca040c002c00c030081d4460040702d40540d07103049040740d014003610384a03c14070980412604207009900f107410000050140200c01805036052a40b0022004c0301076a080e40d503c6038032480b203611008440785031540c44804c103d06041d00c034595400980e0b0760280c03070140103542551013903642c0062210302c0c1c0c030b42c80c4c01802c03a84141203040301141d4645030310050710305860720600344990317a40710348005840c28040c041600301312403005c41c00801c072504003180b14080c000d00d580354080401840c1e0b00301150324a003e02e400b000140510800c000c00014034503c3d00c031020a50900615240c2c803440580080c0ca01110180c0b0110040300030300c425400c0074880c00e00140f040004881c100030303844410035140d82000c0c007020300c50348c1c9400101c1c091040750352001c4c0003444812800d135a6010441882c5014001000c500b80100e004004006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 418033111 1250 418031861 418031891
    0xb0f091e0c0702011b051b010c06090b060307080a0c0b16050f15070c050c010e0a0801020406021e010903050403030c020a0b0c2b12050417040602030d0614010e040f0f0c0903020301 79
    0x844041c6e4840081e12441c031003007074810310f000203809003941000184810640441d603a4811346601c20302442c14600c80789030030000d052826045a2004a00b940401205004116888051020b5400c030180c060f40c2c07002440b2180c0d00d07031143c10380b01074080d004655001c3c012100000c0c5540e45842d1400554040b541c6014007a20052207130340000d4155006000c81c0c010325845568180c811040c024050b00015465101003400c9030020b81003540580d208441d1850624100c030030103030b03101c5810302c000c0c440701a0340e41c3c004000e401070380f00043c2440700c81e1500d02c04542c0c071300e02c2050281c0030203140151541084459559240c990303044070041c0c00000c541c5503080501401c0c880140310429202c0201100302e41c82c00740d0080c107000308180c400301c003030401c0440480241d0006000400c8150300442c2c4890011320100101e901642c02900a100586512a1542d0300258509034015086400049c2d80004441400252182d0820303200d5051030701e0003550159810460351000d4a000340d00800c0034003d0a207500f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 418034361 1250 418033111 418033157
    0x408060118090210080414190209060301020a09120302010204080a0b0f160f0507051603110901090606230c0a0b100b0304080304140f0a060212060102010b0f091e0c070201 75
    0x3e904640c01070a0305030194002d484481c1c01502c1400c0100d1a503510b000d0050500f2080f2000309480304180142005601d02460311a4004404400841c5030295400010301000518031230500359041c000c6610b81803500079819a0300a06556040c4c444040540c83c01000ca400216010ac0c089a01e400110360705289a0150250310483e036225403070300c01c848200a60300c5030080c150880d070b00d1003141074450824001a0311440190700c10410700d043d141c5441c00b000207070388050f0001c5500c68540102004090f5002e03a000804105003051328041b403040480301c904510680c440000b080c030600d854442003080e170052031407007600302c02c0c0c01c030319810f03201d260381c14061200313036400f0b0b010b884103002060109110f40c0401c0d4a004140c4211242601200e07001750400902d03032000c0d9541c55000c02c0c00c980b0b0002d10654240c4c0283d003480200100511307800000e1005411003110340c000ca102c040000d402070fa51803a1002c00101d914400186031a00704c0650285612185089001032060140e200302c030719002c450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 418035611 1250 418034361 418034363
    0x12060607120f1d0a0e130f0b090c090403080c0f0705060f01050a0f08060a23090109110a030f0f05250920030f0c04050d06150b0438040806011809 64
    0x134031020301c0e191001c007414007080078018803420030090964200013119041000081c0380b040d80c1441d01d510f0b0910400d81040e9001442500039003480c020000025404001a6401400f000440340c442e540d0004413403d501515900070010300c61b1b14213000718031200544c158100c442c2100c40d200c0d05915020185800b242901c80d49200c0d030321440102d881005150428942c24424100e030314000041c4110b00c0407c20360075540d40c01181d40d102254002d10050482c2c0e51481c8900b9555004040c0c515900d80d0821105d2400c05400c2c0c01d5903a820404102090100c010b02d2000038a1060030700d00d4601840c030f0319a40a104003412903291600329810000310035240d628041190400030304540c2d490784e41803200e2100400305007404c1d40400001c50710380ea40001c6e40342c080c3d008080002e40204030b01b0304039168105030f403c84080303503c05210800100580c680828160f01141e00380c003a040e4400d405400078001c004050240c0321901050100d00c01b0400a0058100c13488942c090b0014100c0d95603c0301100c51400d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 418036861 1250 418035611 418035619
    0x8060907050c0309060f0702100504140604060509040b03011b0908061803091311030109090b0601080405060601181a210114010e0102150f09100e0312060607120f1d 72
    0x104202c1c5d20340030000d807080b020442a03492801400d6400140401e01c08042080800c00210b02489000c036024030400496509540c0140ba0904240000c0d01d41e020749040c65201d03580380e101c01ca42586081d000350040c03181d48039004c040074940e000068004180b40c001c0030755600c210400a0b05510711141c00010700781d03486002d1072500852106104903140700001142c480b80c0c1f2400d0b952070743c03044200158002c0284810004402809140080c001540a4001c5041101c580b0501000c90000f01e40d242d0840c3d02400c10b580080804000050002059848030a80880c100712074045c00ca240300c028110000501c0030018507507da0042c88201c603000f8019864010a20200301042e940500806000800d05004460103244507440c499446541141c00d001804042e505100b4540c1040003505594161040c2c24414821441cbc40c0a5481c09071401c10018a036602020034000c0d2551411210312541024084203149200300020b00500c1480991800148204507032810491030b12040d03401c8034200030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 418038111 1250 418036861 418036867
    0xf1127070509061306030912020307170903070302040f021207080915070509120106050a060203070f080f0c060901090c050d0b04061d030a03142a030c0702040c08060907050c03 77
    0x1500c00c039a1500b2200d16240c1000d0100902842c00084883d500020070301564049481c29061610000704681460240705641c418401280000c082658241c2940e100351015500c403940840080d14122140c0d101940007864440621881000b94004042d07a56052a1107000d5444100d4225070152007290b0305d209036081426010009190148216080003080c54100c0c00c201c4954006580042c0501c00041207a54070b00c42003001382000c1e2a00002000f540c006181040c946407100100c40780e0f4504010f0800700c00050607142c01e03042c2001c0d121040c1011084909902d4600d42079802008162815500c030418207900040c5460845120f80d441544007021005944980e981e40000d02030b504540c1100c0e10500c014400601d070200007806035062990ba000c55409410400c05c00005806050785c0582d03036050b40c1310082d03c05103205560b191507600341c800da5260f54113021102d49004890000f50300504040c0307402d0b10b15502400c400d01070807048800c00d2081d21241c00903600d1384903042c401600d9400c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 418039361 1250 418038111 418038121
    0x5160e0712090819120e0609030d23131704061d0f03030c01090b09010515010f03110f071208190b01050c030d140702010902030601090c0c0f1127 64
    0x54000c454207601c0385542c41e0a2a0044d2000411240081c102c031000514101c00b070324000c00280030788802c100d0080d01401752824000b0207140c6174410713400d03919071041c0c5800c0c070882d0034100032121880c0c0c002804014212404c012440300c2042d0b110f4202914003803c90504100440c0a6204031800c40d180d54640f03003104250808002c60005410b1310480c1c0c000a180125007590300c06100130105100d21b00c2c0001910985450200d000c480080d03c401c0c0036a240c042000340c0c48540317540180f9584070900300a1641204002d088004c0c1800003800d400b00d40020405d01b0b2951000c40140c008035100b03409420040540510885003039404035801c03541d180c40c0301304242c10071100da8011030302070328180b5144c0d2802c0900001030740f0310b51122020b820481d941c1c140b94610803512050164102800e88028416a591500080d6440d1418050258031700c1c0e40d44002a01c00f805640d18628055011180762491400c90602807070070104c1c601e10f1406542c1b418500400302d4510040b0b0030b048401c1007007050b85a110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 418040611 1250 418039361 418039397
    0x504150608101805010e0d110f060c0c030d060618120309030611070515010303020d090e010b0a0c021008010302090601030b061602150304210302270f0d05160e07 71
    0x450481c0d085103046000c0c0f00d02083c02030284042081c0000f005064a100d219402046085030340c812041c01c2c0c10010421009200203d15281c10589138100c554072060326820a0b400d6104200003020070910b04030000807419000b82511254503100009002600d544500321510f03000c100c02c0040014050950071310001c0e84035401488103480003181e07a8280344072684d0340d502d000f070804001b200040c0301030b0042081540c104000510044249014180c1a00d420401e514500c0180142204510042011240303640309600300403510740c004102c0000f040180b480901942c0c02030005901079000c18000801950180c0200b01c405a000f404441c5084403060308410302965804080b43d010003503d4003640b203142800061401903008ac80f1706a1b11036080450b005d50304041211003020b150041c00f000409040a26810440e11144540c001e0005481c0c4000707014968903849055025902616150030320200080b1601d14104800010f90043e4951001d42d500b114200c4444001800400000f140300f10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 418041861 1250 418040611 418040621
    0x11d061221040509010501030608030a080402011404060f11010203071202070606030b0f07020601061e08041703073b130902060d050727140a0b0409050415060810 71
    0x2600041c0d415008403005116400c00020102452215001c10b090049151080010340145400d00b07080121618040b42c050b142d01500b0b0706076050215000002c0d065900500e9014411010010955541c58503260003070215416a08048001840d0301c00010000c4014821640200d40948995a120352140c00c0e40d40603510050048070540c2d11a1310020000790448441802801c20000050480ca08000c0003860b00d41c050340410304200920001042c0b801140e8056140d545080c40c00c404580c1d80c0f41029000c0340d100322500c02c8444000010015240d078401d550b8401440241607482c204801308030304001d059034005500703100540c01d045220f400d18102001074410640c4410100709200b0702c1d0006903103a0441c9005038501a2900e00300450301d0392140c800c031940140e0441003007070030290ba80c00e445071b01c1d124040c2656025034060402c0310b955a0205100003010700341841d60303980c0d444840344005480d05690403294171098449144003080c003409088103440b020700040103100f400e4446003010381 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 418043111 1250 418041861 418041889
    0x6030302190c05060301080f120306090a020f1c020306120a0528060e06060a0b21060409020603130b0105010504031e03170f07080603030703051801021e0604020306011d06 75
    0x882c0e009030004464131881c01941c000d00a400c0540800794a409415040c10300801503a10001005c00801840e0360b00e8042240d04120f2030ae50040e01c0742216041c10f040b6201c2da21050080c58148032983d82c220701150015171084009413071001949907001d50042e51001c0034034004015400c220813140e000c08200c002c0c403041041d905408110810681c07601c004580720211080100d07040071007048680c0c1498103401c00105100c4030058035210050340320020100e201051904600031010114803d591250071811100760010701c1030356039041103a070310002c828030910100c94111000000244940c05101a6011070740c0269900b101c10010303000004907800050000c4040c000502801c0c0446907064440a21412014800c9541030411401c041c2c02d880d8000c00307807403181e07000300b101c140001c0c1d00c44141c4070300a4031030001d6031841c0c2d2100c0040c0d00381040040d04070241040c489060401c0000002d01a028500070b80075240541d8895844520384840c18910b80e09803c800f0000c00d500e4202034200403c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418044361 1250 418043111 418043123
    0x5030a020309071d010602011104080c01140409140603120a0203044101021605182502030a0809010b0f060a020a1502041a120423030a170a0603030219 66
    0xb980c2c988a207208001c1d001d078500e50401c4c05a400500019409200344003800c06850030b600e0600f13192010440c1d540da0750320100c604101000b03d030070100c0380b4a00c00b65000b5000701c01007031041007a00340100c08041001c80e82076102c0c0c8111042c0d1007a901070501100c00ea80c3c0554055490300b0b042c0401c00103c1e81020078452500c0c0d18080b0b100d04000005190521800d40800d8840c915100704000245400407400345004d8403401c1c24010801c0380d6842480080c039141600307014440341e0b522068a0840c038800904101135400c094a0b021019070701100400307203902e9a0300c0b96005d0392a4482d48608039200c406000d80c10040c0b4100003501490300401400c0011103a104940b48442140d69542d80c0190f00c003072816250344c000c00c091102c8503405803c048507000c100030060178503404a01c60000107202400c0944410420800c1d0304074001c0c05107060008012410813280e070364400a000a01d0844d02c1004c00f011031900c0b50224070044002d019a030708598050b070042900d00580d180e01c082001d0b21038002c80341 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 418045611 1250 418044361 418044373
    0x51b121803070b0106030c020c06190207081606021e0a030c02040b10020f070e0408030601050a050409110a093309050306010b2a0a030509060d02070b0a0b060a05030a020309 76
    0x64403401c1000349403462282d801035076507516241e80941500d07005d485110541d0414922412a901e0780425142e60300700c0c0054001d00366082100503420036040e50002e445502a0403011400d11940d002007500f1114103500711140b40d1151400380007001c0b020013084e41e0f10381050200e07030b010a202d0030006071554001400041c401c00f01c10700050307074400768900410260b0001070494410707070010b101040003010101c8103540580340c2507840e40c84900c001072004d030500c170b00403407454009407240088d1809020380010030480080302c0680101c0503001608004d00144011350301040b00780344400030ba0510300c00c5c1e11655104450b003290202d103a0700042c02d81d004000c040360001a1710354040001600a051312410190780b2146a203239544107954010140c07505958400c18249044000200d4400540d05842c0058540c2d400f5030025a95100341c090740e60303803680041600b0080c400f154a0b118003070b21010104211309442c000c01d100d510b0203241c05000100f0018000640d2a0801c1d4004541c000b2030171b8143c80c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 418046861 1250 418045611 418045651
    0x1d06160b0f040f2d230f0a20090106110601090204030812040201030e0109080705010c020f0607050a17010b090f031b04020706060e010308070309090b0d02012d02010e01051b12 77
    0xe2140c4c03c80b00c10b6414084010b09146105050340641005400341c402900990892441065484810580082520300b2441001801d554040c01d10302d4040e00040149480d540d43e80f100810700c01900c4030705041401010000101d8620034400c50f421240c0c009032240c24425217030014090a400280b040c0d040c192038407100f40c000305080c484d014455104052043d21205c8a0900908460b88061036900750f43c80011501400d5a0000d070260f400344d06e074580156680545e003800c8800c11511041310031403102e160f00205658801a025007480003050301d1155521aa00d030405a079881c1e0705240700c849946007007041c8054201600104400ca028500c0132171001da45040c14081e81c03030300341e0050301c4090000c01d5460400d903100d0305940c0102001034050140000150000340300c1064460024140104400c1c2a9a661000030110105404001202a0445c0341900203400782400780e00000352940307050b002440749031008503680070031020b00a030542040d40c1e80704814460340c070162503000c4d00c0c800107015038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 418048111 1250 418046861 418046933
    0x10e0a0b070501060504110921010f140a051504020901050c120702090f06181f0312020f0102040f06110a0506073c1d06160b0f040f 58
    0x40080400300400c903034074691410030a0864403150081407069040803118030040ea03100c4181c80c14903108a0301701000240d0590700c024107800c03001d07210800f035080c9601e100e8025100d40c000c1007400c103001c40c1081d0b45e5a621950800326071040700d9803c1d1001b0b0007d00d400c124101a805406048418140343e0f140002c0c882e0340030725200a40050a894141c0082c8500460030511001c58000b825540312030450300380702c00010650103000d0864440c1c1c114640015038a81d411040c06164411314098001d2415100c4c14a2400040385034a80c0e0098171441e0030581c420f00c814403c6400711005800b0700143d40d803c12004407960740d03100401d00e03a6442554030600108100380407850141d08107032100c801d0907180e10800e00540c20040c0d48680e01001c40c0903400d01103c00200c40c811014628601085040207107910406048144224940c03c060301040000401c01401d480d20f00780b60042902000e150744106a00c08507030000c94004101080380102c4800113040412002c480c80581d005e19200f14800b2031803e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 418049361 1250 418048111 418048129
    0x90c09030503030a3201140f13050a05060a05090c28020c01030c0503130b0c040f080a140109080403140709051317030c0f070503040503060f090c0117070e010e 70
    0x30a20303070b542d400304000b6640700c01001d4030324500b10a001164160349140c01100c01c000511030304403800d01c44000a02ca0b03236954040b141410304006c103006407042da0104842c00900003100c106108614200104481e4681034114008541005003005155500c804100340140c000301e00c2e040b09591006a40000002c110b07503150030a01240d80181139a00ca80c100040c2541c1c1c0c01c0440b101440001c10134042400b54011040c000b480d04550380303008546403942008040d218950000c40f42d26001c44001c601400081141b00c610340c010900c0255000c880c01c00c0608076080080300070303c520010030003040010707005102c02c0da089941800b42c40030155110082000e49104880e40d1407901d0005007200200040400045942d41c1100030580c1035141240c003031021403245d006204400400440c26004000d42001200c02030040a0181c410a052158200c10f9910003600c0070101401003158003c411f510815001c6032026070b0405082081d2075000060310218004045541085805401c01c4100e817a10401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 418050611 1250 418049361 418049371
    0xa120219021f15090c0c02060309010f05180303010e10050a060519020d0e040f02041a033709050a0c06200304080d0807120f02030411060c07090c0903050303 69
    0x7500004038003059100c00e080d902d22100103420f03e00850501c0890030f040301c1c102070b500190000a0108600c0100390345044000380c00a500220001c01c0082103101900f24274007404242205111540320b8583d481c586045004421150760310034001003050303036541d010054120740f0518a40c9421902c890105030112207a030040700120700001a86d811410400884401200c1c4a20240080140f0b00c50002e06041003042904d214503180c1c000c0b81c04025140e41142c00400107101c8001e201916504404925041101c2c20300e036000041648101940103100104882117407039200c00c0007800102917901c014584c810742528180b060388034460014090401c00c4000d84955200d40000440c07840d00f0598480300700081f4030b1aa00103000400015000280c150702c00d4100d0b04108000340d4403448111000500e19040c0c098050030410039642910180c0c0c0114015802002c204150304210028841c2a200e607a10304d040503449000b04100d4032102e035001c404040f00c1490300c0c0084aa5941701c1502e15002a00c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 418051861 1250 418050611 418050613
    0x150b0c0a11010f0e060318070f03110603010311090c040b0706150609060c0b281e05010e040b04050c060711030f0705030307080a030204090204090b031e030a12021902 73
    0x6a850511401282001c0329240910b0200c44008a601d0300400c22010304039a42d02442d40800419150880c0110189a86091008075580390740d88403640c0e552031407944000d4801512428865040d0304040c000c92381030fa41c0000c508040c1165000078000c0e4198001c0c117020100380d0501c00820041e815070014403030240180008181440784041120122a840d4401030030302805500802656030800c8050700c000703800259840499841520400c2908002c0d4060310764000c041103000d1450600e0362041e100c2010503070b0f82c0d052035214500840110f0b102802000d0030318103480002800101d85901c2280d01030b20641c03c1c2d0f03240c2d00541d80410482e4100d0b03103084800000802507030b010303401c0400c098190040f13290010030759146444040f81d102d108101d4003078034601001509610090180c0c0441d00100b0b845041199681d584040382802007540710440d5100740038a0714002c400724a246040d10f80e000c108005103151240d4030301c1c141c889100d004510704481c0d800303020500408694510150810440350 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 418053111 1250 418051861 418051873
    0x20316030f0501080a031214010f30140705060a05040801050a0b0609120f031303061410120501060e04050120070b0a0911090106050406140405060706150b0c 69
    0xa401409075801400c070707081494506001040a240001906040540c040c1030070f079000103000700c2081c043c01540041100384200400001100c4408044250444840e610520f440600403910181240c0035250720007030450100c6078240110340018402c0750b4021000341100c03910755960303000c1036854010b101d50001142000c00d00f00f001c2d11080c020f080c0c0c000e140b40001c01104410701c0002c1c038070340640c1c071200340981c80c1280715801c070b030f4002c010425450048004403612060300d82c0d00d02c68503400074042110180c0c14959400f100f40d0f09a020f20340107c0c101ca00d8815054101340d411044c41040c581e0a445a641329540080e0300800101d689000710700840020803048441001c0040604074002610b0022900300070300c401040c020300500741c10814661010442c06c400c1e05009050364000c4a560b075001c0080400000c0d000d4003e40100100c807440d40341e40e030841d051251490158000c502c502038004a00708046400100254845e003000c95030f1035040c0710a6600c1c0d0f00040c80d03582026001603450350000b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 418054361 1250 418053111 418053151
    0x90e040230010c02331e010324090f06021e04090c0206010b041d04020a051c0204050907030b01092f03010f1a0d0e03091e12012309100203 61
    0x40c4071101d05030059590458803079803a24400320004080d000300b001c0840e100004500c1d45104c2829002c001d51a1151b005050358403400e202c0b06150350262040307400962042c4401d050724841c010b102c0100d1304001086400d810355202c0c640a503000405a00d203020000300406010001000030b00050000803100048a240d03421002c1e1510806800c0900c2841c3c0c1400100030b070407900044005035801091a04841d51168030205410000340d40045074010694140d4008102002c040d03505180e008640900c1151074034010f0b43e0703c2d07014a01001e808040b05400521035989036401081d80404100c0c860345a01c4101034014000180b00c4007100100302000004000865002121201408414510b203400745980c03840002940701c2d0807100352010352a00340c40b041c540d60030301c1550031000d006810b50000c10b400d402c2c8a9603000151010a109212280e5450f145080500ca410503010b8080c0460300203001820303041c05540001050780000e4841c0800c84002c4100300d001840c003414030700d00303541301d28504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 418055611 1250 418054361 418054363
    0x20a091e0509031c090303020d0f020c15060d030c050a0804060531060c150e030a02071d180705100f0e01021203010614210412090e040230010c02 64
    0x142c480e41c655032082c84050440c2524560304070b1040c583d00c3c1c002800e89000d19042d4045d004103110688001c0c505202001c07440056002482141d804805562468003480030726814070206541d0b940d080140b110880c000680a40c1c1c4502c1007074050021103e00c600c890342e40c04041e510580008000450200d14a0015074603041112003c91600804481004000c10901d8001c3e030b0700d01c5036500300f0002c01c41c8501400641d070020030181041003401e210f900740f90b5000c1681e0b0b51050400000600c660103000400080c0c00007001408170b05501c446229132502504d40781c0708400441710b43c0e0b0078001d020340050740c0ea540b0300105280c812651607145c1c5140100b8000380032001e454040d141550011403115240000180c00c07a0705441d41070030903101541013103400d20524010054081c110030054446c020340003041d0120184540d00c00c1684e04291401100c080703032000d025205000307221500c007006c100113250a027911111490101e51115000380c0c88076180c440f5801d5041e04000c0c0b6596a80000c00b5554 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 418056861 1250 418055611 418055621
    0x90c0f03050a0519110907051314120601140f01020f060708150609180705090d050a120c12030203070e06130609081f050901090219050109050f03030a0c020a091e 71
    0x2155100301c40000c1100e844000d143d401715950340e84240d40f51800034260500420507180c58060019041051503115640311081d0404880220f10842e102251280c03500800150641030310003100c1600c1e03010001500b0f010b1002e40d041c40e003a0540c0a5800090803c50302041181d10950f020b94402c0342508080e83c1d00605002c1251815004490400c41c810607602c81302d42d1604200900c3c282420203503200c11044425000d2200d900c2e60040001904d0801c0c05000201000f90741c1c000c000d880c16085d82924140e0391804189070007400503811203046483c090003640515400042c60800440364200c0d0800944664021b80042c070300c118800d2000d12016500010700c602804070300d001040700700748201ca420407c40e00310003040121919900007030f0b0f41010030342002038030950192118034542c41e241c014021003d0a8040c1600181604000181d10710300440440d2240002a01840c03401c0b203005d00440f40d01214400580e084641c1d00c0c80001c41800c5445035180001c841903c417422403e11010407001e580c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 418058111 1250 418056861 418056883
    0x7050a1709090c180108061c050604120801320a0305010207060c110a2003161a070206090907030b060c0a1403040e060603100b2a120d090c0f03050a05 66
    0x703c02840360041420210802420b0050b0908017074506945100000e00054000f10344204846020b1000c036041010000707502c4d008a1088110f100c00e90080c070700481c4d00a000f4441c401092503800ba002c10130203541c0074441c803540c2e041c0c44031001d44840807010030700d01d18240d072048903107030b5000074100140100751080b117a40c0200c83c0340240d60011690800c9940703084e40000503099140310b20310f2081310022a4001e0f408070f20013409071040d004100c0180d51449030701e0701c540c84145003240c02085454512038200e40086500074805403c110b800024443d11040040070305040c0741d594202501a56289400f60005030b40180003080c58140724030702480c15441909030014247d00c01d00042c0050703801061180d030b02040a550068032599906070482c1406403960160200f144001004074802c05001071000c05031200300c0c3c4580300c030070000010ba80d40710101c0d946030342d01c1d4a080c082000d80b800e95810556103503000d2031464001507180d2800d05286500380e030046a0691000d40000100300040c09605001c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 418059361 1250 418058111 418058131
    0x507030915020d0e060703020406090e09120306120a050c01090f030203060406090213020304030804140a1718150a110313091d01050414011a1507050a170909 69
    0x140390070380c0d40c03620001c1d699019a05098000c220280758882d180d02c44103102c0311410031295581003262014009501c60f0049600007003903d60041180c00159480782d0046150000611280d1400e00f0031543c213810150980703500140300c40340002c9126040100300c250380d00a074090030300e00c480301c40054050074943d440220070312b05441042001d42e4000c1401c581c0942c00003070202c0c001003e40300290000301008008207285101006120605901402c1c0c00c4c400c81c461115604621410031800e61b03a480720013801000d013042640c12850030155003024215000c0b007e82d50801078030b500000101c2d990360a180f07012a0080228070b400403590301c4440083d91005220140d482c044074284500705aa11a015910700951503c4106401e03a143c2c00d01c0120040145000300145d040615182d101c0d50703417101030361445600340f480030305140b00000106410788030010080b9100340c04130f8a1000640d000002c0640c2c80b03001e241c1c99900400e2240e40403e0381100031004882c0d030380080804002c02c4440241c452280707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 418060611 1250 418059361 418059371
    0x315051005041109040e03040f030b1603050c0a031e02040810060b0403031d060904110307020d03050915090f06181002070c0b0304020d080c030702030c0907171005061309050703 78
    0x40c0611840440d20028800d403404507005503050300e01407a510903030340040c4427035188150002c01e0102041c00f1034000c0c060400b01502e07d40411800b20155501611084040031040100c03222041c02580400315020b8513181205001c01c01c501210704a030401c0d030040e2080d42204024884050b120f11590001d81a02c1a2081c2014115140109a211074500b41d9141c070100e01e101d91007aa81e11001c1d00c01c10a8000e00500c0214200c615004e010f03082a00c118025200d00380b070011a45029000711841500508020b140c0d034201401c030000c103041c2c007030514092406030340004224048140314141c4a83c20203813004a42c0f420305aa402c2c5843c2c0728880d80468980b041c40303040d0025803000304220440c1c0c0c0b0701c1201a220b8469000294800b81d032480014003041e400100151044004006854224021000d030b80962030b00d001403060700c4034129074210001d00000b906910b42c00710020b0141e0400baa0b07040c1c541c4140d49506c0860032545c841400c00e140c890158404008540385402043c1d80300c4010328040c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 418061861 1250 418060611 418060631
    0xf0e1204080304061121090f040b10120e1c080109140703020304110a0807050f0909030a0309030c05150a06060e010c031116031a0c161b031505100504 66
    0x103181d00071805014200500260038a4408900f000f43c0140821b10fa8a1550304114101c180045a8009201c85010301c000602e1907d00c1d15140c42294040000034007414480010481d04a800384945000150103d9684102c4910701c40200700649902c40003540b1003122103615400500000340c142d110492590910b83d0002c0441342d110303a5503030070861908016031652a07600d000741c1d43c5d114810a00d81c2100000e900000d40c008000b40400480310113071003080040710200280035045004a07000c5800d54020010489072034426400001014000d04d06056501e0140c0c0c0e500e41481800961103100c18942c2040c8541c001d5107108080090005080400d01820b546001034243c00d5240d0000e402d020a0128003042004140030300c0003240c03910340700034070020b440b0700e04907501c06060b9100008912200c4009141139544c00c0440343d8040715101d407454884181d544580032aa0f040c0d10484800030813290010010790442d8964010a085420105052508180c4800d00c105141d01c607070301c50f605190804e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 418063111 1250 418061861 418061863
    0x30908030a0c2303030405100e0a080f0a140406050405030c0108041a040213020d051008030c060109020d0b150702030c0a0b0a0810081f14010308090906030c03010f0e120408 76
    0x40ea1003580000500fa5803003c80168050044031015400094040001000204040480c010074440c841450030848100300c0c5003000e544040100d03005003202c42c04c000c500e4078081100040c1c141c01140d4903000880383c481d00c0d108003454109901c0400482c4000c1010710152400b0300502e990004286000312036031804d40c442c1d2581118440d060f500e104001c030080740c15522800062408000c641070709550f01c445132200540140f10440702100c090f545000c01080c0700303401004031105800100300418440c7d08244d4000001c0d445100024101551059098003540380c0c034224450300a401da0f001c41d111821401494141000c07048003a106044100003800203404000c10b68a0240080c0348c034540c2d80c0c0d260b40448100b06003542000d400d5105291a1380e070090724000c82202c00a10f416014000301200701c8200301c0c400002c1c000280701d41c4040c4441001410528089a0700420007030840700808124004203085401e0300740d14801c141e480760030340d520644040012031700044040660303030f1516203024075031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 418064361 1250 418063111 418063127
    0xb0a090f020d060902091303090b0a2015040b0a0e0105010501020303070f020c18010315060e0414030d060e0a06061d0d030c15051501020109170a14070807030908030a 73
    0xb84641442c110880c1486555840726060990103060301c1458103102e4810f0701c1c081440d01c0d0071000280c85041c00f2800d64404010385a10740746070b40720990881c07030030140d0b0b00c403640522072a0b4803244120000101851204c044240c0118040c0007005510704200303000c17506890410001c103041c3d0707041030300405c00741c1d070b0000031a80d02c04964901805404101c80c012414861162041ca42c004505501100090350181c000ca04a80c403034071540300300c0d24030841c0b0403055800d144501c1108a0050001401050b1030001c07111600a0480540e85403804100c690400c568103a00544c0b1860082d800700442e61440340320749405030075142890340071800210450070240c260004001e004000d4103408004040c0105070354540a81d014007100050301ca691410740080804039120003a00380c0010080c641540103100300349080e9003100d82e600110341c82000c1c90308103074040b4045408001020341c613014000b200e8009422910300c50b9800c55910515400c00900480300c9400240c1e10350030070002007030316907044024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 418065611 1250 418064361 418064363
    0x60f1e0f0e1201050a0b0d051908210105040f0605030a02061b0303090c270a1119020114060114180d020405042603060105040b090d1e0b0a090f 63
    0x1010112255000c4941035440031406421800c08850340340364240640119201e1501710030100a1164503504000311040ca24901401c0c0341c001f403030b8401248030009110310718640541c0035117240113081305c070001410700602c00c90402d4020030801405545084d00807040d500c00041404e211590500c8006500c44080c0c2000030301c5400005880c400107a030a80d0a00321801800f020340e9140c2ca041182d560700c0b20b1500400601c141c14565007222942c1c8040034600100404102d503d104d41d0f07504181400902c0c80700c0c0d01b21140c950034401c3e040710100c444245200e041040c0d00101d100b0001141d01c900310f10000e040c95040c0050b4442c481500e039805029100c800614000700c411070b04081002c60b190300e004003000b079001410103040005110f200b000c0901038000f041c0c070b4040e6001001811101c5400b007a60740d10f0000342d04000401c030134080e54003d400400002840603d40d91700c00e9442c031803001301c40c00b80545c0300f444d901d000300c090002c0780002d03d80c0101111014410100c041d910040303881d0f8041d078 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 418066861 1250 418065611 418065617
    0x1080c0613050d2022090317070e120607020c0d03050408030f070506070906020309040f06050d061b0e150a0c0f061d010b0612180a0804060f1e 63
    0x5100030000700c80003801d8000302006420055a403680381001104954491204034a600074034004500300d042148291032092100428140d000d0031a01d2520080c06020400381d0400c2264883c4070010001425030318040c0d0b0741074132283d10b1440c0070760601507606882c40e050704090300302e40304002010350085405c1a140c0d90071034140440c5e01e210324058a00c0d014a0b002100039100116030300000720490001421180e0084003166281e41d01d000c07086504507141d004d010010380052103002c4850905403c8201d40025200c0045209134865010031085c1014110564807107840301c02e130b0007981c0c0c56844c0320b211002461a00408103001100032400c41030400000d05100c0ca00000c9071902203100d0380071410304a41c00815105582d136682403150142c446001b020b01c5030382062101c056540014803903015180d4014280e81c0c10640405c1c0c282031003810042c221415195181c2150010000601042c10300500c560b400a480314100324009004d030541001c2c04007840646203122540750f00844614400c9540c1e27107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 418068111 1250 418066861 418066867
    0xb0c090111060c0a0306050906010c0803060a1221090308030c0f22030c080d1202070206041706011d0f0a0b010203040911030103110414130512190e040501080c06 71
    0x18012116510200d03001c070300c68014401030180d007446420003002c84c880203035010300106440304101b089004090783c001d400300304034071002c100040f8000051648a0001400380342000d07a11007982819141d0a88115003001300280444d91808403ca944282d049040c0b40c807400031425a907628a05110140040e6520140840c03c2207045141c08126080e10b82d1900040c090070700d82c01503000540c1d0f03c9010842d1407010000d4007241c11071000420310080f40440c2d41b007449040d1425002c500a5006140590704103904000100e2244208440c101c40c402d100302c0100b40315031400d42950080403482c100b007801c0001440c01d0000c525120b24585800080c41c0b0f6000400b14100001030f03145202d00c0d80100c2401c6e0800080c070a5004030079005d14100da0040a80110032442b100800085400c100501030210034000081140049903094145c500c030302c14421245258a91070540919804c1416058000d505194007a0589a48410100c0a5810540301403000394180f044454650b076862034018000c02004c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 418069361 1250 418068111 418068127
    0xb04030503040623060307080105191505030106180c021504020103051f0902182709010f0906020403021206060a1a04030b010602011b090f0905042109170601030b0c 72
    0x107a000d80880f07140501d24a0b020007044204e55106041101c2c180d110f40102c113400a81c816040c020540b09040c4a441c5d280000314280172140113120b240002400d00d100e0100108540e1030912542d0044c08900450400000ea0504040305a8400c2d405040854000c500826078aa004106981c0c11550908001c503103642c501103030350b10075812441107850a261142d8000780307000301ca0f8014545450552034002d002d458071018000b1643c204550240c0144075405651003072441d40d8415500300030708a00218840c01803030f1410781038034803880b41900e10540c001401c1045240a90004058a617001d000c1c050518042000400c01d403640c2c0300380c000384401e440000d046104c1080c1141c0185500007000c1a5558486100900800c0051001040210000301d684411800380180c0400c86d006080041c62180c1031861700c3c0e01030320380508200d459800c1e40085442000700f55020b0a1070fa84142e80d04207034140360440340170140d00c13503503030005803500050014000f0950b00c003411365204464448281d03883c416 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 418070611 1250 418069361 418069373
    0x40609020d0b040b060315091c051b0309041b090e090717060f060303070c090c0905040f090c06110a020f2215062d02010216030c0b0a06030b0403050304 67
    0x1c2140050144900a003084104000c40c0140c502800040d01100c90418809001520303280c02900c105070b41d64003189559001c03400c0048005600c0049103841c504243d28481e40c0000c5400100082030503400100350381d105405c0500c81c0c6441600c400c0c0b095010200b4502014000e0000b50041c40003015100b000a00c8401d0100000301c010003400000c50f41491141541d00c2d01e0744404d407400319410b000000450031601c0c00200355040d00740c02c0f210507020649450400401402d1a88202040c0101b4400010342652184242030b0082c814402c0401d4040180c0360401c403092051b0401720502112000180b00c4c3d450000d01011a250b051f030358440e4a03148000081d1045c45080c2158122014030700030400c10f03624581005001c0756074456503000007a2134010aa40b00440302c1000e002423000000d81d806e042c00c0600348070020300e196000040c5461010281004c0e11035140e1402c1d00800c4002529000300000c242015034002d06c4c00300100306907404c60751943c4000002810140c00c201e000b1022900b4490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 418071861 1250 418070611 418070629
    0x120304051501030c0515032401030e030d1b0905060a0c0309210302160f140a0906080d03181208150a1d100623090406030f06150f0512030c030c01021c0b060304060902 73
    0x32404070dd84640c0c80c4050003025000750351010100d52000340300c10427164010120315054610003001a400e103440b02d00101d034031403404141902000440c042c001031044c0040080004044c040c250b412400d074a60030040d1500c5c0b203082d1003c0e558420303420200074403066030840405940400d40e500310b0f0a140324000650200040d002400e009140680000301e480d40040c07440122822914180f10181982604600c0c01c03d1110000e030041c0b140038008413126200340070840d805007110040d00c0312900040c0206103400d445e904040000c00300e8a00200407814070140b040d921030000501050310038244980140404a00e00b5031144d814400c8c0607080d100c0000390103840300c1c2e400141041203c9540c1b804d2010050404100507610b480c40d107003403201076600e01c0400005598070000c250b0440c0d46000d080c01030b003c480400c2040940028003109103a56414001040f6200096002584035807294000da000e014441e90901c4c0c01b01e2030801001241d80f100815a64469004000015504070a001060340c00d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 418073111 1250 418071861 418071881
    0x7060209060a0201061809080304020f061605010e01060b031006140d0903080f060108091b0609040603050618160504020d020d0219091205120304051501030c051503240103 75
    0x142000c40c80c140883e6055100400319651403540040d80b1000300007540c12986000e6000c2c04243c0c04000040140c20a0400450040030140549140c0600004000358900c90038004031103c0c1d454065a0199000c01d020300307009080401041032950500c40e89240001d0003d101354410312039488400602d4442000c181c1d04550605903041c05410a1464010400e42d81202c0d040c40c0c0461080100e0825441074484602c81c0c0c01010080401e001c446041c94207001240a0b516800b00c0c0400c05100d96854030300402008603c60780042c50301d41040301c03554191017098101012558020307031202c940d40c6845400345d070171501d00b607400590701c40790014010003034422002c0040443d07000240650481c82c41c0008640c4801069881d03c4501d80c40700b5031102c2508041c40c018110381d000c154000001c0f494480190740062141e422129502c054010105d590300c03090380151a05c10300c02200f00401c0c1403a48680141d80030200c6a180303940b034400744204801e0141e02da01080d000460003181c0541e402503000c82d00c0c3d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 418074361 1250 418073111 418073119
    0x1612090305032803090320011d01020c0f150f13020a060e0306060102010c020a0605060a053105040308150415230603070c020d1e03030207062a0507060209 68
    0x241021030440402c40705110800610710000d480143e560307071003031141c44503c1e80d02d651440c502c3d0741c070b150101481c030650429801c8255a204858080e02400c00240f807030f50070b414400981c86070f80c28094039050070080445a1115040400300340b001031003001c4410342c00300840c60255031940b6001d03070004161001200c000d4000801040100307070180c101c0034060b10000100c1c2101e03403603a42c52004900340c0e01044644d101690041d0b000d100043c4154000307a40c80680a009003020a568200007054481c007040045420308100f07c2210b01d01c0390326010f41c884087e5094042c440e904103a41c0041075000000d00c0e00c21860300c40c0c01c20600b42d40d82c0e5003280c05082090051029040d85862900c0d8003180b03400404501520721024240c1d0b1801c010701680e10480541d00ea29070781c0744483c0c0a2200034500c0c640300b2541c85024100880700164070015a00e11a07000f82c0d0016218001443d21108440801c1072410880740c43ea030070032040400300307080001c078200da514005844040501e4a01c001e0b000354031016502c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 418075611 1250 418074361 418074367
    0x60f260a0b014104020c01020403060516050c150a0b030d11071707090c090b0f0720030c040f060518060108010b0307050d020912060a0b15161209030503 67
    0x1070240d080c084a06841e0700322070380010b00c1040d4884860100c5207181648164040700b00b1107040d1030110840c000c0c1560040c002502e002e20103e007071403c80e446034004564440c0c1d00c07001e003e030754a0b805d00e07850500203440c144145422a18185142c0c0c0381c40140c1c0601c03883d18001c00140c0031585681000f03091076800303421a07001000028010701a0000004195003512a000c00020303424413a981800109000e9006010f00d075090014100191400b0b24560342442000040041d072401140000c240d03c801d0601c44544505e030510305100d10284155124440c00030801001180f940d000c15002c0128800b154001246000b180352a809480c503644256804044480d101d401c1c80e0114002a01c00e0000740da5003407a907030320380241145a00003604c8400018106200f0119541c10550003000c40440041202186190901a03180b5201003224011222a169154803842d400c000700041c0f4508441104642031014502c0d2003280f80114071405400491200c40b030071078050003a001d0b0009150001e040c0c0c0d503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 418076861 1250 418075611 418075613
    0x100b0a050d060b1c0c1208090a0608010515180415080712060b010c051506010c120c0302010e0d0f0503060406090501060815150d0c140a020d0e04060f260a 68
    0x10050002080c0c0303901a01422904d22848030414203200d158640c041d8161010030304008000c00b003402e50000440d513456007080f85212503520351100900400042da0f0707452466040105100000419206116413100300380081030140e00400d14400d0104e10035580000e42c64106030400c1c03004d2880e580014442d0241311000701341d402021000c2500c0780d004000c2400124010401114270190152010700701d9045078003217554440c04811322980102c414980300000c1062522280210000c080800c2e010400840c41c0100301a02801034000680d06ca00103000c840c03d0300030010304900c400503908010010000006612541c8990101015080500003080b0b80e40c2c40346000743c4010b0042c0d40010800d8010f0b00303407181c40c1ca0101004501000404421401c2c00114000d00000d0140b201c444400d101c1c0b1501801564401c000260030070b07000e03a600400a06c00c0341103000d8440d130340a0040038050350800e1310500c81840191001d008540c0c040080a259010b200890350b400070350701004000501034441000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 418078111 1250 418076861 418076873
    0x2060a0f2c0f0a031e0303020f27030d050d0902061b150c03010302030a03030f14090319030e0a0f0503040b0d050a050f091203090c1f020706020708100b0a050d 70
    0x5441c1e20151160b980c42c211480801c12004944d200c001c004001c56950342607410001a040d5580318442c0c14090b00708044501004400d8010010003440c50b0703c800c100a80c2740b404443d0524400b03600382c01500715040580702c01001441503034500e181858642445e0000c5494002c1116596170480c0b42c4034041100c3c40c1012520b4040c0c0081399810f8040720004565118103040490303041b20303402801402070780c1c00d035a03091700603143e4884404001030b50781006011015200031214402c11403c4055a51034040c89484c640c100d444181d000d040501d0401e440c954803e00180c1042d105821480816090a09151441c5503224036000018880c40224490020018a4121034040c0486003000d003e19541c0700240c050b01481102c28441170342c000040c20001c03219803402150400c090070262822442d00802041d14849000700c040c070044800454085595410701c118030107041c0900c080c0525510f0300c150b00f5600c141240ba02c0108560714040801c49903108a044802040080c2c81c4040c056a142055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 418079361 1250 418078111 418078187
    0x506061608130f0f05040f06080312010e180634090504060e04320d0210050601030905070b0a170a09060e0d120504150905030414010203040302060a0f 66
    0x60407030085640b020541154600e520001c0c1c0d400746030210400c1e0f00c5c11041101504030080e285819a944400100e140341c014402445080d40002581206502d018642c4c4883c040090070581c0511040c84640ca40340000305140707800c454043c07030316080e00051400101601d032404401050303c210000d0582140e41c2c02502c584202c3e0002c40d001c00c00719a55100400502c2401c5400900c4405c0f08a05000c01c501c414210b2003a0400958584502c5012403d840b882d00d1403032002680941d102e03141c01c403581c10b1540107113940001d00b031a0601600c0e5040e614280da49085000d034000c6001c0100d28403440a00c1100301d100c2c00d00c007110b454034540c106020108010482040159815418031240d441c1359840000c115100e840c10750364401020790f00189a800030200548100c0d0891103203141c924001d00b940c000c0e050b040d40210301943e84d03180340c4039036034080d8403000000034151340081c032040003d43d0741c16094038446086030609041c91482e860041702d41e490356003d600389c44031000e980440840b0a120709 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 418080611 1250 418079361 418079377
    0x203210417241602030415210204120b090312010302060a230a2c0d020d0204060902031e16050a0c02090405071e0506040306020c030409050c03060108070507050705040506061608 78
    0x354040700c00803d0080703071a0320079030050000584d180c48107900c82600c0703102500c40c400001e181d402c048042e4000e020041c1d030b005500c0710000e0090703080690144403803a40b40580244406004526100034031001d5201d0784030510000c2e00c84d4502181c04541c003406640c424024a11820000c106000d1070084410181c000310201c100080c280301d00c544040340b900701796002c440b01042281040b04511410015400e140000881e004060010740d000103071642d008407000382054100260b12854014000780c0c03004c02000e0142c0c452801d0074284020700002d019061041b0810307203000e80c0d41c0c0d000c59000b03903800038522800a42201c004400c02c81030204c007044060683e00200c0c00e002c000314001c0d80708a80c040c0c0c607000d15584041d04200403c0045d645074020052180a28252403d09a40d00105000c49204680804641c400041000301540c0c0c403810705640442e00c0d003001b60401d0740c10b03154241d903450507000340c6005940c0c071400b1880907039401040d101200c40900c04040c1c100d005107811052500007102c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 418081861 1250 418080611 418080631
    0x5011e05071a101d09060402090c0d050a06031a04150b0d05100c0f4116020102070509010b0d0c12020a0207300303020307180303030504020321041724 66
    0x74400c01146070804d80798024005034005000710740302c0360200a006480944058421300003000660101d01d100d000300d501c42c14503035500080080c51030518405510004464816030100da80411001964644440175802102040003405502c84008a2402c100101015019100d008003104940c030b03058000c107d080c012603581e8031040c48400b901f55144288483c80c1001c0440603400800343c5000003040030781c61359000e6100020303020140d1801005501c042034422000d0900304054082d56010000d250041400342d42c0c0030315a62610810038118024078681c9012251500c1011074680d00c25000100d2549021030215960000400b02035a24005417040e4038480035048024003002e003502002400c2c2441e007428001496400e560224000e600041180050040b4001d0704603454483e4041c2c0030103144070f0b031000103082c1043d004051614050040207600d00e46140c3d44d481c180b811850544040b603510282c100740940c0601c0115042840c0801001017800d04050f5007000341c0340328107000b800303104219 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 418083111 1250 418081861 418081889
    0x2040b0603270f031b2407110d0c080c0c06030c07150c020c012a0b091c0207050f0103060b030f0708011202012a0209090d0905011e05071a10 62
    0x10522074480c100d10400c01c05940090003594500b02000740c0802e0045c294505851400045401c1010f2502e22100c403071012214900410500da03400c440c00407500e1040a00401d0703440d01c8514014165040e549004103034080110b150055080104804994404010301107038403482c006081d100740c3d400c01c540940b00300c50751003810421080c0354425403005501e15030150404458580065801c0001c0d4440c0d6031000c1d08015551081c1c04075800d170301e219240316859040b0f050504401140c686801014000c0d48070000c240301400319900041c48074102c49003036030040010400303140160014112a071201c140b10303600204100c0700f01d90071a50544214415102c9035520b90b2601c001c0c0200214600c0021b002c1480040b400c0806640c01c940d0030400d2080b01c482c4100350201b80d011441c0c20300c3c19101d40750940d0141040f0314180713030840661000f4000a192440709000800703a8451005401c41c480f00134400c3c0080c01000b40041406904501c01280c4500d203818100407090700c0905c0f0061090240b181c07240303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 418084361 1250 418083111 418083181
    0x70c061d06071101050306060705010c030f0507020f070302040e0f030304050a03020f1b060d0e0f060a0b0f01090e060607050a11130501082d100b28060c02040b0603 72
    0x11802d54000a0700003083c48240706600f001903540703900103881140c1c461340074880c1c100060000d0107000c4007041c1c01d5501080580e0042d15010643e4000303803c010554101c07000998000c03800150710b5046940498001c91a2000008500d043c58080701d8285218007000003080148140011280d0b0a107209500310703080300c2c49440200f502c0f190b0b42d010204c500d03412481800700c6454181c010746010300303a1440c0001c4101101201d00d04d4503400415044968000104000300240301d440341150000064030b40c039009459200000304140b855020304000f091550000c0b50381c41d04d0318001e450307401d40d101d41160f01d070100c107040907100440c0c07100502c3c0c0303d01c034034403a040d015298502074207049410030001070070814a10b041291540e1a04244110046403141d42e014100c80c007045040e0040150b42030000e9203611410a003c1d2805002004d00c000241e4a1608608600781451280866105183c00c13070002c10544000340180000c1d604d143d5010f1000f0040c482e1080100309021141d19510310f1140e111034035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 418085611 1250 418084361 418084369
    0x6030302160e09030301290a0c150506060f070f0c0f0905070c0807020d020432010509060306060108091c050c010f0908040501120e12090312092202070c061d 69
    0x4a9056400c0c0c4c00901c010040c0c800340d4a41504800c01d0010b10f000d00748200c0744128410741150141e0310014019070b0900c0244400c812072200c0c45440d40a0a1100d45451070108184c1e215101d040c103806400002d2080c144003020001d00c560542c86030362202810707560b80c40f0350101c0d0f6190098a15052404c03000c0384030a40202203040386030b54014802400c15150382c00b04103060300d544405980080c1c9440d121801d9071010b10b104140c000240c04100851140403c0f03190680805800040c000d03240701c4d06004059030b00207101035006400b460481e01e140d4446020b503045c154145611740c0c08500302c060a00c24035401c04068081348207a5002040341d0800724040c24261000000b0290060400304030a03c815407050485100300e04c0000f0307011a0100b0800640c615185035041d210101140216000300645400d0241094100721101d002d41803414080c00100b241c54224803109070a440d0502034a203190303060701aa41f401d50800310048050b540d60201810803108418103a4255900d021900b0040c40c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 418086861 1250 418085611 418085639
    0x10507020604031e120e0c090406020409060821030c0f0a020303041a0615160c031a100b030a020711092502030a081603110c0c090105150313080903010603030216 71
    0x100d21303500c686034017020b01c4402d0300030044104621141d02986900984584401c0b90950183d4820500141e50340d1038055003004171000c6400c50105a0442c44103000c1c05148144480001600c0503680e941c3c80d01e940741c81644520801a070052151380c045110000310760080003452040780030300107040718103001071410314241d4000c480b00742d405010350341d4140101c51060007401001e00e00d00108461250140c03a0505082041e0344212040311503501d06100030880e082031160480c01e070807050740a81d810440070b030040d40402005e080c21950702041c11014408007e40c64980c03000050007094050800f66090a00402400500800e400c00700181100c02440001203400d1020036a40d52400c50303d9944110044c0c070186a0144105625030140c4481501210000d11030044224000c1c102400140140f00d08054140d000c07510800105d801a1120500d100840e82c1c4400c0301003040126289074900708400d0f0191145268256191107404410181c0014804940b0003540440c05011680c40d60310050602d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 418088111 1250 418086861 418086917
    0x10506030112030305091905061008010c05070b090a06050c0a0e010806060d05090f030c03031b040302010903082812050a0614010c030201020706141909080307050c070801050702060403 81
    0x70102e071004002c01d12940c4050b41060b801016220610b07401406118681c141d044240e0b22908100c0c02d011104010340d1012009201443c0280000c40d91104064002e00410a010303003102d4441000030010300d41803004448950340301c2c40400003030030100d54190154014003101004140e1101652a056029522051144100a194034034040c210b40440300078040207450b28140e4814143d2100d0b40d2241400585021012600119100e161041e500005020341e04401402500200028400741c3d900c040c4040607a5004007940d44d9900f541002211520440c000301c540c211414404100c44650020080b9000441488140700c1520f8561400085410600c0b0324401c65108080c40380040d4002d0079015161030280c00010305004042e26900165011020161095450a0104502001003280c040d1001040800401c0001c0d001e030b0f94a0082e2002a01d03d1041c4000440c02c10520318041003000e028000180091180c0e08101c0c03800b9554902c10b13581140400d402c0c1182c40e201c0c401800b4401141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 418089361 1250 418088111 418088129
    0x2040e0109020f1e1807020712020a06030e1015050a1a070f02010210141e0405060c13080f031e03040c0608061c0f05011d0705040c02010b030a06140105060301 70
    0x1000300000304440d000d04c03118545151881140c407241143d845109070300030024031800341525407410010080c14410f49400c441c0e0354500e0241d031032000d600d0310140c002c151400d500740001c040044003900b038a010609004101c0503410801d42d030b10500b5140c1000811160b00b9201c0c00f801913200d000700c00040c00d208000c4245640d003800b4181c04103520b503403140e28244c01030050f541d84c04114054030342640c4003080c100260800342014068001051541c4001f0301007010000700700d604041c1e546a8a5207009895200000b501207990f202007810248004010961102183c0089012100c465143d40203801010401001103405007184071070346003140e204950028210941c1400d184e01610003200203441103401120681880210051001c02c42158a001c0c04d2000040e000c41e00d002829910800360703280c1c400035000c010f0b10082c280020710b0300980b20100c0c2c01061b103505a150807401070183d0b1440a9151054801e40c4060068980c403a1040d00c40e00c0343c20079810380c1c807241440840e20080c4210342c0c003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 418090611 1250 418089361 418089379
    0x50601021b1905090903030f0f091b0310091a010f0602101515020124053115080c010e01050403080702030a02060d15140303070308041109010b0702040e010902 70
    0x8074903026460302c000861054030140030a8907a0f020039510300c001c0b034002240c2c1e4400003d001007000710540299107c494820410380500e0480c0945444555030102c58442400e18250b81000b0358041c0320020810141c0c0c03400f040300c03058600300003c8460480800c0aa1b1070407040000c03419482c40159032003601d0300e640050140c00d0301040d4030002402c014901c03010303a100d046008683d4598000e420801051594008500c4c40c0304d680c90b6006480000c1d240b1144c510000004000c03e071604c003001c2550300704c07100848804920142942602c603c000d07500c00409890514200c001000f255528810b071044201201c060a07660b50040d108611496041404554184810030009010b40001c0444030b102030240c0344000c00c0c9501094280d00300c44050394500d9224001000450f03921303000d0341d0007000d100340900354039104540825120b103d0402d024041280480009040c030201c00725270115014050f20f0b80d001036035240b9544c20075401c04d003000c0b84170318144405422420310502a04501c030742c00410082d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 418091861 1250 418090611 418090663
    0x9080708031210030f0819030b0306070c0f05060405162c0403020a150b040e010b0a060e01180e040b01060810060f0e0303040b0702030115140402090f060a0201090605060102 76
    0x200b4150020415201070301041d10220004d00079000e0200500c0c49007000b00d89a0081c2130182214000400340d40007090314100310040304d60740c006211500420142801c0340c50802900f02060440e03d40b940c0640b26208443c140410060005901031000180b08030058550303032250320f00e80d0380d07403518a1441c400d09011b80280340e84044903168140c00900c03034011219006101c1ea00c4120b820006800901c50a0350341c0e0780c0804c1401c0a0049004c4048004002c010001d01c05001400529031401200c0401100f8901c0e0020b80c0d000351b07540b1404c042584090600390f40d5414103d061182c0440f0704442136820301c0c00000d1030902400340140102030540b8401c46460424000701c6072603906170140020080c046602a044d07841c03e1004101400b180101c560369540031780141800e40e01500000152101035140811080450502028000808990240e40d40d010007000402c071844070400142c0c089070000e00040441d805510001009220301d0b82401a0b560f04001a40c07601c03030200041d0b0303000f00100c201c94 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 418093111 1250 418091861 418091887
    0x141303020f0d021e0f1c060b0a1a0403060b0103020406080712020d11041401051e0c1501080a0219060f050f040801180501061e030b130519030908070803 67
    0x2801d044041c00c0d442c102402500050140481010690428080e01800035210300703000e203044140c5207059420103944d80d003004081841e58610040503080c0b540c3c403c4803039a156140384100d80149140b802c07242c1c100701c80303110740c0c80b0075882844111100d915202c04403020354000d00984085484e1903c030b141080d62020010b1380c04d40074990301b90100580c20099a030807400240305a074030441441081c50b85403801c0c5040c500b1501c071000f5905041c4502848070401855008400c0340e00150703440d04e080c2d2220308408119182c0764408810441c1d0001c080f0001c24403540000e0301e100024021104141031000c14030308108454140d0160b10002810700800c1c50060340208003c00c0c080240c4000b02c1e00e09903480140b5030171a440d001408002000b4004154240042401090701900602d03c00141d80c0782c1000c0c20414104461100906450b01080040c00309440d812205441a03008001ea4094100300e109109408050700001c90115180c180c0114a1290010700c0301c0c00e40342c5480c021403510880e04010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 418094361 1250 418093111 418093129
    0x5060307140408070608010b0f0a050a0c0b0106030504110a18090c0f060203070b01080714041d060a020918060603060103200a180501051318060f080c0114130302 71
    0x240c030910000303041d8141c580d000c410040c0000c00860028164807820810001e00c12001a44072180548080c0102516040490704644501ca01410300b140c0c1d0706224a8140c55454107108060410a486400043e42c41c1e09030300180e200320301c076030305404d29114041e0400c22030700b2803030091451f02c184d18450502e607107105a000001503402405030045050391500e40000d40000c9402c500300680004c9407207010800000d40d113601600600c1e01134040e441c201090040202e071540c5406200e5500d03948150020041030080164031a1200203848051501c201b4a002940c8448140c41c05142e01a2020440c066a1144140102030007043c00c0e140d9100c1030300440c068420f4010400d050740484480502c544000c000420040301c094079034914407841440814dc840d100759003d28148081005800308900c007075450300702901c00d1408034071060098075082400420303541e0130404189450004c04507003014001011002d10000b40e0b0b50031250400c0c40c801c0c080d9806402c0c3c4030445640c090a090006180040c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 418095611 1250 418094361 418094371
    0x903040e011e1e1a0a0f0504272c0f281109040605040302152211060a09080c030a02130e100507080405151003080912010e10060905010f050603 63
    0x9200c0c221a21350380b4219001807016210a10b0060029010b050650841100c6410303503a241059400c0a04e4003001d40c6d02040da080e82210b80200c00201c0e40c0e26200554032080800900c18440c00490f000c600303028013040411070a0780d90502c41c40d940138040d441c0010b240c14407080314407200c0311200344000c0f40e002c1042880501725403040903c0746981654441f420503034882c600600d40170885c1c1c00d290070081d04090300f444e01d2014419607107042044880500c880300c44040d00c00c201900d199911760925054107400550440d902007000a1510b0302c27a0b50140e50300080e50100000d54041480d101d00b019a00e0140340b0000350000c041c4152140d41402c06c0d030000341c5107128030094501da241034030650000c0b50021641c0300b0105458606100900408002c001d42d03001101495080301d0903daa80100c5400c03c03480020614440040c160f012522003000800320050500700a01c4035140c0c1119458940100710400d8940516010740016141e00500030181298102041a14514240002e04c5116400205 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 418096861 1250 418095611 418095659
    0x16020c04050417071a09010603200406150e12060108071a07060204060c11030a0321200406020d0e06121e0115030c030e03190c05060903040e011e 64
    0x2e000f40d425076a00018130342d2512410080c039a240302049903110314071010b008a00300ba8986401840000d0035076032490350400c07100e07404d20030850306c4c040080d02420a0b600210b00c1210050161098280c0103070b90490402130444110b09607149050482c3e654980c00d00c074546040d444a04100980035070003031f8810042d0740600c901443d00200d621101309a031301a60000b00020f05080240050010b040c0c2580503c4808a02030b12004503151402003035182d5036000c921302403800c1c14842c52000101c5c1e20824207070307100d006e0000200c4d9400f44800d00c5da4100e4800c2c40c0241c002c0c41d9009081030720400e400c01a03031100a202d0380c03c003801a004d20040d903c0040030880d58154400050759480c4518900c039000b01804000c403014000ea4030030050903500d8000707488040c14144400b0300a07034039001c41611a50100c0401c0c40110705918002141c800c10a040082c0090085109002213108040014030942d80c0c54504001d0036642d0304c1c004031504810b804103c013495409201401041503409008011240c0c9038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 418098111 1250 418096861 418096883
    0x70b0f04140105070509150304020a142101022a0a030c08040509091e0106050919090b0a05060109050a03030c03270b12010504060b0a0f140406031416020c040504 71
    0x100d0700341c2152003d032100008110042146000b038a000c043d84075100c40f031490070500750304090b030115228180600540b208a583c410418400d51592401400201401d0080640e203440c500d0400e0300039032000818500f102820302104018400c20a01010a81c100c0710080c5442d00366a00e0442e821310a5003021200e81c1d10800000403c1e503900c44590303009042a00c017602041001c0b40040020703494000c4011000d9040880400a80d40d03a9810306070300443e503030014168000f0038041c160040400c40030041003070915600780005400c81c0e601c80d034807491007a03e0b00002c440d282c1c03040200c05802d030302c0010001038003141c5420000e071095480608146022411b122400c0ea44c0c2d0701c3c41d4a404042e08500801c210101f404030811400c580d0050040609407030810410381411030170051032045480c440d0502c402c0044100c11540b107660101d8025014a80a83d00c594858034001c000c0d1206125454020548002040003013485080e10302d40c1649a80041020740110303000e00c80030740070081065800203085 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 418099361 1250 418098111 418098143
    0xe1b0301030609020a03020a0618090506011d0d08030c030103050601050108040f1211030309011e2007240b010818061308130603021207020115030303240306020903010e03070b0f04 79
    0x791500901900507500ca5845443c4401303c0d240307000c00c1c032f5440340d201c1c0c60403d820f00c003180c1d0704880c10380500c032400c00c081c4810481003004107803c0301025000410242000040000312900c0300c0203107040c1d81c8188140e0b207659a83d08011900c280f0f050340c029280300030380320701c400c00600500580c0044011301c0c141400c18800c0382c42c1440c1540c004985041c26a5100e048405150301c10600040400003010303410010a0301003107054a413207400794100b904a0000080c041d080c041e50403080429000865a00100d448a203922000038204450825001c21594000f04100004800d40401c2c16560300b8020081940c0740c60540c92986820441940c00c0c14040001e00202e4443d5074007000941681c2c4c50140c3d45090030300200050b100c00a2000d001c40e4500f61090104a504807003020440b80c0614000c141080d802c0920780c904812010710203200c0a220400004002280c4c014180310340045008110b03200e40400c2d02a01c0744034500c40203003c11003800c00070b821503428000890b0001d010300e010004855031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 418100611 1250 418099361 418099369
    0x6090f03020105090c0406150305070203040e070e0108130b0c03060a05040207060e1212150a21030e060f030f070e060c0c090c1218250e1b0301030609020a0302 70
    0x88010640060b5103d00802c00000b00400c8080c0d80c40300140e508201c01850042c6c4004645d9001114400b05600d6902044c81c080c400c000b81c030094110400e1151403802c1a403809000440400d0341c440c0842c00e8600045c6c000c041164020005980150000c1c40f5a41d8049a0001d5644006d04450780301da02c101010510f5110ba1000d04100b600c40d540000d0340002a0452a103084005858201540400c00c0b481c0701000110800e41d420680c0742d22108030701c11541001032004002354016904c111040f001d0407a44a400421140c00b01380603403900c240d2100d211050017181d100b00c09151710b10610820100c0d06107460109155440107013850f000c01461081000141c15500108403403403030b9032010360070222920302254815044810b86030740714a851200c0001400d411002002c420007500d8405810085072024455055094542528407802c418803544070072071220513000d07aa44507565880010b0307201881e4020103132040f004d0401c95045030b00c0c3d60b407640040c040da444200d03000301c022480000183ca07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 418101861 1250 418100611 418100633
    0x201030f0f090606051c12030207020f060a020a06050907140108060d0c0e01030308161e090e0903040801050c0c071809170a030b04060302010e060a0915090f0608160503040609 77
    0x4800c94002c0344c110302e46010800810818082c03070b80c4001341d000d42000000e002040c410060b003100d04001d0b803035000e280009400c0700350b07026800b42c20000008584c905640d02040b08850984100c03800c200b2034a40180c0c00d645c880c001c3c0291108044054040c060a45c00303480d2195003c3c00050000347c0020f91588e580d07015080a038003100c2c004000d24018420145c00c00801e070f0303002c00c0d03034100510f400007841c0d0003c00b2a07503440e06402500700099641e851003446041000050001000f0700541400c00f002c1440da42e90052080b80c01c154a0300b804100d808010108071174101c642040149000707420312400504604841c4410301e0701650359060ba40c00903031200342c0e500100d603a488420f5140c1c1c1618ac0c01809659410300307258415890540d0903c010713a0440b034503000b4000140c510940310424a00159010205030304015005071103c00c0150040368030420910070b0701d2004c3c0300d81090603550b1400380e4001c601a20740c89640040401c4200b080d42c4a0006182d00a001d44000305d02c150458540c8440c141c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 418103111 1250 418101861 418101863
    0x1060906120c080a0305160f0212030a02120408060103170d0c26100905070e0307090e120f032214100623090901020c0d050c0d050f070201030f0f09 65
    0x8011110404140490b035030190004003c1000680a03188555500414601c2881446152141d0054142051207041e000c018000e65024001e1559900000c01640c0c0d03d8000000000052003030000404c0040e42490a40d41103980c94001400c00741d081d40d507000c4114000e1151050100002e110703506546081e8024408222011b0b03e403401c0b10002203500714072582c90b81034240c0b460312015041c13052820458175188111503000100144903100c100049514041d400a80e0341e1510840b1800f103800019a0300141c04052120b040b40c400384c0480c42d118406020780841251004400d00000306900c1a200f030315010301d11024055a030f01c20b01551391b0b2100440143c0038000a5202890701d9128045510518001e0148500344243c42000703800d02040d039601554520f8001c0d1480008180c1d001c0c1c003501a66210500715003552403000481c03100418680008407021628440c1c2c200c200304090148040703591402444a809240443c240c0064015080c2040d22154080d920b8400741e58503500303403041b41c140fa = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 418104361 1250 418103111 418103129
    0x90603250306080d03050411010e0a260106050910090903020c060a050a140408030a1b020402030403020a05010b0a0e15010903050105010609030201110f0c150f0f0307120506101101060906 82
    0x52030070261490b02d800c540300000024141b4090a00c80494181d241e80d81180c18246000c4544c64442c0000c5031b80d07444268461040032a85d103e0500381e0b00646a0082105503120000300700095440702040903c0a058614035410044202c0034008180306800200c0320b14041e004407030840400501003040c580c06180c0080000e00d0204003a03a90541c0103408522140f403003080541490b051162403500c038030030000d103c014400c00c420b40564840d0846460341c03000b90000d02c1191a0300c1c140c14043e4030b80c0c5c0003500489030340d460314440100615006c2804015141e13140c2044080d55606110ba10045110501c044d060150f10350001000074402d0140c04c0c040d086950b00c0d1501c00340b6501c0050480d4095001d00c080c01c1d0030107101c00203e410001007031128010101c45c014008102d40c64440c01c188a40c48000410b000300080c0900c910707881c2c10042d03000e20340383c2c2da5040100c01841c0040c0304540060b00c1c00c96104590440001006206211500d0a980d084000103180740c0e030b0b18084011188141c0c482010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 418105611 1250 418104361 418104371
    0xd090608180d0e01030b10020105010e1312030e0f0f1b0604030b070807050f22051e01032c100c020303090309150706050a061404020c030906032503 65
    0x641580010100c1d004104601080304803081103110380e4403010350b403100030704000c2401c0d040c000c07070781c8281c00185144074007800010202000d20780c0240a48002d000b8281104030140100705000c0c41d6600041101c2e41100d01c8200316003201d0350460242008061800d0b036072003010400f041d004014081001c070094484010008400d4429200032811b20a40c101c5100d00814042000401d0207400d40b203601503114071f00701995135180603041d62240a80e6488040011011403104034034440210642580a1208480d9110303075580c6082200009070150403800009140c0c80f150303c10750003600882d25468610742e1640012501041407065201e40c030503048040e0b4050380c2501c105203c54414841c203100c40f440174524501d0450442540d91152070710150080e00405040307000800c1d0f2005507020142c1c026010b20182c02c060b8014000f424250288410320304c8002014003941c40d280c400c9036808256900610f0400c1d001c5410400e4542000340403020100f6001005841c681e00c080c89412815442e440010f1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 418106861 1250 418105611 418105619
    0x63108030f010504050112020603060d08040b03010806190e1f0e2d0c18090a170a0e0406210f021507030f0e090109021305061317010b1c05010204080d09 67
    0x43d602c5c103070300052051b001070a1076400343e103034102280d5001c0d0b810703142966903185615000009101d5507100310300344080440041440f500200e0341034080c001081c400307000302030b03400414004c44001c003035000001d611110880038903900341241054403442052000900180300e610450410f6588480c20032000d0305030407404152990030b0f00c0da20450054600400c0180048400304060003030409542044107882000502c01c580308203c0c3d20344c1c842e440381d0b566003030603c420700c800c085030010322420700400e6443c4003070501070400e4070402d800caa581c03d4101255880d600d034aa108801d03140700c181d4010209241600150300c848011b049016450b00482e59108151304008001c0d420103100d0604100045036518019a900c248880c15900d94000050b40c90320b00d07405508280c00c0320b81c01a50000c81c00701d0b20070030a40080b00400100c82034035a45114202c0d40e0304140342240c09007041107611501c0090a8242c0750101d42c0412440f80c4600f000524240c0c848510514000031020b03888001180d03c0c400740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 418108111 1250 418106861 418106869
    0x10924080708061b092103040603051e100611070e33101101020712120f0203060a0b1e270103020a02120a0e09040b09070503063108030f0105 62
    0x1951104500c1290300c0c0d05001c0590030301075403041d0320849104081b41114511410345444c03042c49089003007000c8941d075a945071009805000100c40c06000f8100c05074445240c0754103822000e10462503031020702c00c5030f424824162140519244c1d0070350180b1440c800801c12408004032035028041454154449112690002d511035008449545404280001d01e0140f52a800c09030300b00d0400c10308007007000000d0f03c1c80079030080c0036001d400345c007015112511801d800c0c1c012030740d4503075a204640180001200c2c030f400c1d00240e200c00d441064012041d030781e0400c00541e140780a0708074681c48062403110071008025043c2035070010070401a46034107541501054030460f03c3c010140c100700382415070400725400406500c8044421f914220fa00b030000e0071904541c442d103d45000750f440240100902c1c20030781808404024100d840416602c10f1f090f01040a01d80050070701d00c29001864001c824244a0b400d41d4240d03d0461040b11008a0660880e0006407a400c040d6104d0182c00d0505001507240c24100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 418109361 1250 418108111 418108123
    0x1080702071712073905090a1b03050a0e010608150903210603011803020c090408090a08010902270408072103020d0507090b0702090907030f030c050606090f010924080708 75
    0x10300d601c5c0c050300e11260190f881e20460004070345088174140010707130712120014083c00d018161704a841c0c064030b101403e42c41d010340c00540101d8580c1d01c1004810100303000b8a0032140303e0b009250301940241d1042c83d010084200342a40302040c0401c2c1d9081c41d000002c190a40340b2039410031082918003204200d00d9003800d2046025140541ca5480c44031005030b28040d444600192003c0c0c013802c0c0150014040c44400d500320b43c440e51014015050aa659110150081103075403000c9201e0660120000343c40e00f0717950b40079071765600c40f014035020548803a40c4100c000d600507903040326001341101c28040c0034180258901c44180d802e4501507031b900c00c8102c441342120402482c0c1401d2204d022000c1c002003003410240c40c03100b64180c1c0d41c1600c1d80c8409500920341492507200400e0f40c681d00070188101a4441000001d10707101d00211000c41d1240810001c0f13500044035a075038020510b9004000040f09a00104044260440c0d202240d40c40807880904118054022403a0369106580421801a08003c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 418110611 1250 418109361 418109423
    0x4032307150f1e08041b060c06050109050103030e060a0c20040f140106050903100c110607050301030f020d0303090203060f1909020a030b0417040906140108070207171207 75
    0x1c03401c149469415081c4016143c103000308503d4000003410081c41400c1c42510096280e8001103055a40d0300007040c0c07091160084904a00709400000c46450f00d002e4103068076455200e04002041e800c05011071a004100101c04212040c44008007042c0c201035010045581c0c1030041040f200d6010038807050b03440b92405115020310300905040c903a40c848040c0c48c1581c4071403500954501c40348001a18051100c010303a042c0c0d44c0742c00c10610810303802034080455200281c0c01d490080d034074003c0550f400e01091002521260540703502000501d0098a802c10080c4642030000c0c81403020340101740340c10310407240b0b08184400d40e428000d80b1601d01c102c6014140ea80601070062450603400716540c100310344801000d4050607000b2508201c200150040c0c14003a0b8549280c945d561482070001911103032148050b43d000d07082c44038030b065105054880c40f03141946c004000d114501400600200080301e500c01c268003461310b010340e200b590b100051280d94004c0d0500d041c031441d0385668002c9e08580c005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 418111861 1250 418110611 418110617
    0x80109031412191410030201020c10020c09060409050d17060a05130c02071208180f0d020d03030e0115050a061b1103100e0105041104020c0304032307150f 68
    0x40302c10074511502e103582c040498101c03e060744201100e41800341c000b000c070480000c03201404000560010030885402c80303001340d00720340c8611112024840035102d03408202c2c0058004100c241c1850919403003c0d034019001400014030486c5036110780b130401c040500254001032811b801080f00072504044030703400140c00c50b0a245c6c2180380c800001c82540b050304100520726110350b0204402c4d03000348550801000c50801004081e551803400403280d501c00e055182c00e8000c0c00300983c009041c141340280714000050070100301e80c08660200000003401d05c0b01102010b4480804030b000a4080c001c42c01e46c0210038140558003824401000f90000303264205101b080500c48034146455010340310044a01d8100c0005101074507400007203820a030b107440d5003010b12070518022103a00001507011620890140c1c078a001301c403003010200003e81c442e07641c0c0f440e03c590051005001041d0360068004805c0c12149502c1180381c404880c10741002c4007a8030449140c19001410038142d60444040c43c84124546 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 418113111 1250 418111861 418111867
    0x7050d1104081b0a0806090a0c090b0f043611030d050702010522032307050f13150306050906150105160305160b1803040e010306020901180801090314 66
    0x10b041c155280c1c1201045207400051841101c00f50302c0c1c3c0205080070b85500400d54003180790005104d65512030322601155a8181c5000000750751400e842910b40321000140030103206000001048098456502c00c035480c0e8407600100c140050111028881c032985900d80c0700401c42d030030300f043c2c80c1b144900c1e14424025080740d860f02074501d0b44141283c02e52942420802c2d02d41d421412050520880030038540c81c81c14054401009004c140c6d26264080e0346c1128164140c0c2040c03c402d01c0d201c05d203a01c201d58200d910381d4980040b078942001920286500c1003000100c8080c08480260889d04651098510b941c0d40d0082c8500d80c1c0c014440305070700004201c140180c101a20300000c05500c01c030030b821441d9036118941d10003010b10541c1101c2850a01c54115521009103050401e450001503480d80d90385400081030202c0c101c008004c0d50304075058031800e1007a5070719546801c00650b100700003c078100154001085012012281318101607e2745d1400020201c01510b80a44024000800d070760b81c5907028 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 418114361 1250 418113111 418113119
    0x1403120f090405190501180b041a04020d141815040f0809040204081b120a0c03200a120c0b1206012d0c0b0708040506070c0507030b07050d1104 63
    0x3400489501d1281034a000070305940d0030701061804907a40c580780070158200700001804d501c0388261040354540d1440200b1440303400c0420031040b200c540f1107881c48103220791201c41e0140b406501811039555070607000319480290170008100424100c4550201211a151002030b0341e208000c805420300b8446007000c2d05090548501000c5044c0c414001c1c030580d0300040d009019152501036600901c003660032514400194109170750b094a1344850745004688150b4000c54a010000b207050102c1d410800c115801d41c11a113504c001607901c501d101c08902003100c1841c0161300e515584400510313100041076902142490b1443c5620403542c04013044140074001f02c00f180c07160751101a006038007400c1840315042d0004901c80b0301c2c03108640c0326080c0b442102c035021105400000c0c5142040c0b06100c1018951f50b450420703160b040341501d0141c040d42c025800200418000c54048800c14000d82c100c44405030b5030b556110b0200801c4072500d000440108465041e10940e0103074020a8840c0c1200d242000e040c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 418115611 1250 418114361 418114387
    0x806070503010f210c1d0604110d020c010902060f0a020111041508090709021603110a050601030f03120f0605091008061512030307051c090c0b0d0f06140312 69
    0x5030040580c451410840d040c001031513003540915042d03100d02d1408070940e495080309070080000811044803680040028080e183c94401d0580d601002c0740d100d8180707040c100000303009412100710380055640e603000c1c07000540e844134090150030001090035a50352021800003429a080c06002d0f5803200b0003400b0502a0110005800300d81e0000c03032401203001d650b0005014131304000c0798055a5180c2c40040c0e0404084e6813405c10b40180c40c0a0b03102c01c0740400589188550301c2104060103480303900948014030002c1c203040300100e40c2c00c5c06403511040c0800c05400040841d13403a01400c1589030f50f5032508020750300b031076161242d11a40d050074000b051443c0009807515520010850500e50b1880c0707420b042e01e60368801c51101c0e09041c09003100e8491a00000c0074241d50700082c01d52041d00410034200d02142441d016280546a00036070a2103440d10f0202620855040618500611601c2e54040c103d041111700c07490005000d500c0c101104550030105160522285090052912800700040a80449 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 418116861 1250 418115611 418115639
    0x9030f0f0721080705030d05010303051809010b040b092704021503062b080d091a0405070308070201110102030709212001051b1b09060d14010609090309080607050301 73
    0x50003100484da68040303883c3c46800c0d0706c0f40d0345211400615040012007810360103070242c146080d807a10380d040a64008010030211a00911414205032000c00c024402540200b0103041c0414020f084200b200203003c074140f1404000810710802c05818008000a519107009844104000c0b208524a03501b03000020030080a038004103040740c904d0903a202c040f031265240c244101c440c1c1242c60715440390404000800130780844d07801551140d04408000c071540d040d041a0034022030380300d0000d00415256a43d48007864000c010181e050250142d50100364142c217000842c450210360355440419410030710307402a20b00c4008445618a03148800b2030001071800f070701041d010785526003640685aa000012103d512072050b444485041000102910343c0b00086d280213644140c986281d0f4540c1c03074405100300e140040b0742666010302c0000d13500780171411440c07a800040e0501703000800e5660b11101d40000340ca100c48000c40c00070b40c030000b040180381005d10045401141ca450190f1955260500c580d220f91 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 418118111 1250 418116861 418116863
    0xd020a0e0916050612060a12050105190c091a1b0313060201020f2a0a1401060803070f0204050403031103010b0904140601080c1308070605030103060f0908030a09050309030f0f0721 79
    0x50043c0002c00d219079140087d801c01488403400c05008060149011380c042d0000b40c8407103100121100359100240081c1c0070340392024100384c0c0c903205034500e040c11403203201442500540319203108122440034092010000158040018019540d60031200c1c01110300c809142e02220440e48140080c4000442d101e0860312203000c05008040703610042511008007400510300c54080d03101c7c064000d001c201c044a0b00341070031090007008000142da42d4040c144c80b8030806400400c07141c950a2200c0040c50701e580016001030007860001007840003c00c040b4540e0f48280c000c03004072040418050850b161034003802141030088214404103080010011f03085a0020f4007410740c408010035810301c0c102e020281d020060040318203d031411551401c000e02260b00030700080d1211802c0003010030881c0000d0144102d610341c044c14240c9183d84086809005244650301214680010000e032000340c2c2d0100889040324424801400c1c0050107001000d01d4002e842c2d00c01e1100303030010369507000c03035150305a049120380e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 418119361 1250 418118111 418118137
    0x1a1e010815010516060b01140a0f1119110f0604030203030d0203090a0803040b1005041e0b010306090e03090a0e070203030402090c040503011805010606030e100b0d020a0e09160506 79
    0x811100d40050b1414090301a0590b07040715440e06600c144017098010425001e02070701c600542000140b0781145a200302c4400c0d80100f0f46d1070004c40c3d401c0c1d00c41c10707103902d101c00c4170740070740345d50080180042c2c01c650740254080c0d440100d5074224440c186041c0840d17918035502140c80c1b5107031602c0c59010070b8503405815001c82081e075004c40098115402401529445a400340503e6520700d8517140501c030800e03003a5240e0840401c1d03502d010440341490300c5541d44010f10042480704c4c1001640c080c00141284441250415460f44000590f258081c007070000d03841c2c4c03810040c58640c0006000d001b0030844c5a440780080c0102101442461034000c411a5041601541c480805685801c41800c1501c65548020380641c44c1807150f407004000c44074004503140c030410007400111360300ea00c11000c0e0341e004c2c40e0307207442604561403140c080c0d00d4039400032242550243c0300c0101084590001807030304c205684452a0415403404001e24100184841841c0005003200d1903540c6080c000403802e940201e030203403115 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 418120611 1250 418119361 418119391
    0x1002070512072d050402090618150c0f0d02011e1a0909010c020c0306060a0605030603120424090614090f030d05070302010b0a05091603020d1a1e0108 66
    0x6000c01c240055006045290010b1480d02c58290034014202d03680c03021403041d03201c0c82e440454a86018022a003c84000400c42414140050382c0a0362103070451102c998450410115a0958030440c07001d85150000000038080c1e58150308800c0342004400d00c40c581c01c41e45440416004d59940300b01c0701892080d80000042d02d542da5480703d01195240a01c4181d11022386000c00035141015005110301484603800d030781004180c0410305586410030f0324120f0f8400d0a075001400521b2042d0081c50780840e0090403200403044910390101213a0081d04a80c507004c26101c4548031401c0701c603094021072680d07032130003100d8a03141400040030020310218940d110030000682c4489030b5604000c0303801c10300005090310300314008000c024007140e2103500205c0c055420034503844c61916100305c264084403c040d0088070b680c0e07034485101e402c3d105000d141100381642440881c011803014030400d800e4610b00351f45a500c00c1f0f00c0d841003084180d045d400d46025014030303865803c5d00d039030f00c100c51036004203000000c245 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 418121861 1250 418120611 418120639
    0x2160f0e07030f420b0f0903030409050628050607021302072612010e0a0b04050708010914040206030105040c02070807080607090b0c10110d0f050604050708010b070305070f0b0f070e10020705 84
    0x1b029104d2007050550610000c1804114240d141d4070190080b0011540b0703d0b80c809003d4854500d82c641c1d405400d40140b081401002241800e0004017101c1e88010043c0f1150789100c45200200e07080004152a2443c1d820440c1c2d840100c2007080b0141e595000c2100c50800e2500914945100c80c140642032285200c10f0200c0c10290701600b1507181204020002e0002e0301d0040c0004003e00070900c41c0c40300d214100803500400384a000a81401141c0162105266030308001c248005410f000940700c04501c11908009007100c0113002c0103000e80140005001903045c038043c01080c01d16150081d40c52640b0030001c032200c0710000510801805100310000c44c50524804040300613000d001d41c40001c440c149400c1e2951425268011031041c04212802c2100d07480310b06003141c13040c80c240070780002e41c441048000701003030180010304140c0388198080c541c81c3d105561054001041642d140c0c82007040d0b02c013400308454000c040d03e41740c02815501d07007140c0c2c030355244025914491442114041e03c9005620f407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 418123111 1250 418121861 418121887
    0xb01050f01050c100b0103050a021303060c05070f0c0303080f16273002090f0406110a020a03020609010c090b033402160f0e07030f420b 60
    0x2a02d9980b80f141500c40c1a926021900090600021420700013894500082c8c0998172a209903280c0c264011900b0382d0183c00c44ea240001013085074040000d11000f0301180f00002e03030700040342300c06a20461812090600d0351074007074680d181c09882e00f580b1005080800c40c0d518080619060801ca040c640440d140190000c11004400c80a64400680350b08040c0403c1458082202c00c0d501c1c5120042c020295004140070004000102c6c0000e5005803541c5c042401d0825550003107030418015500080c1c03c0c92401d4910b140d903403021000c600940c002910a0083c10380500590350310402c1c0400038001c45c0c0031035100500304d068a0080c0c000f81c00011002c500c902c078503900b81800304000904a45101d0207451200c5a90000c4580113100610454191840d202c0d4041e100707408840380c0300da0800c51766051154800c10140020680d0003059543d00701c8660b5a0000e008881e50040303c2c00244402d040c440018180e0601e428200c0c0c00000b40f0800d0403030080342004840b00403605103110683c8c5401c2c40714003036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 418124361 1250 418123111 418123117
    0x30504021f110708011a060307050a12020412060518070803040501030c02030c0106030f02130b09010b070f02100908010c0305040803040b04030c1a010e06030c01120c0e1e09130b01050f0105 83
    0x70b600280300d81c040214140d20154040c0d94110707031781004440c200300d5400405c181c034401201c0040015405200c0ca000941c010806010007190048000d42065250040c00c40320007250f05003903c02903150420b0000d54086008a001c8001c0804007508845042016841c0e891140c3e200315810107603202e0321600c200d4424404d40d40203010100080c440e80c3c0e6a41000c070784015400d9000d902c00c80c611b940404406440d44101560002d000c3c0c90200684c0c43e0100324041500200815554000ca014a510040c1d50300001840350400a44480180170b0821000d00c1c211038a100e017450a1521300002c0c440840d242c00b098a0344550302c42c0000b070040c0e0f164541200c0041035100018490107513050350f90001543c98081318142c41005a803084541e4681c001c050303440752051540b41c04144480b038111507540b481d41210a4110a50800e102c01550280c0864505401840c450411a62528003c000c600d044101c96810240c081e0028000301102e454884088a06108944c45119170a0203103482e41d000d0300c25 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 418125611 1250 418124361 418124387
    0xe150c0d0213051503130f14010507030c030c0306060c0206160f1202011503020607120e03070807081009081b0c09090d0201060b04261e150601030504021f 68
    0x801c0d074580c202114030100400c01c0340281807240803640b0344160b2030341d44002641d128015030078015504841d43c6d1141c641c940425601a2101c40000004403810f000034080d89000351300c40d907000903001c1000f820041c22103603800c0144080500304241000788550000c1c1c03d60317100da01100c5c00303544c1d03580d100b44441e8844405500241100c1e011038061301030050004c40e10702944a240c009012080c01e00c91102c58107146400000d601c444180070840c049161180300c484020b40c68200340500c4254500060714120381c81d44006241ea10a00050140e0902170006400700800b01d10103010780c28065403070075914010f000035040c81708010880e21410040400090b100c211002d07200001d00d05100080948031088560107201541c2403c1c000141c58031036804840c11180e82c04440702e0780214803c2c01c10034011101803d40c1140c41011001440801c0c1400c544a0613420300d00104841020300c1c009004182004000311f06043c6004100030140e2038500384080c00d480035000150b0603d60060003540c00c4442581 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 418126861 1250 418125611 418125637
    0x903070e07050d05090606130f0e0f030a03061d06010c08040315061d220302070503070b0a18051c06090c09020d2904050606040909030504050906040e150c 68
    0xc1848080740e0000010080004a00341c140038035550b1605481d40d5410a590003a0130040311425510a00b1065200885018110f40c010440c2c031074440200b8a81221140c249910350400104050307140c4d01485907a005140704045281054034006040380444402454103051290b490365800030868104119005184c0c01650403982c0c1a0154554004121a002d10404640d4a000c442c40d800380d91202c05208814482110500d400e003050380d40852904801d0403401c0d40b0a610010031595410300091001e0284000915101d00380d406d0020401c3c0360400c049008444052400e0042da100d5000c041c0c2c004421122001c4054081c0ca403240041801110280280540040200c3ea84034550001c00410b0f00400090000c030f01c1a0418104a25003030f2600c0c0c1c0c0b0207407604c1034220141015040654010700c001c0410b402c1c40e40d50031031003040d108000c0003180040c0000409000300d145c185050340d00118213903002c00c50504010707044c1c2d59609524902c02c45140c44400087c0f984c0512604541c85041180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 418128111 1250 418126861 418126889
    0x12070315050a18020f0f03030904021b0706081608270a0b0601050405220612080c120a02030706051005030a05010f050a09120f020a060501120b010e1b090307 69
    0x354040e0040c40e0079103080340c44600f40010401c80c429041c00d08403050390000c1002c0000b80f003241c100301e58084202080d07a05400700b400350001076500c82c8064496614004606480c0c981c07024145401c0940d0341c0c01403403c0c014401c00b44400c004001c20850403010050400b00181d403a8030381e946c05d079403240c12403a04402004084500c0035600100f002101c081c45164024000d8440030b0055800b40034a00807250041139141040c14080294080200a248210400070700f03580c4410701c5d02131860000c80140c400040c001103203007860b4410030804200d510b0804a481c181410002d00035100c5c428494003a041039100c5003c030701d410f104c0124400050000070120307520088545000c03800380c00010340d105c2c40030b403038200005d0002d0000e00418040380c0c0e2041d40181d00c05011601038684030885205202144a541c400d0b0001421034460940a040d5504900c52025514544204074090507007001c2c0150700d0100500003803445500d00e10410780c00c0e8001c496220300500700420700d802c4080d444084000d1402d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 418129361 1250 418128111 418128143
    0xa180822080601272a020d020a03030f020909012d1d060415170105090a02010c020d030c021305090606033903150123013507020f0d09050f120703 64
    0x72281844174000302041603c142c40c4496010b0781c90f00c40e041a1a000368200080120000f8841d5101490071800c1d00300041c01c0011070f901103440200241c0004124861455110484051450384180084041c0403030843c0907090001c0040201002080c60b0310a40304070000c03410955558004031060011075000103a090b5492510072144200703408481c43c2c0394079050101d00404400724071070140ca80c060b169446504600d03401e0141101c1801c509500b00f100c0c8114441c01640c03030032440d0020310175803080481d0b541080755403507080c1800503018920a5120115092124604a0b402004802c080250280e8a0810601d200b0300980d00da2145074103000e103506540c486182c07419a541a105000701c601070300070540583c1040c801004101502280ea801d180d5107041c60800c00c2c1680c1441490303000d110481c0b00040c1d41c80c400702c0542d81c0f500540c000904418081c0c0080000c503101c9040c0c0d150013040d1390324000c003140780450341801c200e015424000c030502034001d080000700011540442c00210310544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 418130611 1250 418129361 418129391
    0x703030207330605010c050a0b0403050408160f06020d080105091e272406060405100206040203121c09050307020d03090302090709060210050a18082208060127 70
    0xb045180701042d0380340071004102940b041100d02c0d5602e40c043c0080204c00503644a2030380f800c10050088003080010400421130410501501c0540c502030200d8002403410a0080c07a203440160f00050110340c04040101a0b0f0359100070084d04480b0103841044154a0380c5090020019407001441f120340f590000b8000013200442d0718208200c10869404165940030504589a10b60f003e049920005541200c2e4416058040c21039040000105064580707a500c0d0301041c1510102c910304c00158024408000542c1014864404055070800c161071401010781c440c008030041c001002d102880d42c403481042082410011101f00c00d400604c2500802c0c0705142c003d0041c401400100d000c0c0309407101140c19580924498000c0e2080c070f4002d800c0544040d603000e00103000040481112540301c52b00441c00302220b0502e100c155001d242e456541d0b5038001c402c0740c603d84100c0301c292000842c0503820130a0302c3c0042811030542d211f015804024456184810040b08010000b03010820300e0f00d0140203061301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 418131861 1250 418130611 418130693
    0x80705041119480c0b0a0c050f060601140c011806020a030605040203090a03030b13050108030310080d09030f02030703080f04050109050607050a03050703090306020409021c0b010f05090a030b0703150803030603030703030207 98
    0x4032560403215100c1c1505c09c00c60700e4000555640303012501a1102d0b2503800c000c403018000302c180560001480302c8658030724243c100010381050315010383c00036175101c00c29810300600b00502015202546141404102142c3c0c2d00c281700301c081d04050341c6450034060785d40c8110140c030744210760f040184031a50311a0701440e201ea10a403401d045907080000e00141310400071440c1621410562122039103c2d186031200d00c588132031150120f072b0501030b10307401000240120010f00764086030340d042d6545560400d0700240c2441c0440d007025210781c9040c424040003070800101c401209501d440e241d91200802d141c265030742400354100410355800400c0c089045281980600440c241804014650101c1001d26000310341c0e00072501030010704020340458105000e2402089598000360480c090780359240c4641c00c5500056820500283d01d03103050400c08003d24a0a00117804124051880c2d414802c00203642c03449400801130a043d0041900014404c50303110300c402440d0020a4000e0801c02070505020940c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 418133111 1250 418131861 418131863
    0x705011508030a090f031a061f0305160e1f1206030602090406060314060f01020a06050901060512060c0a1209020306070c02040510080705041119480c0b0a0c 69
    0x1011404002545c1000204a5040301d0b00130092000d0840c020490345282d50b00181010b81100000b0400024134452000c0703103074848031540d4005000e08081002030817003a007440d1480c041200001d1004140d07501d0305680800300d4600110b0840c402e19a1505441c4180300458040c0c049160500020503c9151f0b00240401c103c1120201300040d240c050030b500f110002c545031001c800c0c00200040190801000800d80d00405004031281c9040c0c2d03035103c0e800e0358402c03603003811240d458002c1004241407a414010400900c9005040c05141c40f41c2c40501c540200d24207603003005900144946800d00d541c2c0070240442d0040c0c103454440c0380c9004041d05c00215420b003240501d00e0080018070b511056410041074942403c00340c02c5440c03030081000090180c01031700440112003041400200250740340034800c480c495495401c0d1502a00003030f800090b84c1c3e14016500c545000e04120503c1040115061198034404d068100900c840d041040c2141e0180c3c00000b400c9000141d00d510240d001402030502e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 418134361 1250 418133111 418133117
    0x40605070f030903020c0d0201050d020d020409061403031206010905040c080f01150c0f08090a062007050901030b09072111030304060e0114090405010b0a03151503020705011508030a 80
    0x1d64000d0608404a91510002900507044500c00d150746103800030078290088d00505d0440e0815622605820803a401a2074000c801a8001000c01040b0400c1c014580140210341d0f01c04500304004011a85900c103100284405885800c0001c0b10b583c010300740784000c1e0401801c10006c01d201101c01601519090b260500850001c1c00002103a951401c40154082e0103a03441081007a03040c0c1d540d40365113603151402c07640e200e010f1205e0060ba0310741c1c400d010001e1510741d51715000340440e84100c05519059085000f46504405011312050b104c000e88181100c4e407203801000707580d481c44211030802c5581e400000d03680d40004048207900c001c20065072882806420721202c8040c40c08101a03507440303244215404200900092091580601500800d0499480311589050390401c0080e040b1042600108a030701d1001c1402d45000d58544a4080d070500b2104038100080c1c03c0c241c0c01c4040305480880c0d14101500010b1082c02c21100790855180c4000b0150040301d26500c48000e203803240c002c0e2804c2400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 418135611 1250 418134361 418134377
    0x106080c0d1103040b0105030c09040201091712070f1a01030b06060306010c200a05060c0c0409051609021b010504020307030605090703021e12061b07020a0b0d0f0f0b01080a0207170304060507 84
    0x2c0d803800f2b1307498a0003513074140c542041d070a01d000400c0a20216440d000e403241e018044c01c007501d09820100034a2100d100d258420744a0300c6500d803546521060560040030013082c1401400080c460412483e0014001c80c0d41c00e480340e0f20709004071150325207810000c0454000303e4107541c1c1d610b10580000781d000c2c0c08450402c003a90b21030080c41140d004406010b40313150b21040004d90307182000d074094488140590207407404480701e11401102c081c01540112502e560000d22400c00200d15580c00103400801d100a000030304142d00044e5881f0420300010f030020751b4400215500920421150008560280c01d5511001400e03402034560311000c0308442c00703292040d8060320644404100e142c492001c008544107082401c0301e00c180300341c1002c41c01301d0304441034800104000d00e010010304000d150207840843c1000b010440346054441001c405240d00d4103042c1454256a00130140960007600e081d001030300e60b80396040c1300361000348549144030302d90000400c2c0010b11031719400151140000c2e84800403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 418136861 1250 418135611 418135633
    0xf030c36050115030b010c0b0408040e040c08060601052b0608100911030a031d04140a051e01080a0b0c040506030403050318060c03010e0a0f06090f0b090106080c0d1103040b010503 79
    0x10984800c404481c1c00500d2012081f400124103420b0b81e0f030410b0003079049a007441d455141071900c440707054800345e84c00522408108200d01040100550000003071800d00d052401c1900500a1404a15403001044c158590a41503102c1070768884070041a068007155039100400c8085d10060200c002d0644080408940034419030038000340700161245d1558600c08100221410000342140c0400c02030752080c5c5403020044c5e00054020b00a021311f01c110400201810001c8115003070160b50a0819201000341c1d00401990202250349440c964200c00040850f50f43d162010740340d4800c5410081c0d21200c040240814958002d014510503c0c103041e8405030b155461300300ca5641d80c401c50304015034080800045c01000e420344121038002e048a50040742ca0b4560b01089030503507420740c2204c003040b50344070780c1c8000b0600207018920a0b00d4068031080c01a5040000050102304000e2104d841214000380b026004103556000784101402c144540d9281d081c285001a8056001c1c40754601c81d200b91007a2038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 418138111 1250 418136861 418136867
    0xc120d0605040b241b070e060f040c0f0507050f030a09180207020a03030c0501020903010515010212161e0f03090e0a0c08041506030507030b01060305010f030c36050115 74
    0x60303800d504402026400c0300b40c1820342009030302062070807082c0241701c0c2100031070610070080130002c0c000041e0760a08501d011018080003d80514585118a080400b00012a6013041d0324100e06e035401d140055580015080552802c404004007000d40e01c40090303841d1005902c007030108282c4003003d08503801c940103a42c0a500368065407001135803214071410b0030000a40681520f6040d18412000907003803680607030010342100c800311804002d9080022044445607030500400100c80e525001d05400c02e031100c600031900b45d400a4006000c0400342c61166410a40b1841000349075a010720703103c464119074078009103180f0852280c4640280080d010030902031582c0241d0241181a80c1c13800365a56035070303e0380011100b000c507031800d0300c6582e0903011020640600083c80a1401400c0c00c100c07552410f5801402c845051744080034480c0300050070300002e003404550b041181d08850804500c00b0b01000040c420b5140541140d65510070042c403020702d1503281c0c0200d0304940c901001100350168124040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 418139361 1250 418138111 418138129
    0xf1908060420010f0509060307030905010914301b030f0703020c0a0605070611040815041406070504120614011502060f06181305010905060901051e010b0c120d0605040b 74
    0x90404035201b807041030703202c0c24090059a80a2200c0c503001c03881d00c1950315003070300f11501c40d8400c0d202101e980c1076102d411041005954000d85d400c40f51b043c4c068501c074140301107600d00c6c6820301405900000d40001a14601010b01c1140703079042c030503240c1e6114591950042640803401c1100580a40c091201c60362815000990840d525030310795500e0b20000381c4e1008024803841500041d000c00901c40440e012008000c50190b40101180c18980c0341854100010364a2b200c0e07640c4a480d034004070810110b00d038081d050300e0483d4004100c0d030035105144c2ca070000c00303002640480d410444015000240c01c0c0f08801c101080d07422240c00b1358101da200d0080000b4411411110b103038200c003021000c00001013081c00070592040d5459011880f00001e80d40d06800c0d1001c083c0151103a0b1702003802d00c0014075080c410f05400c160194403d00c030102c501007484041e00014840d003101c00201181581003400103000c00f10451100f1480c072a079444c0c20078440b0b401040603000e424050741c540f03030344d50185081c03500407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 418140611 1250 418139361 418139387
    0x8040f0f1a0a08040203101a0f0d03020307140a0b070e040e010606050406050a020708060106200607021209010314010b031005060306030304090905070902030a06090f05060f190806042001 82
    0x1825103414682c0c0401d44900b200039004031b0b0503200b07144450307074410070510460740762604450a5410210244040100802040b443c00b486070008108420000340c000003100d100c0ca0b0b00c0285480c0311410403c2d0b00d030401d440c005025002300c1d011001c0142e55a40584020b600c1401140d0400003544423a100320308031002c50185c88c0215904020600402d402000540109039141c03040b02c07032481d15a0304040c01c0c004280c0c00000452040c6c01c1e03003149050200615016030b43c10f44000d04091502c0d01c4029903602444049c00303182c010001e404103259110340c01003000d0800a2461200950350307940c41c101a41e004903003403448500040008203e92034140101d90180301e0003002141018140080c0d4001051003440865540c441c9000000300c0c00e200380060b6100e10203030840015800e14142c0135800362a2040001d000051411041145540d1090300f249084d100035251442030001400090100c4e9072030b60460803440c45010100302c02c21041c0b0a183c0815102c604001400c11140030040d1200c02405070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 418141861 1250 418140611 418140659
    0x3060904080d110c0d02070b0c150a09230607030c0e040e0c0306160909020924220302040606020703021e01121802042d051308040f0f 59
    0x4100803075408400ba21154000000001c3c0c10a00c0f0a0504001d60102c6009034458008500c45420250184030190042007400e81c0700b8a0101515580c41e11042c43c503000143c01740c0d003080460f034200702d65070245564a03881901c1c99901440399004000c42c58072800300354120703c146000500124468041d416040c841903d481c500b400c1d0a00400020340a03000165016208018002050b69410056540911a2144006920044560000c040d5501e50700000c05090040004840c00d031228440c001212014403800340b0802c00001c003100b0140700b24417459860108071104200360f43e40c54090001202e02c00c9404210302c94cd9014141d071280c5440c44060b5000c1d400304482d2104030003108031240000414501080c0d8a6150079280e0204d40d41c2c04407d21a42c020302c00c0035021810184209040803880d2400011018142c2d0000402c5c2482c2c241880c800c41d0700d8601044280c5440d01c400d45040342c1c80490692610b484a21440703d040091080001c0120400e00c00203484001240f0282c1000000c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 418143111 1250 418141861 418141879
    0xe03090a03030806030c1807121e1812090815400c06020d020c28030b09061e10030611091207060e0102010605131503060f0903030c03020306 62
    0x40c400f82d90b00040100940d40501406108040994a0005214522060b10015600360074000c000400d003000300040300308a103181074010078071078444004079200c0c00100b072000300d0320748442d100082100c081c12500074100c0030040500100103407c01944001c1d01c01600803500709000e0f418800f101c0c4007081d2141c0030300e5400c0c00000316121448030340144500c0601a40c00800c104072440c0142000352000381503171b10000d6501c0038480140d0600883c0c1000b01e0b24801044248103134400039458260220088001f812140d0310300401000c0810a54020758100307014903090702d842c0c45415280c086c1101d54065503c413603401021820351031803400e40941011496001c82038103540e146802040c400701c0c0c0c00000701c42840340e02d00700d5840e6810310804040050285c00d400307190500103880000a819401c0c190390500317000788803940b101213004803800100400420861030058191401c0030054002520050800c15900400607441c0c00c07421940d4801e40e8104903212070100120100c1c0020b82e080c952012441c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 418144361 1250 418143111 418143113
    0x506040b03061e090a0f0b060117070e1e1306030303051014150f070c030311031204082a07050a050406050916050f0c06010f0b0307230405060403150e03090a03 70
    0x10043d03c1d80904900c040382d40001240d00e400b03025501c580d030126040b441d91010410030f960b01c1501440010004081103007182040c110140c15803081d400c0395801401c503104e042070036080307541c110854207401408842640c0c507a0701d2600040c050901081c1c01090400012500c082d8158807001c040350200682c480e508041482004280c580303060400d24049414006010703580c4655000700380c00b52040f800380080e40d1462030051316191044034240340300e410502a05110502640b04680c0c00307540060056900c3c909400c00042c0220281140c0411504002e0400c0765204005801025220300721034061003143d41301c2c200410748450f409103c0d00160040f01042e80d8148901108003000c00c10f0034800d041110005000c10340d60001d009400407580b00d03000400c100365007035006502501c00303180100e203580b030b1884014088610a134898001c071000d1070214948501d0b12030655000c0e103c02001580d540c0d82e6070801d0200448240c1c13032040700503d01150492802e0000085a9990b1400b0304001922031035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 418145611 1250 418144361 418144411
    0xc051e1911040f0e070603020c0c0d0203011b050d0b04020901051b07030803100e1308030610021609020d1b12020d0609020c060106020d0906020a080304020102011508010506040b0306 80
    0x40c82104499000c076845803020a070396503000d40c82d14000c0e040f60000303001141c0c914482c07402580341d011909061041109001c040d278085008481241c06503141010300c0128808280108610101180c0020314807100580140e40000103018000354280d0a000d0360a1800c04c01003280300c1c40584c5030105004001125014505446140c2c3c2803d000e001c0da2401c0d81d403511442c40720791007191305081e0165600e40600140c0000c1154035001014036100003030561b0381d503455041038400681283d21501070a080841101d10802c4400c558941d44516031865650716100c0a019411040e105039055007030050589080c4042c0c10020021403580e40d0364035100313178820794180003503000410b01e1b09401d40350300000ca01d10310203000a04072040684001c15180d03140140007070a22003a60381400c2000000700003000004c1d40050078005064028540d240c0c0ca03203844c40140e0040c0300c105040d40348880c1c00d4000003a4044190700851151400b03480138030120303600104054450004580c0994505a94824090302c001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 418146861 1250 418145611 418145653
    0xf060105041211090903091801030804034806020f060a0b01030204170a020102070b030f010603021804090c0305060604061a070503090d050d0e0a0506030a1e06060c051e 74
    0x402810030059042c450f0b0086000341c4130403585a402603000003404403060600c4040c00100ea802070800c0b143c0c070b50542d61880980d1042d03110260580075440b075006100c045c0e40104408010030304030300300e8803031403402c5145541444030b5620710340184503c40b0004003680003040165190030585c3c041d0419a854402c0003000344511048107042503030074480400c503c1000310704252580805401400408010310009250040300d41145180c0700c1e06009004400541c80e003214150349083c02e016841c0c55aa21f20390008200c42d00d11254000c0c00e060080007480b01140408090b40d001e50180d920641d60b90042c401599400e102c1c604c00b2440b68050031b04402556800340512910900c141c80c030301204440003401c03d01907820f050354140c22110b24444040d400066a0031100340584003004030515010002d2030345d000081c03400f203100d0b440392500c0310185c2031095094040c40c61182e04100ca25150780000341020384c40c11003140d0600c50070702c441c034943c00380e860900d440d10240310040034005402098642034234 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 418148111 1250 418146861 418146863
    0x5070507120305090f070e090c03030f04061d0a0308030402101e180e09060f100b0d02030402130203090307021c02091801020c07092702030c040207080d0914060f0601050412 76
    0x8011708118120540d024000700e0f00400075101c07648410300f0003c0880e0705110b80c01680d20321a9108001e0100c28190700b01c1614101c03405428100e040004240381d105400d90641001ca030710441c80720000c410084070340d0155002e580283c945a40e40366003204262011030892487c0a040420006038004c698421182e55260001030904884810707036a4181e118850001e482c0680303d078015004011301c0460f521400f41c1d00c001c2884407010127a140224400d4288114a807039216190000001000c0d9101c8080ca1080d000031000215624648200030f90707180e400450f0124070810110000450705c0302000260b2291b140c000700b108003280c40e015050009a01808030704040340d5024044c05e06125420b02140004099030400071410100b007100c0e80400188101004064651203545100580c40000d20310020703501c1540c0050b07445405040040c0f02d4003c10320750381d5420742410040010407914000d0507000c09001d0040301d0b92516850f151110364041190b8090006500340b004014510907503005400741 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 418149361 1250 418148111 418148113
    0x4170102070204050906071107050612090a170306030d080603120a140309070609150f12090209100611190f140a11030f0111040308090103021c0b040507050712030509 73
    0x503182e400b003010345a08031134164258102500700110590881201d20f4840c103002c0c050f2071824140b0300000e00502405601c0d4290b80680170002c0d074200000c04c0f11f1139180b900120858020060300003c09803640c1f044071114024000c3e6217450304601e001d07501c440c0c0074080080240822461031007298500390000315803101040500c2242006a600c0b079802180104d10140140041d03d040000290400c0302c1640100c503c00c04401c01a004994807a202c041c5000c0759141001140f1400611321001e8543d50802951181c00c1c682407010401f00006080100e408a1312009210525000307207c0d20707614411003644000355403e810000107090614a900054850040c03200c100000580e220f00d404900c250482d07820034480750740c0e6050716041095a0707080c11000024003a1500b081c05030b501d0b60142d48002030000c03034046041d011760b0b8066019180702c2c3c800c80c40c8031100050320300401409840f105a50500440c50900810301d0140700c0c1c81240c4201c2c1d0461110185924802c000302e0051074001c0102841d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 418150611 1250 418149361 418149367
    0x40c0915051e071208060f0118080d1206060e03070b0717030901020307030e010b030c0d150e160509040b070c0c09020a020a05070e0f040f051002040f03030305070e010504170102 78
    0x42070910b420001510701c1e5650000303440361420300d0b00c039a005020104510500088070304008890380c03140c0160455510a18019910f088900e015000f809010f80100d00a401a00282000340d80d019001c000e001c00c07103540501100c0c3e60f6107000e0380c10402d00c080c4d90b80c140d00444002d02c8a5500000140040752041d42c140c0d84030402c000d051a0950800d803032280c06a5000014461780310b80c54001d000844850314020441c0070040800659a50b00b002c411078004c213408a212001e00141203071a61b09480020001c4c0034440890b11620b84a0034001ca1480080c4049580400c60b404c110100511955001412a000307444148094070709003c01c910480310485581c1c00464811464005000400b165400030300ca100c070785103400e50400c600c0380c10880ca010500d104100d40d046622034a20b8100e0f404c1640c03001c02c2641070900c1400c0942200340c000c0081d00000307002495501130424501124080d95041000d41c5504208540340308028080703600155040c0403d104d11090310b00c1c0c0030004075511000500e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 418151861 1250 418150611 418150627
    0xe09120a0921110f0a23060703080f0c1809040501090c03030f12050c03061903051b01080c09090105060c0102040e040c0905070504060507110a030f051b040c091505 72
    0xe880c00e0400c1403000c20070711051980003005035416030700c20790f544210b0350300d400900c80c0c0b408291144024410b1003404d150010a080400141c016118000c0402800c11a034a00c0c42c0c0c200a070611500391103424a0001100000322458441015a440c240451002c55082c0752190100711030740e04043c00c02d54243d5618041e050000c4c1101c4003010085100791907a0282c24041000a44100c4510151204450030001080f03200c80c290021603502500444103203080c0789001142500c0c1d00ca054000a14078452240084000c9458104003140e01509980d564002e940c2c914000d07116000301c503180d03904070b91800d005010502e00340c03000d00b10700205000014182640c80d44a4046510280c03000d84da084007001051020011900695038404441d090151416281503801001d0b0701c40c00d540501500f90350050a01a9940c0c540c04078000c0d508113490941070042030800d207840c1c000b0701a1650400010444010190900d40909074417030501e0b46030b03840c40f1841c02440080c8809294040d004124040200007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 418153111 1250 418151861 418151879
    0x2202010c14150f060a08060a02070f0203060c0c010f0c08150102011b0908010b01030203010e011205030f0705010b0f030105011503021e1b100513080904060302060307180e09120a09 79
    0x1420b001c030290302d01840c1010078480d01030f200060315081c040c4010070002d2100e0400051803030340000b03000900503a16a0603060060f0380d07103594031f0029454020001809441c1c01100040c14070400200000c02c9400130b64140601120345050300a80403e1640c000101c1c148003600300c03012040010300000c99001c01c1c6200207501c102a55040302d010403903460f000c0c00703144424481d002c00660203080451565040451045101c241403180c0c80403000030f10401e804001c424801e85c2c01e45c005110420b51526680e2820501070721684407418015012200940520718050050604817003c09507403c070448034006084000e50302640407640450b4a0b903031203c2e4903145400092041c2d01e042c0d00c2141004104262660500c01e1000c0000035640c1030406001c11409841c0c0a58462984004c0305030f0344405400214000e00700d0b030b5002070b50004002c801c000c10680c0184101c401c40011100d50a03072991104881841c2c0c100a0382c00d6002a442450540100040b41c401016112020b00704450002c0d5503242c1c42c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 418154361 1250 418153111 418153123
    0x303080615040603060608010e040302060613020f0d0209090604060e0c0a03060f030503030708010b0405010e060d0902090106031d0303220f08030a0f0e030a020d0f030b1e092202010c14 81
    0x8000039179100700c00c1011552000c581805015400307122605420305841c002d51307030a40a84120b114640c00344401d900f501440e81100c1e8146d90001c11036840340c0014001d00c000b50050b04102d070044000000040842c40e0071703c1a0415512000c08400b29912601010540341e041600f0309024942c1e101c00104010101c003088070000c61165008503079910303101400400d5441c0691040e85112001d1105200c50303a000b4600300540c241c01e8807116128100c2e451200060b144640d006504810200004038800e540f40c0c2200d5090b6800200900c40e540000300d04a0750ac1c4070803120001001e00446040300011411040c80d250640100325018a50003203458a400c00d92056601003025036031040040c1104000c0d004030804042424051400c002c81218003a4a550107aa00c02040009000892000f68002c0c1d02c1841c0054000d01402d600d003000302d2145034002c840c2c1d481c4510510007030001680e202c0d14400354040010b00105803441e81c1549034019120948a92001c848803102d41100c0c010b02c00040080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 418155611 1250 418154361 418154369
    0x3070c0209130302011503050a1b15120c02030705070e13050322090603120309051006061d0301020f0712090306050c2721010f020f0a0207060513030308061504 70
    0x202d002906881c1ca40642161101404050f18468060003003010038800b24204a480340c02405803043c9070502010240500d41039003090008005000f40001c41c0c039800300a4001098184500b00101110a0000d0340d0340d00403030000421a80c01803d0070b01c551004c0d414840d401c07000da052105c055080f95130700c0a007107403c41c00f00110703d101c550310403010044010030310300020700780c0e0201000303001d041d901c0b00b2a201d07541d4034641043c50344908020042240400c00900c400580c008204191520f640e0006d21040200300741c04003410540c103150f0150314061080742e0204480e200c0207464254590790b00725241c40301c40c0e0350005202000c9000408a0014020306100b5620385180c1c0e59501441c5c80c0400100c11f0881c11129250b400007580441620352200640d8211b007100d80302024002c0610785603016103844014020707c54000315500c1008903030b000291554446640030b5031076190b00d0f44404c890324020641c07120080100c2c03120400100303008031440e941092019041154010509070700e02900d03802988 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 418156861 1250 418155611 418155631
    0xf06090d1b121205060f130507020a02151c1103060114120f0a0f0c050d0f061509030b1f060c0203011d03180306061e03160608160e01080a0203070c0209 67
    0x151481d000f00310352041030341c801c0e4200c5038a0012208440440c40c40c6031a0326403c13048903900d002260409008000c440c03651a0300516909910f0765070a0015607030b070040b0030116000d154980741c20201e1f0030603000d40c00042c070aa000c0c0e581503039640c000449280c1704a07100510040010000124a031012011a910480204a215000e03003004c0c0301c1601140c81000c1034030302103817511184007400d07507002040f506550349840e00819080740c038110510061200d540816401d44690044049440c2c118862600301e0b80a0000051a903a9810a9a00d6103031000c0c2e440c004001500342c1803280502640503102c41d01e0000c1d0001529104c4481003803101012802d6a1900303500116580b40d12020700030605040740f000350060002400c00e000895945490b204013241182803800b820f174410386040000304101d40c81107110141240c2e80d52005440060181e409444240b081003c4030215030003801e0850007007106139504002c07955200d4401c0000e42003d0100310401c4000386140c1c016036a030541c0346002d0420300c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 418158111 1250 418156861 418156877
    0x518100e090715030b0306010603020c0f0105040506040308061e10030605060c01090c060f0503060d0501020f03040c060f08040f140c03030a081e100315090804060e030f06090d1b12 79
    0x2c2203e14905101c10f45040815042541d0103010391004500030f811210603003070142c2ca82c501c2d500c0c458148124600700c445550300e860100070a200c00043c0a9009900031780f951945074480505101145071947c03c11040560b1560b90382c9042d091402d1605283c0d681c501e80003400c140c44e000010a0381d40080482c081300c1c0c1d121048a01071181c52559100140018180f4652412076008054102c0c040245600d1248280c64410b209204c8290101e42410719401c2c03070304d9034034946407904031000380060141800181c1c001c18520602406035403003030301071b64000d846104d0210b072503076508031101e50342490308815020702c3d028842c0700d46080010306480011038803078031007a1800d2000c40d10241c1450030300d1007881348401d0510494001084038034045d641c2028a02a0801b03e411640d8003411039040003e150f1200001c000518507840050568a01c2044040d594011500c899845d03071208181e0300c0c000c0581114082d50841d0740100d01898050b022860381082064035a00c860307815615031003910000c030f0b1480c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 418159361 1250 418158111 418158119
    0x13080d020708030a360303050301080106051e040902010e060307031a2707020c0901090522201f0801050a0815010605090607021905011106010518100e0907 68
    0x14010480035001280085003000a001030042c00c00700f190f403200444038074101c6a4001401c06004802170030005418600025541e854005c0042d8005d01c941e1a82d9460701002003518504803a000700000d001d4904032504000140c00c000c0204141402203061051a03842401143c40c1c1a019521070b10b025200014404541c0000030950009080c186125101c06d002000c6040300f021040b40f01101000b0000c4040e0382d448100307a15194141c8000d0750301418503000050400680d80005110b00c0307004203080408510015070560600070f4050060500070101c45002c07441c181c03140306141001000384000400b55074054100c803442d8446000e6400075010400600481c03c2580014009040e80b800a1040e01c400100c5500401c40c18028003040010010b2244d54a964441c10781d059943c00608181c00c3d0700c540c8614010705079aa02c140342c0822041c0102c520010800700f10103040f16406031808070040d11021031303401c4110000380a08091900038102081903489542d031a44a11803401c0100802818 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 418160611 1250 418159361 418159363
    0x506061303060f0c02010905121c0501030503090a0503030a0e0f0301020f070b2d010312091e06090b0c03091201020705060a0911061c0902010e0301020c010207200901061413080d02 79
    0x130040d801d5a04141004001910001f61391003513044400b1002d03102c14180c1513104080f202c4014440d0418100300010083c0b0074040010900030b0001c07074003510040e60f10000c0c19181d0203108020804907803607120011190801846606420100600052906858040022503a0095001910103a604108000003114400000c01d0130504658442400850f034280074113407100140801000000c40c03100410245002e0f00303c24001d8030800e0070388640f00041c06021203083e002807098400080e801e07100005d0006520742103a14002d45c01c0080d616000461042c4450302d290400b4120071076600304901e00c0072800c2804050b004050120000c22915610b0074018040c1442000c801e02c19001004224030142d210380c0e03480185542c2a20101c0e01411500042c0d9661480d4000c886d015400040c40c0d000b401c10650060116600c2070541d414145101b58500041f03900c0e0800003901700c00f01000600c691401284946228143c800c0c3c1185000c01d4074050a031824441c1e400940203502c40c1d021140140c0e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 418161861 1250 418160611 418160621
    0xb090405072316120c0308070e0102070b090d0606030f05060f0601080106030c1110200f0a050d061d0708070c0b011814070509100e0904060506061303060f 68
    0x881c9401d080d21400c81445074020141140c0305000064005140c1e50108018121440303c5070f0003100c041844c1e6020040905174805800c2d04a00081e2100001403441e40200b46110118034180d008060076403c00b80d1003405030b4030045c09030358000746003003440380020303103901a1740040c41c0f14299510542140d440c10502c2c00740301500c002c48003001d0108004850741d03c00c04e00d5046500354900841c61101444041c0c4d907240051448040a0041d4201c0c81c0070042c15070000c01c4006d84a14400001c071030742d01001c3c0e81c9406100200d02048204028012070648208041c000311422074400098050307551140b9924200796001200141c01130204201e10036400848840e03000c60181441c01204070b460741e0b103e10000050040400c00b542001c0c0d00071540c3c6843d4840382200440303165030a0103040c42c94000d0515003001d8940780c85240d0b50034001c1c5a0750b216078200d111141c1c01070711301d21164586582e0300c8041c11008110755040070040c891609011510917500001b1402524001411000300c004401521 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 418163111 1250 418161861 418161871
    0xf010e150106080a050a021207030e0c030a0c0b0a110a030c0c050916030c0302160c0e090a11012001050a0c03060b091305070207050315011503110313020303130b090405 74
    0x10308004010850035400c010001c1c0c0c00914035000040e03c0e612405a64024010214090310300820b400411501ca60107901822084010100302c0e2654040442095564803040c2c00040c046a201202045000104030160074034129070308150003189240131203207240002c070180607000079005404003014005120a200c0c0902801d8900030028030b00b01c18000f246c07032071802c01d01041550b100131400c801880395040d9100c40d801d664852076054200e007040e0000100900841d40360300142d4004c5648002c00080280c0040e60100c11045109040401514100c2000307107011031700341d14500140c111078028402c80348031304044c8000291002143d00001c1c2256805d41202c02c142d2010010540180c1c0c8407080c0880304900104003140d03a64070540100c1c284609644800d400d44518410013440600619a0328140c4001d071100800c07000f03100004509075400203030f140790150b00800205e44803584090a40300c4060019045034541091800748001d5540c840c0e000000804021030310403d41c0c80c0c14002d0903044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 418164361 1250 418163111 418163143
    0xa020105160f050712030b06072003030c1903090504020705060f090304080a080706060806040b0a1b09150306180915090201171b1611030a080418020c0f010e 69
    0x501c21040c00f81c55031159100c09061391141080641009200b9001602d00c3c50015009a80300d198920703155071920040034200310481c0d0941c0c03407000c943c1400415a241d126860f801401d90090001e00c030200103e0b40f20303007502001169100802c560b02e0307030b000400003107106400800051610f14501031000101801c1d0311450b800030401001325038400105e5403101d50300001010f680302c04a280c128010b00d210b5010700b5090180c2010002032007002003c4900c126809030081c06401c9082100f412101c0c140c1c1100c1001c1640c040f030601816003072043c0c41c200840c1c00d0400080890302d410b02c103541604550321200340252940030075420005000e5508107102c0c400c24090003034201a50018102480710803200d04040041d0340012001a607040007100302c0c6142d41c58050341c40b8092100200110b00d00380050b00c823610043c0080055080020780d4071005a0442000c50406080c0070000c43c6a41c41e00c03d100650795002e0000d0151003e041c02030308681100f140002070b144c00b01d43c603001d045c18007039499550301d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 418165467 1106 418164361 418164377
    0xd0207030b0a1e0b06220f0504061410050708030c03040b012106050901020c0f03030603160b070201050f120a060807090e0a081e0a02010516 62
    0x152030241d090302005680c0d420082003503500040382201040162154400e981006601180c09403c00030f00d00e42c03030181c8450030480400d2000c0c803455256501c8180422003044c41070b00c0031000b440b0540e402e00c8a240f40c500c84c185000480e401e07081c05000490120f01c08d07184140c00716490141d220703d6254407030504110100c000c0d00b040300c044880c00e400b14000719810010b810b000400300000c9100001c1070590b40d03101806460082c00070030381507409101c6205031410034042070048195040083d030b203d03d01001054907100514043c4866201940320620240800408542000e6020b00f0718130750300c10440006034035a2088040401e80c0603030910912644d0003141e00404100d40e510f50841d24201c0d02c0d03610010031510544142080d640c003550003076000442c004003800d1031a211024a0302ca2034a610101201ca501c40000100180d551f1820084201410300b84440040c80c0352400000d = true := by decide +kernel

theorem cover : BRFrame.Cov 417985611 418165467 := by
  have h0 := BRFrame.cov_init 417985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 417985611 ≤ n) (h2 : n < 418165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
