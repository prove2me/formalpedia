-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2757
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:58.978018+00:00
-- url     : https://prove2.me/submissions/d0c0635e-1fa6-4cb4-ad90-922d60407add

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 495683453 ≤ n < 495863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 495684703 1250 495683453 495683497
    0x3050a0507082703060705031308040503010608030a0809010b01080c07051f06050a06031a040c05070602030a05010e130506010308250b011e030c120326090d090303090506 75
    0x90b20a07880880d402c0da16515060611010340800c07003410305881421400f809030740c50b16a201030960720005140f84052403540085200300840301d0141d402410020300204292500e03031841a036a0f40c00240e01c90f01103508400010610101400344d844010810794500c80c603038582081815858102402c22205d9019900c4010003034031401d005607001d503229040c0030130094580b41c24030100415607023094041600700200c5098019030b5108146640030161000280e0a0080c0011100d41c001d500c0004e1420340000306105000130550080e138183c07030002e0018100ca4494205e0010030b00342c003072401049600040010070105017070304041d1140702981c00c0304c0c420b5102e4107040200745d101c810300216140d540603001402521440000c002110f0248101400920b04507124130000080a1180c008045041c00000003018071840301c4801c4004c0010b901a0515034040c4290584081100d04168038841da511500700e017840340034000c0480b41c043e255800300c00c2c2014203020060b0301005003086407405d241c9110f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 495685953 1250 495684703 495684713
    0x60406050d050601060809190206070201020c0913110603010608070c23060108011407210908120702010b0405070903030c021903080a08090a24091b050102010b040c080403050a0507 79
    0x124014402c0e030140c45190f041ca9409480500c000d03141d5122540400ea603044841c001846104c40d598044400503111161440100d24141c4003130705440e04008800140810406042c103000200c0344150803440901500030240905800244a4040026000c00c00304040a00450389000820702501c0882c4494860001010b0400c142400400290388544010000e040d420b00c28445056100411100c090518640080403041c6800000210407000040204d2685103548050b03a51613000260640395070005002d003104c03000840e4039001550030014074100524240c0f0401c0c0c41007036507466107043d50b82140c400720b41904d524801240c1120180742c298074940102105280114441c4104079a0390995540c01060350030040d001d54107950045064000203041c0c004801c150109102000404076221080c02002d00020400500102100c40c0707078280b11030804403180e0582d03c080c1c00900519069800307000488001182034400900a24041000a03100e00d004040302059864868180481c680324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 495687203 1250 495685953 495685969
    0x1506020d02010608010605030a02010f030f0c03091e08030a020f0c030712180b0d050702030912060928320a1505042301061a04141e010806040605 64
    0x100401691110308910540341d424003036200903001e13490090114a20f041c011070764030940c084c002418480810f0143d0f84440c030030380c0400310290251105101403014004003400074080c1e000b041d507a4074441d4021b081408030032251400170035800184113155a65000c6e03544000d40104004041d00002002413003408d4508201811707105000e07101d407058540390504042c0002d00d0b9074071580781500c14410b08100d5071000c9410f8804003103640202180a40e00d6040072821441070f01c800c03541c018150f080500111500144480c0306075211004c403112002050300307000002e540041a562003403407001814002411038000004442c00141d4492a03012009400f100d910441404625950707100070020414010b01440f003410742c108483c0d040006041c40d440c0e150f500650200542421080e0200172580179409600c80f0004008a0340880d500d928010307034580240d072241c45030144070000d488580c15103203001c80c495407000006440704021200040d005413041040213000b2030340282c4d40c5000003465119001c0e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 495688453 1250 495687203 495687209
    0x303020c2104050a0806130305250302010c030605011d0f0a0f0b0307020d050708030601030908090604030b090d02031309111303082101060c0b040f05012a03051302090a15 75
    0x100c00b9140c500b40303000e01c0010080790f4001240b1345d01c500b0521050000303860700117032034540500d00780e651441c1c01d07035403204240d519803040ca03413000c102c20611007455419071240518180e542e03028406c8641d188011541c5094403061041c01c41d480320000c2c085441e248003800540000981901c565a565982040300c104582c0d00208940c0000030412110325814401c3d81c0c4580755500305542420050307210111300d130100508640c185984d400401061204104c282c0d000040000c100540e1191a0b180890205400341c80c0181e2503c183d41030390101d180044141c45003900d80500c040c0c1c0b0185080e2456025101c4500074404c521400c010360003089180c400400041d6000306012a07943d00700720f00520391300960407103288091604100502040380c2c0039941520041d00100708001eaa26142006603440b205000020803541c80c007105980c2c04104c0c030b095049840380680004540441400e019000c4d07510488004034802c1c0d10000030340051906618503a04880c1c01c5800240170340f010b0345141c0401485030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 495689703 1250 495688453 495688513
    0x1a0a060c0c080303010b120402030a060f0b0f0f0d20100903051e100c0203132c04030905040903051c0506040e0f0a0f05030c01060e0402040c02190303020c 68
    0x200d188081c401c1d20403440c401000d004006503d1580340c2428030b81940110340d00309595250050125040d941c0401003d0354050300010104100030301c000d0f048006146034940b1901440181e000702c5120700e4056000d0352940d2000c0d05440b408191940c4000a50800151105040e004410240304540302e0300c42d8001d544002e500c92100c1e05003182420f03441c03c0c508803e090380d490801c9460310140603020564042000a01c00c022036401901c400a84c00c5001e5900b12094407410307801c000800c40a4208564568481549419035400c83e07102c0300380810804030b0f406008121259000c00c124105903109015132400707894014184101d1440e44035081e48425030740c5103221b480e1818482e407440e06202c0d00c4240c1d811078000b00580042a4400b1340c541681c80d1000d010034075840d0181e810f00c0780a0046400000068000700426030701c0f8404101d1545055800b07a016a02c0c2c5401c1444140c00010360240c0d00400c0c0b40340804000e076aaa00701c0c041d42c0242c03410b24643c0282106042e00c0c000035440c0d04044401c2e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 495690953 1250 495689703 495689717
    0xc0603040f140a0825110405220602040e090f0a030e120d1205070e0f100c0b0702030a02010b1008060d06060b0a0c0501110f0708031e0405060402010305150604091a0a06 74
    0x2105110050310340405c03040300e43c1c1002821352000580c400202003010a042d180414a60b50b1580f510305010f17141400641e550b40309454100c100310aa03801003003503c100318014140340d2955803d06544144000f40c10540d58070904403030001c2400f41010408118008051002c0300303400d40e001c1800c00400e0301518020450341800b0150185107801180e510545a1900e40464211240005c4400c5844a0700034051070098000710740d881c0c415030060050542001e03444889090400b8020364a910012040006510b880c1000b01c091074409904c080b481100d65421116480e04010461403a50300f10044400d02e544900006114400c0c101900e054066a00c0e003030000361450030100e0075121a02c0703d0003007060040004040c9907a580c01a1500d450300580385c5902d070354640e46540605034074020740c1343c0072081190400040080c0010140d00c141c0c800c3c1d07018046d0340c6132803042c400c4082c1032511003540124140014022a8065072007444010960302c5a401d540080002181c50385e149500120001210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 495692203 1250 495690953 495690967
    0x506071407150f031d010c08100e0f010501120f150303020601080d09150215040605060f03070315150f0f03021905060922050a0b030c01020c0603040f140a08 69
    0x5028100c010040002610074000c00044018041d0002110500034503903a45810300729100d03410304100e045d0792000c0c020802c585810001800b480811920701c1940ca03203022000c01c4081e0308130000340c0a2545038040035038503420a401034868100c12014106056541c042102151000307009192a401d030003201030900c00e085050080c14070030140c02c800390341d0340000d04015007107910aa41108a500191028615011a0000320f0510007130381c044e4880a0280e038140810310850390305c1140140011192a140f48545c0c00030b15840c3c09603840058080d4440210903486000160000e56440c4000c0b0745803030300d40b0f4a55409111005007900320040b08103050300c0500c1181400c04045d100b13909014100805c0b5490000060b129100d92100a80640604240310407041a00c0b004d0070390090541c034041c07140d490b2a0042000400080216a10900c964440d130001c1754004a56419100f0703020b0300c0140b45640700c2c0c850500c0c030a0806821200c50030b4a54110410442c1441258150791198400581e0b6902c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 495693453 1250 495692203 495692243
    0x10f03232a1228050903030a0f0c0e0f13090b040b09070819020109092906041809020a150c0b0114101d03070f0806010f2904050607 58
    0x103500d03020000c40710800c00046039014150406500118148441400f040d204611039120140c041244600b01c0c20a030611180c5034010000d544030341d0941c00204034100c3c01c801c413801991001640400420580640081e5500f409400c3c0c1550100281c480c2c9581e041c036204040466203991026585001c150f420310041213030000420b50414000c000511000d4185071440d030300d5400ca94007110007000e901c145942164044c0700402c0080c84440740401400c2c65609003420407140e1001810090241a40e4001052600d002a64291101d84041055400c6008510f10081c6001c1405907442508080300207010307444000381e107900f0750b126a68590309034580d20300880d2115041c1c101c1801e2421f801c41d80d00c07841d01ca480c40c0520703110b213901e41102c2d4005a11600a41e104410700100d426014248012540d000c0200f100411a0090350840c4c0340c1c0d0380e91300c0e40c2c1000f0800a0140c03511800c494900c01c1000da6054548129513445010444e03e45643c500014036558404031088810104107207003100001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 495694703 1250 495693453 495693511
    0xe0d03050402100c0c090203090c0a080c0a0e0c1c1b02030a11010203040812060f04113105060d0e0601030c05030f0a0210050a030b0a060203030f1302010f0323 70
    0xd200c0c4c20880c42c0341c01141c3e80d8080d144214000c609a4a80c0440051a01401003010b00403203c07010b0301e4002c0e604d4594031915140c1c0d081c1901e99002e0444507000083d50000d07a8811440f035140c0c00c22080c24150303001c007130034108031880f200c0f101c07020380b41d5002295030720212040b0840c1c54029002140d4680880310080c1461070202d100c2e6180d42d20500030440400c07120700840e81d880c4003001340e01d41160740740300028140040b001c1c181908240340641c0044035080308001000c0803810144280e03400085140701009001480d008012142c8070031008005c0341c207100c1d01421202501060200d10244000001407521800741d0081d5000882c1c034070200190304040c003481c0b60b542402806800210384540100d0382007901480b0240030000d0008448003180e209520038140070000400f50a038255071a00020f50381c2d0800e90308041140e1100b00840e00b8a50414040c0c80c142c0e40c1a1210b100120f0031a0703068004180005048802da01034140404d03074a00c6031203641e80304030f01c0c1c800f482c1030205241c80c10504003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 495695953 1250 495694703 495694729
    0x41508070201020712200a12110a02150c100c020a0327030206090a09020c0102090f0d150203040c0e040f03030e0d050d09020411030f06011815120e0d03050402 70
    0x242e40704106030b10200c0c01c41c3c62a400e142c002400c0c191203403420303504011410503c501800b2500d000342e13090401000090040f8a84050350356444240e002c0b0001c00d0a81c4401c24224020340c4402e0404006603103504001c007410101034000140d4940c60340f2041c1031030170390f4290b521280042c0c11100d0f21200f00743c0c01010500b8119072080c041002e801250030350b0710707046aa03800083d104d4103001c1030012040e69941c1d0202c018040d4000255296000300c10020b01070b40081e10024412030342c03040a5032260030b11403e11612290032907072054680310f03040c000a0080d40054416204452005c90101e160a03245801c0c41c0220f100f46c1d540c80501d00b01e07040007070443d2400154401d82d90460b4003041d016a501400344e82140301041800103810300c040c80002c00815501038044094240401000040c42200201c0fa220f01003c0c1c9403080701d01071015242d0352a540d1401060f005501c09400d8a03040e504c1605c0c0302075906110040040d12a09943d0401d01d040000c40f0084002500c0f035017040b0031400c2c00c014400013 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 495697203 1250 495695953 495695957
    0x1302031c0f0f123204060605060703091208040302180f010e1303180503011d010605060405150c0a140d02010f0b030d111501090506100f1d011404150807 67
    0xb2203800c010b002040380c1c0045840102c001e407120310a8549011500d010f6206214009a00800ca00760038000c134100e08089500395805803a2032400201401d100084501c22503040d5589914107040444401c5480c11600c0107a4001c44103120100040e100e2016603050107094240c0d00e2a00e2400348082c400c41403058114004852250043c445944c17008405014100d616080054203810b01d10364410060005900044d03056007004841d41c140110743ca0841881c1813800003e0280715102e00610965202364814103421000d818281e60301e0306c410601074500c110180c410b40720a906680c882201c618000415220707103401804141d01d80c2d503024070541c150340034011028000326119600094031013100391510010b02a880040c1e411019040c1300043c00c50880d001035480650710f604551008000840d0701034020000e1401415100d03003e40f0503c042e45107a0b07034031205a04041429181031128244e08181803000c1840c98803810018440070f04003800c048038040313003d0030b81c8400007000c8000183c41d03041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 495698453 1250 495697203 495697217
    0x906110c010c110615180a020a0f0207030b0f040219030809030706080115110f161a1204080a0903020d081305121002031512071514030f1302031c0f 65
    0x143d6402064043c3c0c040410090544241400d0000c14a02d03103041072499489100b02c010000f500d03449030301074881031845035556060b40544485c03d076a81c1d100703804040c02e405c61140c00594202400010701d903100b0320240100c03000da0003941503400aa000741d00304441140d00803c115405080810050006101510340403905500d0802148603405c01003880c0c00400c00d10329480303114024200101544200c0e418100c0e00100c0d50718048561482c924020180c44c4801700380c1e27206e03c24003154240c92901107224580d0366262a9035403191015442110b8420a1000c101000030143e070341c0d8010346190900446c45075903184040c1c10302c903203000960313001340d445143c0300612200030010001d104111004262001656504c030588018545404030081c568003150303d2048100200d0007150140460b402c08900444900404405441e22404214420329250041c400074218103112030303110344c1010441060100c1c0042a80129040c00e0000500049526000781140010b641c8a08108035605183c40c12207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 495699703 1250 495698453 495698477
    0x60506030c09010504020714060c09100305160c060e0a0609050c120a0308060d0803041b0506090f010309021507081e070309030f0c150306050108090703080708030a0906110c010c 78
    0x602d240410700555019540c04a842c2c410480380d424403010303c44410084456038545030301101c0055001107401402840c0b069034070600759009024503070040c002c060919407000d490020840d6000b40750241911616140c07041500d1502c0b00b070101c0c1c15820302a107030220b1151400d0601ca4504005c0303039a028010340cad040f00c4007500305d940401c200d603040ba49407800456980b210000100800c203032800203094218008140800c02280021041408841c01040c0e40081e0350b070010811940074044a00703400c4100900040e1440d8880d51160b840d851000307080c1c160b2480070a40c00d002c2a00110021264010001511703a03620310490f01c400c40d15001d0385906032500503550303801410500d05102c000d0200b444c01954000300010480c3e4403000d0040881094011500480002c0c00341c06607104840c0032440e10004111000004111030054075040346189140c02c4055441d642964002407842040c42d945200200004409010f40701d0b145040d900c02c141c98000c400390603800c6941640c031050030302807485141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 495700953 1250 495699703 495699709
    0x21b01060e280e0102040611010f0603020310090501021309090b160903141e010203010603140f270d0e040b010503040209010e0c0904022a0f03030121050f0109060506030c 75
    0x102c88500d106040c2d80409010956140580142d102d03442240d400840c0101d80143d020540c80500328108009112410302140140d040320b9803070001035095001460101001c22140d000010700c00d00c282c000501d80381c45010314840d03d02e4540c00100300251100f191301d040c05950405030303810168a460041c4400b030b00c210041c5c0207030f1051000415400d1020a0b00f0803203501400161308000c02019840700e1400e8010500d0300075442401118013081ca4035204401640048403003501c1194031951212068a40707000c2004030000c0e1829004411820030b802e092080307010302903440980342ea41c40c1d00c1044500a8100001d440d504075280341040420320030003016a58540f102c17411200000396420031901d074048440c0c0c0602c9103030490f0350082e00004e040582521a030641003d2440005990b143c500c042400712500c80e02d0480d140c0c6081d82c8280018000007041038114580c691144c100000011580d58807a400e00ba8081c1301211565980e0f00204144641d0b8069654004801c80240c41e41c0b400c02c1d000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 495702203 1250 495700953 495700981
    0x3050c0433020706081906051309051209151612032f07060504080417060906011401090905131a060a0803040501090b0304021c0f060f090201080f0712021b01060e 71
    0x4803659201006c4000b08a40345146d0217071002d0f05014004003841022207001c01c024020a510444140c401c48121036005001d0f601540d140d07000040a00c0002001d007103803540160400c00d0b8a6010300103a800c500e00040d9070440d6900d00c0400b540b00419520000705805034034021011034400b941d100c03c0c940c50082000038044401082d445580000d10742c4490800803030038041d94200c60b801c031a80050b81002c690b800611144100340c0601201c80c81e80e01c62100281241c0400c40150208030300f4041440b2101e000d400c02c942c000326030f0b00440e0103100c031521101e00a061002114071100801c03000e000081c1400c20392000641070b00002549403526280c00244a00c0d0148502106a0400f00116003156207141448040c80f042d544c407005882c809040140c0e40305403c5004a41407464140c1d00a90304415026255405405849050055403120001203480a00810f140104212410700303401034500d5101600362400740f86482060381030f8140025003101d1068100c01100700d038030008c004c1e4280b000700e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 495703453 1250 495702203 495702211
    0x60103140406200c07050915010e090c0d0f060801050f070519031b0206010518010e34020f0f340312020109030905090f040303050c043302070608 64
    0x100000f41d20920780002006612411400c204020f400145101207250010b403100549904413500044d07901c454200d180101c0e0800706443c00b15107010800754640c0342c404180c6600214a862480ca080419104070007150304040c40380001983d00c040900120350244500c076400320800314240f14501703101002600c00e0180c08413100d4800c401200c4d801c2c0b114030a40042c030a9612200f42c4507038038030840070003030f4468100b4001d0a0082000a00b031100c0000c403080a60304850f12250b030306095483d15080e50789551418441e69650b4040812031500c50b00442d19031121255050340038104540301e80300480c1c02c184580c1940c0f1030b16403050340e05406c2c2c99000c100b40c41080d940d03100b9124601c05290715185152440c0d40c8080d0a4540003030501a0180d01074006030172041c0b080d80e0380d400071070315501000640c0382c7c25148000d1032601da500040000e4040c2d0320054005000e84040c509103551400859082c0340381da241c80d20481d00c94121603d020064055180f072590745400549000b50800c80020610340c4018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 495704703 1250 495703453 495703463
    0x601080435070807060e030406050d051506032404270201091a04090b120a02040f0f0f0905010c0203090d0b060103091a1008030f09040914010e0f060601031404 70
    0x2041100d440a991070604652a040194564a60419080000c140d4200394400d4400d42e081083c03c1c0c07030350b8001008503006d5a6540d16510b04042c00502041c000b048020070b215007101c1d404445c841603507110b102461045030000315110034241610484d615003491003480314095800c008050303103001c1c410307210f160102140c101004061011800121541282c41d071004078010740b038a41030504815114002c00640302000c200340007508110b428426448900c1ca4101100e400120b5204018603043d000710365200300707468000c07418051103900302c81103900b00103000440303580e01c1d1204000c00500780a26415204240040c506012002011883c00d4180c51801851180b60324005074060b07001f40d004105054200d440d8100b614182c1c0044010440c007501e80d09109200341c00d0020711740c1c1c800011035081c3e2450b50045803c1010590901000d044043c504840e80045880d0604451000b4452030403050203007001810081d8a0248003400c1200141c4201c0c100350405050809d106e40c190b0049804c5a404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 495705953 1250 495704703 495704753
    0x3040b0c0a050d020d2a0b0f090d020327190f03030e060c03030601080703020d0501030624260c06030f01030c0e07050304080a03150308091002010204080a11030f0d1706010804 77
    0x1600c004c06c009000c502c00170f0086050f50140a00b0300b08a0030300d54412a00e0500300c41000840f1130f416a642e015550040d51040c0b01101c1c951000320201090441044d0054000c0c840491b1410001d14400c200d07410482d100403207280100b05040d44400d110808a400f501c401e8034003040d902c080c81e200d00c0010b0516040c05501c6000c540d01c40c0c0320760704940c544140d8603410011940c580c40c020b00034101840c0038440442c2828582007041810741113000841c1c401d14914100400c04050340c40300b00201000c090303a18082c5502e8694540c072844001c5110311584915a87e456046240a15154405c2d07040030401d014803000f00b29105400004481e0401c3d00941481d45031122084110041c0c005024a02d00800641710000300304001d9802911902a048801c1800b5a220520403400c0b40594030078201130b9444800120045084402c56917100a8050107664030241054001840d2104801100c40050020b1406415502c00e40141035013041c402d1030640c100341030913280c003c0e0100c415011442c4003024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 495707203 1250 495705953 495706007
    0x4120e090103172b0603060b1c060b03030702180106110a0503070201051b0d0c02090711150403110d0c060b0d021809010b040e060f0603010504080a05030903040b0c0a050d020d 77
    0x880070710344501c20340c005040404074100d1130700010b40540c1c84210350003070070300d001c076480d910b0700c0c50401c4c0780c25030624200b80b0800d14944808020700a03e9044503007501040209001503101e0142c081c048180401c0c02c4455549441401040000c0da080038440a4005000e500c00103000070048928468092a0a5898a0100412001041e81840c3d11041c920a244110000640040c402c03e012402104c560410b41c0d0784450a645019800b002c40619420001d952450301e20b507401e185400c54003e10344074500c40f04000342a4500308004107860007190b41c0e8003c52082202c1c40c01440c3d48100b0a41c2d07405949100f036804659080c08000d040340c864021900000c00c110400d40c088200c0e400f00034000c0c400b82c0f847d51603064850324259540c14001d1400c50000ea82030805005460003140e00010b400c2c608446040c08071142d0304081c0003009075003c10440000d500a482000c2c0400c041303454054a08540507180103460105044a4201990003011107100c2490300550b00c0080419000381c20700000e52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 495708453 1250 495707203 495707227
    0x606010f08091002070303050f1b161722080a12120b060a05040501081e04031206031703190b1507080903061f09060b0a0c02011704120e09010317 64
    0x30840180d100311504c007141000c00e06074190090b0340141c5002e40044415100c4040000b9240c80040001070510010050b05105400301480b2880060041642d0381c020050301d0f840d0342c1d25070b2040e501ca80101014000d241600b80118a0900046c12418000c0006995030340c1c1d0a1401c00400060000788030b80402c01500c0040c09821208142800078805c940c0c502141c54080c0c0250000e02400780013032142400034040c00980702941c4400c10711121450490b81d541d40d800c58040c0c402010304d41203103890307001c000300042980b018044000c8813021070640700d2610a00e10141202c4038040c00e40c0050030500c40c12125200c01030000700402000110a0b920452410a00c54610a03250015050b200d4441001100400c9800f4040c501744031040140c141036541344200c0a0310314500820461410821803804154044c440c07160006106050800306505010f60b03007003076084226010703a8034540044401d10100d038848003241c41c1c003400319040071155040d030320303810200e074500081820302d01d80024580800c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 495709703 1250 495708453 495708463
    0x110312030f01151e02060106030e0f070302090c120405030d0b090609061201142a07111c080304050a15060b04090905030c1b0a05040203130b04031b21020606010f0809 73
    0xc12450340d0304c100c0507180070081d5210007d00c01c00000900d480100710750b004002c00d20300d10714103803070004110690440d001c105107040043c15a40e681d071410000da800d82130032020010b104600690280d9101c1118803200010384043c0300707520380300c0d0000354101300095407900040c0360030500030345501d2081c1a824842c1401041e60310340c8955012010400c000e1108003901b00094444075104034500301c0e0f204900300002500810b84d00070070046031a082c00c042814000c01d503011000140c00c0307a82ca00d4106494000c0941e0094405a074a608105082c03814030446050003004194860002c110321803500203081414041c0b40191422103885010380f00c20b00c0810020765408880b0001550316222803004100c841004c40c0300518028010003600040c6883c180c800c4c1ca1003209801c0115a0801842d501d88581800c018811414071101c44005914000440c0d1b403907a08510803154a01d0030b65810b2030319801c4156600403e4110343c8036000b000780030f0360700c561304400c00b076001d0401e605a40c849584071400d007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 495710953 1250 495709703 495709727
    0x4020f0d05061903170f040308040305031308030412030503041a090703063902011b0309060e0d0e060a03061517090607020c0f011803110312030f0115 66
    0x581000309010030524440d51040d8010780c0210b85008402d83c07050901003202400740b201401c103940401d6600c1038502403000030540324001d0318031289070680b03a5031804841e8000c0d400a481c6a8404141441515940308140000e807060500940c1854605811481e0b80700070004003d00f00500440420704208035480030403c0d04045803424030f26031811403407040c0c0e141007034032007030712000c0c1410f555031041c40341c950058ac40c010054141041c04d41d80c0c1c04071080f03401c01a4404004542d60b0b502040ca1199540d82036480d18201950040713030f40c0c01c0904000d0b0942e880e00308400c440d60402e14005603201e8020040c0d81c0d580000352280d07519111020815030086c501079010400a40304d08040c2c3e00e5043c0d0201c41904c070036034081c110b45010307101e6440143d1743e0301e021610080541e00c000d8020300185440340c3c5886030710700145054844828481280c2042c820315500c100d0701f4039001c40c4441c8240c07506112402840240000315801e518040044078400301040c860801d0314a656201c0d441d01622600f01aa10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 495712203 1250 495710953 495710977
    0x16050325090903023405060a2001020d11030906060d080d0204081617121b0f030c0601060507080d201812120f0d021b0d03181e020402 59
    0xd2004074103001e51207811700501c9119445002603416680d15800740e40ba8800c4001d0f0351100b01d8141050300b13000c0c003a8407900d00038090103110905c003110007082d8022503180394003e40c000768035101003006540545461070f0070038140d0401402003002e80e5800103003060307202c041114071940102d014107040d4601d11a807030501400318000035020070b18000c00165203440310f040799009500d07540e80b07103212035507541d01d25a109280d810460750303001d032508200c0c00390102341c100c5005010020f105403082860030300000314100c80ca4202140d0400030001c140030160040c07142d418503d142414981c0c421080d07200e6240c40c020540c0c0c0c0c1c0c04141105044050014800c5450704041c50395900c051854002100207846000e0710543c1e241d5030345c01c16a5404210b207640007502c80ea00305e0811411031100f02075900f1250400d81074030350a1114584000c1407031380c103062810518010303100308960402c0c01001d03200030b486086120546514810300003150405102601c0051340300748003081406100040180c85000c0e00040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 495713453 1250 495712203 495712211
    0x2061201090b13141609080109030e040c03110409020f0403060507080f0901020a02192a14030106060f0807020718061409130f050309060d06081605032509 68
    0xd100041a40400c6110004a40210007141c001c01881c080c1c404544c000725907403110b0404103518943c4020301111680041c100f13a01e0442c0c407204964216000382205800058403941e904800d410240f0540800041628080c0191aa218a002c1c0c841c8100e1088007030f050360004051810083d05815a0003955000310144040d092581e002070180c9400d4641c52001104200461f120307030014404ca6207403000d00d4000e0640c602e01a84407030104400b05400340d9419a013203000600203904c2c16080b5901700d00d064030021903e4105240100921504407010307009030f1500c02c007031042c039410051000c580c119916141c1450f56404500300c2c24403a0b01d17440a40b503107821008103800c9480ba03070400c070156484811107002ca0a0580d0402c4141c1c04c0680e0710702c429a00380082c01e0003042e001100c01504602410440b80380c41c03601d0012880315404017181c144155640c0b58244001001401545182e55102010048460070310000903114040080ea0704504036034480000c03001e001c21000c0030000d042c0709030104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 495714703 1250 495713453 495713459
    0x60f1b0b0a0c020c01080f01090e0c090f0702100921020102090a0609050f0102240c07050a03080a050f06030706050a02070f230a030804050d02120307120f02032502061201 75
    0x2000b41c4040100140580602c1024a2041d4400c859152050b884a14000c105918110030b0000a0040c07040b81c10081c004d4500c1a041a101c19490300d01405510801034218075090000904040b4a0500300300110300300813040c400b25178207030300c240d9144400da0b41000e8005482441640244228903040d0b401103100c0e10001400c80c0c010039040c3c21140b0645401c0c0c508026940126160001e0030b100690a0800d402c0780007050110200702940052040b00452602c00151a00d45c42c00040d03410860000c0c0007281001600c40d0980074190700910300485d100042d0070820700080d03c030300703084c020603040040200d02c2a15075403003000440002c1c0f9079919411104c5840300400b070f03201090a00c414078480d0a0032500d00302800e159409800300c98020301d60a003043c1c241010030281c08251a02664420314128040003140c200f80010164144180280300320a045442d001e03102c601202c03400d00542d00240000d40c000384036440030010444000813901c07142e03071191001405030b000c0d801030420000d4143c0004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 495715953 1250 495714703 495714721
    0x40f0b040510050406060504080307060b040207170c0d031119030b100c0605010501050301051e060d1404050c0105090307060c080c0304180f0c05161401050c0d15060f1b0b 75
    0xd00c080c0c0f00c0940e02404500d80303c440c05d4030944918491030718513030300402a0502181c1079a0142c3c2d001c0400500241ca0100d5685400c04800300fa10a0440d410000042e0745a00c04810803c2c4600d6000d81e003024000340480300800340441c052101d980701d0001d07210700d40200f528460781c4000c15880000701111a201d028400003020018000002c072200b501c0c007400803403198010703400d8038100e5000905000c1c419480c0701884000c407405894a03500210103101c01c00408815008400e00b61010389801507140c503060078420700e040c45030641c2e1b81c140001000500040e440104884058440c203082c8104036401614240a10b841020b81c1a109404041008511354010752002403099040d1141401030b41080c1e031180c0c0c12140c18021210100d6130030002243c0081050010386030719805603002d00c03480c0b08410f40035425502d00b1582895104000100c2c0ca0145409100c0c00c0400c250002c401c0c0001420141c1c054440382d54100c210080c400d40030a60074907804981030f90211194041c4d5160310b07508044e400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 495717203 1250 495715953 495715981
    0x81005090a0207021c050703030f030e0109030c0b130c1224020a0f02030310091d0d0305090d03050603030f1c06030308060f0d050d20071509050d080405040f0b0405 72
    0xc0388175820b07210074038160180810001c0c20f100e4010002c3d18115185503010303651000d1401e02202070580f1209000e00c1004280714460403140203446500d008100d034603200c101410018a4224105507030803d0301f010440c043c640400f500c0c100300340007030a5170035410080c441c0640c680c43c0a0070b0302d0f001c1c0340180b011117aa03000b8040d1804039444921120144000580e10303030008454015045080c0d1004102c0700c40581c000d020034060070800502034042c0404002d04240c0d1041c0c86102007501d510901141410030082d107400741100c2c1c0780802860405000103a26445000200c07400d80c08003090f507403810010400c000306c92017104c24081040d02d68030314005d02032410441c2e602e0300c509004044003607a4105100c0105400742c0c8600034007204109410f082d942d80300b914003640365094004018900c003340c10000c9078090038000d80c1c6101c19003002d90380101040b10382c2d0020f60143c000030305002c0c0012415426941a80c800300e6000c21004480c0e15008001c0120f0100d46900c01d080100b405800214405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 495718453 1250 495717203 495717217
    0x160602160b0105030706020d1b1505090c0102030c1e010b1c020907051801140d020703020c1e030d0c0201051c1a0924040f0c091806050d03081005090a02 67
    0x1e0056950b070382c85080544660070341c0f05000250f0084c0c081d103000e043c441c1c000c2d071240d011035020070791b03044142d80c444a41200b444e00c40c41015650300d07001c2c4102004108450144402c007440198a89483c803d000f40d1100300b081c803640c481054144840005070020340018403416005018000c00180c00000d4001050308000c091b0b009a065801040c900f81c071031421619031044081c850f02c151079078103004650400d9002952207018600f845800d2011000c0d00041441078013a034001c10960800d142040b4280c070649500c0f03680c6412440e0520f01c191404200382000c205581020101103505000687c0c85215001c0c002c410402211505500f640c080c1d4001103491601c1d00140301862041014440303110410f4868165018001d2190420428824101c046444010744007068529000101605036544400c2003408641094414800c4c0001143d1114084080c0c02042c04880d24090101c0c5d6011510b800180801170083c0005020101a4400c000140005894205a850080726643c000e410804c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 495719703 1250 495718453 495718463
    0x20c07080f030a1b110d1110050903060c040e010e0a0905070902191d120f010c02010c020d0305010612050703150f0617160302030907080f030a030509010203090604060216060216 78
    0x7213070300c11303041c00342c59a84000a1307407140b4142d13080a80c10040080900780791104540c2840030841c1036086071100340e42204445070948641e5102e415400405003062801040413484803018082003100804046066046410004848003140c4458412001070302038844064114030400000140100f4281d0042076442d003450007056000415010490303415072420528075160f04220180021480c02c03000761500080413800311030041d4000d402c0d0500707542c003005458000d40d56910610280b01c0d010301030340080c420305242c10002503040200250400007601030807da402d0756440092403541c0a94000c0d0000c00c165008480e03429590500d240d010340182c0915000128941c3e08240513100c3c3c002024000d03d542d146102800ca031aa030201c3c02504010302c1140a40300c0c210002030414014170002d9013584c10348024590710940e10710040d045c0c0f6005010394034503130310420402002c0000810061b8105600030405a641c100d02c454180d450146141c002d428140b0018403041980010143c000c04070740b040d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 495720953 1250 495719703 495719717
    0x3e1011030708070c050a1a0a0902010c0b0a02040504090c060327030305060d0203100e0106141e010509100210050612060601111606030905010b0f060307050d090f0f020111010618020c07080f030a 85
    0x38818901515049c810090128030b070710511000164940d403d850384079400030001402c150740d0b5000101510041641941e42408100003880350aa1600803a20501c4080d00b400564045110503040c612032f200f00050201030341d900c0420f10542c0c0342c5550f1071040e07800400300c440102c6440480f4005251001d20042ca40d8078000002030017003c40d0843c8201c03aa80240040780ca2140c1c800b0882c803030280207040d607040150400c0800c0e841d0b950700300741c610000600e90023070588a00d480070800c00c581d805005144902c2c80300401440c05d40d030014000781c3c031180c00e107810016000c85405d00b62502850508140038282c0d25100806c0c041c2d0705038860701c41a40910009c0c04050365507402e105910179412161390700124104001900140a0303c02003081301192600014186c41d162603040c2c000b0000c8030b00302c90b9242c00c0c0b20082e0956900821812401048200811015241100c0d050041101d1000380c1e0360130760085815800c0d80020f000e40703070082c01150140c0d403009c14403082da00d0316544031081d850086110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 495722203 1250 495720953 495720961
    0xe10091a0f0c0708030a021e12010605040f060509150301090e10020403050705090705090301111803070e070e01120617070e06103e1011030708070c050a1a 68
    0xd400e0180100c0065080e940b9003910f6845010217580002c1810202c1502082440307552a95050810580602c03580f541382c8503e41e00070059001d44042e03011b4810001d050005100c02600810502c046848600f89aa507035100030003c0b650340d283d9401d82e400b070803001000000c3c0b00100c076001007000c16a0135040e54a50500c0c030b102d85c02240120f01000d02243d00001c0d0520460500e00344090300700c0c80c20b08040b4107000f620000030342940e0070243c0c040c481b01310204900010903210300080c1d20300f609c110041d207035850500d00c0d203080d4244010710302c0080000305d00251000b039008100604100b004028288141034441c10400c450341842a0a18010f1048a40001c0c4a00c25810200c4c05140c0040c694003005954444c1118291b032400904055400c03800300c281040000c08000304508180110900c151103004a003642c00c0c14030f1030410a480504202c3c0c10304000038038600700c0b036008029007448020307078079101402c0703ca8080f0590001c0041c42254110800d01c4030703021620341d54020300c160f80d00306651 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 495723453 1250 495722203 495722221
    0x81902030f03040303050606040b0304050c011b0b1b1204050109050d090e0103032610090c0f051611090106020c0306060d020d0210030209280806010506030a0e10091a 73
    0x70510780340003629001403011070006031007a00110b401c02c0c4014070642c1401e448030145c03032480e4400d45c1d08503402d5014070054001942c000305000c100c8008018503002c42c5c8141d8603402c10144000342413002c60105210800d51411201c425030b00d10b241c04103c880c2917460701d0719005000b40512803080e905403266400d40002181700d0181e101c20b45619581600040e461664251600003440c5002c0d003121010b5508545e04007001c080d503038820059a007501030050300c2c00c40b01c0412100721400c95810010780340d00e070b004115040411110f0011000449002d00d0045040203a8640090b041041d40010200c00000b00150700140d24110b91004406076411a241e0808004142c4081500203402050131205000903240103030300d0581c0428076040152415690300b0002c2c07002841c0c0e100343c0b10309100e0101040406005544608090500c07503000301400d50515000440782e00008114070255500e400c0e00092680341888000b40240c0658024031010415203811100e180c0003030106500c2050240018044a0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 495724703 1250 495723453 495723457
    0x2160302160506090d08180409031d0328150504030206010e010509070e060918070c05061e010b0f0706090c05101e0c0c0807080a0312020a1706040906050408190203 72
    0x42c00202045c008000b156071322201c0742c00c469000300105400c41d8050f699600c5a0080792040307880b0b80d41e0180480300c21400c241d041c0c4210703440d440c02030f44080c0c48002840382c050b42010908009402d0308100881ba8541a190400d03203912645045017400144400c142c1c0008006050f0340140400d070506a0704c400c1807003c130b85011922200040c200c500c40040c9810202e0050140a8000e0312183e561a40488500000101a107903040003e141710b10a000b8060144041030b008881c0084003507a042007172151941d40c2e0010300596035103100c0040e0700240b040c9131808131035070907501003000d0203150032900b040c915440040c481c4034041e40610a035079039450b00c14000b1a00b0100340c08001501c030a5402c60803107007103d001d40229400d25004001144242c41086690010005840201401c103440d03d00107008041011460707401c940103120a903034154014801c1c600880221841080d00d5417500000b038082d18120501030089450543061006204410f4001c003c2c812250f00011b5140480c101c0481c1c0d24 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 495725953 1250 495724703 495724717
    0x20903030a0f030e060106091805010e22210f0e0108041e05060906041101090b03130c05090403020c2b060c030603140d0201051006050d0506030102160302160506 71
    0x40d001009000403a9000d8495890000e00900d0000340f01041d50701c0300c514015003a007145002c9074441604002aa2400d19602d240c500051418403080d4584403c0c101d201802034003280b00925034000c0e41c40c68440c07050303558501c5600141c4202c07078400c070341e00c0740043e58055942080010700c803104520050790244401c2060f59806a65040180c0d0b91034070780c10114900030308400454010000305a000c180108a60b40c012981c8401400081c1050b02d0034030048694400c0b118144103c1180c02c000d400304400581ea4803104d002401c25041c00c0741e01d488014a0880e4201c13581c07084003081440245907001500703031a2202c0c140c2d1488400d030044030401c20500340703d84c01141e03a1381c0e4200c0d01a00203403070780d044400f180403981004250385491707954403102c041c036003802150654008500c1200c02542402120b800c605a00c20030010a030500c80010035610400c00c002800b9902d820224078161001d604640c1e92140010f9541e12614092800949401e400c565041c0c40d240d0701a40443d0303501e8290119210 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 495727203 1250 495725953 495725959
    0x60612190507050409030203090f04060602030301150c0f240e0d030e010209060703170606090d02100207030212010212150d021311030a02190311030112020a1805100602010209 77
    0x103403110026a40304180c0844101c1d5203001d041030004090301c95016152503148290061074480c4d105ca401e2004075140c4092481c407507818010304211464010007200c0c1950b40d458042e042c0e20040c40030941d000303104540300501c00d120011416003400a0f00040c4030b401810055182d20b0703c00c1401000c41540d070708042c040441d4000800041015009034008200707a00c100300093f051040e000c000884035000148203401103600503070802c0c01c466100c203031075034020004c803081da040520000220f20b0842102c1002405110300e02c01411649000700040c0c4025075000348401d84014802c40040c2c040d4020300b10156201e01e84501185560001500d260407a0301c010704405402c40c029000c02c49280900ba1504950302e9031094860042d030480d10081d441642d4102002d070f511050801c0c2034032449100039801c400c16103040c0c46551460a49000c40741110181c50790410040f00f503000040003c1d9032503111641a041d4103a40c045501a5a0006481103c00d50226002c06940f140203a080c0e1007848036080e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 495728453 1250 495727203 495727213
    0x160b0619061b050706231309020c01020c0703111c05030d09140d05040e0702060613050a110304120305060a062703020d1401290607110307060306050102060612 70
    0x10052140c4040a4040c4a03039004102c0c010182d12094105120350b001140041c448900e500d1818084980180f8001c030301c5451203103024419044624151040c0c018901006d4002500810500d000d4040d540c40401c10740c2901c2032030340e60f454100541c14203038540c58024070402d40342030142c404c5901d01500454008000d103241c01880c0c0c40e5003000b070001c900100c40b41c100b2903002d17042001e0700300042d813030070310301a10381c5940c1d10300b081c0400040300002888130b02107501c0740c01002420f48485c01515204001601e000c940380d180e10041c2005030505800c0354884540100801c000c0c05180410442c02842c562030404c4aa00d071642844696107160040502046296421010902180700e201d00c51282d4000709200694176580000c1143d0301f4040146d56105030028412106103080c460300f8003507426a8000d001642030140c01180c030b221501210707480303010042401c009001d11503c16030183d00008045d202e141d503c40d800078000f0645402414014801d920020f101401c2821013042c800d440300d40240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 495729703 1250 495728453 495728459
    0x80607211a060310030506010e040c0b0f0d0c0509181e070512040c03021c0309051c14011515020d052a21090301050c04050a0e0c0c03160b0619 63
    0x480b49074005000c0c10204c0c500000c1c000003003902400518003820650752100203d04160134a014810b615801021340e0079020415034461312111004c44a004103801d8010501c03000b150b005840a02550900319040100c40c0c5008801c11100300b900b610400b40c240f2600204142095170301c8201408417600004034404120844404110b004c2a541c424072640405101d6504c036170104a4100d80d40189581702145c0c0c2440700c04040c2c010280401401c0d040d1014820030a8010348031034410004503000c1c00862032a560000d1500080d0410105d00a0344642100d407555900a002d40d092322050210b40140502c40e6480c0b0214030400c00c5850070341c100000b003002640759001180c0c10341c003164800c1d1014030650035134070b500000c42c009010b0802c070001007aa88403c245000d041c00d446008008447c82441044240060354644410105483d50141c240519684a400d02d880502c20001d1101d024030010551503480c803114040c03500c1d800d00c83c1481c03030402d0301c0e10780a20100d40310641c41c00c0842030b4968424 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 495730953 1250 495729703 495729709
    0x12050f01050c09011d0d06020702040e0d090603020d060e15030706090f142706010f080402100e0d140105010504111e0c03070b2d2509080607211a 64
    0x1740e402000800b0b4082402c4000e00005904143c4060085511980124840040d0b01c0d1503c034080b11240b8441c06826807004401e00104440c08501509080c15804501014800d010340e02400103054015040304640c2002403035208640c00c1c180c400c522a100e04d0303a000c902e252007110050202c4000c034030400812420117070312640100f104055543c01085079009481c900c117181e42d441c4544a00703071035401d107039080035800144031260030a00d19060088100504c401601d9100c0d200d02d0740809171a00001c6c4c4c04084000840101401c00098217160202090303261111042d44120304a8108036402c0049030000b400c10902c0d4041d040702c08552000c402c10f4480c3c0503042c6001020000203220640386003035407556400030303e81c80030b540b6483d070b0f00700007015080c0c0344621102e0408080548082005145800c2d00034124104661081c4c0c1c0e80e2142c244170300300141e80204414030141522500755005031a14440c02022400e0320005070030602200d441c1c1c280d0400c0c0c41d114200090082050220300a0408014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 495732203 1250 495730953 495730967
    0x405060c180409080c030307201207150b030f06160809030a0c1e060204080c010212180a0f08030c0c0a210807020a080d080906060a0509041b12050f01050c0901 70
    0xc02c0d68040b1301000100c0030694140000c521904054891010b0103400206c60394540b0021300e091070301c5901c0404154492007859003641c00181d407005c208a4403240300f10b10400640b1818000c40d825201742050510141004640c0d6071007468000c00e160a851a00303102150b0109064805001503002040032004180c4543c401c218058051402134000d40150721014240511018040e158603a0200e4184510a42031080030341c124030920013040040d5401322078500a1142c001d45000c41c0005101d64400307915508002001001c5e48050002c0050351020074039282e5209540b04449805a038250300c55a25011500c58161120040e14881e44203d02c640102c00c80780d0001c044d20314000c04d202c000010707941d42501a01500e60b9402400399100c400341d01525161016080020603040300c003c00646403594030035402214000c60790a9000d80b5903061600180315820700b960b0f410b02c201c20010030080b015080c0d4045042c8181c0c200c40030008034000443c00c03034100b61102000410100911101503108401d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 495733453 1250 495732203 495732221
    0x804050d1a0c130503121606090f08250302100c050403050124090501030206030a09140715110a050616170703050114044a060405060c1804 61
    0x8658009004910280070003000448041600790400180c038020038910101c203400900040c0e00900b11034040d5002d02110707000c0d04201080c00303010301400809001c0d140d000440d8680d00401030545070710890401c4480c5900403040740d008012540402c018030b61840540d500840d8155001c1d1403c2004403602c030014280c1d28034810100801800301201040080c400d041c0301c811105203030800b501140c01880c031900610750100346810310341401000585c6175201203039441404030b000010100300354a480071040d204207108200d603114202c0301180000b45c40e40c0d0580c2c2440d1503141d01d1940104240840d549852140c1c1c0100690081c0020034105042845240410305040c00c0c00818155038942d4141c00940441d244030000f91200010001c0c0005002410700d000f2081d035090082410100d10b0240200c46a4030041e002100540a06840707505035503001004103440400040400709022032582e101420f480aa545000b00d86c042400712100d8822034050310814003114884400590400000b13203203200d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 495734703 1250 495733453 495733463
    0x1203151804120318020a09050115051e070f060e0606040b101b170c010609050109090305030402091b0a020a0b06010c020a0e060312030a0e1c0905060c03070203070308030a1401030804050d 82
    0x844c602c030041c0e9030012490081c001110001456601d040d841c01d11180300741316018180003041040d98030040704040140160050100c0540c6c2c0ca901c01c1c43c0c0b110855402c0500680600d151003c0410341c42c40c08039545004410850701070044002e1041002140101e041040d800f01d04550390742444d01d080c5460510046008000e0360b0141000110301c8030aa03804100700782c0ca113075551402800342203082d20542c5d000d481c042e00200000c00c800d40c2c0c084c00c244005000a132003140d1003000110003c2e54454800c208270003c184894030349001141c080c1da41d00c4840c43c100c0c2c071560502c0000e01d0b035500c510820b04650350000e01c00001c891408884d4100002c02610031a050301810110556010040700150700802c7c4030b80c400107c3d101e0166084d400c160301000c81407426072698000201540c4d0221442c8107682e401c4844640e54010701c98160b00d1031040d99030094141c000d035a00001841002e8000e54841c0090000c241710400c4580c0c440c2010403000d000044c46a0b00c00e01c0144010300f804c05c514115140f040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 495735953 1250 495734703 495734741
    0x109090b04021603050301061404050603041407050604090609050c192a200d0b010614040e040f03140403080f0d020d090813060512011712031518041203 67
    0xc0c6075041200b10401e0261302207080080100400c41c2d1002d0700b405030050401d1243c0c02c040c1400b0021f1028800584080c200350854161060540401e00c9118000d11004000c20759959644201300064442031142c442c07580d14120004d5255292101101c460181282281450079141070082e52544c0c41030b01d8007082504440b800480c4600e161481000e40c2d401441079050040c84034604440201c0b84a10711805815503a4a4100064102621034191151414200340760281005a65020701440d03002d0060441200c0c180814484210304004070b9601a641c5c110351480200900e00191056200092100380200401240a030400016041007003001c01d016240884110380501a20181901980c2100000400464814000241034010081d80c18887d00b070071440e000300e02e1100c5051041c0d0f01440300114051054990510101200211014841d601c9040002c14a0802c1040b105920301502e4104440321301601c00181c1984592360103001d24a140540c41c9040707010740048120001e101d10b40b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 495737203 1250 495735953 495735967
    0x30c160c09141006031401261510050a0303080f0c0c0d030b01201507051225170a09080c010e0606091f120312020c0a11040b0109090b0402 61
    0x6409040c42020041100b41d845080881506002010a510074014035181c03c17003404184d064041d003030781100c4610068040d8001d90505401079854041d20390b0550b40a0401c442032418404e101c11402030080d00900b184040d11042480500005404050045014240010044086590f550750710020340e07020f003410500f0b0105c600b86040c241c0109800030a44074500c140d000e5a000106503415940324003541c0c40145d00d98101078541030850090860000b8540000d00d001c0d00400803981c0d54409400e1040702c5250010800203c0103091070518921b580c840c500081d924403520550f4908103c03010a501d094035481c2c1d50b00010101a0700840d1182001c3c002040004402c2c0714505078916064098200d0345004000c2024a60000303000151079a5203c1c0b60015004000c0040c20070380f0510407100d2106074280c03d003501c1d004002000d101d550b41c000a4003100004c0003103100303100c043c0328400043c07081e40e0200801c02a128a01902400910190002c00881815070401c128004002e080180b600e06 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 495738453 1250 495737203 495737219
    0x3060f0a0f0c0f0e0405010b070204051f06021608071518030b01121a01030503040302010513030204091a071716090308030408070b090c0f010323040b0a0c05030c160c 73
    0x3240d002d040e010031000c0b400e42100d903400c101c1000345070783d04540800c02036042c0304d448002c030f000364003019008641e070324005480003141e040716910b514500800f8180c0e40d59200c0009640340d645204003110034150340d80002c3c20359000500c44003500d0455650b502c03c00a640b40894013008032455031089410f1984000000c0f03160745401501825130004460414803e50422990440e0f424a607042c405285200410200b04040241d40c140c0c1d90928001e903480c80c071241034407000703030035600040d41c028600404d120401c544142c100d0b0043c4007150000ca42541e60040c159000c5503510b0034045c3ca04103010000381102c080340c0e00e01c5a11384090030302010300c82e1240c49409098004980456284200140d035105000c1901512584107141000034048a120400405e03083c4202450716814941c6455808052136415042c442c0c4044001d1040280e80ca414204420080025035088407581c1c904207800c0a681d11a40440e40700f40d0190100300d203860960000800c40205001003915100c01200700860040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 495739703 1250 495738453 495738461
    0xd121b05034f0605120a151a0702092d0c0d05010b0c0c06040602031e0c0303070c0309080c03150703021207120605040c0c140304120b0906100503060f0a0f 68
    0x2054502600c002e0095016100e6040c4400e42140051210a1149040318402002450351110308002c0c0407940e0b204120400545003102d800929040d20744218020b40c0c2c1c14a90042c03c80b00f4003ca03030409003511a0f910800400241c90314004000020415084249031001c024075041200030702a1458288490501070841e0000c0c0c02c11543c0b0900000c00015180e4200060301846408940341c40c42e180c5001c030041c0d030380e200b008003445c003640d90010031841c07882100041e203040c03c04800641c0d569140031b43c001096030b4035002084000c6120081d021402c0700002441c01c1111101800404014225140b11201010001c1c240300405808200201c0106400400b0901503c0359032201c0d40e5511441d401842500d0b0f0325001140151318041c01e01c8000c9a10020035132550740c00180749001d050062600c18110b105a030441c560300070314914030a0820545010540c0306030306a005807081034a0b20144528446094814540c2c960320403000b00b050710012071085074001d0000c2100095401e142c0007913078261 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 495740953 1250 495739703 495739807
    0x3080c010e10090b101211370501050c07150302041710060e06030a020105071e080c24041e12050c070b0a0203030c0c160f0303031b1e0c020d121b0503 66
    0xf98194103120b1b442106075201000034010900f41141468150b4680c2c4de80ca0701d01c0c2c0b02d04c40001c00f81800c00d075107640c080ea04440c050545c05003110741c031560001d016a44d4044840c03802d2242c500d04600058907100c00450b0030b0155000801503c3c07130079440e40044a654020b0170081d030f481c1c075819001c009400e000c4440c00c02401e01c100c10300c5840e020700003000360400100d0103640d00009001680c58564842084032036922640c450f240c040407a003032003d0301c804402c942070001c0c90a8003c81000601c80c0d0040041d169040e0b40b103044500150b1a200e00ca00d0902624020602590041c4080b81194030008013411045144604a03642c4196100280e590008240d0001032031b2a0381d1384042c002d05916004d245011350026028455101a10301c2c000e00e451050703805080094100404444298881d54010022580080003003d040703020f03040c42007100c43c0801203000802c1031030701c81c0300403102e940444044c260f400c40301440c1040e901c055009405511005030700c0342d460418140d0040f00048000d14401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 495742203 1250 495740953 495741019
    0xe0604290a1e0e100f03020913120201020c07080111070303050c1c09020112050f0f0712050907060f020d0e0f060f030a0614031603080c010e10090b101211 68
    0x9440c40d100080c524440040c1c031500340304184d0300e0305111501c04400b88604803641601d1222560780d4078112038503501030100008250601d0840500c1406a05402800c040c0790310805a41d03001350380300c0e0901c0c2200d506802500900b1404e211001c0407c0c040d522181e84600384002081c50940001c04941c2110010f4020b506442e0f0ba503004202075507406041140312079489079080010b0300300044202c1080e03100500003a05815020700040712180309580c0d5a030440b4000900744482d041c66490580c071540f25018090010764400300d1203030418800906040000b9468503464403500f041c0050052005090b166039401c007a0400c5260640603261008601c60500d4000001d106d0303003040856610300900c5e42d0302074820360084030180c41d03949290015104595010010b5035803040700802c028003401900e400c200f02c50003021120414a00e064110070525441059240c115517120b00f140d400d00045401424041180b0001e8140056165071800241c042d0040616200c110729041256a690801c010014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 495743453 1250 495742203 495742259
    0x606121f09030315050f0f1f170703050c0301030f0206120a0f050903090f01080901090506130b070504061403070201140907050a050d080304170c010c08010e0604290a 73
    0x1407503494800c1394061804016043c0c0c01d1442c0c4000240850007188145100f005680d01031130641e070f18502a0950303181031542c514541120300c1409032503400440d69000701210381200150100d4420700c40e003882251040c500c1d50540e4290f4450312122180365804981000c0f080000e500c65a5400d42d503070340304803079801000c034070f00c0410b00b0090f007500d501410050702c680c418000a001641c0d041e042040e400d0003031918041a944500209000d400d10500142140c0a49020700c00c803086010010040795000d10607014498582c180304039075620a5100340400241e00380100300001c10000c2c021a001a080e10003c24115405068102c0441d41514400143e501000c0300b009141800c80002004241c12a00d041d000407075521500254480180b0040c5092010031094040581c103c064034640d1141200801c402c84410ba0043c0c50460f003801610130b003c2a103000150700d0b20b014095400c0355220a858405c0406440b032805e0f644045e00416a684800d041102240c0c40c105185204044075500000403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 495744703 1250 495743453 495743471
    0xf100308190215010806010b0d020426061006020a170909090d0207120b010527090303100510020a120c050a0c1e0f1a12090c0f01110606121f 62
    0x1030f14122000580070700d194540401000209004180d50341140c940815450340d600d49691010000d00c2590843c3c9204403010013030918803441d54036801141c6002c0c604488403500e4900c28504202064451180180e10190306240028060703402007106a0043d9038050078640c2110025070728101c01c840c020542e07844020301c031307902c10340c100074400013408010000000c1c091140c9035000902d005020702030140c1c52a00e0a02440c0c00d0006004510100040003a403884c00c00000340b035283e134415104200c00b003050000c082903a280c8035240d60500002a00107254218456030b4006511010819140911100c1000b540c040f8001303104a0140174401c220102940d801c0c4140c0c0c00500c0000401440d4201d000d180500ca11101740c0e01080944194040c14480c103180301e0001952481031901c01d4050f8010102072000c0c082e00061030905502085980400c008120340045826048001285001360301080208040342450424a501c4640550665251156022142c2664a410740c920049039650304000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 495745953 1250 495744703 495744707
    0xb1206182239060e0307140604050319020405070e030606040b040b13050a18030903030309060921090915032904080c10140a020d0912020a060b0303120f10030819 71
    0x10405403c5600303141c0c0c0220020404286d45a0710780c007803142c210074007203446000c0c3d503070300b101b81c03001840c0c014125500c40610060f041507000050f0b000701c0c0514103001c04030301402d001d2100c3c24030302070300600100380d82d6540e5001c00003e04460071786c0b2a0841c3e0341e062140703400e484413085154446104100400c0b2801c00300c0600d0100c0d130401107420041590b007200c5400007030344801d502c801c84e501403501151a51140c10054028640c410004040110481043c0c4c60390381c081c0203404c100c2c00161a5110b10396640e170b41c54000d482e0b01d40320390051114192010310019000030b02c003030300400c0c650441149101035007044c2920400265001d54640202042c60507503407408101c045e0011913034000501078002c1c022450701c031a84c0081e000c0031503640c0120ba00c80c484201c0d64440d91020b500001c040c0100540d450307029440d40180326060354460700f041a01456401c0010071600d5040f00c00200e038020f42c1ea40c0002c82625640a0400c10414801e6200000802c081700007030100030b40c0314103000300c0f00b0919a0700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 495747203 1250 495745953 495746063
    0x1120213032310050402030a02090c09031606030c02012d021b03040e09030909070834020106050a140405070c05071e060314070f0203040b12061822 65
    0xf00d04080c0307080c42c0c1000010b803000700b4201c034500d9042d201d001c03c0c0d8998141030105802200032580e0148141da00a002a031045e2400500701d0b0f040e91010403405400350422401c0c1c03981d2101240004000080d46c400c1c0020360806c0d0414101030800041c10503010440ca500744295800d03d4840303692001c1400d02880750b002d90b60079000510800114a40060f02007c1500444001d181c0e400340803040d000500701c080624021030303d01d06486000b07241e030000e210380d0480c102c810445002c0150301c1c10f20080b0352401c040152030f060350030491402d0828203090007040054030004201c14204444001e01e040081c0081008401071b02c0c1e13500e903902c003034502481c200c070701200aa44000205070504040c0304400200140715070300504c0078034040080c2280100e05a1440c85580c0c84048140c4d4001030070382c040795041c04101e000b40d00442c0c8840440819000d800d424003070a0b140c4010038203440880000c040d008030701014950b4868081e1141c10056400c440d4107101d100700c0c2810140640c20035940c4403c134040c40b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 495748453 1250 495747203 495747223
    0x50a140106050a080c091c050d18060c080a02070f030507030b0c030705033103030b031020090f0411030603010e030c070e06042c07090203010302011202130323 70
    0x1030b20340e050403c5050018400c0a0261000c260f5503800203e010554941d100305009481002c242e510481e40b03140741c419a140c2054602c60001400e9800c0c009015041101c01d42c00c60f5402ea90300250007203642c640b2019588a1030f520804e42c8201240001c00e110381c44c10749070046004401900c010ba185050150529500030038901d64000300f003003041000c64002003500e80206411a0010411040706506e01c0502500929050a104500901002c15500d50402c501c0b0110a5003980c0300b12402c01548416100410400402d009990700f6200c900740020002d40009030000f0f002c8020500f080001c10122004000c250000b41000000c11503103080c2402000100d104d040011031900308100e80c015190541d601a00e84410041c0e0013003842d6039a030390040040c140076041340740303074070b0715943c5003103100f504040d10119507405031803000200c2d281d0342e1003030364100e94060312202115105007107040000d6009028080c44485006404804500840c2c11900200030f258a00041d44840342e1071a40b400c82094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 495749703 1250 495748453 495748457
    0x250c0602010f11070b040f02060f07051b210c04020a120b0f091302040905060a05010e0c0301060e01051b1c03060803041d041e0c18050702120d0b04050a140106 70
    0x6503c940000031035021540c14135000122904580c03210b03e0700c0542d001072200003a5120501190f4460400301034070052620b40d110724200e031420841501507402c010f8850b074000350f1011442015545d484d400e2403000184500b07413410745068606820004003244c0080e000f660009600261018007980749200d50000755030200e840350240005200000d6510800400b59560325000c001d0b008215103640e0049580d0070b07440010b4801500d060b44c0c0d004010a4240300f151581204507000c60040300408084a0581d402640e4103461450b0300f50043d10f05520254440402035415100c6101c2d40b1360611103001800c0582003203904c8400841e50040a035034140e0866145a04200020882344201c016003c0305c0c00ca841907180c00540d10fa041030404860b80710141400c640034102c56100300039039020500282e8a650383c0500b41e038807146c10b158003216021a180b002582c050000030b061062660090724010705e80042c007103400400302002c5030135102c09a0b5104000c030b849603207802405d030401c1000c60141c00070b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 495750953 1250 495749703 495749711
    0x213080d020d0e1923040515151801030903090305100518011404060903090302060c1f140415060b0d1508061003032318090f070203040308250c0602010f 67
    0xb040c561282007505c0c41030714201d000550b01c107131907828609000030030003900520070001d91405c4520229203940b0885140e102d00302004410324040300c4981921006d0506092070040e000705003006400400807440140c2c00d0000b940000400500c0401011241d05081000400c0504001c810307144032a1010001d018241d0600d030304401240d6840c44a175030f22a801c000080340c0c1d8402ca003802e0b901100b581d08040e405c43c000280d81c40c1e0030f010002d0082458030069060201401092801c0c004035600240d03240e494171600340c04600401c4607424022043c80e00da003000a101e91b0f58540401c8103134400c04880014546031200d00d42d4004102e4106c00007000d5040181c1300034900200c03100c40c4541c080c0001414003444840c4c411038035560841c04030340e4107002d650750390b6500703116626a040e00300c2d00c1c51071074480d04074000043c0201d5503a100b81402501103400841c100b0b811176a4007010ba42040c054590042002072003850718a8400076105001c502401c0014482d034102600282134420b000c04910400707040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 495752203 1250 495750953 495750979
    0x1050606030105013e160501030219120f0e0a020a0e0132090406090219030b070f020309030106150906020721020f03060c130f08100213080d020d0e 65
    0x400c4150040c00756600007800400300050b19a03248105403000e0040404d201c0f042e1520700400038070203802101c010680c080441c1d47d01c004409038440c80051484082c845400c01c0407440c0910000345505070001c0000c42c0c5007203045221421100c4c0d60134540d2803648000e04000c154184505042c019040b56a50400c482d81080b00d1001441b05141c98410300c003842031106004403d65540f081c150000c01046400c007804c2034205200600003640d003d074429a4070b203171102100e0100170b40e41d0040780c0e481100101c19a031070304000d0310b10174007041d050029400200702d11004d80c0e80c01e104001c0070b1702100040003010724801600a041244540142042d035006080601486040032020040230441480f4180e4181041c40480d401142c1c00c000c46405200b032006108030840c03148090580380d000c00c40704200702e6a0361100402006068428500c00d0b800076000c41c4100911900102580d2080c89c1511170010b0380e620071a45004a80040c480040e080030401c00e144652203d201e000c201b00450f0708044c1054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 495753453 1250 495752203 495752207
    0x9040c151803030c050a05070e2d0109020a1110061a04032a08010e0a050d0c0b24060f03070e090105130c030b21010b19031707060507030b01020105060603010501 71
    0x80600018007800134407044d1904009041003000c803800c0e449000c0c1d800d80359440d07440048402c3c090380c440760703603000101c06081c5a01203000410b980003004c40b04d6107280d03440d0800c42002540454034100070055000c6211407100410031031000014041080040c81501c1d18a8188420500008070380da5041c00300810804034001d0b107030003140d24035140c0808171f0010300307680405560001c56111003e00e508050b806101c501c4082a0718010354021300a480300ca240807030040b03481143d05140149003610940204118060740344074500642500c080380305c01d100814000907041e40141d480020440d40000c10011110351003008410740390340075140340e2070300d505000005440c0900e6000242c400d513500c80c840c1c8a05442a0005d402404001c1d01d003807034034103c201c5044119000b0b1881c5805640c00d00d2400d0400d81004410004001840030302c42100743c1c110794440b00c0203202e210040c141d14106020100115815100343c50003121640c41c0061042225000a429030b800242620322505040c80100001d036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 495754703 1250 495753453 495753497
    0xb070c090e0604060c17090a15021e0d0b03250504050115120914031e1305010f030e1203090d080114040c0201060e0a0603051006030f1103010b09040c15 67
    0x95070000005c00c0000c48290105c603039224213060309507601e20020510800c4400030a10030942c2e070140c1110080c1d00019020350003a4455030f24503890054100c0503d000d20540d41c0040c1408481d06c11001c40e000c1d901c900080d1404c0e050030620344103601c001d181035080d804a01000c2d0001c0006484c05c0c040c1c2d600d00b48440d80080031f61000c2c01d09020740380e0364880005d91a5400000c20340c1d880200c11a0982003001d1341587c80c0c102c040145100c828101800c0b680291090541d0100341002001c407105a0500c2d0044841d02e90b01c00f01001807540b9890144130880c014800f0b4401c030800c03080c03015124039101c020a854846032200395024020414018443e1035a15804518565010307070f00854041c1c80c0d02340c00c03070040400d41c2c8412002c2c1000000d10085030095000541142d01500c220746d9010303003c0c1905422614507200007007604602d091044001a138111107a808403000800014141040d0380201341e1440080724115018103417060140485010700c0c81e000207a22840c0b800d9000f0a00859554440e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 495755953 1250 495754703 495754711
    0x61b020402030717010e010510081308092427010e0609120a050312071d01030c050417072405120a0207050a03051201060507020603070f030f060b070c090e06 69
    0x900e8000000480c2c90340144c1c400d42288603c9102c4513035560707582c406215250310030700805100d40000d060328010b6621038112107002d0803007120840c1c500003c03a82d90070115441ba40c1101d801207501080c1240c08208060030070131f01c240800e4004c1d42c55140c020070b0f4410550540341d4051505c91307007d00000a0b680000d1101000c00240c524a5403241007400080c00f000744440e000070648075104070780e810401c0100240c00e0b0442c10034801d80f26919008000c0e90b5080700c07403905d10400c0c040703140c0264840d0b209420101e1b0034626814101d1509807281d0244003001d00080c5001c40036071001408000d0b241c0d800f8080441a07601500c40841c121007080001d01600c2030a5071003189129950104041c400c1540c107c44001ea44442251a040d0041c507002c3c001c0d4001d01c00760106904440c0c00055068000c008680c11103500810140c03960355441c0007a0b40385d1400d084400c04040c1e40e0f4503164141c14003485804040c0c4641d0000300c2c0c440050386410040c4144d90740000c80e04505100c280701c0012000121079400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 495757203 1250 495755953 495755959
    0x60c0309011805040c0207050a09020406080408091c03020c010207090b0d06090c080a0c0f050d1208090106080d11070f0815070c170a02061e0703090201050913060807061b02 76
    0x85102c02c0b002d04201d89240380c00079030b032161800c8200144103030001014403c80700240c420060796070380c411041040b030107280702c0c0300f000c510100c0000e00010300702c600801601c1b90007050300c0324582c608a0004280007100e0b40031000b41c0c0c86040190304543c0c04204804c010b2600d10010b111003c240d00118001c10b00440c401000161038080c0141000083e01c2020041c0100303000b11003c041300c074100f075038104525116210070800c1c0e00b0700124040c28100c0c0005d0100380c002000d440220403d44048441500c010709080e00c6540c3d801021070403d90034080402940c03001c4e07803514440d11000c20f0700c82c1482c84990282182100c0614100030014000c5860040c03021102011b10403591003d400b034490344005100100803444c41c10000c441c0c41e4032880906111903181c3d00b00c498075640c02680302c41e49628003401a888080d001e001440d0544aa009030041a20601d0802c0c00c0170600d0022990120440410504c40ca407641c10a00400c0c40400850000341024034014000d42003150010000a004400c0640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 495758453 1250 495757203 495757217
    0x100905071511120703110111070f1a0109020d06050a031e0311060903180103020a14030c0f030411010e06030f16050c0f060a11070206030112021c1b05060c030901 71
    0xc0c0180c0254840003800c0006000d80f1484200c030f11a544a82d44003010441c00f28044500d2070002400500c0f401e000388a01240d03845c03410b18640c441c1d8046000107413013110a00e0304450342514008019001358020706450601503200c07145400300c00d0640c1c01075004980580210101080030409003071200140301049030000141c101d00342000c848008280c40117016521030041030020710795001000b4401c00b50400881c6440c0c1d014038004505070301ca03100c030a000048074060311004c2c42e0301e0034004541101e032030551a03140c483d2501403072810b03800071141030710b807548090010071043d600301410880b0a20200c03110742c51032070840c8030100000070141c0710590038000080014a2a4025000c50b10382042a40c21611944000b00c1e28035504c1c401118085d105070700b04107620b900e01d40707400183c401295004003179508580c2080400b1040f8540c5007016039004081600111303884084620700c0f01c444d406030149980d8950004c5042012070015802940030380300803c200b001c8020040103030f41c90f483e02440c0c02c83c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 495759703 1250 495758453 495758489
    0x204051b0306210f060103120f050a110708070e0a1103160305060a050a0308030405070812040902030604090c1e0e04120813080f0904110702010801050105070f08040e0910090507 78
    0x71141e08a8080c00f041c11301c0741d0350040c0c102480c0041d450b4106d03403088a00e140f0b5031040403c1110f8440740f415049001c92018012000800d00914400d0200c02c0184201c3e4403035039440e030b161840c0400c0ba91064070b225051009100150a490151469444600a1031441c50400c498154950809440010201a82c030030104501da902c110b40b841c01081d0051400d030b041c544074100110140e01c142c9040b0b6280c410319800144a01c030102e50038007030720210311401781002e00c1d10504c5800b942c401400c0c164450380e162008000030710703550002005800c0f0581810090000d02c01c003902d8410103070300309010060000d803c00001449009843c04500c01600d000381c1c0075154851204d03071151600714001d14001c2d0100e00ac1303041c000094007600b0b00712400c071018000b0150021182c00148522180640040c00c0c0c2c0005008950042c0c0c01030590701c0c41054515214000340d1100f407600e4025803c20703a018407040d42400751040c410003107071040b148140404c0015a4050703440d583e40380c1c500d100c0d2400344c0101c40713209 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 495760953 1250 495759703 495759739
    0x90d08040305010207030e030105090615060703020c0415080d0e130209031c0f0906180e070513030b01060306140a03030e180a05040302060106080403080712090812040204051b0306 79
    0x40c40046030310200940d1076100364640909600c1a44401078040d600e0007002503414070001440502071410501c2034005443d0030014050181d00911003a002e510604e003480c02c0a841c4c03071207100c007140400b00d0b8445107181040165410140c0c6d00510a0410400403003c83d200c1d03440f00d0b14422040101000140d50340c8206000c6820300100500c80c04000809507100ba4145030800908800c091032581c8500c500f13074485100f82e611102c6001c21407401c3c4c070420000c0c070100c900612480e030080400e042403414500c102c4495400a00560000c41384420241e004000c03090300340c001e407400f030700203040f00310b00c544d00260108036640300c244006020000c82c1c040c5e400190f20ad1140302100070314040780e400350718a41800601d0150109540490042c81450f000264481c071660400d4012a41075403580026100e43d202165101070b0481410707e015522003e038000170b000640100903c00c0240d000300b25903d0580100012150010b000245010701030440000c0710300440100e0754446421902c0039110031021303401d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 495762203 1250 495760953 495760957
    0x5100b090f0d12081602072312030c0a0c0905011212050f04090504140f1504030519110c010906050706180f0804090c052a100c031a0d08090d08 63
    0x3d082c1082c8258003200913644001604d200700d006400541ca003078110348003282d031000381e4821004400456550107000421590350100c00490003003a808603400480d4103a41154030080b8088100e501901c0345e10200000c16a0500041c13004120410a940c1341c500115179581c05e02c44002c2c04008411403c5ca520742c080c02c1a250003200c0304180a482c1da4540000c14001c01c4160786c1a04c41d40010140040743d0440011060782012082c0041d0803011050007410103002406002202404014420450b201007400c40b0015180031035a00d0794001d145421070f441c2040d0445003646e0400500c8101804499003010455503103680c01000001c540341e0784000101442c1c4040b400901c10f41078665098240061840500240e07021007408000c00640090103403460321406050701d850240315900c0d01126002808003210136284942543c02c6013034009117481c212010200b500d80442c1d5901c401c40c040c1c0500c03000322940d01106507409608107480351034180761070040441042c41140304c00b044108101c51201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 495763453 1250 495762203 495762229
    0xd1209030210110a0e0301020a090e1506070b0618092e090f03020d0e180a090b0103031806050c0303180f030d02250c0302130b0a0807030605100b090f 66
    0x107420083d1404101414941c0e0744408024400a030f4502c451085900e81072084900d1202291580c0402038078228503030103581801400544210b6141c5410a81d82d103440303004007051440f40c0c25054131071400108000000803290f84002c041c01ca0309081140e4010000b449103c8540c500301c2800754400e031284248140c00360741010620141c285001d4604001c00c0341034001e401d41c4030b07400303440d40b800e00b406085568428100f43c260b400111b00007102a10411007a8541c3c0080103140701044014842d1924000000d003a03000314001070004031b000d8800510014a140030307000320b140031031610380c1540900c1c4d031b2030201608800890700700303450740d9100c0d4604001307048204014105803500c070b07903001c04148000c0d00443c3c080e142c103100c401002142c04452100001c2d00c15448050456034609540030301c03103a40d5100c444603e0503642c4200b915004c0c2e03500017201000b004400024038990303044d0316216040e2200a426a014941c08400c18041c919010307050300d4a0f5141a6038020780400160700140706502880 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 495764703 1250 495763453 495763483
    0x60f0d020a0810050106020a050a031b2112111207050c0d0e01030b0406051f050c072903060114071505012c010b0d05090c150c010606020d12090302 65
    0x1140c0040c44050200d50b03c41c1d038500101c000c000710380e0b80d0941a6110a0510780c02082c44c0c001580540000380500c0d40d0900d44007915002601807192a90366641c0c0b0b00b065201d5803422407002409050440e404280b0f019111000b04003405032000e030902c0d034040390088509400842140c0700018407094455410f0300c2c05a0488011034280100100c3c003d09034500314440703640064100f05031100c050a180c0a038004a0b840504042400810400c500206400b109209030030050b003000040c100c03a008009100240c9a1280100b0811203001289a41a010100c0c2250300c0c5206000300aa580c0e040b403201c550b59000700e001c0581d00c1c20185403500f04008161480015203240c1000480d8011704080400c40155500c103a08908c0c030404017a210702c0500034070801c952070604104403080c071490307a003015811036802c2040b0385400700c2040015140070458141e07070f6510381021400f400c01da002401424014003a0b07001512003541e4203280140350351000c1510222454540d210340f002c15100700940321102981b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 495765953 1250 495764703 495764719
    0x90f090408030a0c08060a031b09020a0f17010302060a110c0a2409030503030a0902040618020319021804021606151a0f0703030e0708010525080708060f0d02 69
    0x1528040009800035111031100ca8900084421981e016122190241b5801010300440c13a00e1682c980070240700c0200b6906034000c40c41c1d00010318035107a00290805e09800e132546d02d079020191000500f041110145407001405580040000d40c0fa840308980d102c91a600e002c042000e05000c0b5145004202d94116801c07500d462000030384800c000704000c0001800b98180d03100321003203650031508082680006005a04104045203604d01d4682c0300c0d400c41c0d13201410105296a6443c0c0080e03042c02c02c2c4071290b0000350001b00b001400005000c1140c0440c10702441107003407140d103490001180c0c213801c03a0306010329400204400e0440075030104000482e84050188240645003951132003d030702e6031207008039840e4013149007480340c480d02055600c0100c0c21206036041403030544049003d024030b540050002e0240c07100c0803c0703021081c0110b070b1040c841c080b8042c0c2d02003110058990402103503d40c800802101c01c0600094540c4108450b80142088900c80e89268580001500c141940a00290b0000c0f41c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 495767203 1250 495765953 495765961
    0x111070f03080403020f03030304030801260717010b060f0306010f210605040b121c17090c19440105040c0f12080c01020d050108010902090105100e06090f09 69
    0xb5510041082d01e03c241c2e50180d081034003400385030f134070f000030b0380d0003008144e0300d00042c001041503007504600903140001c182d03c9024640c0036141080047d801520740480020300300a41080700f4007a8070842c24050740d09070310b40a4004981d261502010b00300d01d042007009041d0385111803190410821108040b403000d44c3d6400180350307c0380201003a120301402142001e0301101c55160900b01c10901055000c050450310b90000002c0070454000c074011010b00c005555200d01c05003141d020303d40b082001000500c4084121410010080940c1d000f1222000c1502403d01440f40460310803c003100c0c52808610029068103c1c8281c1c1200c0020fa2909210794400400b0800c0c00540041d406240501d9030900000d40b10300040b1101d0b40d560040ca00b0076610002c07071000182c0480300034120f400503c0001801c0010300c0080c402615000e078042c0380c95039103a094440642c601010300c00c6c0100000c494501050304040009030148003200d0b2501d1240001107401415a01c40c50716000003240014101206458 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 495768453 1250 495767203 495767213
    0x21050c040f1503050105060c030a030b13020a0c05060a060b09040b0117091005010e0903040303051b060403210618020703170406091203090302150406091a160302070807020111070f03 80
    0x8100202c600090030480000740c0c500307110b8200d178492200325014500d04015200160090304124960321f42006081680c02d14600d010300c05000c898005a4686504070b40a0a04030f14051000e0403400801e8600300081080d861202c00700c6034000d02c2660041050075072200141d03480303042ca11004c014001a60104201030f08042885e40182818850800c81c6980300d8050b980c2000007240e01c01c200703600c10402400030030300450107031a40340e480090411056a0901d0380e541840000d50b8101e0106501e0070310141824042c605000210200b45001c0204a01c0c052000307585200002841f00096030000345401403500c950f44642c409250040f190015050518210008100004041c2d814007030149070140e45a1080c0181055070380c16500410020740c0705198001d0041e00a0400c84500c0c1d41c07540302100050144094010310150291000200e147c08036503800076980030302c18070f02010f20421680c8001001c50080e103002680a2801e8600000c050a0840c07034801c0a4000403600707081e03035100000304a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 495769703 1250 495768453 495768479
    0x2502031819090b100c0f06020f041203121107050d12090b0907050109170c06090a05040504030e030613020a03061521050106050603041a0c0f07080d050721050c040f 72
    0x1200303a0344040d03841c00c0c0810455626142080040006006c4d6039010045409600078000520007450040d240c240c1da842c5c20b455881081a040300030030070b887d1940040c1343d46031080d114107a844010003840d200c10f0b03654240c2c0f106040030154082c0010003040344800c82e50741d48500e02082c1e01c8507506c851400c1200e08156245498410107000503040000400c1400d003940186880c0e521280081c0508014001002200c0c1c010b40000c68202032000b90000719aa1140541c81c00f85000713480b00c0b8074a603803c005060600348010202419140721420180040e01c58000c0002142c1d00103000041420101c0b14811016040341d2148080d1086558038100507801d143c5007154951003a0000c120040c1d850043c420ba90200321800340000408420072002d901d902130310140c0c4140840d078203500d4640703603c900750b0a0790017600c02a0b48030f1a02144000d041d260f0361150340d0b000f08d19800d04020b1040c8000e4202088040e03440d40301c02081c0c0fa000800c8501c00e04200741c0300900710603202d03c1c3c0d06940f02c0010200e00c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 495770953 1250 495769703 495769721
    0xe0c032a13030c060906050d09020102120f030411061312050f07080303240a0909061514030c04090b06060703091d07030b01030501140f06090d0803250203181909 71
    0x300c81c0e00f80000c0d01c1800790b69101e040f5411911703840c1c106801100c03d00c0040521410680c10742c00b5600c1540f01c048001d90007444800e00b003d404c140c030b030b042504018050006488049008032030401c60303507040c421000c02c0d4104640c284410b40d0308607040703850100e0800c40340b2350800e00d03944503041020840344000320180d0b118611072000290204007090001e00241c1e41314032400e2300400a07a0050180300005d40003050030320f0044d01c01041035040441c0d40001c8805a0b8000d0803c8048404109040e15003070000c0c0800749001c0f03600303001c0c00b03016403101c0655500241031700d80f0031038000500c5c00405002e16004c4004240d400c3c8001002240e202e030bc20599002282d03581c00103464003c0003c490760192140074103a0302110610300000b00342c0c1c0306114101030100049070f41324900f885043c01039580c815003c14200e103da18696244e003849140708988046418107500c2540480c0f420039692a40001515841100b801d0003510a0240d400411590400e0701b070100c0303108491350008a528a101d80180c40c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 495772203 1250 495770953 495770963
    0xb0f03040201080c03060f060904021b0c040b010305091b0d0b0c070c080a0b0a0c0203090301020c0c0108100b0d050c040e04060c09060e0901030b151c0506010e0c032a1303 75
    0x1d0380d5200d104d40110391004030303400c5a21a40300c088145007414040c0240c09a0389001d0001440c0960000f085240b0103190302c5e902f4120791000290b0140d504043c040c0f135044420078241800340d070901e49607082e02e84884000d0f40700141000340b5528120703a02c1012071820b6941025141e6100d040c04030580b00300ba884104d050b81c200003210f400003002d01e400a00b10741e006401c5081000c1b6074552100c004081c0ca1504952021440700340691040c6030b900707100504600901800900c4429131a0303001500100340241024429034400c40700704040942041100c402c04146a03000945d130ba54508104c02d04d010366041401070040c01d00411040180e01d41c4030009140a9845a01455903106d40132250018441001a0414041c90041001441c0d050740b99030420f1031454450345000d0044d01007081c410b543c0260070340c003800204500c07060180a2020034003504140701c00c1a640c0c40e04500404a910000e0314000c003210b81201a503108440d105840f54007980c003500e085558580341070a070000d11595000960b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 495773453 1250 495772203 495772217
    0x8010e060a05010c06151d091006060f05070f1208040c05040e100b18040305041a04061d01031104140f0f031c0e03031b01150e011e0b0f03040201 64
    0x205a10700126804226a4140d50308441105981c0c1c03020054418005c40b60038812030040b0101d2201ea80100303c0742c01c40b04034446407800340303040c6500500d00300c65180801f0441b4503040e41031040591203420001c03102201d003445a503410311031400c1d0300c0f40c0d501920050715146442017111446030b4032001341d5000c0c50241200112161311801040f003180c000c0c076260716881e4800b00403442c0b82030346a002052800740080074401c080622030124000d002d82158210006500090300f40140946501078140c1c10340031216190929040860240010411150b560b10070b0107002009240c9030f100383c110000440307000c1c0b030898940b44d0701c00c800c86000e400e0640311031148070130070040d4000f41003c0c4805103c04600600503d00c580840301038507500c07644014030388200040c01620068035101040244001d1203100d0754000020000351751542152546031002d000c6c07510011080100c40401d1901d14150352114010f50440707071800716000b421010302d80c0031249692000c10406442c440c2e2001440c4594000e0700c0703200f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 495774703 1250 495773453 495773461
    0xa0b04140312060f102a0b0708070909060f0501080c09130f14060906040c02030d09261306050a0201020409060e0105030606010819020a0e0d11120d02060f060312070308010e 76
    0x4000c0c4100080d90400081c40d0020114200948101b4050440851070300c4074203506040d06c503503041480c21a01070000c80d014509010303a00c1d600ca104d1000800d807042003044003900705002d10112020310b00c0f4880c1004050404281002c500c0c1c0110b03007990400924003102480030011302005000680c04424440745000c41c0c039820a9191000030340700c0c0340d00030140e0100b59601002c02c00204100c400d000e0461000340000003612029101e0764000038018080d5018030340d80e5a070120039000c40d412042441300d60600101c5080f00c1e045010b6010740e8402c0c14030503151010114106d00a014507480f20035194200000098002c4103501142d050f03074019000d07030b0b174981d54007030064840c10829224a100c1902074404500801c106a000e081c540e451481c1c6207440710b50034000030352118550316040d248061100c6402c022444d02900846d1062516000f0b00341c8440c1850000e500c400d0010400480080b00a0004680c5e035814004407000190240c030254841c903484c20010600e00c000d02400700441071910100e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 495775953 1250 495774703 495774709
    0x709030c170613080408030406050c010c030b060304030c0201020111070606150309050318010507150510080c0609150d02030709210b0c07060908030112110a06020a0b04140312060f 79
    0x414003501c840c1000341400c0d15403004114180c0c0d001941a03d100740103000102d0001d10600003400108480c0d90f03207a84420010f80c82c0e83c2140c1190300808285460300039a0f20700d50300c5d2001600d910a0301400c210380c00000600040c0c1c050890100310b00595800003400f0340801c20355500500994028154460841d1042c500c140c003218443d410203440750b4000e10145a951484402c00114804c3c18903000d418001250340d152556440d121411403215140c504109140e985191080c005001d07a034000d25042007906c000c030b12684103150025000340e9044081c140c4450207107080b035281c14a031801c2103580c0d1420800c0180380d2001c81c011110b8412201c2c5c0b480c0c544894003005c000206030044101e512586400d103a00c030581d804100f04440b03440c1c0354920707040403800840140d8009c00021600c43c8a800b110324001d2000c050768101c4038480c0c580c00400740100b66000514038071059010318070b00f0050300c860518001203a9840c0b1448610700c0005100c601c1101005907003030107002c1c20b840010305450340d1410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 495777203 1250 495775953 495775979
    0x1d010e0106050a05060309010b100f1d06040b0d110304050a020a1a030f070c17090a0909050a060b03030c010c212003060a05091303090b0304080915120709030c 70
    0x30300340e00404000f8144414508100210740211100c800014020078000204e80300d9800c2c84d60090102d44040c407299102900511210034109500614118004202d8000740242c0903c0c007425031510004102c11105290b19400640c400c10001c1f4030503120700c1c00d49007281e62455100e0003240104140c40700016410403031066515004215190103045558650030b400c501d94000b8030388400c010240000101050110300000d212800c050030740c03030340d814804082c44401e0002e9444030310301d14030b4408244041600402c809100540c003503c08244900c207180043d245000f01280220036500c2c00c2d12307603809181c2110036080302081c0d0a902c00200018841c0e2001220214038505129664084100002a4201008550202c0020001900991034001183d03a0b403204485209080c514100d0350001d05070024204801000040c60031480c502e40b80d600c1112034024108101e008000018001514000c6034058071600500094120410724102c24018212903044c4001e0381c3c481020640841d502d0b141d811 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 495778453 1250 495777203 495777209
    0xf050a08030a030f0b1002010c09150c020d0501090209010b12060402031312090b0c15090705010c080f090d060b09101a0702040e030a020f0106080d1403060a08011d010e0106 76
    0x102071814010740702001c0d40500205034810b00d00c2980c0d00c0100009a80d291458100400b01c0e50002410300b81241d030103000f00310150010048501c645520340d88450307003d83c1021071a13038143c0705400b003209145480e5000d010030b50002588001075400108415407407102410303094180c041990000c3d02c1d03280074001248402e5402c501100a01690b58000c01c1010080031449081460160500f50f80c55044000e00d41144503080342035000b402d00c8a040c1c40708020040d0b0068041009000100c0c80d1500203801450142301c024480080819248958004001aa10740650142c26540600c0f0300345041801040000101c520460700e0754003141459100c00000c0099540102d040092000d601c80c1a003056082400200d034450344500c0040c46441301440640401d00180d001002c1c02001c0408080c00c1d1040c90300100c00c0d56200403404200e060b40074211503c00c0b070068924a43e01e88450010030b40445807500b00503a04d41c20511115029146580400c002040e500020080203110451441c2a50703103502c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 495779703 1250 495778453 495778469
    0x18060c0d181202040203040c05060c010b011d0117090a060606110105070c12030b04020903011401150201020a020606040914010c0f090909020a03060e0a0f0807063b0307020a030c0f050a 81
    0x1401d00b8005040070b0380250b802a010b81705602c07099941350300062305644500305039a9682d44404c40082c072035070000108030a0751100c0004481d03006810000070419050440302c0b00440f40c130480420342c40403061001000c403a8104209002c0c00da10b40002801c183d01e0712940416541c42c02c030001e60518414030107a0300c020740c005140c0c1c2500380e410320218040d041c0d881d40554860750800c2658425603092058a00c103585002e24018190700d043e001c040d0342421000c0340c10559004100d40c409955010480300d610090880300050001304500703140e071700e00f449480012101d40c60001e141d03004a8000004002d1034981d5a0340c1c004031071b120100041070303501c02c0e50000d4011000120520004106812502d82d0700785100451b040040d86844022120365183c5007640c20740b00000d442d0007400800c2c0a40b00f1401d00120318503483c001c04c040c841c4040350901d0f210f0705808901041e1841007900a2048408458005109540f030700d44034100154414014412114902c210103000625401c1005507003088400328 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 495780953 1250 495779703 495779729
    0x7030b060d12050c07260f0f03090d080712020601230d0204180b070c03020d08091e0f010c02030301081027021306141003180818060c0d18 61
    0x354010f6869422111075180c0501a01c100441d03414040f00304145981e20403000d800c1c0c00303030105aa860900d09018031080d01c54110100031510400004212000d1a905640299200e0442d08103c00c0d6130155a80042021200d040e1410540380c1c006001c6050351a110301d99540b0320280720041540c8a060342512ba00170380225005400f5103090703401400e4200c50f100101c091420380e0f40c1c0d0001140e0003222044045081040c0580606078100550b94010040e414007201c81e0070304180440d40d40d039446192810b06100e014071201b1002d130600140c00c3c207500010091003002019240a9143d0b0424020a81e0520950952001e041c0c1240601000030749242c1c8012004840c0861490020284120681e000354180c40d90058000c614441c0b58005d05106101006580d0007904210148040c4103007a0101420310042580185040020000040d8403ea00310355a0045401005c85560000802580319101241c0e18144441c00310343c032111800f150392170080c103410412241c04a0180c500a400c1a1810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 495782203 1250 495780953 495780983
    0x702150f2403150c04170703060f020f03160c020303030a0b09360307050a0303091e02030705040f0b0a060207171501050f010c02100509030f071a2a07030b060d 70
    0x55080c400c0c0d04100701c04c08482c03501d07469580702d806007a5004c991000503404030908205001c501d01c510304038030002c4c0b50154a400c01409041846000144c40d8046610b10f4800050340b441c01042c4400c600c40e4090250390b124030f07041000100911140c603501d4041c071004000541d84840c11900c280e40f400d008581e12812031084840341c1c440480340c5000e50010302c020052a0040340c401c001413940d840c829600403c0c200c4092800c001d140c225800349100c0c00b103010001c000160350119194080d2502500c001401c8241101c0f640d000c0e01c080a501a0414460440450105c1e801b042c2c02c0c3c165804585d46146444d01105001e03030b6144441040c00b0900240e00c0140064030700218045140d0710140343c41d18144005800003294513420400210103e00001044400c0c0d040030701040c00582101800b421080317142a840703807140080d2b0742040c05184070005440c40c00c115408101958044120143d8140c02c043c03260b0503036100550302041d1400d080c0340c0d001925a20788001051546680807403046101d6031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 495783453 1250 495782203 495782233
    0x40918080313030c0f08270a030204020913110301060f05040e010b07060e03160c06020f030313020301200a090f08192301060905070306050a0e0702150f2403 69
    0x10700c40360b040f81048030310388080e0003080f01d070440444c1850068a040d5994071580344400300c403103200e040c080050032404a6006060740c0e0b41c80f03c1000c4a40590307026a98919030000076408607440c04900c64090310300380105062100002c0914140d07650303a2548010112140800da449000305e00c07604800031000d00c0180301651503e406025658441c1034082111051003070140d041d500400c020010300900d4050b400203000721000d0303c4001340041d00151881083c03903801a43c0380c0c80020702d14600c25107050074510443d28254019100e144140100c0a1040d0b5600d03404c0001d6480380aa03280001c11040001c51215140305c8540111030451b0010140d06042a80d86642d20b12006000c3e200710b182051001c0344001c841462540040e0114000501c45040c040f5540c00c03202d025181400705407900000b400242c031880d2050096070080541c00403555215074040349080c03009022001407a410f001400000842c4d5000705004050100c1c844044048500f0365064042d040f0241d20381c154480d0244450b808 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 495784703 1250 495783453 495783481
    0xb1c14011202130e0f0606010906020d0305060a0e01060819050610030504051e100f0b09041401020408011401080f0d050f1b060112050d030203060307150509090a020409180803 77
    0x3031014122020a846843c00d01044400003100c03001660803c07108000244018808503134000e00c01d0a00500340c0d42403220095039040780601801c06e0681d50004a08941d83d1900b400c0020868040384268941c4c5030708008003880301c16101c490320030034140c261b010301e18210f0040c144110300150004020300051001103002d85030251041c1c545002d880407a00542c400201c03504182004080280100c1951803002000c8030084a401c0745210300d04074000c00c550f65000c0c0300c0e40d041608403542750348158888100ca80244940da001081d55882c03c0745520302d0080c088400ea0407a80320b002a13034424101c010310162240c00c0f070100000014010410f8416400508000d454403001011460000d110f040b4541403516a007030b008050818000e480c2c07041089402c20107510003d44034034084d0b0860902d000481e5441806008081e12047d200c415058028816004d40328020700040115000c0d0601c0d50b042d500a50207801403e00184c00c10140e1428200ca544021401da90b00c0b0004528603910402c00c0d0300c0c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 495785953 1250 495784703 495784739
    0x10207240b04050705030114010207030c050f1527010e22090203031b210a05030a0209031b04060503032503091505040603050117100506011101060b1c1401 68
    0x11540e07502030303092075112842654802d101c180c85080d80da50404208180c0e40490030503050446d03208540600c0061b84002c01042195425251070644041500000c0e0035a540c891031345903036034030105500240300503c10208040d0b10000c41c0b10380d8500d0301c0000440b501d0301c2d40c0700120f40000c00340021a01c0944012034121310303c124a0b5001070a25a00e0340000c5c00e40d8400070301c8026501019816215000c018084261160424180c0300c00400000030649418080c114149041c8400800001c1000c041601205e800c100014203840740710445e00b401000d002088007d080c021450300902241c117040002c00c8490207855010301690304000030f03d03c10365032907614404074100040700c40c0000308103031070320340d00700c24003400e5101c840e01e0b90304110004ac1207902c140c3c08810081d2800b0500c10400c6004244402c43d818880c90110340c5545000050301d885008401580c0702d50f180100000b50310140314081c0c10030199a6241400224000c1c01442c00da403c43c41d0360311244c0010200410110106035005004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 495787203 1250 495785953 495786023
    0x403080313030e18011809050a03050d09021215010b0906041a07020307030308041203060303120203070c050d09080c040605210a1e03080901050c030a0e0c0909031b010207 75
    0x41940d80001244504102e4604041c0d81c9044c040140300294940303d100180d20788042042040c00d400ba00d9086da035490023403010f02070140000d0b809201100d5600000307210368000d000c00401c03103400c02c9029170301e00840b000c0f00a0301d14400000700d180c0e5086001c03141100b00050400f070510342018007200940c00d0041511001050400503038005031003d00580008501a441d00c40c1c451410742048288490321403142401c05260036402e000094000d581300c04007903044280107071280c0e0b07200c10641d1014010207029049209890960580340d80c000c60f00b8040d80c81290541d02c0e604da0381e00c1808141c90660043d540d0081c1c0c21400740080d035a01d10101c1d05020252000c0b03c0c541581703911000600543c8120520070000b2404c080014160052042900000d146008001c640b400310040b1001c4c0c0000f0306100440c07a15402041c1c96058100b040c07202e5014024204185401d04070b003807950341d82c003038651040220a5820b5217000c000c010302c2a54100c540000c40c0400000350a00c03e2801a0760414000344 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 495788453 1250 495787203 495787217
    0x60f0114070c0f0302151e0304081c0510050316151206080309040e0610030618140102040501030c050a020d0e01050d020c0106060221250b070201150902040308031303 73
    0x10500b4021031100500d0300300c0f890452542540184403c01d1940142000c0c51102000b945025014402c0003900480c00700302100e4403900c49240c084141c1c49121086c807006640400e5210400c4c0450780a64080d10000c1201c003000c907968002e140c0c0318492756021162044507800100800c001c55041d02c0202c040b04d20f0242c01e806071200160301210240e0b040324a0a07400401c61401038142807080c2d800a0140c1d03401000f01d0b14110301c0c201449071741404010941a1100402414225142d4000b60620780c0411129605102c07684118000d410603c9108e00003070900d440249031601900485804030041e9001d804145034800e02a510b0380041c441c00c504000040021940b213209610180285580102c00841c03264030b0a00007e1070b108131100c020b280c01104515220903001418100c0d81001026100302d44102c004613984231a042ca0484c020345401080802c00001a81c1940b1030f400e90300b08075030f010149503100d8000324100d00079408020441141040415004070404114101c03880c4a0324000c0707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 495789703 1250 495788453 495788467
    0xd020f041401120501050703020f0304030c050c030a030810050a12060209010905090403110111160620030f041a0708060f0a0b0a050406020105093c03040308040602010e06060f0114 79
    0x700c450300981c032102540030381e4030078002080028064240c00807500d280c1076052164040b180c0a06110181004051000c4141003d08200d801d00014100c0e8038018191080c2850034100034050280c100c0340840d005c1940300700806c0350b01d4000000d100b643c1050502d0740b103184c91503071040c000790b00c08149035040c07106330380b4000b60790398859400600c10303403080c1e8900500c0c0f02c0c2c0700300c06402d442e524140500140320500c0042001c00b000107441c40c03111b80120f00466085551501030b1680340d41702c3c000da03174609400020032500c415101080c9000d10300c98102416415035403041c0d400203001c241c0b480380c00109050040341142c5019a542120004018604030620356900741c03078010383d400314100c02c0115201080401c52150203200f05540b04c940c2d02c018040303040f0300c2c00060042402da06030f40e40c400c5559007007840c445481d032030702c40c40d59800030400c596030303243c03203041140382500603101d854010340c24501102c402c9580498241d0140902809031880c0075841d0340151420281c100308241501030900000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 495790953 1250 495789703 495789731
    0x915020a0b0c0c06012421091110020d1704080403080a110f0c01090f1d071215090f1407030e0a1b0503060f040308070507020424170c0d020f04 63
    0x10702c1c000d00100c40d00040d8101d89a4910104246c081410f90074014520306401f5181e4816900a070960741ea0440090780c00200d00d0620900756440103480e4119040810528513982c00145070b4969503201e48070f805508890001c90704d0542004c55000b0849102404104001343c1442c3c0684013942941c180006599811000c0900d40f6000c40194291540200b19103041c2e941c0090034800506000a00442c0182c240302c1c0b00396070004080350701c445558469001880d501c1c42404c0c5422060350341030041c0b0034407126041104803c44070b40940d4440c50328220001d16002124464011030005003984490190341d25a0b058004110444525203603004085d8040005000901000c51304000705018054403824001854603042000b06105405044101400040b1740c100c0390b501e07880340940c5001c17075803a582440810090008140c044000760610745902c1520003600040805546e903149050648102443c505641c515078011126000301907000c00d0405424213803940f0304c200b44050004100000e40c9110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 495792203 1250 495790953 495790963
    0x409020a0309020f0625050c03060c040806013611070f0605182802090901050603160b04060c0602090a150210140712060803040b0405010915020a0b0c0c 67
    0x80001981d00d0040e5000c62501c03110160420000b581d585003014400715646292000d14140390003099540307200c480c2040b00805c008c040a5038064195962030506142c040d42c2500305000d4420035014440c00450000a5050029000d04441d8845400c0c084403400320315111950510860039940c4619501000b07040e084000c0c403c062148688404054041c20440c0c11148050214000010b03598050042458006101410325402c0200c0008104514103001610391145200a4006c1c000200b0441c202c04190300c918807a02c800c0e011346100c180420b09100848019001d00c4413100e0303040c0001d22000e403045040c03500b074510984006280c181c0007000a21112080d51140e8141d0303181000b41008168103019001c20881640f50500c048015a03840b91011000140102c04002d40c041e60380d02c0a01050308040c1c01000e0350303400d69590300d440d490200210f50050083c4d9000c80c071006800900d5406030703011040f50b14a16070181000c614541d40d020071885001c0e01c1d8110044060081860b01c4d80c0a0107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 495793453 1250 495792203 495792217
    0x80306060a021e150108030702220632031c0f030609023108030d02071a0907050f03030408030d0504020a0f0e0f0901020705070504021c061811040b04030314040902 72
    0x7001380050000e5641000b42c101c8140c00c5a21590014002040140c60340c4090320f4049403d00ba202c0e030071011110315000208480e0b4001c446803001318002c05500d440110300358509003403a40c0c00c111070052400c1410341d01e54042143c4c1c20580061201441401d1250344c0e514807a0b04140350114880355a2165401aa0810940181448200c05080d5528034080c60200b2007c068460300424052a1881aa80301c0c01075a620580554000400200304490054080c00301e0800d401203420b00c3c01c0540f8501c0da200840d000f1b80d4040c954055000b11329142c000b040e02c0454121a004500d42401c002c2e06030061302010300220b03089540244003050000003240d0301400740c981c06c00176109618014138501030305140544502c0700c0340d104009500105038080b03140d0054440550300540d45124a00c0f020200446d40344203000c4103032600502080800b000ca825000404040c2000d00080c081c00405682900c00c81c800d95040c1c100130401040000e0050045840750a00c1c0e0602d01e003030030340e2260a1002c0c3d9000031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 495794703 1250 495793453 495793513
    0xa060b12060a1a0312040618230913210c050708010f0513120e010e1003020909102d0e0708060a0603020327010207210e040504080306060a02 62
    0x1005002d035020414803001c00465048004100d5144880744101c0310f8450340c05800204954501308101d200b15501c001002003440b511278210741043e0310480d102c5440c10f850b0480c0b040c408907010548400b50038508001043d04070b40042d100c0b200c8140004007100e4416503140c148200b91040700003103076081c003482c2c00805c1c0800010400b0003404a43e1000c4842c010704281c2e06503101c12420020034a20030340d44564101c0d070300b80245a007000d0700c0140d9514412034a036940c4542042c28bd04e00050703250b0060010fe810581d100050740d01d607015612140d00c0580101c62924aa0700310a03012508582d10700e400e0602c0c0c0a01d100d24440c0c440c00030480e0540b0440d44c060200d00a02c0c00d016190074003203002d5000f80070034901113041d4100040c00c0080100344006021540c5500102d551800d9020b60440d01d490340d03c05061461903c0c2522000d410100003078802c00858943d50366074a00381003500416200e56031005a851560380d41404004058101c42d6418003144207103031101c0d074404e0900c0d1903440c9000101c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 495795953 1250 495794703 495794711
    0x6060d0b0f090f07020d182304020a050a080c03011a031518060f0a030b18010b0406030f020a0b04030308040b091903050430060b03030d0c030605100c050a060b12060a 73
    0x10280685080c58191040b000c000e80e100c10321a403c0381c0da078008012350341102c0d601d4001c402c440e2518040380160b4007206501a00c0011030000315070f0058024007003802c2c3e9890f03030306103560f440c3c6c101011030200344140700c2d88200140381c0070548204000199444502d50580e840d5805c20140410382060220600d442d801214405000c81c5180c21780d00b0160b04030741207681c01403103800c5599060390448003818601c0c507040700c2d00398800c0868080d0841030003881c0181c0304000265403402c0c560050400544242e0055400a2001c0b584200c3da404a50907a070300758603150042e0703e40e40d407100800e4074000d02040c903d0150040d0702c4041d456000f41d0850542c0030b40e031125191800d180c008130f0031000c4d41c00c524214030420284105004540e500440ba5190030031390006101c601e00c1c02103404d5100314209030b814030789004604030101ea0154400d809480301034520301d000c1e2040e8071050716000d085030009442e1390300c4580c400000075400d40008030020405002119070014800605113406829103421422a40ba = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 495797203 1250 495795953 495795961
    0x1b061a0111010b010f030b0a1d060a0f1202060a032a08240f010207031b080c0d0203250504020f12060301060609060c030e0604080d0905040506060d0b0f090f 69
    0x1002400da5009400d40000f082007000c48000a4941950089028140350b10b0720180303a699039610325240700814080328003003d0310038614454204800b04981180c440c4121503170100c0c021f01741c103601c5010b0707921410400728100752507001c008964112940709010152683d52500e098442c0c01519028034181c1441d60884a000d0031014090340802401500340e00024814520005110040208104403d0712403102840361000102c3c00e1550540003d0200d42281c1c454032114004210030350300300c8501206a402034400c013402c00007200304c242d601030350551100602845100c1030094507c0395030a82c11400141c255110082010ba800060003011119404912502c0b038020b10618154040003c40c0204030050400d5000380003c0418001c003402c0001d981c002400705400b50343c45040028004000c16111965150002e5859409031101e000040d00e40500145a0500d40507103070188500400d102c0c00d1003d00032005008200780e900581d400200c1c000100816101e2800040c0550380c2901d81120602d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 495798453 1250 495797203 495797207
    0xc0608090706260a0207050d0914030706140c0c040e160e0108281a190507021b0a0315050402030d02070317160213020d0b090402060a1b061a01 63
    0xc641c01402880714403c114100320596900e907a83c0d1030780d8407100c040182c881858403130007405105802041b0b8485c07201d1140c040d43d0494074903801c40da02204c0c215090700070803040c103885088030b00c20a40412400ca00410301040c0900181607003540e0402241e00c1000c403800003030143d401e074403031040142d00304881c1105c1c000403118491016003c181c51041c1c2d654505100181d64010705001300c0606020b1401107804140810710020840c0d8100b51050744603184410341d545090000d0341e012380b0400780e1509483c2d003079019025040c440d1800380c015050464200f801e90409004d43d000d42940055050000700000da45d4880725241d004840c00300040c0c034a03162060614003000c1d038040314203551040d04208001119005403050400b29030f00c0554840341765102e10040c82c07500d100e00070341c00000e403510119003100300d03405400310403030380003081c0306100403403050181400e13050394060f40140c020030010900c61f00030344203000c1041c103205000804a0090301e40d81c0840e109100b600030141c80414070890150307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 495799703 1250 495798453 495798463
    0x6020d0c020906010c02150f040e0a0b24040f0e070e06030f01090b0d0b090105040302190b042010050a0201050604020a0c141f02040e070f0203030a0f02070c060809 72
    0x1022a040508401000e03800241001e603000b0846030400086480d03107021900e500358442010708201d1401601d841c0107a0f2000e8454003c0d0250004c1048401c000451518ad00e009880c84040044d089800b000304000e800001c0154012080303142c0001000000f441e403005c46400c0b001407002031590303c000c0c141100001d1500c0000c2003480e1140c1030a00030300c0047d83d01c5050607411180d044100150a0080c500030600301d036441100544400300d0b01041120551040d041a131143e8800d80c00d031440703500021300c2114000c84010020f4420034030880007030005200700500020b44070880300c64001c0c00c0380c1c40d0002009485003080901c0022030115220326040e80902070a908018100c80560604001c1a002002c4c0a415440680220310900303605c0301100051029600100481b00d2000080106650b864080c0d4081e228546070120243e00007151148103600c1108045030f580c0c040c0d850360300c48004010140c503003030b0810940d0907400c001100c000f56090541c00c000740107c1e201e1004d00d1410912550400d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 495800953 1250 495799703 495799723
    0x230318131515120203040f06062102120307052b0914040c12050720030327190b07030b03070302100f03020f0d06170c090103110d050a0c0602 62
    0x1141000d04a07545030081058400944a0707840c1c4000e0041003640049403540c203140b00205205100000b0300042c004550300c4228200c2c040d032014420203988500a6220491a241181c1a07050104040c801881d0009146098420910440c2c0c100703006030301c0712820302e030503c800c1d201050042c04841100c01800c5803101103840305420b1502890707151040864a819084141a1156686260405106004e643c04942d40d003c01d80d020055844d100201801c1072400101540300c00c11701c203441000b2288000200c03072080058071f0303110140f000400c034812171380310600d420b0320058010482131101209188003014502070155101a4017030600100290032074500120003802a00981400d00c00b60701d8407105440c401540d40750511390180c2600b0110001d0007126584604040700046540000102d40c001d1000c1d107080102661036004180c521503078a038042441141c10a0242004201040c14042490304010014095680c0403250750b881c582030200c29501214220358640c0240304d49981040200301d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 495802203 1250 495800953 495800989
    0x90903081006080408030603100501080106081905070b030c040902070803180c030a031805061c05070503040f0b0613051e070905060415022a030111040b07230318 71
    0x80e42054401000c43d01d00070405064908000040b45d81504c2c20002c00504500600c01081556140c91585000e401c051250940c24402c03c5000710050070a0340305011000c2c2d200c030051920714a030207200020790b080200f0340c15023008140400104910980002e001036841100c146035071786005544100241081a4002140d1780007400120498800144405400d50141405084052030044213904c000c169040f140c1c01190102d45080c0307040580c041081013220510f4140944e541d003910407102170004640260041303080403500c502181e102c0046640190f400344c0a40c180c4400c8c0201c1d80b0947c5e00075070b2106c9000da40c81c1d2160003507428800300302e0380051061808480b0700c5d00d000c0008100d030003540901d0b43d880800c0040503130914002c11060f0456a036032021103607000084610440000c421104090281d420200e078600102c101c04110360a03216043c8290741002480d407203819012403410388040c4050041d40c440c01d40904100080d05400c8001c46c1e1035101100003c0500120002c02c85050340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 495803453 1250 495802203 495802231
    0x6060303090b0909180c0d03020c04060603050f040f022409130614271312020a02010914181005040b0f01051b0309100f030e280c0e0109090308 63
    0x403c03591001c01c299000350001e80e81a001740c903544900d50400c1603000e841d6a000310a0180301081540200c1d80602c1660212001c02c4400e903500e0041c0d0507900102e44001410780c078800040c0004210303a00e00d080e85400909048900c0caa2507500f0403403045808031680040b0004030f0030b80500c0c0b401820198000c649840240840341c5080c5103410003003c5082043d108903040040c14040b03502d41c22120521070f0000c0c02d141c020381825500d1440c1400000c2040c0c900c541401c000b640d0890000900c1d40100b41c0c10380d264058240b42104001600c9841815640e010310b0f521036511411096240650040d0449580c00d0320107450001040102c070b5041c0e202034090800c43d040440540e03049801d5036102c0700c11124070200c1007495407602d03085100d902e12059204001018034641c0c682c1c00000e503007410403c0c2c0c40802500451448042d56500080300500070040c91f00c11001071140b00d0808034650b1351151980c2c8410300d89455246102c407600742c107c60f8600e0703600c5000304180b507805495240c200300e4500d4444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 495804703 1250 495803453 495803467
    0x10180e010b092812060e3909010501080405031603050c010e0a0f120c0501020c07051c12030c03060506040b07110108040f0201081803070302010902030732041806060303090b 76
    0x50703500f814500c1141480688004c1490a10407203030032900d9105001d000b5614042c041546510300604202c00400811030000069480d14124984056007124005c004120b168a02001103800360030081080b07440340001c1c404241d4402c00701d07a1400146100b5150251210600e4098600311445c0040400059200204484c0410b040901d0510f0654005418001c0986146070640e04a6003090004005600c00030b81140901404907404040c3d503001c44a0a2048000040030011a80f010350050301491821744200c009c240280c0c01030b508985035080106081d981c80740003170078641242d031050800d001c0007d41070080004200400c040f2210900700114241810780320f00c0c18503203c00303600a043c030000c82d02041c2603100c03444080e540036420700e04581d5038019521b40240079103620901240280309441001c0f40d032010001e0400224000c02101003030900355180e40d4103d02c0d0700c40180541007039892621580c100d01d21b2034070b85d00c0355004000100e0011710758500148500340765401f09403100010300c145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 495805953 1250 495804703 495804769
    0x52110060e0402060c0708071205060606030103050d121107031e02070810021c09140c010e01051e0c39100804030926100b10180e010b09 60
    0x9400c1a0103580080c0c9178241102100d19291003604030290754802c3c41d0001441018024000c00c1c0700b4426000c2d0341c0e198480d541400090f00080c0401081da40041d1202000540701d68102210241c01c24400b04a2040c0814403141c540d210100950010340005000103803050840d01c041191041c0703100038500700d40303001309042e1210007801190111540000e101211801c03055a001c81c400c0d081482007040c03200c00d2400c0c07145104100d4042c0c1d030343e00410324409810b6004280b6140012410f8580d24540700300751101201040e03070000200694941030241c015508020000d840b0002001c0740801150580710700c42d0380c58a008a003030080c0e400c0012201005c1a01c42100200300c404103810000d00302e403118501070382c0036510303501301801c3e503207400042c6901089005d44203034003c058181528210500900c040301510220500550410b00d100001000c492080010702015040c1c0e1005521440c0c80d407405584003002a8400005000049500300c280e00e01060b000f0740203044030a1100500d056035400b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 495807203 1250 495805953 495805979
    0xb0d0209070c060e060424111b0d091a09030111031f0e090a0b071e0905100302030105060a051e0307090f082406040902060409020a1121030604020405211006 69
    0x1101002c1c545024081ca81149070000c8c000005a00441911400d4290400030001526845a0f0062080e1038154070014054080c4609903000008070324a0303500701e2200305005034408a611a0103641e0b801686401d04200c4002d58050851707050301403240c1105808940c6900c10607000a1040c4c2c03040d105006c841c1000092405582c0d40c058090030340d0b1b54601400f038500703030f00401500c005400c4845e4041042c641c4007070004203a410841d1403441d0385003a0101141203000901405411480c10070481100303a00440103443c0a8400c0d1914540304501c5070481c99290f0002c1d6058000724410880500058032400d1a840c00741c000031000341b544c4091340c040168010305205403008100714100200f081511a50001074140750013612180c2e8440c0c0c0c4a00c144000d520034035642c00000e02008403000d0200000c180703000540c040c0e840314118020204004c1442c2e40c0060f080030340c05582040001069141d44130400c118040c2c4a00400c61000400161070520792025071402c2c5280ca082001e014140034111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 495808453 1250 495807203 495807233
    0x503070f08060d08070b090d05040501090b160c30030f0c0503040506040803130b0c0307060f09060603110907051603120608010608030a020f0c060406030b0d0209070c060e0604 77
    0x500214240c441002082040042c024084c003940c4002502d801440810800c0f00c3c000c180610866200700403007034084503a40124011140010b060680403c1710320f090303c1c0070f081d91150304500c58170051030541e030b04010034030b95604c1158002954a0380c40b8184900303800410315489150340f00741082680340d90081a804d481001c4c0004c0c88101c00792182449400c1042c1c8001c4c00020700020381d07440e01d0b614095960b411155203401040300e040004a40910318a080d21290b0002c180250305000e129a503c03c06070007074100c1a07042c0c3d85e840c0301d1a8003096250040b04010744c0110304540c07148481105001c60034800800c0081440010810a030044c41501e01c0d0348000d43d01468541e0781b80494000c00c0002c0e003c42e80c00030780d0079800c11a002c90720040103c01040d003034445c1d408450015100d21101038555000000d445e03440b400c24401004040c4c000d1300308143c02c200040000c08901c9003640050041101074811307200003100152200b04108203403082c41c110024100060045141a60721072a000741094 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 495809703 1250 495808453 495808457
    0x1606060f050f041802030f010902041b08010308160f032601030b0a1806060e01080d110c062d04060905090402030c04020a11011a090a4b050907060503070f 68
    0x410b41d0034500c209130903921000365006064030340907002100418041d0043c0304062380725600d8241c002c07400302c16600c0400c0ca004465158081c46a01c0c64076a1a140e8005122407071000a8140d0035070000707113600c4900e20314148280c49110b0400c10300e075401201182602e188072061410075005001203010b500d1100c0d4824084007011501102e061100c80c150441c20300010b1403a82808004210f045400500c40d0507503041000302c0b40c030040e4446048480c00122080986160090102b54102d41800002024449003102079400c84907074001c905009550b0894680c010000c0101c1c0034041c3c035130301a50031401800221540c14040c2400d800007612a10044c80c0c040c811a0700140078134070b942c00b80c03195000b2a01c4200003000840301d40d80d4007241e841c001d405003c2c0b04103403000024801c0c0a031803080004c42c43c80303400003801d103d8504100303c0c030301e00400000c6200c20314880c42101155405806102e400110300070086118240b10000e5031800d00c480c1c0120f020b2000134002c00c610345030300500d103800c042014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 495810953 1250 495809703 495809711
    0x310051909060b030f0a0f0b040f0b090c040c0203040803160c0e01090f05060409260f0f090f03070b16020f06040303050a09150e01050304080f1606060f050f04 70
    0x2103086140030950392102000058105428403040c824554090440712405500340c41c00d4028500300580c0f03803020750750000c04080781d640042000c14101107119612a00c5013004140f40c032040d8035052100401220a400e4079400804080500d042c5401fa52004000b540015400c00b81040b5800c2e031079004083c05c41d0700b1000d80600e00d2040c4005010308500500d0100a042070b03e51b11458118050240b841c00400740c9800d1401141041c145449200c15903604090034000c00d01b9420034410103080701985101295500b0310016004001c00801003234400d14a81016581d251400141310045603070b5440640f181d004200200038a61250b01194800720009141800300b0f801840050301d0303c200c4400c89500b012011038040b081580140081c030039186141c980b400040e41e140007107222000203102d000001410040c562129500a0000c0c1d60050301c10070070303242014000640d0340c1c80c1c2e070449000584081c00300128a024844144980300261400100301c140d81ba083c070f00810f0043c0e540710190382c002d5a403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 495812203 1250 495810953 495810961
    0xa0305160f0c080111040321120f0b030616080c0a05040f0e010302010315030c051504091b230306100215041b050a0302100c020307151d0d02031005 65
    0x3a00c0c50240c1d401010420000240e060030140e080c100c1c00740000300d610b0468421071542e441029502181e620404c02c000000b4010040c0070780705c05c030a0011003400840340c102440003241c2d00840801c18112403002800d07100f818109032920b4400740c101d2000482e05442040c1d480d911484042d4055842c2c51000d0796124500012240b03031085a011041c050310b600c0c004110703c00f43c1c3c0c2e05141200d0003640e0900c09003421241040741090309100040c203110580c00200100d042683d12120704091000b121402c19503030fa03070000c00740c89031142d6a01204401c0902c0c40002a00026100e03031503404000c40740802c038924141c1c3c25003440044c001030322810f4a03405c00751045d84200030401ca11180d080c40aa0141003a01d40f00b015401701002000d20a41180800b050b60300b00715440d4002c5940080038a00401e03860344058591040c111410398043c0182c1300041840f42206140381c41d51400b5941d04c0030f42c00c100c498070310a1403441407421446040342d19241c030f0150707600180000030111000c80c0011541c42d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 495813453 1250 495812203 495812227
    0x703170f03070810151d010509030f0c040c02031602062b0606120b01021f150b0702040c030908030604240815010e04150e0102120411031b030a0305 65
    0x500031441244110020400540c95481200d0f20700528220507180401d50710b400c92020586506800e000001c1c1805c03644840303401540400e4000900181070441c6004401c0c1c020a08002c2c0e00e1490310380c1580149030301c031400d082c24460211003a000748061400e1410864661140e800c4800d00a8811400842c5e47c04407101c4c80610921110094030b42640d40c1d102c4049028017810051040002141030114421400043c1d40900440341c04140d01500c1000380140303450f00741036100440031141d0303990761800c5400c50b4544c2c02030f0405805170744519915055684104425103c20f0b14000d01054108801d039000030780c0050a0300c0d00301904480c0800c1918080d680340640c1556210145410311a01600080c40040401e0700803514004c211020320507a207d0f0580002428250b03001800320a0041c0020940c1101e44d20800075401004000341c034010100d130314840500d400b034800390307200c1111b01c0c610b4140386020800c40c0c50550542901180c00340703000c40000c2d1a40e01d5180003809001c400165144410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 495814703 1250 495813453 495813457
    0xd0b03011508010c08090d020d080a090b07021b04140a0b04201209010606020a150623040c0305072f030406030219030504020d020f041401091b050c070317 68
    0x120001c18049059990306090340600001c282e140c022a030b600e0040f03201d0740c0d0f011030600310708903a5800a102411104004a80f101401010514400d030313190541e000040400c03440d5800b4a10a500820000600140c0300301000480500a031090740790102011184030b010740312075032043c4403c0001510718601c8001c01c0191043d0141c100660640f10070040f180312080c0041c040c01088140c1c42e000d0b581e01c9114076402c03142903018039405a1321141901c400140f80c0c00a04421507005d000110b02a0b551701000c151030a54088100748007901e0780241070300317420603204011140c40146070902c80350602400191002007400b01c0d80b03000d01d41102181805001c1020780c125100004422203940d80e503503010080082d0002c1c102d9050319440740c52406e01040c1f0901406010300e800809850340061560300b0003c0307480f4000012130300b00345c80703000e0781143d0031910120314000d1030207040104054980580555000702d051170785806006040c014542c84440c00104203068a51000742e030081403000000540540c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 495815953 1250 495814703 495814721
    0x4030e130609020c0d1d06091908010525090b0d0902030a0803040507060f08011e0905090a020406120c050d0c03080304050a0b010506030705070b0a0f06120b0f0402060d0b0301 77
    0x40d09181000a100030b140c0d00503c46002c41c9019514110031354842101c01000c074820366902400d076108445400e1402c04000c12090000a1480c902c05050900c0854800700540c04804103940d1401041510345441e01c006240d083c0e0755418000521801a01802c0c0a1560060085000d00451094004523280d0b1081103070b250024100c0305402d42501d0302c0900c1b41e02c100c5003207440c0d00032802e000401600a80c5402841e074050349540c100341c3c0c2058200700001d4611b918207540185149000580c9010500c44d85010b0b0500f00082c10b8441c050b40140310035140c143c0c0c410b80c00c001ca81da214002080504002a05131842140c10000e201602e081a50042c2c48a400180045400005200411500141524403030344181a51200ca80e40c074010000203000885484010840420007000000c1c11040a5a4801544d03080040c1400120160908445094021030300c5040b155480b041030144602d196584403c0b031b4040132103103141c1540846ea01d8013a0800a20300b0540316070704201c00c3d940a4015080c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 495817203 1250 495815953 495815989
    0x2b08061203041202043602030a0209160305010b040f1e0b0f030415050c030a020306190602011e05040201020c010c060204091503021e1e0d0b0405030307120c0804030e 73
    0x7110b4540f240748074419002c600c01c07846180b50101c6c100c0d0100c2e910300e02c4160070700448200c00c40103440c0b080010301c040300d20780200d84c1030151001a00c010703990305040c140204010f00c1c00c0301d0008d61401000c0c0460f43c3c10382020103080804e03c0b00300f1012407496551820b84510300c100c0c0240d01c1011801002000440e006200c0d01140030695440402104015601c00c0b8002c10760403110400130035026084030302c01c0d0f480b0754213020304000103002402503400840c1c000340041e004100000340c00d0100643e506040d081040181d44030900721010812002c5400104c60b00e900040084c1c1c1010345c0080d50701c5030048896410301c080c0600305401c0c002c150b81918010038132844188140d1045500c11403115a0070f0108034819901c4c480303000001c40c00082c14040808000e03062207603a410a401190040103030340700c900e9002d015012100e00061408120314000c511400c019a00c0341031004014140034985120918110f150848004015030311400c501d4104d80c050600c000c40083c00e134040342005210462403c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 495818453 1250 495817203 495817207
    0x50105210a050f0d0f110a0807050c151c050105280b03070c03110615120304051309020405060306160311160302100b042901020a050604030c052b08061203 68
    0x842c83c00003042d0484a0215940c0310441c401d0031031020713215030010451007070f21584443c841c0350000c1c4c000e0006001140c092421a036007180e130700d0300140c0d0303030400c1c09452035242d5004103001b1040f030611004801d1101080070300b0312541d814072001c6100000d403241c2402c0c1003444509540f07034050b078480b0882c0140c60b01e50415942c038505110060040c07001c10004800044150341c2510900c01d021400d070b40501c0754803603035403078102400040000701c0d05031001c1003400c1d000400c00041c05070b583d56504034241074285030100381070b1254010402200d2009140364000d422800c1044082007550754107110030141418002a410302c40c0703411082c2402120442c13607002108640c030b2401d00d9000a45c1680d440354009003444142030b00000c0c80300359070030b8401040a038400c80408400c10483d016104280c204180304640e5034140c2915013070f00d4030f2420b5805901040500d040c20080c042d00307020720094034811001000100f0150400c2c17500c03141002c8034020412180d01c0114810740e4401c011495070ba004401229 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495819703 1250 495818453 495818473
    0x60a030c060503010e1b0a0e03100f0e01150308030c07030207030c06030f0c0516020d151d0c01020d080f1807260d170a14101701050105210a05 63
    0x30b0300c0c41e4030a00543c4082c81a8000240000700542d240111030604050ba15003071111400b800c1c3e488181300036080c0d50500500c0810141c3c50b229104620852a840c400402c5000052103410f00711206500e0086031480d0029062005c501c41c5001c4940084030b21400503594203813030404074101201500020f141e071660103000500c4651513005004d9000c080340e8100301461400000740d80500c24680d40c0e20b20304065054186c05845e189001c40031703050245802d114200c80710400c500450710f4460040512800009400228400030080b8011920080c001041007411003503000d8007c100080002e1117030507002c2c00050a664010000e20f14110305401150400b5484108903204240b0710383ca0380c00034520764181219000740000710081d42004645584441d02e64240c06c01c20f401e50b009080c01a259101c403070032011004141d884510901c03516079035042e010b0501182d149090301c1c0d80000b4096030b05160051103107546084224894551303030002c0b1b61088941511482c10100754500240c405c0c084c09140c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 495820953 1250 495819703 495819707
    0x1905090403080403020105060f0f0d1511040806010b131a0904091101170f180708030d02090901091b0807022407080603120301092007060b01030e0c06070803060a030c06 74
    0x181e008511a40081c4419503a023001d1002c4a210300070125444030a104280c1000d0802c01c0e964100c4501461020180c0e00c04010118152905048a8031248500180800500c442840700c1405003031203c94991a0585182c030642d9403034164081e040001501000021881054208480a603d009041480917811904003461440302c0c1c513030742c079020407582080e00c0100090300c620180310f14104000c507445511440c01d684015031841c0b402d81480d208013400846c3c1a08100302520b01e01c4413050b0050b039500c180c00b040c008081810790100200c6820810890354001c11046c051551542c03510703015030640c3d00c0d110224900500e03003411015608080060441807014020305030310840d2a0340319900b040c0c80310424143e440a030010086400350080c00144503d0940307030000c6030020031072222501000041e420486450303000c0003007224250f5644504002da540c260040c058801c881c00060f04582107034401188a074801e41500a000000010018049903610780ca140055500140b80f50241c40e200c581c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 495822203 1250 495820953 495820967
    0x2100c020a060306050607060b0d1e03030b01050f1606061703070b07020a0309170304170d02010f0b1503061503011502060c130b031003050d030903110105151905090403 74
    0x8103a000359041000418040c0c06400b03010110ba03005030902e403401d10251250300090003442c3c00a64803081040301480402c100982030102c048038000d0b1480703030036480d01c2c014045030009a40c85040c41024015031401d4618007080d14040d210005400d4041021450171800910186e045101c41100c3d0782c8000b640000008040c206a61007441c40d015580c82d800000c1c0d0341d0b030850460040c002803020405000703a803841c00d4280c1d102c132000b40441e4286600d902035130740621251600a1140da01070040d400485509000740c21414042c1e40c4104000400c140200c1d501900c0c2504400d81110000040f50268031114080300d10800402e01d215101d5840b00c003a800c1c002c8245043c18018400c580c0451080c040500464006000d150b07000a8100d2409007019001e8000800d6501e107001190000000715806110305003082c9041e5500054038091850081c0c0300c1914030300c0140543e031418007000243d541440c1c07404c96241040340c12044640d007101160001206c1d68001c5500001e1b50001d002c105070704120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 495823453 1250 495822203 495822227
    0x20409090302071d1f03050a0605070e01080f01140310090819050c10050604021207031d070b0a08061203070b04060b0306040c0513150b0405030d020f0303160c0210 72
    0x1094440300781d910013010380c00c0b4002c800f0b8110665501004103168070307103081c800c21040c0212007884521a83c0c0780c82d05401c24554190a840554a0b80c0401401d1944a0115004050f09007080612420800d4548225420501070600306010101c145511130b6410400413035a48540c20742445031610b42d240143ca20f8112010780b801401b07800444002e0306008009a46860003d81e008150f107071825846a00542070181000d83c100f6400c104841c03c02c5c000103071003403140c02240c0b004154440481c1e0301d40c000785020030810259801c89030081c0800d2840004a81d07402410303150003600c545410b40080d20703411241358400f5540c1f00008201040003802240c4511a50048608002c40c042c0e06041c552551801ca800a1441390300030020b03c09860009100b03141000352620004080a01081a1200c12480e0708091038841c0f02140420143c981084004d2000c20284054904001038107270403507a0740405001c42e80b07080da441d24100303000d61052840035a641c5e002007908414803000d840c00391001d00040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 495824703 1250 495823453 495823457
    0x91707060201181a0a0204121208070302090f210a14190f060507050c0f06060301180b0414100f020304030e03030c100203100302030618210a030509100204090903 71
    0x524800140f0006000c030160358000f0849071812085402c501c20b40c44004100317103c01c0f9824480841d4403400f80a44001843c401e5111103c000d000c2d500103000c221004200100305030040100310200e031201c4000220140b0305803600d0384008024401000440070680120880d84200201c03c01449100c602d85440e174404101503d00517000d214200b858031800c664090700a481d6045200300043d0160311160b0300c0300441c130304642060021105203040c118080d880c41d055034841400e206086c5020702c0764000101c0605460000301030995207144a120009002416404e4401e0000c200080c00744007940d111501d12000700490004038044d10001e40050364142c1c0000c5c040c007110f403000c1c2000802c5401440541c0f0061a102e0820014140690f100400100c00508600f00c00001170728104900750040c008080344500740c5188090803450030f05800800c0c004255000f1041140760034880071500c0401c41c51901040035a15a26000e00e0040c1f00c030300c110308442c80000c2c00034038803906070f110004543c0f0903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 495825953 1250 495824703 495824711
    0x3060f1202090a0204031202242512020f0405030c0a08120c03130e0f0603010501030804051212030c03011a030c1603020c0d08090a06051903090c0305010507050702040b0616060c091707060201 84
    0x501403144030080c0464038981040409000cac0d4080c1078054400550f5090646000b401a69101c0031850990300000a5150071440205040c4030b40e00e0280000c2c5e04000d0180c0c3d507510f0461400174003959400c16030942d20000c0c1000500340f26151010710844403c1c3da031940142c104282c2d10829070148401c01c444103040c001a40e00030503440c0c0340c18040d840c12250440d80c01814a4109000c00007150705144412003280b00e07601342010122043c074051849001c0640301141c903503140070f514868210701000f1070390040c03500308104180c00d410001520661200644074102d03198061030164644040d4200d02076000450740c00c1c0c9801c20460310020003108101f0717581d45c2c01c10f50b44c07400262564001d03040c0d02c00000c0c3d0070300c1110405511030380c40700c2c0c2d44500641c0103004459a90f00e90508456042c1d8011000810015000e819802c1c240501c20101a00b0b50b0042c0c0b81900200407121400c04140004080315200d0300300e16542d03072140e0340d01d202601550043c01020805499415540c1c0400e10880025500f4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 495827203 1250 495825953 495826003
    0x14060a05090303040209060f06120108150601020d020619090501290d031b03031104060302031012080901120b120f01060806090312041a01080a0303060f1202090a0204031202 76
    0x40b00340da01a59018184401c01c1d2548801c1103c14103040c04142d400400a0001c1124a25000b010314020106000602501902c40c0d0746115032800003400c5a041d50300010403451f5182e40040d4207a8414a503a50f99107810030841500e00251003460405860756080c0419151549140d0f020981050040008003409414400138462501c6207d44041c0c040380404c05a09282e002c0c0c654001000b0744a4500002c240780c50400c05c039039980054008000081c0d002c010040030190000380c0300060401e00b490005880c40b035135200c050501c03075240c0c0581000500d400d006021052500b18190510700102510307091804510116690400e6076000d804960900c1d0700010305078800300b03c0c3c070702034048036001c0c40c0f5020500310203099001010300100ea1616010310040d8041c14804203007406491050094500041e45081c018241c0e642c0b40c1285c8007e800f1003208000c1503001d00b50250005a040e10340250391703602e50f030a000090040e81d00c064031061604222001083c0d0119100d1451010740a01903400c4803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 495828453 1250 495827203 495827221
    0x70807080a090609150503040503120106261012050a0503031f09020f040b1803060103030e180f0703110f0403030c050f0319081305120a091703090108090a14060a05 72
    0x1d11343c070034016500295402100c0e0766100750004c581c0310340204101c3c0d2400e0501464607060040076071100300042c0b105d440022600000014440c400d89039151724a80904207a01091000c401c284140c680004105031014100441400700003401138000302034079200d127001c0c10f042003c03002d4801c2c9500c4280700f414001c03820281c2842a145480320051001d4201420140301250f0b0754810000ba9803110010440d854180c0e03070400c10700c1c0c0070314420740e06c00072300305c4061050041507400f00041042c40140d1000300000310359012036050340f0142c189400709030850300d401303442c1147c8a00700d1048040140040e0101c20b064001281004044c810000c95030f4025a08c004e141d12030140701d0182c2c031950780340080061224410b02c4020340181c0c140e8040700111000d5900c840c607104010585103250000810200c09990300718030f864001f0003c0003040283c990003c4000c588030f12881035041d042c007502b40003203120050200b0581c0303190381c0c1c00541001006c40001d0305940d9040c04585d80c81c0c000e0304100c0080c800d14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 495829703 1250 495828453 495828467
    0x408042123010f15030204021c0204090915020a020607050a030f0203010e010f0506030f0609041109130c140a0506070302120a02010204080c0a05010512060102010e01020a0917060402030a060c05070807080a0906 92
    0xc204d510301c2c072100b401d50f801c002c041d40c0300c00124104020403072480400700680e40b008100800f0700e00000254400203150100500070f520305903002152040c00300410580e00401c81d960300140a20b02a0b5603070f000d0501c150000c20444840c0300d202c610200011409034000b502c150705881cfe148400440242e5108100201c52200711049001180502c0114240342807200c0815002403082c01140c04040b0100c002c20140501110240052000382e07002030248180d10b242000608a0304116901c51038802000c01c5400505204260050500140c0c04003407606c240a11001c058600c000541d9840d80440024085c1d0480d0180c0c2d12240250000344600d403a0100e082411140c041e10340904020304083c00c840b02590080c40325066540395034061000c62070a1004045d446071036101d96840e01d0402c850581c0385400468503a4507903001d08280405641c00241e40d03502c180e8086804a001541501c00300c0d19805110801803444c0d0000c22034004101d03c000c0a40b4401c8103640e0b801c030005239039840c220707405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 495830953 1250 495829703 495829721
    0x61b03091406160c020f041a210a030c020d0b070818010b0901090e010e102711190302100c0510091205070201090509010b041a030408042123010f 64
    0x5402d18030350700c3c0e03031460140340c03a002c055000070005034a000040c0701140a84140e141800b0551a0300403402c001854050060301e9105180d80006242007140032455554522018005e014800345101080c02c5580307083c0c5180bc0b07550b105000700018180342d540034080803421386152444002c88440101a507105102c0c00b0701d00750b4018130b025001e07441c044d2050300503c281088455195201d4030015041841001020000c601520700003a0260210090040d50481c0d03c0c41007106484841d001001300b4034280100038208021a9400d080d01c000c00181d10020046070300003900302d00420218082030380c222001d0b000303060003201504d03078211003065400c040b1103484900030052041800c0d02c2501c14030500140c43c61030b01c1030614440481c2ca447c00140d403035009078002e003c221000501408084d003c1580c400364901c1c0340102c14214282a600c207001409240140303560039100420b10440409000310303807207c00382c000c5d080110741c02615040c0d400d480f0100345c42803195030070300d00c10004040c01442a0220 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 495832203 1250 495830953 495830971
    0x120c0f0f06040f020118140f03031903022a010504120f080109021b030d06090c0801120b0a0b091003060501060509031b01210b0117060f0409061b03091406 68
    0x5642e4581c0d07440e0103021110300030780c104402c0403800d8407810402c0031180301a04100c00024405c0101c942006000c40b40d81081d41d019800c01d02c4054903803d108071604114a8903402c0c0540c4900c0184074000000c0d03030f007030500f050301a610034020640407010b500281c0103d01600c141ca04151513888103036079107248260107600060001c00100000b0b09250b0240400014001411003000350640c121440d40e04000300c0d1046407507880004010b05401449203003030165940c10b01040319807605007884100d030700c1203c000d80511000400203142c3c0e40d50341d000406589000385243c4071414480c0314031402c2d98031400101d60346803801c000400c0309400741e0199980180010014143e00740102d00c4070b5000a034101049046c016444012001a0115110403510b4405401d0000d1044110400100350300c0d03510400e0100c51340800c00340145501c40d60141c0c10502d10540b004202c1544500e4680c00401000c820901d400310945110b0401c0d581c141c1110003000d00030084060b00001c5e91541d5603c03400c00340c0340013007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 495833453 1250 495832203 495832213
    0xc0519030317060f030106030302030c060906011811070f03051305120d031d0604050607021209062d0301080717061510020705040213080d0f0207060e060c120c0f0f 72
    0x401c030b1140c0d8000b942c8207102400c50b5241070480f1000c2400d66200784c0088001da0004611800c0d0107004000b1a030b406030640c0020049940f500e0542010190a416425011500e550120006c5040c0b2400c0302c80b8180c1c029281c80c0c203042c0c24240141907801c19901800d00b01c1c0c030300c140010189041c0850800060030700d006003904240051080d4010b068015a60410301c080152a80424405005a5226a00590183c809442d14080c000c0c00d003040013980004a910a22213183c0340d032144000c1d60070150b521340b11401040c4003070507150340c40403100c21204402d160001c00410f80c0c490110b000300881d003540c122801c01c0345009510341c1d2228421140800464481c8021070810300d0103001140100e03c060054030322058440c0701103026030744604100d90151000e01400c104001d410010704410341d1040c5031410306803000c014025140e031820300c0b600782002090380d0b5054456613203030111040104207004444070f0340c6203455540080d0304084100c580d68000d0303058040d40741c1d030049008400240d00002600c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 495834703 1250 495833453 495833477
    0x1125081516030b03010b04020a03091a01060504060507050f0f0c10020601050d080304021503100321080a0b031006080607090e0f0c1c020d0510051009050402180a030c05190303 77
    0x2030007818001c41d0a0744c10341d200c030700c100104d840e14402000804859a80441c0546650510075810300c07030009141d0f034135050040100b101c181d002054030182d401d903161180c0e0b50326450904134500321418244429a0027200b285c1c02a1803400541410f65083c1580c4801208400080a07a1202401d100301e81d002405100f54800081c8410b004507030061006002d20009100a5605011508100d482c44004110180184107200b03181c1e42e5403121001c60603500310321000c801e0f0000e09982000e044a0030241e1150015100c50394207000304580072941d01c40400100d513503030a00b40c0e074580060f41e003d0045a483c10010a204407404812841004401001103d84d107a000941d110350707000c52a90300104900b14102c0b024015240010b0542081410700070800d405e0200f4120092155030340407a2103128046504c50035541c0001c0703900c0c1182c2080f82c0c010b84485040182d40c1a45046103820380d40b00b9800c06012082212141d070000c140c1c1c80580361505810f201c2e019000c42e00c1040d00016001c907004001c65 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 495835953 1250 495834703 495834707
    0x31e0b2715060d030201111b48060a021e01020c0d0804020307030f0f02030d21091506030b091603030507080a11010c0201020c0f0d0c02011125081516 66
    0x1e034107144284000a40340d0050030310b4050a802801c805030001c10301c60405049401d00b04540351540403084162001070000380c054010828110009c0c5d2580317190703596204402903030514690300005016005950710604810001c0d2503c9544040401000302008a4440c0000520a98202c0c11200000380300b44503403c07100b9281040020022a0305115140000c03000900c0c881e98122118858a10349076501803520400d428043d141c140c80c410801601c0400c001c64450498030303008521a00c0b00001c11072902d0a1004c0c00116900c3c241d03400078105240042002050b000c0a480b40b4442d200780c40b6690360900064040d4401031201900190050102402103010344005010303074000d40c01d000d0503c07000d180080f4252101d5103443e00243c0d40c04182e8071581c440600907070100c00c001c1c5002e000b6122005c00040d00e444000390000c3c0c10009640e03041a560801007180016441e00d6600c0039204a406100f892001d1000e406030501c1d9019414032404500c0003840d51600480b150b01c81010b00340f81a10007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 495837203 1250 495835953 495835969
    0x1718030306120102161110020114011202010e10020c0102150106020721120210061d0c030702031b1608061b160c0311040509070609031e0b271506 64
    0x41c0da482d5508000c0a014400c145d824618454462000d84c42c140f00d07140b0400245110440203407066905101040c0b81016517015400e042d941c0003812009505050700040300c8050030740d0f8040b600b09650040d036002050300001c228504840c260700312812a066010600c80c445000c2c803c480142e441a0403c2c0080076100c0100107000d07513024800c1c4802c0d10b00c0c0e161808201006818800980c0021220071902610b030b01544000d0112001e1000d034681c1e01e0300c50b5050b0340b680103000860181c0f01101240800d4801e004071001004030200500c0c882c400081104c3d100c4510940030911721144c42c20000c0e10200100e82c40c0d00c184908030750801110f2001c00d02100c43e900c0268281720b2000108001030010b180302071088041c2d8054070315010340c000028244011544080c0c0510221b44c4209820880b071a0f000c03030f40f0320a580d4481c80c1180030383e200b0030f00050700d040c403040000e2602524200304400d01070000032000482d8200c5d901d08640c101008207140d1a40058242c0c4034108084000043d02401d2241c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 495838453 1250 495837203 495837229
    0x32060703020a03320c1602040b0a0513050915040b060409020a05040c03050a0c110706050706060b030c0702041d0d050c070b1303050f0c0607020103050a0b0a061718030306 75
    0x38049030303a001e481c0c074844030115000f0440c0e1a14001600010a004e00d0800590b03100e840500304500d011080c0c00c002e04507410742c05c0b00038420791300d503582c580c89500d984070704000400303006c0c00100080d401d14034544050041106c0326885440384941403e01c900c022454103001c0c5030071100340411030304c942050101a0050a4059802140c1c9180004072501c40707200300300480c812a0303800251400c08000c03010603283c124500d40b040042c4d8203a010f8980401181c00c0c1c2c100e555a090180d42c0c2c40062400708003404d0700360301c41d40c08140b021040214600d502d8006010741032003110300300820012050350510030840e89904450307680c0140d00104546000e8001440d4980c1c40c1000c0340c0e89140e0b1907502a1055000c404500210381d12507404004202d400c101100c25a0400d070701a0104240d04804200c15000e050300c040d04154850000c1610844d2990000c0381061029106030b00711038654801904060140c85246081111103002558020019003c1002e4030305c0c0304061440c5072940001c00084000300700c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 495839703 1250 495838453 495838457
    0x6010e010e0f0d021023070503030f090f0a0b07032315041401120b09150a0209120a0605060f090f0403030b0303040801062c10150512010332060703020a 67
    0x18001004d40d80302a08070080045d6540c03041001d65001c6030400440d801001c084040072001d20104e80064804000d0300c0d8415000e4800c00003a945010405142c403030420106483c601132031100d035081c03290382503040d889940c0c941c0701071107007078140d406240038190441c10070b00c400204030000c1a641c181c00f03030048110000040020801c20030049500703607940f42c02c5c0e00c0410303190010503181c0104a030802c6060351000c01c010181140124507540400d04800060030115601c0c0d00048104950b5103509003c2240341140d400c4843c80a06450200024502914100d1089030b01c1c2070548014581003241a00c10b442901c10310704d4a413200d5a090300a08452424140d1501040c0004580b21001340708080007004151140d0000c000840340f0b06100d5007991440b0403543d60204100070300c0c1168040e81900703d4405c003d01c0d501045804d42d0488990250541541e40c0e0003035807000000344000240d0301500e40801c61400c448002000c4c84806c06046551a1032660b60009400503a8641c02540500b507112594 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 495840953 1250 495839703 495839719
    0xc0801230c451c0311100e061b0a0905040c110303070905040614061204020d050a0b06150901210204091d010b0102010506031005130c0b03040308011a16060e0105041a06010e010e0f 79
    0x2070b805110a582e028000c100c0552300c0003003044014010100048ea80c0e00024050310701c3c0c00b09000d402401c8400c1401344074003840d1110110a9824450061030301021084000d60313031242040e0500503c0b80000e0b00c03c2a01c80c600304038022484e401054505800300c10000c0001e4507004c41c4c00c420708100f10b4010000e9031b10048000100001c54001d105400c0140e102c0c1d20b0040280c9084400c0102d101748008214910301400e2203400541d03604500d003c0031b002e2059501844101310a802e4030045c0c819a0440003070181845103d1001d5414a0341280044104100038800602460012400c1381e0b02100e81607810b6212144410302e0700516800142c200900307110b501c0701503c43e078480c1e042ca0603540d0310030060f00d8000820030007415840541c29015040705440c11040403400d209034890f5005081c1001c0c0400f600001420402400f940111500c012080080c405c0d0302d07140c00c0545072000d0b185000110440328100056240d84a080b8160500005031112488c0c40508014400007400d0954416004641 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 495842203 1250 495840953 495840973
    0x3110a05100503041e020f0d0f060c030b01021504030915030b03010c0522180b0607060c020a0209100f0303050c10090c0801230c451c0311 61
    0x30803451107114566521425540e0a03c2d281c0760124010040b40c20041000c0d00d100360380143c4c3c600306540040304040b0b408030304041071420312040c2c028070402e008020030300e842d610301c2c43ea94050f04420341c0700100b40c0948440724030140c1e00d14044c130360448009000648011052000a040c5150034558520524001030754440c0c100209007103c1413443c920003c40c0c1c021400b2180080349a160881890890066140a40ca0101e484d85116503091903441d03603a40391058860305842d0042594811504a0003e111703031544140301a4407150b01c017506902a2501e02c000410000f8441150703421905180c00301d07106c3d9895500c00b1175568000c0450200c0e103019840700c04c15400054000c1a0703170940511f6a40d00324a24280e40c02e42100ea06001042036402c099116881e1400104d090765401207155506a503a16511020040b001c0507454401c98544038098010300100682030705030346e4803041d407a000c04c3d40540d204100043e03001d4402d0540f400841c4a500c04001920400c202c02074044080300b10b96207200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 495843453 1250 495842203 495842209
    0x120408160809100302070309090221130b070503360f0c0a050a1802030603030408100b0a0509160309140a0f02240d0504050c18041a060a03110a05 64
    0x200c542050703884039004284200985084280c4035041400740c2003c5260191656000c1e1801345a44581510941d000c940000408a032440d1a407141c22442d5050b98603140a150b00303800c5500003001a14090343c0f14000526641c0200708480c003420b48010f81d0b54109500c01070b480c81e404000b02c24450107613403a81d40c1c42d51740d40341000048565040b01024040030314056083c8060300080b0b610040c4101c005101c20440c64a100850b851080c6200c0c20160380ca64072140401e16600c01c0b644905440d104c0c0140c1c4001c0c0464560144c15124000c64088560581e00d000308121003000396a1480e50903051101e014619020381d100720300b8107101303d540f6014400050007a17800d000450304103455101c01082c0020443c9810988005520f0a6149054642090303407544240780c0905030b201c008541d60344000c0790500030108962010110028011441118201c400e008640c00c1514121404184200d4141d0004039100ca01441484040c0110103d6869502c1c0c4412440848007000d4105902d4800811261 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 495844703 1250 495843453 495843487
    0x9010b030a020f0315090f1504050604020c0a03051213120305042105040608010f0b030121060203040807050f0a1119080a030c0507060503070e040906290307060305060303120408 78
    0x84590880021007102c070200380180c4200c007c05a0b00000c0c900802c1046401c64206850030703c034400d8500148907502c282c0070800910030015022070034400c0000c40820941d20a008114190000001c00740c0707604c400040d103241c5802007100a148079a55081c0e240c070648a41d100b03680c480e000d5881ca0714501001c10003020b092801100d0f400000d200000d007808441d0300710541c2401458822402c22409141c50084a151302040c014540c80580048001d052010710b00302480005800000c115564182481c00742d0f0240e001c1034003104c01d0700500c48009005900070602080351908245890f41d002c0c6144200040188100740d0310464480900000c100140100840010b00384242c0b5007040f00740d040d080c094602403444c1e00c035a040140070010058500c3c2d0140280c041c0368002c7d01d002c1003040300b9140c80346c003a200300440000b514040764020b940d0890a455540c07050b000503070680fa000380c0c445404600f41c804c112101030700f6a00401c1040600101c00455684c01070180b180719043c0203584141030f146d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 495845953 1250 495844703 495844711
    0xa1508010c021b1306060503010611030c0c060702150f27010207180e010e061f0b070605180f070e06180f06030307120306050411040e18010f02130e060105040509010b030a020f03 78
    0x417000300050101c5500211044000490000151304101400c070374280da5000c1000c02c903009e03480209104045407550b00004502194035001d844e1106030000c14001c0c250071a1200500d2941214040702080180401d84200c4c0c54040e0b02828815040c80104001c841441e502054001d5840800340100e020038800c81c41d94241c0080138000350706080ea01c007441c8106250040c91901180c410070171402500008460109a100300042881c0d038030001002d0004220640c002018015809011902240032a4680541c0d04490b040d0202e074a5101c24440722003007001200003200305500104003001070000c0840e503c41c600408407450032000781c2c0c400d04040c10504c44900800e4841c04140b00502d030502883e200504c03040012400c00b0318101e894134038080064030034016602c0081c0030300c0d4540703000c0d00051a4000704c20000e554600c07451940c07001200d0103200d52060a0000c80208120358030030382c1101c0403500001c008824903400e14440e083c02d948042d2034084034a9081041c00a00c90701d1074013451203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 495847203 1250 495845953 495845957
    0x90c05090406210303180b0408120a0608070b070215130905010e04030f03090224070605090f03070201142808060306161b0b0a1508010c021b130606 65
    0x26540c04030180720940b82c4076041445203525104800700802e00c404148000c040d05441d001c200d90074240c076004002c075903c001c040c00080c00c0604100502080300d00030003c50340b02d040c5640242da104481070003101d0341c0340035210494202d0002003041c502c0c150043c000343e9000030600240441070036034501465100100c01c0071071940009080100703180c9440b40a00601d40705c0c143c00d102d8601580c0050225240c00c1440080c9940d500c0408195103400e90310b100d14408400006801041c3e410f07400304982c01105040700e0715410306e17000404508000c10301c03030008501c01004600707000c2554015107882035401d40c074074481081803280454a01c0181c0100140c54000d045250888040150003002048010715050084c0c0c04030080c417400d19840b40c3d5980c40b8072044e140400d01e1200c801c07100c0c5440070080c84090030380a46401849880c0d0460750000c01508000e490b8840e4882da80c1003184d0907202c040c0c454101681041c2c000705c0ca090101e44480051140050240140c021407081c041c00f294225040200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 495848453 1250 495847203 495847207
    0x90513020f0c1c0f0c0b09160b03160c0c1205030c010c03200a0e0f120604080903011b020a150b060c01091502070503030610050f03010905090d0c230304090c05 70
    0x2c4003c03003107400d41ca010072490704c0703800c00034003a401604403460328000409001656000035a105014840034400c1002a642400c0040c4e54141c03c2000c0d41040d00c64100040002c0301280910b4040c200d9200b0081d0700c6264208440e00c0e0208110440616440983d9580002c000702c0d1405202072090940801142d140024041360a0b0141b1440e034041098500d00b4400030443d2030b50080e0025000c51540001b110700c00244000b100105100c4180070592842138407811080c401000300d0704001d40104030701a402081000c40260440c00f0315400304e07009001513040ba4140c100401c40e007606010026042002c0819032203100f80200c0c85591045c48601030a075961750700102000354000c0700f8480b0084089040d414912252540c98a911000d041c191040388400c1401003214014400d4074400700c0340d01c295a80300d41c3d40e480e840c009003200b122811501c3c020600cce03210009020b06005d0008627000684c204030b0914a0b1022441010060b240078014030041c0000141d246160042540c00035079984e40d15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 495849703 1250 495848453 495848473
    0x804080c0106030b0712061a180415090b0405090c010f080702071a0705010506010e151804020c070303020f060c0d150b0f120a06120f1412210403090513020f0c 70
    0x4494252304040d0281000c02003050300c413114801034800304803d641502070701da02d5560001e00213090243d8a000825100c0d50300140c110241d512000c10b001040e14140195270f100c206843c2c44042503003000c0d0209849101100c2c5040c400c0101c44d5100803203004490300191912482113a056101400d06540e040000f480c1d02000402c0c010643c10413000e0900c40000c8041a00140c401208410107003009070001c1800d15a42e4180341c0c1e02e8040400141c001c5542d04005814039803a010345000581c013500c19034213401c000303a2001a415106110000e036031403d2040c0105408050f041c81c1e00150624500d045011502c1103500e001050b0404250003115503d005150380131a507d40300030a4403485504e0803400b00404c600070096018107551280e602c02891006d4545640042c00410545096120382c4020401e01c1c80740030300a00310b59142c02c00003803800c002c80114158425003150000c0014070455810026410000440f203803000d00c485016007400601c030304601300c030b42121030031001903401070448c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 495850953 1250 495849703 495849737
    0x603020405013b07030218060c030a09120206120711060a050a110f070828171518190e0a0b06121506040b0919050a0c0804080c0106030b07 61
    0x91141030441c3c6091600c1c5007400321051412101c020460740c145a00003c00c100700d0066290320107110000200386503180c028421074142d03260000085600483e104e0b800c0401c1c98801002c134090542d500604281ca001655550000200c1c0090420020f02180804400d075404040c8a1184120341c04580024140360480103181552000d42180040b035208000d604102c00b051001c03100e80640003005c40c0c1e03a8120307a0202025101144900c00e01c03109203420080c141a902180c0440400c0740e61a41c01c0d507035104d10001c103030001041d000f520351054141c0140140d03400780301c90266100750340341c20f0303940100800500384064031a80c085c03d280c250800b484120402070b10702003c40e000fa00c00d440a800d0305e20196a217036030310102e07450343d1403003d503e12000803566031b16a042000303112400b4080342c03101c1c1018030007400210300c1550310b00c042034100400200750b6542ca00c1120102d914070754032064241c4a41d220150627030301c01d070206d04c0d80f5500e0b50030200c0492101d804090042d6255525000c40c140b0f40140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 495852203 1250 495850953 495851009
    0x5190207020105030a09020a0308071401060b09130e1612150b03060f0c040b07060f0c0e060405061803030705030307020111120c0a020a211101090b0f0406060302040501 74
    0x50511014414004140940d0b840783c15640d05c460005800200c4102a00000300d02c108590300c0100711210004180040114944020b464000b1a500030300c0b1440c0c480d10540c40d10700452011680007080907024104600f01a0821072600d02d005040e10700c8082c0369008643c1c102e00c00e400810080842240c92410003a00d1800704203080c601c02020030280ca04000002c2d02d0302000352a80d02102844d10124103041c0309181210002c102c00030703a81d90b49070a14078040d40640720a694008044e864609012143d80c011400701c1c03245003004054510b458180000c014044e04183e00441401000104505454070300304001c00c0841d02810003140c4a1500010003130945146400000301c14009202454104140446880d00824591003080d06c4050080d0128548000920040d0401c0c824508440114042c1000307000e19001540d5403003540b8590000040c203964042200828000c1c1d02c1c40000c900d07004000c030554020344660b10204400b96070341c0010341680c00a80182006901c403e02103405000c100f80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 495853453 1250 495852203 495852241
    0x905120102040e16030212100305010b090c0f0d02070203030414130204080d0309020f040c08010f12050d03050c1b0c0f030109020d060b0301020405030a0c08010c0825090305060a05 79
    0x207600d41410401a085400c5010b454070342854018002c8014443c06501506c60307410428480c01401c2c540881c034010140890710090340c0c19460110303846040c0c180034a8161042c420481d040b8035155100c0b48601c12030b03100700c880c040066401d2041000503a0300784018030081003501074040080800340704000614511040b000144e520400081144407408506d01c4004609420001900d041070f001181d18132101110456000d864a20141d210582000d4000c0c16259030000c585d021325118480c003070b5029069200900583d0064a061704c84512035003015500c00c1c0700650340b42c102140c25611481074188250b03103107607940100540b0b012608140c242810030707007002c400900480c0702d17640104130b1040d00c0d01e0010b045141c440d1036000c9640c41c01d4045400034500a0101e5000c6020b5090248001400d030042a419500341507003020014800c000207401030441c0d4401c03010950b4090764041e0030701e4801d5410003e104803030900001165050142520a4046020106952a140840d82100c1c6080c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 495854703 1250 495853453 495853489
    0x9041b05010c050c0409030c02220c0c0b130c051e0126060d080c0708010225020319050a06020a080702071a04031103011d030c0c091501200d0905 64
    0x40202c0103d8800215000c6514007031358006500503807030a04861400c41264007a4121050441d0081c10301504150303c03405958421341041318820a0354200c4400f02c07004000380c05400c008000c10b4200031050f421a0029104044145220f6900e0010031a074140403019503230140d400703011038085941c0102c5d50450301d20000c0114420307081401c414188190f8050718041c0126903204a01040003008070860b100107042d1002c803880e8a40c1d030703040349000c1e40c4041c00c0300706034003407582d0005000c02000140050b42c5030300601600c0011110450f80e00580b030241e90666491040c10340e40c0000caa030714401001e646645a4940c0c00b64580351001a1070b00e040c540c0954a49081d1107a20078900800600381c50a503544011000c5440c0274090001e4054140b00da802c0c0c9105560034181c0030209400401052218108800c2d40c540800c08020000d0084003124075804540d40b040c07030600150311034210300c80c0b401545075109022810b076103d51494005104d110002050030101c00303000034900026800720a034044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 495855953 1250 495854703 495854717
    0x503030403032c040e0c1809071208070803010311030d0c03021b0a0305061501111203011202040207060501080c0a090204050a0303030207020d06050403030618020702210a0209041b0501 81
    0x50b03903000381589040c604084601242120108504100b81205611258020310034014202d1a20700d850301c800712400b0551044c1008842442c01c010000c02c05c40c822502103020300051440c00030400300b00c81031700c0011a0711030b0040105c6000904103401450281d4040e141e1322030900942000c0c1403404500300004000d0007019492080000e0b800030b041c2021120345100020810315a1010507030030641a0001001030082408200c542d007000300c600451200700344d0b20401160781d0742c00c4007910388008618440c0501400c00040c403c0081d010310102c14284090001440c004076a10390b80200c4100b03811581d095086100584c103d444c0140e0040d0140401110440c036140c5004009861b1a03001c0c803004041c590007203a110705545c1d03800c040d2042c07250080741c03c0c006840c01340350060003070030140030341403583c4840c9815810b039861520988400540c0505800c8510704603016602550513240c00c150324034410284070500580307030346408600461251318100c0500d9901000e24042014a40142d8100441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 495857203 1250 495855953 495855959
    0x507110c040c02030f071202071a030103030516150606021e060f041a0c03010302010306090614210d02010509060f13060507140406120501050306010f0902090607020d03020604050705030304 83
    0x3080c408008501141c00050182d070059040c0d045000700076403655261008503180c82400803041c020310030702c94070b513003664403040d00c0e11a0124203918508085448582c144014400240190010012000368203d04c1c011b240503a61050340c0c0e402850010042251100340800043c0c0d010816500203503e45102c0b12000c002c540509641d44074010002c0503540306150116060004480100e001c3c007180011f00811482d2050168180c2d50081c80200c1c00240752900c005040c888910810098506540f0106010401d40003000707001041400a81d81d0b20190100d000140e03101080350a07901503050b000455146401d003405410440018100c000704140c0d40100107d600ca03081c2030100f202d41c88140040c141d02c1d0314004485400010300d945580840c000360110303506412007800c090540f4406814002aa02c540505031140d41c2031044041202014130188060801b0707030007801403400301800081c1443c00540000303074412a509420740260b0400814403080c400184400c001a142c154011441c2500e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 495858453 1250 495857203 495857237
    0x4050c0c03120a09020d210c171806030702100b030606010f0f0318080d050a111b0c13050124020d050c0a050d0f1101060b070b07020a0f06020406030507 67
    0x414022900840700e201c4000425558140e03024800d0f1340d402802c0c00050450038031300308141c00c020200b00403404c25910100c0001c0c9204460200078284e00003903400e104512120102d4250700044078001c040c00d4014240714581c0c4450010b18400d090f558014040b1501c1c82c11542c0c2101e41901c0c1e1070340240c200000b002480d9030440908908405940782c400d400d0b40700d1844c11001888001c40414507042100450010f0080010280c03e00704059513040005850741c00d0054100c4460a000c00704000d000e100209807036021300300700c021440d448000e83e000900501c00103a0b01c2c009280400065603601e9006218100000c141c1240d4000c0350741e4000c2491b200c00307001075602c6106500380300402070005244010400d0511040900d039034030200700e45400002c50070103044134401040d500001104000c422b00c0d550014040c0104030746043d00380b14500f03c85a00c4448000303900500e01c80940c400c030443c1c4000a152440c1c10010300d0f028140058946081650003002c0d1a806000401005006441042d03004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 495859703 1250 495858453 495858457
    0xd0e070f1e2711040501030c020a03090509100f0e04030f05040803090d02040b180613090321140103060902030607030c20120706140606120a18060e0c04050c0c03 71
    0xa58611907a040001812064103a22a00b8203051240d0504218048141e103a503800544250f03402600c0c2807002c100c03841d1049a40b04c0f9460b2000c2d0000300103500030401c9050500080d070704410300b1000341c110640c4480a032282c49900380e008440903940f003000c06c002e1551000c820310b006070003850300e2803416181010003690790203455400c51007030300b102c1d020400310341d51540152000c00000d0046004c00b024103211002c80b0508960032801000715000d00b4008200c240b2400c600701d681601c8080702d40350107036549800f89a4071208003c5045c0e4582c0b00c0070a080a03000a40d00031440b6103030126030540a07106041c10407801405078014142040550324001e9000344000040200006d80b001c83e1260743e2292a00c3e202011150381c0c41030b20b0001d10201484820342100e81d940c410b00342c00160340d80f244030a004040c0b01d48400a0041a0003401144003c5215002011110800d124121007100303951148401c4402c0010900c00c0d076801701c4070311219401c1500516a11220046d01c0713900303000c00296429282c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 495860953 1250 495859703 495859709
    0x5090106050301171c02060a2007080903070905090d0311040f290d0605030609061b07060b0319050f1f0903091a090307080327060d0e070f1e 62
    0x3035102d44610143c0c540403c0348201d48180c4080100545d4008800691100c030183e41a884490410003a10070380580504800110951848031900d811244d80303900903150801c00300d465250003019000110f00703020b80a0a800382200d03802500b114064220701030704441c0c8100d90b41d4688c850600c02000240b0315440050308544410202094045606100c5884030b02c040400700000d6001051402012120ba4800e0054a030700707030111289a140c01500c6c0d41d40b00382c111090308000c1141caa504040c44145000b400b070b090b02c0f500012500504a000290030540c00441400700001c00100140034400204074456101c221540540b18018000300202081c030140c40e64445000d071110480d40c101442051030500510b800307080d181c699480e00d4682c00d01a8850390303259200380b00d540004101c904022044424140b40200340c2c802008694440380341c00da4052590540c0810240948000b1902c0b9008801c041c541c0400500011418006000034a10450300b0124400400d82c6030180c0101021104800b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 495862203 1250 495860953 495860969
    0x40518060907050a050c010c11010f05040b0403110a0b130201030605010320031902070602130b040b04180b040e15130222060305030f030f250f020309120601080705090106050301 78
    0x134130350503140169090f10130030416429075840c16151403103070303a403020364840000707030344002440386510428503c026902c0503500545400540c0001c2030000e80034074241d01606c14a00300340c400010454884c180601000c80c1c1025000e400307400c203c000c40d03906100700030207400242010000300c01a40c06860004902100718404190004040758841d801c11247c00201c0350000303029036903000549820406501312074621000401092000300701e00e02d1680c2900c0aa4a000d24000e003024501403038040344103082c0001c803887c076a0b1090202c0b9a5100ca010ba10a0b01100c80002d210766091a080c69800020040009500320f1000c0b0484005980e01181d070000d0b401e80c1c0c01404000c41c03810328280020440c50340b004005100016000c00c040c2a0a40690b10400003040c0f00481d43c0e5401040c1c615904501480540d40c03400300c200703000018000c0c5441d804200051046900784101e00000c203442c00090410040749030b0014004218260f020001c25000d40805d0b24158015454547e000e0705602060041002d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 495863309 1106 495862203 495862207
    0xc030605010f0501081b070c0308120601030203070e09061206040b041209030206072a090f0e0309030d11160b030105010e04060f0603200a020304051806090705 70
    0x32114180c44010040d41d4071903aa00c800e9051b0469850000004d0101a0104420380c28450180d881008141e5884107001c151404a440051400d070405004104109100381d001c64003a00f0b150007a540e519a9442e098002009080d1481030310f4810b00ca80400c100c140002010458040c1d405221000510803129904544d4000c09010194200c4800c20040d00000c00d03810750984000c06c94a01180003001583c00d05840112a80c071074019030391180896000072005108420030070312014000c40c80c2082a40103e0703210714038000c660092102c0404540c410306003e00040381302d48480c1c0c11402cad1550b1500b12080c01e640080c0101c0d8000785a01c8183c55003420544101c205842d1403080c0d003e035007460300303000714003401e00d40d40e0103000f00c1e00b024402039564580f02c0207000e251010790090f5031980d0402040c41810110003914201407a15041801740d2500c4110002da00b049551920903 = true := by decide +kernel

theorem cover : BRFrame.Cov 495683453 495863309 := by
  have h0 := BRFrame.cov_init 495683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 495683453 ≤ n) (h2 : n < 495863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
