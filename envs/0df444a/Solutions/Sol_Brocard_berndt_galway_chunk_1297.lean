-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1297
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:14:21.254735+00:00
-- url     : https://prove2.me/submissions/30f892cb-2a9b-4f68-8fec-aece6e56d2be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 233093525 ≤ n < 233273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 233094775 1250 233093525 233093527
    0x531030c05120d1b0f08180f060c0301051219030e0f09130501050702190807020d08040e0a1109010e09040c0b120a0e0c0a09020c070504051305061515210c 68
    0x404e41d1003400c0c81301c0c4512409420b1000200d07030514001003401c1c030001c0100101d40b200a03d1001d20310800c02055202c0d111801c1102c80c5810021020556600240718040c890400c10b40c880ca603400b00419110f90000044005240d0151f0a960903111002d038208015000052103240040c980e58240006d0b008540c0703110b4007040e107803150400600b0365000402d03510540d440300411b10020791003c15407500440d0006c005030740300c14079131002881503a4407a6010b07291380c81c041400319450202c220f607280100240c2c2c03810000700e1040c04c0d844009008230380580b80410748100c8522482e003480c2c0c0034580d00504c2602021101510f564a50690380c000503c01e464104541d820041840c00d1485030f0381701d03101d444006103285481840040d41c40e40311405078905141c0c01191080803130750200501005043d000700180300b9460300c800414103214500b030003902d40d88102d801190310469144580070a540000d40300c0c03020306010070300c1900a035004808030280054010003441d4a104986440f038015000e134030040b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 233096025 1250 233094775 233094791
    0xc020a120506100f06030b060d091b060f0e0f030c091f09200706091e050d090f1502070f14180c090904140a05010531030c05120d 57
    0x36514000b03000308040120244200140705003c2c80064460485070b5500c0c0210312518070802084190080380813030400301d42481c6151080001c3c040c0d1074003100e0044005400710700d65402d400c4401c1c1116a031200d000c82c1143c000b400c1c1c9d6046c201074149241d14041d045480410204000c03842c000b0381150031844a5001a0003001650b403082d08070001450184010300c10102d046c0390013000d0140300803021500741e400150f0a003c0040c0358008811154100e13405103400498503031040e0219103031740021100760140c4010240640c1c00b0381c01610680700da02180c86a80e40c21304500700d0105812003500c20540c07041800c0003883c480c40b00700503009011003032000e90610803120103100c044c2c141c0401070489241f0020400c03100c0c04090f41529192402200c0398803440c0c0305ca05100340d9a002c3d400c106460b0b4003407040d00d50180f060542202c0c3c000c502c1d20441590041541038181d40b015801030201d0300c03030405c1c072045002003846455804401d0740900c0c2568087c80c000b100c2e003022ba40c040103001404c16214011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 233097275 1250 233096025 233096033
    0x4060e19080102270306060904020111010507090306050f1b030c130801060305010e1504020108100801050a050412020c0d060908090d050d18060503040b070207080a060209030d020c010504150c020a12 87
    0x4100d0f5040b00d640342d401c861011360b0300003944420f40148a14052608000043c055a215804140070840900000c1000d0b0400f420014842c14250009444850410000c076a07900c110580603807041c180e0481c1c0103081e9000c0c00d410b510547c8007500c1041942801d002d210266a55000000c004003100e2000003110341c55403400d6425203d101181003c141c1141d00c0c1d400c0484808842c8590080e42482e000e225030b6102018a040754030b00e600203103100c0d0328000030030101c0c0c2032950089000c0c0d4019185482a0140e2010803a41d403001030540301d03007107907442c0700081c005184e980150b080d0341e00c81c850603800c200e840c01c0410701540704403906403666484800c2400706036401c0680640b400144124040b885800e1580151040c44007030002041d46400e040001d601d14404c3c0301d0300001d40b507501c3c00d0743c081c18614240240a034000c0e0000340d120340243e010300d174489030000484008d45141a151a8103091030500401e400c1d00042100800303008a2410910040c0c0c2c541c0501006801442d1418078848842d0070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 233098525 1250 233097275 233097307
    0x507050f04080a0c1d191401090203070e030f0a0209190c09090c03021303030e01020a060f02090f0f090712060f1203030c0f09050d0503041d0108101104060e19080102 73
    0x44a61120b02d01c007110b4142600400c0517046d0301c144840e50070340c00481d016809100924411100300030340c1c0d40708000441c1c00d06068009500686140d9a182e0420005404240d1182600c04d181241940030701180001420228519503019000e4641d91012079801d1401c1d9080e01c10200b031001c00292251410300000c82c4500c06d078103c0c0e20440c5000c5007030070711001500c80d03d2000c0e4040503043c40501180101c081e80700304401c85003150301050903c2441c080c0d0311224040e400400d40240300d0840003044244030304140f100c5600c0300d0b0380100000c5041e00c414a0076204c00c081034988420840c2c80340f4021600c1e0840403200320041007102036140303041c6110b04000f4101e0300744000304000c00c084240700a1a090388828110151070040380c0c80800b001c0300740380c010310f1442141d011041d0455106250090b00940515a60407076129105503480c40400c0c1c60301d881110402966020068001d000a1240074030840300b065080001428401da1440703440d407450340507411940300032901d0303400042d81c0a07030401c044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 233099775 1250 233098525 233098529
    0x50a050a0b0f010f031e0c180b04020f0304081e0c030306040f0903080f10081f0e1219090b0705071401020a02090c0d02091801060f080f0403030507050f04080a0c 71
    0x8802c0b286a94100142c4040e45800b07071102900200a20301e03802c0140d40da09410f00500d80e4007816000b0280d64034601902d0f800071000b0503445151500c03a40c030055080c00e00072904032107801c01c19180345a0300d40d03403120341c203400912800b0346907151292510312080c10725000341411103500c0011900c0c0d1500d88100000e69950320444040c15003058502000217400a6910343c100c14402558041f50741c1e0b2601080329041030b44e00c104020321811600a0318102e400740b10040500c0244010f001d01400780e1b4456070f035800d66401102c904d1030704210000b041455003107903001310003543ca48003213200d41e82c2c54001d86607040080700b900e01ea0000c0004000c10001c0a00321b40f02c0703203820f00242c201403201c2c0d0000742100380002c00314401e0b2007000922a05082031a1704591092900800070003050f13140032100602e03400700b40140c0b408a010115007441301801002c001d48500100890780300140d0b15a0f400f24082c10000d0604403c3c410240a1811008085c1c030150016240c0305000b02050545c0e1300b0021240480b507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 233101025 1250 233099775 233099791
    0x30a1104050d030311092e090f0603110906030a020306032b0516080a090e01080601030f02103b060310050121050a05070201050907081b0d050a050a0b 66
    0x2000100041d4655084aa80302c54250500050306050703080102c01d58801e0310401d0343d0080c03054040030088a8a0030900b40700c601c2c1c011040c400041d0071502611035a03046d0156488400b1600341c1008054860342141140c03413000480207091040b06d0001c1000e44c0c2007550350001e066004410002c0d80e027400c00c00300b00d0b502112240c80c8a160207800204001c500c0c8050701ea000c1140010360918101c940a02c8a154103034000403035591072143c0600108001c40d90b008013500e085c146400042c80d03810005100d4103803a04070f03035480c15207500c0d5400c1020640340e0300010800d002d02c41c0c00311120f10380c41d120080c0c041e5800b10020300900009080310141100c03003015040c0316140600a01203031056510620054a60a003840a2480b40c1007906006540044c0751065816003488104107a142060304980e0141c045a00280569118a001c5945410240c003030f201e19a84409000c84124103421160511340c03601514184802c170300c60b150242411640740068585501c09038000c010010310880c080e40c40440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 233102275 1250 233101025 233101027
    0x106050901020d03090b06040f1808030f0108070b1b010e06010f06030b06040b190c1e060e030313031b02030f0c0f01140a050304060209060310031e0804050405150603040602030a11 79
    0x695906c8403031203000d0041d82c0074030b07510913003580d11242640c4000b14110b031002d00c0c04078000151400d031482d540100c481307014402c0c11400000d08558005003540076a00110b40072814940d0003c84138002055841a0340070079900c0c0c605501c0c0914091100ba03001e0410106e001c2c5049040081c082c0540301760240003400341d40c0800042041c10050004d985000b04490304030342c13115061200483d0311840002c80580002c0c080442c40b400034a101800d4a01140b1500d03040c00509040c2024130344078041100d641041209013089035000903c04c4130316160700c2c2c01c0c00402c03045210040e0003191034151462100c00c0e03264031042d000b0342d85181050080344194000d05e0301d0a80d038006400e10322402c0c003030b9007081c1d0103110011020070308001d410f4041e90192107002c0c0c007983d100e15020072500c113410454030080c1d511041003d91070480340706088454012a8008424914003441d11050100605008048811110b42c1882050301e035550240107500071070041d00b0240c0c803414074600700f00032250b500018001e0300740 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 233103525 1250 233102275 233102291
    0x12050d0906022d0f030d020c0d0c1505040311070b030406050f04030c12090320091f03030e0a050424050103180b04140d0306140402040f0b0c03040801050106050901020d03 75
    0x481d01c0f6800701902c20402c109a880f03016950039182000e07810301040740b0b000c080341c2e0300c0e5031300d00700c1e405000c518560004413100904045810740341c00c4858075002c1c00003c010340e0120251181a0400e070782107072182c0307015501c2c0d0b00e6072030101f130908010790000d418118000080c0030a1200c00d005407601b240d41000b00c1c0c3d40e58200750360080c050b00390380003004041000040c40c0b401102d0040c1840030086400191000105030400c0c00c2404040140b4070852003000c41401094a141b403400d10000b2101d0b03c624030b500c2042c03c50b00c0c141d0799100c04142c0d171640411b094001103019200c0d03000e2588016128442d21444508110241005072a01d4020604141c0381071075401c0e400044065100c606a000024600b4035100c904201c0c0d020030806501c1d59092103002010245039030301d0341c410300c00c0391101601485028480010003080e4030032441450110b10080c001840404603010007080202a80403c50707145c555611800750940b5000d030b1002c4041070000c076002504e0b5805103e81c24280c1c19510303040016103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 233104775 1250 233103525 233103553
    0xa050618060f0702070b0301090c0206090a0201051c0f091208010e0f0c03070201020904060803090411070c0501030b120a0c060e0105070c061808010510170a050a060b0a12050d090602 80
    0x94005040c0c1d00d10800318800f1910365030082c0705101c007801b412110755035a50f0b100e44007403026112a00b0040c006114110002e103e5060125110131070076816540c4615211010082c44440c0c0010902101142c2d920714500b107194001e489807911480c41000c0b0f094058003c010090060b41d0b05038400c0c0e01c1001d014003000000800b010300581c2c844c0301419500d07101c0d11840b50890081c02020207141c0c03c03a02c1e241000c2012a80000a03000091003101c0c18480e81e0100c07144542c244c000c1900090200c03242001c1400290b000e07401c440c500d104064062400030700d0a1100c20325046401c1015511030050383d0302402802e83c000726002c20000c1c203003402071402200d561441000e542c41e2080200f00595404400c0c030041e10850395200400040c0000e11140c1002da584000d140002e1084d4003a040e41012680303054440403e006082d1038111000d003165424689030040078040c03140341e25a128510940228141d071201c0c0c125407501d40280005d00c03060016042c00740c525074080d0800c00555110000300100c0c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 233106025 1250 233104775 233104783
    0x501031208010b0a08181912030915050403020307170310090b01050a0309140f06090c030106031203050604020d0903050a0f05090f0f06312c0916080a050618 69
    0x4030000d0301e00101700c0d42e1550842420700300c0410300030b9203500956038114460079449184000e4180505440040300000360380035812900030030002000380740e030036a1030581540b050380300661050003401503a207000025550510341c5000076034210304102d008810300c4110b544040c080d10140c102d000c405c10003000d081001a05c0c0c0e00505124204054440e0656020024170b800401e420442240407201c0d4241c680c80419102d80007280c40380418400ea2240309805d140500800c0104d17500705444050710701102c00120301a2400900840d0055005c110300c98411b07d2a118100901d4000d5803001e4135040304c0743c0000c1c00410410048020441d081c0000700700c0d5600d641140e69008411607070581496840000b0072a507014030005403805510b103400d88900000309074003545a0307000304414041a80c0d110800c200ea2841c501071001100758201000071882030141c1e507019006220841112000c0544880f40c6900320540e0b0803003012071300100e81030301c2000410402035422044101d003281c0c604102c68a090742e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 233107275 1250 233106025 233106037
    0x50403120302041208031003060c020c0301201210030804090e160e060609040f0c030603210206071d0d0309051c0215091201060602061006030c2f07090501031208010b 73
    0x241c00345c0003020400c0142c0c00300360360008507800030080c031001d201c1d000c0c0652120501030205000b5402d0943e80e00903a00ca4084002076801032416450405231008003241c8803450080810891000740e00000c0049580d00c00a04000c02241c0c0010403800103120700c1c2030a10911429800c041d0060b2082441508602170240e6404401520307a1500d5000b00000a0040c16240242c0389180780b8040200c0e10055154228800b44c9024081a02800c1e0700c141080c0c1a031404031070000c005802c203d001c6140703a4400c190360a035040c03501c000380e00c220079807200055050418400440100e8020001042181000070121300c0e941400b1001080c0c1e0002034010039a01c4002c0d9946441502c400070b000102c07039807508100000c12416000030003000b0b86903074010f5079400c030984507a400c00c1d03e000c00c0000e5051290141e031020f1074543e50b803858034086004010398000030741d00b0803080c021482d803c110341e022002c002c100b0080400e240c01240c2c40d451030800070f02e40c1682ca0072240030000440014080003c2030012600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 233108525 1250 233107275 233107283
    0x81c0e010c0303020a02010209130603050f0607020303040b15031501090b03011e0b011403241c0f060e100501030c08151801060f0303020c0a0504050106090501081909030504031203020412 82
    0x103071700d450101089009200d01100a540f100300300c1c01010340351071a6403001c02980e20130000c40d51045a403101040d41c4002c00c4a4407c0161701c100002800144201c0102e0303080000c1440644ad10404540042d09010704800e0442c0e030007900e440100706a140d5401201401c1c0d5055008200800c1c2d50381c21202d400001903284010039441c0d04620f4001c1c0d102c0d000015080501c0c8002c582c076030500484c1c0f010079180e07032904441072030396131301490006203841030010000005072180d40c1c114100650b608500e0404180c420f94925640701b003d400c030300c042801a45140c04448000240d55070440c42c050b54541c000f5042901c0ca5031009140b8904209083c02440d00000300558051901104208039400f4028a80148803200502580041059000684000611000c56555101a4542007804100c8809100b1080007072075030202040994002c0303845503005143c9500640c1c1400c03002d0100d00c01c0d01c0002500728005500098200188500070300c040301010680d1606618003071502c60103130307524009803038058 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 233109775 1250 233108525 233108527
    0x203010507210b240c1203010f090c1101021308070902190c05010b04180308060d051c0201090203010606080f071d010f020c180105040f0b090406091a01081c0e010c030302 75
    0x4000f644d40d642c400141e02150344003076400b07100021000013075030300f007250b0350b0b81180300b02c0728032001086403c0700381c071305907038258103a2241c50340380035002c2d0050324000c44c5010600c070701c9021050303543d01c0030b000030501606101d05180c00300385043e0000785010303016485800e840b4030612105a45050307801c080f041d907890b94903241548410720300304140100700f031381c803030030b500c980384c101560400c2070140d0101603000d0180d182c0c94007558030301c414000c6000c104030005203a900312400d44112105044004002600c05100002c0c903543c0e21f5012a00310340c190380018011812200420140b410f40c00703441c6a01c15901d1902071b005d4141407542c0f0400c20320160045050000c00030300388410394801c000941d1003000c0103080d00800f40f1380841104081d10280102c5000b2420840c08140010031800340400c2c2d808050845025950703142c80b90b130b000b00f0402000315410444849025054182c13092014043d18070440500740c1d03200d40191446141503240c1c4a030050000028a400160380c02101a511680c0c05003405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 233111025 1250 233109775 233109791
    0x9022817010e060a110c0d0f081e04080f041a04080c060c0d1b0602120105010e04060e04080f130602012f07030305100b0a05091c0c1403011d0109020301050721 70
    0x10540c4d1b0044041c04411403251034400c480c0c290348a19054802000c2c1c0d25616190789401c07004a8a030260307076056100002000000c1000510740300010946142d41650003824180c480d10034115203145080b00310602500454103102c420424045692016011034001d031400000c51509919051a0301c07a02c1c0034002c030b220340180c80d03c0c00780c1c8002d100140e00400442da01c0d1500c110340c50008100b801124001900da60040f0f800c2d0800341308580c00d8400d940010004c03079031155104809030348000180c0c18803550034840024900340c42d00c04600602081e0b0008203442480d95040d032a034480e041041240c91001070704498a0355440d800702c0c1d80785074061402140540c3c407181850b4140c0819800040103920014403c00d440d903114025000102040b0f541c20110486440040c1e03580c0c0100781e000d407208080080400c1640c800d1086040b15820207000420300340002c2003590200044030b12400e10f5a51140308807400c518080c4a1194040c10a083c10110310301701215141e4082e00c414005c0020310f55035449 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 233112275 1250 233111025 233111051
    0x50306030a020a1211030f1203060d080406020a060b0904080f0a020f060c0a0306240507050c0603070c050f070806180a3c11010309022817010e060a 65
    0x304101c0260007400e0602020f948020380d1140060a407801d80e45400c01c401524114a00850400c43c50752415009201100d0b1200c0386490507800035242c0741d400b0072101e4944000407640c402400091010703801a0410620909180c8181c072400310405200d10142c1c0c04201c009040c0c1c0c1d0507110710281038110309440d0328210358103034508241d07400c2011081c401c4104202c51902c070300d0014451a21b166030180f1003d070307480c0402a9082c2c0e0885400040300c25494031216010b1080b00600b2000e0300550483d80100c60750008500c46520039502d503030006002060340020b1040c104aa030b02003012410080c444c031481e240d0b00c1601c5820141280c450241806210309269000f000b0b03001980f50041c0d411440c059201e009226003560100300041c6c0400c6101000500c208030184106500c6d4000040d00b060418a40c011002400b5105089a01c00e16003001640c90b50542c032103068140c0c0300400c0220b2080d0914043e1019140c0c01031214040b681000d0f000744948101141c200c1d000f0f0750700c48001c6400050450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 233113525 1250 233112275 233112283
    0xb0a03090b0108030a110102070c0e1b030109020a0f0807090e0903070c080607030506011103030a0207031b0f110402090a090e07051302220303023706020408010f02160305030603 78
    0x140c0036101c08030820001c6640c1e50040001c1062680d42d03154010501b019440382803c1c0d0081c1c02d80034083c035000750010081d0810594401c1d60042c14040740b182112600030030781c84150001e820003225242d01160b440e004d1070300000d03e4501458a0b040c5080d040ca0000001002e81555019041e030070a840300c042440708100f001504da015611148520142d40c070b6000890396000211030101c0000e0801c000310308654003e00c03c00b1000780b8080d0180d0b1640d80c80054490107540440c00450402690b25070401c08009604100043d1034880c1c14001c8008140c0e003016005078802c00d80680c45284100b00160749541d81802c08811602400350100780c01c80b40c55000b40c2003010325441030707420410544020410760302d694000d00c0d6001603240c1c4000c60400050b060055501c0c2400300a001da44200d95800c0151609015104814060b40d210014010825030360240c808144608580164010900740301b487d00a001c0d44600d82c2460030114200355001c10003516040c18440068207010000000c04c1d40782d10248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 233114775 1250 233113525 233113541
    0x50411040e0f0a0809040f05010f0306090f02090c0c06160906032301030b0405060108010912051b0706030e0f061005010f02030706090c090b0f030c0f0a0906080607080a02040e010b0a03 81
    0x120a50790f192a2904100c0c4803a44040d44452146280911a040c42500d03486481e0503615072a83c040034039400d5945000052001d254140c8128070200f48040040e96094540c0d88a885101e58064407582c00581c198984400034107200c400060303016603d01115400405201190910703c2c2c00328030611040102d0200011918102117550034500c0040300384118944820302442c41902203c0d010b070b0340d882e030413422a44032400c018603494090038104049132182020740a80403004d68411600303000001d4603072400301c2caa4400c0011a44030950000621410320895030100181c0300509040e19021142070044212405003e0600c50009481c4a49034030800645141540c03008081120705030074102441c0b4407034036100c0c44210351b0600300c5e08410ba0800e001d41c1c6440d00310141c01401145908000c005010b1000800d81d034015402c40300016004e0454095400244407a0010704000d0818180c028038001d00203010264060042104110030207040c100181140c041c207000c11388035003002c8802c401a003021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 233116025 1250 233114775 233114803
    0x11101020c0601031e050307030e040b0a03030f0f020f0304030605070203160f020406051801050609011103030c090916020a0b1b0c0616230304060219030e10050411040e 74
    0x100396016515000142d079416280180c040900001c400764200980c00f2912400510640003840300c0400a0b0096110044801d0300400201c0c00c030310650089404d01d1120341c0305500140310744002c0822a40c1000b4104106500d41c80035181c92101e82050f16628443d5200050001d079651340011201c40c802d20964050b042c1ea10502501007885040c04001070405440982c85540b401800090b240380c013141c0c2c00c018800196840000341e103024200110754008425450501c40740c80c1840307a10030014401148580d050007025a00d0306803440074817118010041510025510000c0c0c0002d8a42e00092250a8164810041071440d80c0b0a21428150340b084108041e0f110360120394008128000300380c030351045c100c91540c0c4e00c01c2d00507040300725403180282c100a559411081c5041a080c041c400096510502030030025180c00310f003107070000581341c80402c071200090b03840200304603c010500c414030803016400001c1c03010b820107464641440980c1e0045501c81c0d5518202102d142e5002c0c062140b040180e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 233117275 1250 233116025 233116027
    0x40f050f06151f0c020d05010f090f120302040e1914280203100e0a0617070e0603010b09061023090a08120306010f0306030813080c03010b1e01110102 66
    0x10050b881e00080044110300352080c07010300d01051008a0640d2a103000410541e00d45403011880c0e024810704142414041d282c55407a1000c038600143c05014039403c461240701210013540c042c3c1001c980340f220007405841007600410003000320030403041c100e9400c0740b9903510b08180d440280034a44001c21882c03900303904c001d2200c42004a101701359110315003105c51021090340800c1000c030b1290100c1c84200c9104007036251000c014450f0400c030380075195001f0101c840004509454402c4c00001c0d00f140e030414817255011180030b20800c00491402500f00c00240c00900072840803900007001c42100512035401030345400040010284038040c502d0711200c400714420f29403210a150b0950300c1e40400c90b40c9000b02c3c40d1140006540c0c41c0055404000030711014520b045885803001110b200100b11084020951100300c08030210b1040d0000f03111900030280801040d91414900b20b080c542416681c4c4d2083e45840e404908a03210004003403040d036002c20040e214038603044010385034005281c01031440c541c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 233118525 1250 233117275 233117281
    0x3090a05010f3218010e01020d020703110d053004060617060112082a03040e01060309171b010f05061906050405190b070506010513020f03040f050f06 66
    0x101644203e80714000c5161070f01c03c0c8041641804201d0f458140b8003030349a220340b0005865564800c03207044031051400700208141c204a4807490981c1c000c0c5d442a81042d500080711810107412903102068444201c000e894010b400600142c10f901445100c00403200120703074410341050403005104100c0c611143c03690041c2c109802c101000380840d00a0781c150902d414000c46840800090250480f560000046d0729030540e87c0d50741d010b942000541200040c12800703800541100c08621000207403c48000710f0300d691810030a00501101a8480340905140840300000b02c1e101142402c108480301c0041652107000241c18240c524031164080382c82d520380395405660000c103802c03440c041d603000c6512401200700070742c0006401c076080c0f0136080416004c100070815800c20040b071610101c40e1449100c1701135a0398011307040680c0207440865154100d14010301541c502071041c220800c060120460a1400d1452035914a2001400c06003ca11807041c020080107401c0005c102c03181c21503820f031b0b89181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 233119775 1250 233118525 233118551
    0x105070b100e060a0e060d03210903022107021002190f050714090f130c1707210816020a0b03070201050c09150306030709021602041b0c0803090a0501 66
    0x222a42c001c021003503400e280810054500b00e1010816583c00e0b03024440c0745d0710340c0801c00403a1030615800720144a100b1000e010b001d0029507030600c082e02d0104000c500042180343c028100304200c4a12100c00780c507007201c0b41113142000e040d529a140d05039140015035403044004e038940071024401001051502c0d004900f00010001007405045c894012188140e407682103107071400451006a03074111100783c0000d50440351000c0c80a070008400000e24141001c107450740c0990344802e400c40c07054130700449030688844404000740c00c000c162280038400207038501c01d00700e918541c6460002e44102404241810340b1182021a4070009500a281201181e40c0308140f542940080300c40b800594a8100010000540ea44c115190300034002c3c070416003002070462203440e43c0c00180039550140324665000c980d00e50613200405240205510460300150244100020b488048800301000303000105640030481e0001c071500b48055000780c10903180d655a5a500e4600400c0b042c01404941c2813880d4181c1031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 233121025 1250 233119775 233119801
    0x2030108030d0501050f060708031506031e15030303072706171302030606091509010807170721031e090e0f060f0402090307050405090618070b04140105070b 69
    0x407003038510074003507030f030380c5000704200d03043c075604007d0300b1440400c032140000e804ea130002e40d8080c0c205400014941c8280c0d020903895001100d036001c0c5490042d2a5002c03980d40c20740e12940c0070003180c1c1c0c9201c3c100102d40c00310341c4030701024003102c00340300304509000d1103084882c081c0d84000c3c2c0000052851540d030b407c001000c2881d01c3c0701d007002d52822300b00030031202044204801401c0350054000c0c085912000c007031000d002c030014100d942043c08580d100902e03540d0b8442c1c8070b00030031340900204a040d0034481d01b50002404003400900503803044130204040981d00c0c091061303e5002e80364400d420a500d0600f611040c44003070144d00d1000810400c010b4050700001d8141c2a80e0404070b041090340d03190232040e0b401c2e0380e066981c01d50181c402c0c1c0c4c41c00700606d025001082881400b0b42600c050700c0c0e854010800352142130f0b541e01220b800070020070a5003594141d81c0f40c00540c1910003000c206140c030b885503400b803140340540400860130075020310340d5034090800c407040c0070362240300d4886503c0d043e0038803050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 233122275 1250 233121025 233121037
    0x61a0d0609120807090506090d060e010617010b010c0b0c0405031501080607030c05190e04060605270d0b1e070e0f01020304150e040608030a05070506130b16030f0203010803 76
    0x1402210801c0e40310039100308180c83c1319844507215075803000e003800200304051300301d0403032194040301c4817944c4000601c2d14003038543c8041d400000410840e05010700810720b0400c00c5000e01c00350b8903214400810784c1c2d200c0c2003071407116084a04d0250688a4580c004024820360300450f80610035100102030545440c00f8060481c0d2407441581d84d41c0d00c400f5400c6080c1d5800b01c68807000100103010702d07021400d2494106000c3c0f202810000c2c000e004080101d402c3d5031283c1d000b07002203080400c031004e00b610880d1010800a024800501529071100c0c002400300c2c0e04500003410700c0258500069084046611031850715035201c01051180c07074007200040001000720710765800740d61000320700462940000140c5054500c000c0f00e1041c1c00c40c04040c01c54860460395840703a03005480d0000014102ea0500040c02d42100e2030baa03296030b40642e414441d18040d00a0940300039407000040e104017080c00104455000000303681e0044c210b01d0340c000110081d02d007410620000e17903c000700010b1403801c00402426 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 233123525 1250 233122275 233122283
    0x703090501050f0f0d0b041b0201050f100e072a031b1502070203070308070602130e06150d0213061e030e0303040f020a0b03010f030b01090b030a061a0d0609 69
    0x101161940d00444040c040c03010b00b01c03070801003401000da05280d00006801902804007001070302e480c003900040c0550b22090f20341e01e6603a0a1089014503a582030045680c458181c43c03c01c2d0311414a80c6429100000d248034995241c1240350100e01d205104030b0207004055801d850b030389078000411070910b480e079030291804c50208001e1602001140910f608010400d9004100e480d00e14803440140000703540480350481e41801095000310014054001402c00070740030342030041e00c4015014000120184a411006075130200c0001c0003510354965402e58003600440184a84506000401070003034040c81c40020595000000041825a4008030090300c0091a81c1c24030340c0d99030420801d40c11140000b049c114a07402c01c00006011a84031191503400714400b80042c80d545595504081c8613400a80000c482e00441c1402007041c8803101c24000e01409070080e04000000c607500c0002ea0384c0041c010000c0100352141074411010700c80003141c41000101410000d8150304614110008004150b000c407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 233124775 1250 233123525 233123537
    0x18042007060605011218061d03030a02040503071d04060b0109120b090d052802071802070c05010f0507060f060b0a08190504020112151502030a0905101409060904020c030703 76
    0x30f01900d058007942c0712000c11b03e04918140c3c5959150000640b025410350408081d000d00002502e250400c011880703110b907245c006031030f54185401c25041401c198403c00503001030229040706841036140103038105500c44d500003050f40c1c0200050728203030000c5e440340d154a114071042c28240140303400d80510503042a801d41c0c54121200a0688090040651102c480d012000e500034070181c003101c400c60440040c0c01104e011580e80d6130741e50898590100b40a14064001c285c0c6810042010007880261400742001c2284043d1808020300303030702801c1c401815040d1984280c9400d040143e102001400070079101d15a40c00c000035002d05000380c25101c6100350790303000c10590f0503021544111030040381c1c143d485000030100301e09840003900c0c80341c02c1c0b032004043c0e080001480e01c070420300c0d04030f02c3c002540142d0303151549000c014100b102e0927804140261104c100910b011070340709410002c090310300c00180752501e8418000c105d41e80104190240c00a00c009800340c1030100020140030005c0c0f01e6520300c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 233126025 1250 233124775 233124797
    0x306090c0806130e030a030b12071e05011d010804030327031202070b0f04082a060702060709050d0f050706050702030615060a2607030614061804200706060501 70
    0xc412115104c0c0c0151940c0c005000108036684a900721102c1404001d04510328803401e00b40c85400c2564a50200d015004001c448100c69050b0480400007401e09080c030b01c01c05101320144402103c04001c20b01e0400c822440000d007014000d03440141090107180410b848008008015520070201c541c060303002c154100b11594491419000b00d84c111588034030002e500362a0383c03110320402c01d0060002ca034101001d0100d50318040300188a03962082c0036110000c10025070b0884c1c1410401d004e4440011500180104001c031900842008200da41c1900c180b10024880d081540c807031401241c2c010414050001c000588690210240c00301c03900071410307140c594507819045002d031440c58081542212051040f01d100a000e0340b5502d01000d4046481200300f41440d05550b00b0384000c035003040100b60751350f8090009505e00d007104050b071841034554615006d01d81284803001040207240710320454507420390701c105440c81842890348010303481c41503440702214038007100500f4050040a00141040801e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 233127275 1250 233126025 233126059
    0x309030c1a0603190f02010302070305071709040507020c091503030705100f0b0303040602060f15030607030c0f03060305030301120c050d080c0138061c0b0406050108060603010e06010306090c0806 86
    0x59244c034190f003e024100c0c0d40c1c090740d0040d80a500700d81070503420702505102c280c0100d0981e0700c0c0001e5440420910340e980d81249030400003100d030081c0c14003086601c04030880a2a855901d8960742120643d5082c02d5000c041c04000780c0703588503c9c0402131090242c040b06c400c0c030b10750710742210141d0343c280613080c00b010f451001410354170300883c0b0844005034464404a01151401242560031101e01c2d211234003211500c8010924012080c0d030160006590b0f01c6c0c01c4420280e02004c035814403000e40c40c0c1800b801d840c58a509640340018007070b40d2004407103160050208900d02040e8402002e01034441030300307103c141c140b02d14a0f802c00c803501c928075400e140102c45040e0070708101e914a01c2280206840c3c1d54000ca103200825100703ca0350503004a000c0040b1202e0380c00c8885180c00400c900300c0e001c90921048004d00c0255050b5a02c13960510503820180030456581c1000d81e41520181142d41c020b540c1c5090040700686241e5010f000d000d483c0100e5110060b6100c855940b181500340c810402d440d010780380c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 233128525 1250 233127275 233127313
    0x80f060703291903050307020909061506090a0801060b03010f06030204060f030e071806090e010501030b0705072108041a0105060414131104050307060810060309030c1a0603 76
    0xc2454100d11104100c08200c0010500011802c4014002c60b4041d606200302d201112070030b400981c1d1a510100e0040c00b180b030414030b0560300c181c000740940560705010442c110f12081e0785c902280300d040c0104001280d42c0300d8445510041141c407000b4040c566076020254004d80c000e00030141c0b0104a440041203081c001e000b2034044840650728078103446044801140100f444108400d49401801c20000c0d491080d40c2000b4910800303c207000504600e08103050303080390200c2c03800c5005a4100380040000c100c3d0041c1180d4002c90604026507035141a260080c282c01581c2d650b840502200510031032502ea02030b0f0400d00c80c501c00c0040110b014a40011075030481800d220720ba44c801010002032150b04d02040c0d035403030a10000340c40b4040c45940c0c0c0c140c54064500d08041061529404242003101c0d14042006074001c00c0e0a04000e801410410150351042985004450605849000303c3d410540b0a0381c040e00c0b4140c1040c2201c0d04058400204070f591b05054401c3c9104c1d00c28900d80440d08000c04d6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 233129775 1250 233128525 233128541
    0x120601020609010212070c1a0a0c0201140411121005010306050f06030a0f15020d02070f050601050607080d0902010e030d02060117070807092c03030103030206220605090115080f060703 81
    0xa0300c000010b50750b41b0811580b032481d0500454450003030070300c048018000000b40c0d5004900209010030f45040d00e600081c2101e802c860017003c1c04102e84140700104400072494403003401c054580d95a1a0b0802000c540386c8070111658650301c501c0c000000050148651016002d200880b4045449859400406a6560302d400c8061300c40104a0080c000080d5000c04d450004000107a000d42412210890322049801841c0d041d102c1c41161400e030000c01109102d034501402d8126081402c0401e40d8955402c2401a5030a03401a19030b03521640c02076a004400c0114414001000c64010000100c1e00944800003842841c0c8480545103150900100210385a0247d40a401c0105641c0c2d15200280005e0136508001d054954500c031005401c1501c4440e0144510301510011503480d4075500e402882c100008113045440d030841030306010064585a4540b10890300070703602107802e0b1138112100d80100404d80280d02810000440001c24000104401800d48402d10648607655949030b02501035424031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 233131025 1250 233129775 233129797
    0x15040501020c090403020c0a030c0812040806130201030603300801052b14030a021515040f061e030519050d0c081611040c0e09010b090d02061206010206090102 70
    0x18840c14600d070401c2450f1642c000d00034811144248803841c040f0308a030045d6001a5040d00c0342d520180800365081050003422000780300c3c80351510703140903500754032514050b0582071100701300d51000040d60701c65001080a55045004000b480010700d01c01864495244003292150040c9801090000c2c0100c0c0803a040755405031000700100108000e00700b41c0862400c1e030404085481c2c564401040302e40e04800d5071191241c006507a03447c5602c1c8081d02d403489081c10104071100c1e0000300850f003001c41480d070a06d18025075000c1030708035020403508042d0100760410810a03061180e10000722440c00f0311482124000c034141d400500441c030001c51500c014070009006a400301184440b0b0038880d0072403004050203040c8150403c0d0000480280b60b600c03408094605400248002006180900c01c041d0303604114240044011200c9010a69500052050341100080032030100020789800b6504402d090f0300405040c0e46200800003203080000a551081c014401c3c04001896140144201c50b0764500f1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 233132275 1250 233131025 233131033
    0xf090507050d0501330f1d0901020c0109061d01062301091203020102040320030d030f110d05010603150e04080717070b06011e051602010504030b0f04021504050102 72
    0x300018002080b0050b82c08861543d43d414080540c0784200e60049602c100907800072038001d614405242c4ca028a07500860a46915030104100380b1070340100d00b000580114480d0100e560b03403051103034028024081e43c6889075080070784e60410402a40e1240c1c8100440c00c4051862400006a480c01ca60850207101c180c030141c500e0aa0030503c42e2206a003451344149800e50784075845040e8401c2207210641c0840150307402140500c00c00c4082004581102c21003000140000078000009940d0400c0f41402c40915a458850320440c2c0000d40210b41c502109490301c0750f0f00c0c0c610700040d8009050034894140003e00d0040c40c401c001c88a581401c00300c94184440d6070b41c42d16241c40d01707a1a94001c820807071703104141580300701d5a142100e01421030f490056030803000d185030400025100e0b1503002c0c03002515009461a07001141d8005050320540d800105041e40350050b50703c01138419214a810141004c2e13515070800419100746451148134030310989064690050914111042d070103103002d03e90250704 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 233133525 1250 233132275 233132279
    0x31106072309030a02030d03140a181103010608030f0408010f020a050409050a0b0d0813050118030632240d0303020706060302040f090303180b0c1c050109020903010f090507 76
    0x103010014010580e802002e980307442915900092400310048410404652542a0f00001c0701400d001c0950000c008200be1200303003400203040c2c0352100c41d80d90081060600b51862002030300e01754050005000c511003100e984e0a450f001040702900581309001266007069528503103910f180c02610b40c011b9581d12007600742401c0118080181c900100002440750303139580e444005990341d100040545002d091160345d00c41078010308110384c82c02a0007460600004070b004008210b4158058403c99401c060700248844920881c6507103001500303035106070107102600c440d40c2d01c60016043d074003035585100b080d064041440ca030601300c0019508110342c42148400400c02181c029001003145903c00e140005400f6201d41c00201101e643c0ca6640f00c01d2a95004031008041c1c01d0b12541a010b40c10410155000c1915550f9515001004014526100000c84c0e000e11410001c145000d54010008080c05070350303101c204100c000e4015800c164071075800c124480022007001e101c0c40031659084809400b0940c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 233134775 1250 233133525 233133587
    0x90f06040f060b0402040b04090b01030539030f06180402010f0f0509030f0304050112020906041514030124081504050c09060d14090f0c010c1e03110607 67
    0x1501d076030156074071500d408994000350744910042004d4040200d0003038a035410400f094040710724070065075042c14540001e200c80d2496200d01a4200880444800c0c4100c40c8442c400340b0001c40d095241d0100ca42c01300c01d1010303030101d6910b02d61107502c1c00c1c6c0710050506d4800000d492034000594010b0701107009495450304c2d2500c104031111840e9401e007025072a0440c1280824038040482107085503541001c10140150369005003c084401c5000b90154101000d07800050864031562150040007440c150f45d0030580c0d40190402d11f080300f45000816101c5d0307034a60145100500050541c5540755403d0701d0441002d000306070302400350740324400261f034002c0d83d40c050000600004d0000340c80030a0901507000c0c9540e4440003032240483c601030200d10201d11030481c0f1000309001d8a600e000341c00524103201a01c07030000f29800340705d0092814031a543c0490403d0f400170f10b845501d0304e074444080c9101b40c082c1030304810a200b035410b4040813115581c1e511601100c1400c41d001d030249500c94455660554a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 233136025 1250 233134775 233134793
    0x306070c03180305060703051603020a050d051e01031b12050d030c050c07030507050f0a05031f0902060307080f060603060a0b030a022101150c02010503060919020c0f06090f0604 78
    0x803100c50b4040752880758882d00c80510701301d000c03a02070001030741f60303010401034114101040e00c3d045d00a080030f6051101e01107026000703000f0900240e04456403107000600691600d080c0c14501507040340762a4041d6100d0800b8000403d134505440704c80e000900c070000f80e0341c0c501440d4188060b000009080c81c41000d0030700324040e291480744c6404018080c0051690100c0602046000b54481c00040c4189413420b02400755041c502149540304143c0940c0030040703a1804500200310b1400000c0501c0c0709102c0704810001031444c0c02000c1e4111001004106005401c149024019084811000340942d038003810000d2a20045a04030340103e480700b41084140030344c4003d1900298592009401c0007080c1940c490b00e5041194802c0180341c0a00042211610881c02c000d40081e031440c1070741ca048031540018082d0b03c40236242c81c0c05054660002988400210705030350025181d408150f640b050098045541c48400d050428910b00468000c9980120000f443c000d0b09008280a04040e41d9180c071036040e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 233137275 1250 233136025 233136047
    0x402031602240411030f0d0201060f1e06200d030507121512030201020c0307030f1101020415080a1b050a030b240703020a06050c0301030605160e060a050c0a0809040b0306070c03 78
    0x148941b02e890400c03010240510400c0783c0107903000282c080d2525000c100c4100f07084d4826401003800d81250364154032100c03503900030740d03940d41491070410054404039160b00e04020115581c0780a0080000c10380c95040c1c0040b4000c015581da890f03680d031080d03d0031808681c2c40c032482074640e00070710b10204201840310341d07001c44460084c0001410310503180303000360550740105012030026841c3e210313100009401c030343ca00d03907201c82c0e10000b10304040c00c0003940004000c5680080060080c82000a00780002c546c0050202401980a00880c000d003140054041d8003c03c82c0702c000300c4c0c01c0c007040c0031103410f1140c20a40940745e01096030300d540c81c000c110203509a20460090b0118068482c140005c036107140541030240d0342c940e0800c0d540c1e6145081c00c030704441024200e090000c0ca8075000c2c0c00c0d55036010300c00f108196011605269141d541d00341c251294441d0412408090040c640702c1004c0c070004402600e084281602c01b0b101403101c64040644400085034842c000c0b544c40341e1040040f03441013042c104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 233138525 1250 233137275 233137279
    0x2c06030c0406031101080c071e020a050301090302010c0306090905060c07080405030a030c0302010f060324022205281e032a050406050d020904110402031602240411 72
    0x8028010003020600303445454000340d500701103414944003556481000035034448100c40300c0da410300002c0d40c0c68261140174210303900103c4420000c29000d6690307016510000700802002000705050924000e8044c2c12032903ca100440e14204d070006000c04940502103040703a0002c00b6040e00d41d20b03810420000e412100c0d0583c0e60071024400821680c034100651051b150203078864030b005511a240084c04e40700702070055404c00d4208401000040c494a0052282000c3c6051416070706071040804c00090141a5030b2580a4a600c0c0410300e08008402410060320070985074461004030041020300354051640c5103021020324034004200601140401c100720380303400051812030581c1c03038070b80401403444254114800212004584c44881018100c50000c3c04161001e200c1036141c80005039040e5800b14010b401420f003400003c040082424040d0704d005030081c421502ea09080c1d50050350105254190805486809403404d01c1c907100c02420340b445055001c010750199200c0d07072000030506041086903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 233139775 1250 233138525 233138533
    0xc1305090f070602070305060c040e07050319060f080c0301020309030405060304060915020301051903080315060706050c0c1b03120a02030c07030b060f0402190f170a0c092c0603 78
    0x71004107051005074001c0080d070b40280a100e045042c128200700e07001e071001c00984802c0008200c2c070320b156020664810002d090403512540d548419100000c15558901046860194040f038a40324405168054480510032146044810f03406c0c0341c200e10042e5190b50340c5610a0104000c0ea16000c3d004541c894410301c40410b143c0c88a603102c0901c4012060145441f80d0088010301050406840003040300000f0b035181c0102e80d285031628001884003400c0600080e14000807010b1a0f2680d00840320030301c0c1c1c400d40400c15860104bc40300941d82040c0f140005600a4081000c00c0c0307101140d9040c0030560007400ba209100c1c20001a4540358043c5001c0420b50209100d810344001003808000c00560150b505030891307103061820806151445450f25200d54810f000e81940d040241c1d56560119465003003c48000041c00b00c1551803240c04280c43c00119092420071a00ea06244c0011425500c2501c0300c082e81908c03400364040a290101032880d4a00092440707801d150b203a04941c5411500190030740d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 233141025 1250 233139775 233139793
    0x20c1f0210020c100b0402071104050c070203030d0b0909031207181d010807081203181513021804050a0f0c05100e0f06030112110f0409120e030c130509 67
    0x841640c005180200c070740d800440f90112544c0c0c0d80d005450385084200c504501e40320030390740c0351182c0d04031003c03904e13005541d13580015070001c440e036080f105010b4004044903190114040440090421044410302410900c000b04045000c0000ae88902d910280703c03403910f40e40e4142c2c0c21228803010f1344500074a0f14100c48001022080740082c4d545581e50707080d501400358107280c0003518007a071984c8403400030352183e03603a14820b22840c001c0c0c87d046450803c00300303005000d0001440c9040d001d01c118107440ba0340f050501c200c10101c500c0058926100b90742c80c02000120f2002000b1580701120050211340194600700002905078200b0701c4440e00c18020100215111408508586013100c120b0303001c1903030079000031054581504103a21041044500501e150304040380c241c9090401080104150302c590800802030343c0e0202c640314203a2001d01f0400c403a031501c1c2400703d02c03443c205044c480851124255100d041c100401c1110700024050400c9041d6a8030301040d1000300f400a0640003180242e1404d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 233142275 1250 233141025 233141053
    0x71b06050133030c031b022d121308031c0e0a02060913150b070203070b0f04060f020109061406041515050c070305031207090f08070332100606020c1f02 67
    0x12000c4155041c0d40101182e14480d85110040741e0104508a0700c502d00c0d040000c5901000110007040014600c110780d180c01c81204ad201c0d680e446904111090301003c40c3d00800f2a4001043c030002400392041407150806051003140c585021800c081c3d0006070400403180541400c800c6600714584c5c4020000758200c000d4140c9400d0070313190b005141107000c0094220213514017000918050030183c1d01c1180703018104c200340718943c0324900c520024030030034000c00c0025034001e60010205940040c802e01215030380010325480c0c91401c9412612992914051505000001c15540d0640b184c6058500c1e04105110003954150459110a0030314450101c1c040000b450600240c000ca001c40c500040707180c05d01c0140a408201680c1141c015440001001c00c100c40700003562504580c0c00c19141340322101c203401050400302412544418940d04a4154038200000107801188011140b5003081100d450740b10480e1a00c201d0403000798024041003180c2070174410601100b0f102601c5004891403104840c01e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 233143525 1250 233142275 233142311
    0x40f0213141b2104050f0f16060804050601031b0f120302061608060d062c060c09010c08030a02070506040c0e060f0303070b071b06050133030c03 64
    0x1a08001d100000c0d051280c0c0c211031458498201c0002903005050240c0705582e2210b051a0920812100402c07001207001e0050900622010407454404e55100b0703109114030980e07031041000707100314202c0e203c0d80000d50544100002401f80742d20602400380c992071070b125000c0e10b8160390031480c10718041c03940c00610f4a40441c0c0801c000d154540c01901ca00310241030107401c10360010007066146a40303840303050304958050102c80d44204d040b11a0039800e40c0e00d003060001426444480c030310740c421310100002c2010503840049190000442180d143d0b542d82c1c0b09000b06401410500b81c042440b8140303500010b0b2030003000c0d5510044800d80107041c02c000d03841e941e16203101541c1c291409030780a101072000b140c06400c1940d101c2d0042c0d4400d500c00d941e40001c02e969110301d40014141d41890380100da41a4418800c1c2c400d9210042030050480640d030400034002e00c0300303200f0406082105000c0c071200d4184da905c0758095803420091800f131241085002d42c003600350043c020007010745d1400300440000c0610 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 233144775 1250 233143525 233143541
    0x3030e040c0e27010801050903041e051e03010c0e0616051203071206090c0c1401110307170f0412121103040b16031a0d291b070b040f0213 61
    0x30074841008081400510f4401206812246560f410442003085041c00081141e084544150018101e00c150300d070703901510030b03060300003e51002c00c0448800040f207030100784466408007180200f2803195009000e0300c40301c44008450380c2050301400304100740d841d040e80d4fc0806a020340c080d11091034102022036520341c403c40d48280441d1400e681034224007441c0c03258002a14162a08118405040728060a448a8500d008005007610450316074424020f4001050001051080e551203081041010b03150120300b95450511414440c0020703a5810102070450040340c0101c00d41d55110002402110b84526100344c6d80c0100b41c881d07100b1072002d20400c008611440c0105003020160404000d81e00503c004101c030203041505155080c03401d01d851013544030311508100c4940409440926004080e00c10351115a020b034200c1084003120310301505020f5100342c1740c00240c5000c1c058816a512940c0c058841e020300510000400a400207010b020161519130005000050700b0342140c8010781030f10485 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 233146025 1250 233144775 233144809
    0x3050102121006030510090e010f09080d0c1404060804031803080711030a1110091805040515040b010e19150806010b0913050403030b030a2402030103030e040c0e 71
    0x258040000c9011401c0c02c0710090000c500c0e00303000505203a8000c00e0101c516014540b01542d44c3c034078a803040381007548042c421825519003806001000c0c1071190454011040402c28242454101601248182001c403410319000c034101d030a182c10800308980a5000038811410b002e18000c10400d8500c0c0740d40543c0c02188a0105c0070740e00d40452801c800000c0301545064060762140000e40300244140703070a0124403400b65404903030510242c00441c0c0340e524a500088160000140d105a41400c540210f441180144110344190b624404500300c0444111000b40c09080c07102d0052001d40c511074802a008004441d841030102c800030070a404590740b48a101c042903919400402c8100010b0060390b005086a40420f82852406e0004c81d458904900c2c0305200c40d40e40e4400107080500950004c00002c4015080b40c001c8601454180c84484901180c0300f8a034001d2001814011107900071641a644c0c590741c0c003041030f01c640c0284005003140007481001c0c407030302c0241504a034490b1032040c15526a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 233147275 1250 233146025 233146057
    0x1e011d0d031103011202010e01030f02040b1e090105220506121008010612030c0f0b0412170610110a02060310050910050603040206130b0d05040b070804030206070507030903050102 79
    0x10340d036000d400c5480c40d400010a4a105000410410340075008a416031074080c01c0071a001011180103c008084440d14048054030108001c6001070300c0070082d2441000003080009460408542c00308070b4010081c03118005201040441031210500c1c03541840081442d018540181d21000040c0b5540c001840008001821204124102002d100b1a100070b05088008112040c2811085011031904010107014000c2c003400280420039a90940018543c00c0341108110382018603051202c481602031040000e000a0a00105c224404907220b00a8500601d40080707080031400030341c4c0380d10700710300000880d000351801c0030050389501c0003d46c46608490f00310602c2e06d0910042090055000d480c1c594101b03d00c5100344100d4403040c00301c0340c0160301251525201e00c010011400c3c0348901e604070422016012590032030724501a002540101e20541c0500c00980d1045000c0300d40e080c3c00c6401400691140d40843d4034140500010301c4c8950007072808566440c0c4948545007680e0040c00c0d00150707804 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 233148525 1250 233147275 233147293
    0x150403020d35030f0703060503030a180b0a05070b0a0203070903170c160906380c0a030306090c0338180f07020a2402040e04030c020f040c021e011d 65
    0x84132020b4254130250500f03017001154100804070341c3d40d00a00000b002030201c001c00c4074234031280000c03910b4020700c42c8560066440038a200018038a400002045555403896000704091070034500070707644110751603a0351515807441d40e01c60900780c022590382d003120001c041120842614050003000c40c0d0700a16a402e0f5002e03480d000c440011500c4070340c4208890030244002c0d8048135440084480421030a0302c10a81d4482c0c150501429813040400040d110311412a01004140c0c00d6004ce03c101c4155020402110900181c10780c1a2503601030005c15100746039000c864031400070080e002200c8255203070f07054501500008200340004000c496034104410390100301701d00801040c43c1d903111455101501e86070101d60b0310207105402c07010354140d060211200265141010b94165801850120138420190800d420060b0244008a1045e4010304240f1062286418a4041c800c4850520b40c000d00c50048030900194035800c11010f8000655268000c60003c019100307210030040403247d0141104075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 233149775 1250 233148525 233148541
    0x20304060e060601020d05030f0406060509070201050f0a090809010c050c060d0e06010801090b01060806030c0604150206060102190f0204020c06090706030c0305150105030907170309150403020d3503 87
    0x304000300030358110f5211b4807868507404e6004055039000f00015441c060641c44d036250010103866a500a01e41041248041061550b41500068002c845805601c800c0d904c0c3c444500c8280d4900c10b2002c0c0c80390380e00308100d1142e03500c02d00c0da620040b80910b0580724903144000000d410b9a004c0141c0b110015207600c8101010f10090242d5070042268074020403c00c400c955174903886860501c01c0b001400300020004245031000d002d18021440c000303096039030303658403002c08003100c244a401410051060b600000c41e1035000082c0b103814458440c08044442d8000d950700707080e86031000d50072a040340d004c1c06003003c004001c10150b800703440e802001d02821350900d44010115021101940d0805003400188260f8060b44103440c8803086007864015035956a09001c00d20b0040ca03a44030b10b000408520740c1c4140c184010000e004403140c101e0382d40784180740070034903402140100c1c0006544812101d801c04000784000c0601d541e14151100c07031000224100850124061216000164428000040240c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 233151025 1250 233149775 233149783
    0x60909060302150a030216060203071d010801090c05070204091212021c0902013e0102030c0f1309060f060e09040b01050609040209120a0506100803030622020304060e 73
    0x160566a404006040c51500041c0c20001e095040c140404000600602d0a600ca901152900c10f41c2180c01407090006140581c000c2d401203c0e4400083c12444508048652a0b003100c171840005070764003611a401d00c000f00008084100f1075505001c010480d450040e121070042c00070aa0086c1c0228008404002d0080c01c5100898096065140b0400c001c0c070200384000f0001803c00c44d50400010b0000c064401a0707410304915481000200305070350800000130440743d081c2c0300905440c002d444c00d4410710b4846400c1c3d02060301c80401e0070b6024405c02c001805044c0c041c0071018442c1c0000e000580c0d0b2142c2d04021149690044040711170720810901c48940c0254120004000a4034181c0c810300d40350b1a40d042c444018002ca0707100320720002c1c1d80b2700340d590f030758060329406003004111107100e4004034800c03551035410010032995030155100042000a2504050003100c103050051861a91140c0c02c00c800b0390780300f1812032980200b00e4400740c9452100d101541c4203d116000009140400110803494 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 233152275 1250 233151025 233151029
    0x8040602010c050f16080405040f0506041a0a050f030705090f160e060306040b0402040512030d050705070f0f02010309080c0c030c06130605031803030915010501030c0e0d03090801150609 82
    0x2440002c0040308120341c4d200302183d442e0303500400e44080301142d61806070f10602c125400145e00c282000d050040812856000d140181c41c12201003049402e549502c03100d03555090751156101e000c1203000c02080c1400345082d140310324001c054804860700c610008400c0141034078880307243c0c0c40d40020030002e1403441d4107454400e095403c02d441460f1000c00007608602c0001c080c1805161034080429440e200c1e60191000707440000d08107501740000801041d90b9400c01c1c462484411304110118000c1402002180e0a440d00000150351034003007034403072818811410f0340c12410180d4820700e010218214002400340148268040e0803180e507400704141c5006004004540b091004221084280d10025458401c0f503803603051241d1a40d0b540c40304140703807070000c0d09000840e000000402c070f01c541e004943c0b4550149449a040e1060b600c0303d00460481c0c0001300242d0106440704800f02042c036210b101802c3e010300c41c2c900b15109944403001c05e425900010781083c0008800ea400740000c4d600844880c3c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 233153525 1250 233152275 233152277
    0x7060c180614030103031b15020a082208031308160209062e05070503030c121005060307110a0c030506100b03060a0b0708040b040f15170a0c1b08040602010c 69
    0x340040c02c444012510062000401f84220704c107081d011030f1038810342c990789107402007400003001030214041300107984100b034000001421300c00010030b5020f0b00c0300b4440b100c581000900030340000f1075541120130303803010700a030000d185901c5005001804501c010007001004c010840142c40c101e2040c010301e910050481441810310384010402500c8540000b0511403c040714042c84428492050340c09218401c2d014100303002c00400c0200315101d00d4014800e03002c205480720a0755a807810070f100c0146c0107004690780903008201042650740718091452803406840191268100203270380b40586040c0c0355108440503040101080500c0462075200d40003440e030804404d1035482c1400019054a00901489203121004102001404000020b85019141001c0c8246e81d481c0c41d0081050116490322502100915511182442d144994580200385648506031483c1d03484800102c0003400b6410525402c1007000281c28020640710b00c0141450303400b60ba0307407c3d540c5081000080c29a070158200f40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 233154775 1250 233153525 233153537
    0x30f0403061406100c061a030102030a060503070501021f0506060c0a0302060a0e0f0c12031b0703210f0822061506030903081803130305010b041b200307060c1806 71
    0x180700c4582024040403c146e00110020b0350381d8078594200c6207400d01c851640d400d5032010042040792171480d40400701f950000c070100c41c051a610001240d4403200c018007070404840e210924200b80c1801d8000c01c0c4c210f90001e11240c1000b8400c085503181405448050f00107034005014030802d00068440c0303864141200000d005c011400c0f030b0710556584400d161441c0500001c14a00d4403982d014030655201228034845550441e10f1440140c0c2d5030842d9000c280c0300a50703105058049944099030440c0803460342d445401428503030404c2941d0350803000709140c20200c00c200c000c00c18440304580024800384910307000941000c2030310340c840240456412070320a0518140101c404203801880c1c01c0ea011545244100030f581c0083c01d041d045025503020300d000d83c45642804410494103402a821400f025281007260b00c1c1c04c2042482c811200d02e10001c04907040545400c150b001030f464201d4054194800c070707403424003603039140c0088038040700c4140001b4004040c03016044080d00d000c48006e05c150300c0c04d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 233156025 1250 233154775 233154799
    0x305060604060516080412140102030103030e09070e06030118051b030c070c03050607080702010e0c090a0902030a050d03060317070203061321050d0b0105042402030f0403061406 78
    0xc554648114020b08007032010102d003240b06908020039000b40294032201007500d45644442c2c0c9000a01400001c46d0300d001c0074003c0e141d0080c414401d5034101c0c2e40543c0c0d20865144007505002c94400301902003401c00c5107001102800361a44002180280081846048100c1b0130001801c12a2130107041c00016280303800d0300b40d2038041070b00192500503040d1203405640301c6131450030f00e2a005a43c0d1005001e4000c00f802c10030819080541e503440780710507400034020b00036001c20a540b84c10302e80384c2d440d40c0180903002003890540d207036000c440602d01c040e0440e2244071841d100c030f51030b00c607400c07441700000b944524041c001c020a11110000c10340301c506290b41049031650010f40c80e01d03401011306180c05030701c90707100c010b101428040c64215030101c05161401e54132000c004155030301000052400c0c90400c02d46440c15403080c01240c04444600da0000a04610a18890b40194074801240304500c400c2c040300c0350749550034004100840c410000050740692001c18030352a0b84000305114031541ca00c11341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 233157275 1250 233156025 233156029
    0x1b0209040302030406022802012601180e01020c07030b06220603021206070c0b1b0304060e1e1c0e100e0102010609090305070b27100b0306011a09040207021003020316030506 76
    0x200e06007040e4242441d265003944580c540942410010720389011098ac0030000a40e08280f40180540d136400410502c00401d0095241d800d0b0b10400000c0329259000210801c041802c41c054150480c000402130301c4041d00784120208031031004201304102c1c5a44020030000c5240188012039121385580c00b6008034944024003420303904991001501403c40c1d80c000030320b900c00390360ba01c802494081640c5501d03030a05040c50402400d00294501140c410000c0100d00700c0c80011423a1030780001c1c02c004000034006455030b490b500740032940c20000c0c45260b4403c00400c0d44c03030855910321880e940d99603900803807545000a09440c0c80e9800300b45114a4088140040303640328080700c10356500f100c00c2c00600d44a0040080f070f00303141650b20100260551518000c40100845e510507001510b40061241002c0c0030101034884200380f15050182c507010140c80c0302c0c032070301e000500140c20740148014100011600070030b8101c5801682040003070f41c000304002007600305248114480d50b00745001c0044e07103000c0d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 233158525 1250 233157275 233157343
    0x1d0d020d020d0e03120409140a0209030307061e06060c0614060a09020702120d03090b0c03060108040201081b0304080301030b10260102040314060412020d050702011b020904030203040602 82
    0x941410821600c1104143e0f49042041e501c01c8102010703900c1ea16a40c81400000500070307000c1d001f2070090354001007213002c550380c000e03902d2811008001e14a03000141d0b4030000204103850805010a80e900c481907812111842803000400345a20f4050150405151403000c48071380024044401d040d882c02e004450716200348178010f17076901850050381c0d00310303500014182e8a10000015141d1245203021191258140c201e4405070b4170502c95901c07070b40c440102d001100d000440da0540003504200c0041c002d584a0781c4110f030810708614440a10303602c2101101c0e03055204440a494507140000104100041425010761040d04004810003076400d00b0035603c915032081080c0351006032600105a556102981202c00035540018071406c000c84900b4400c1c1c603807a08503020395440c0c18440c00440a50b0000c034140f520110240e80b654075000301540195030000d24030050091010220140600588940325004d01942c0030350019070b1240e203042002072800c80707100c92000c0b0881e942e0034144003d8800c03403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 233159775 1250 233158525 233158543
    0x708010302060a0c0530040e130c0306060e1005040c0f030e01063c03032a05010e0a05060606040513050a09020d1a06010903150c02010f1d0d020d02 65
    0x4036220350f0b450411101310b50401c00c2d600090640c0c0220700d030300101c0d0142d0384022003007900c1c0152410b06680b90300c03840c005207008078400c0011740aa1000040d0110030101500501144207043d8450031644035200c00045900681000c0200b0404c141801000404440144004c2200325401d0080d254103002c010103e070280341810307040c0341c2c0f995000030003ca02034020002030481058900700044100803400d000703000048014501909c1e004c0001c0100f94205018001d032030b01901e810702e40e010107501030804403690402400d08900b0800c0e80800165082c041c207400940c1072001040032200d1414010b0420324082c280c01d204903c1008208955180c202d10902c4030700c265200003499699495010018109080d0020343c0403030052404410400c41b18a410f91288414601c448165241801941c00c00c8080c0000360040d841c01400070342c50300300da80007000e42c10103500c00801e8088490041c0130540d58002c100511010f04407031054941c0608010004051107240300618560b0103019010f500c0d12001c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 233161025 1250 233159775 233159779
    0xb040c0f0e2701090c0e030712050307200909010b0d020906210d120501051302130302060c070302040b090f1609030c06031d0f2505120d1103030708010302 68
    0x101d90001c1642d0300c003400700c14910582040e401000d048421014040350090140d034840c2c80c0303072148217059644181600400740c0c002500610180703007048d40300e200340c004800c4121550b2104008101c0000d03005241005960b5545590224000400c41000002e8000501ca495a43c0c94020810501d40d070300a11020015010f030303480c824545840d804111481c400c080740383c0084400c601c401d00706840006070310b4414400c60f5507080a60214003464810b4130f40a01c03405030300480d0b000b2181258601580240006520608842d2180d5529804240a50854084403450b900082801c0080d03040c07500404444500844a0030000e140c410150151440090000600c088401c0e0304c1c048180c1c0140c411f00e01541e0845882c011071561510028050310314210b400d5015803510301104502d010000d080d415004804002d8800710b4140c0304840725802601c8019102c0e80c081080003d500d0301e829144040545510001c5c1800d0b01d10b0005c05440700c000d45d03901890540c401c10402105a078016030301810b580d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 233162275 1250 233161025 233161037
    0x1009020414060f0f040b0409031110151a1204050106180b0901140303040305150402040614180601090f0e06152805070602031e010f1412030c0703030c02040b040c0f 72
    0x808010174001e00c200383e880358000345840542010b03d504007000485410342e02040780c03916500d02c2140802e0755a10b2450300d5103100801828044d02d01700c408103025503142d400001d030514111020f21184a10240c4041d143c40e5984c160601c94840c22541054100c1001c030000e1108420707440c0803d030307821014404c140380100c25420b8000c482d901881100d00540d081411a80300c204070550384143c0c00015103049108503d05040002e200107109440e103442800102080311244240c404035925500061405e810000025404986600d04170114400b0b0a100c6109090a1610303c0c1480700703110941528240c039000910070703a00b040600401e0324441c0d01072044203640c0504a80c1c4196114050120010300c240e00100c200207003888814845030b1804101440103c490b41e0340c0c042100c51201782e000d503200001403690700c6091420b00c0e42d1054030800030f1404492030400320640007801c09030140c0007140000e0032400c502c1c0c298641406440c5049104a4003040003151108001e0100c20540e0315010078005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 233163525 1250 233162275 233162299
    0x108030c030f0d1407031e0501080c09251d0405091002130b0705030a0e04050c1b070f0b12101401120605060d020706140402010f0c050a051009020414060f 68
    0x550041468400003a0030350b0000c1c10508001b40242c1840c10300000e680080c070581010b20400703401041d04907000f4002a01c6060038250500c4a0507900803c2100000702d140d81000d1200304880700c080c1c0f07904d510703900d0b0110303410f6003080038021074000401c040c450307824101800350303d1002103a0025002d2421000503601c5410701000c3c3c00f1a50709502000d108174000c00c0d244c0c14084040000d0814110300d603154000ca0540000f004201c8100786c4503280a2075040c0182e180b1081c0d24212151070030f180c002214011651080518040c040e40e070480e03a1101c0004c20388403c034000d1041c40302d030440c41c0c0001200740581008101c0c08201140026a410044030380c104010900b42d980c0100003400300070307018542d54a807401402020350721840c030441d656898031080144814000c203c4a010303c0d4140d50300409800100005c881203032117110240e80c540104282d00000407010407519014802c81280412229140d004100c102d40c4228002c01c0e000110310100201079440c108003503a001c03002c07652142425 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 233164775 1250 233163525 233163547
    0xb0f0405160909020907170a020715050a0c020f0d0c11060912030a18030b0103080901020f1005010f080f0c0114120906010e0606040f03020f0f18010603050108030c030f 74
    0x10148a001c0310380114003000216039108a508549500d40c001e40f0b880761130341c48245084034004c8841d0490130080c40f071500843c00740c80d803039002010564000d1420385000040405c440045450544140c01982c1d41c03242102500341c3c05016070150001c0381400307001203410380e68000d0581c1d2500c1c840204400d41940c40354015580e42000d843c902c18002e003400c146600c010358115541e6010840c2400070910700c1d08410a482d20b0480d0b1034098951052062449c1d9195681d041c6058115501c482c0c1940160a411422000c0c01c200f46609401100e0307004c00c4552402ca5000504031444d0003d01182d0001c4c4920912a03e0008041020703410078031709418008440384030117105024095880c0541508074050043c10440001e0f180d059079074440041c00d047e25480200041c51046120301d858401400f8030410140c07030f103400440303001a4040d14241c40c00383e01d08005422442111030000c42003103040f00500180b0b82c14801c540c09024298021480d101d0198651941c03400780510b22400703a08002010100c503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 233166025 1250 233164775 233164783
    0x10306030f03111b15090103060b070c03060c03020a0203120603032109010c170703020f0d0c050307080601111b03101d010c09060e040b0d0b010902070c120b0f0405 72
    0x2503401c07205041000c0381d070b450020b0a80c15144614203880c03081c807503000791000400c0e08229048600a040b84600300034026000c0b4140c209200f094145561380324001880f6403840c0060410500c940d10011140c1d0941c0b07840411a01c90f04541d008061050103400c0702c1540004c106c880128050000024a130380e50030000e4918031030761400203003048d910490160101460021344e8040c040b030760000e019540d140e0800700c50303000b22a0318406a40b000c50000c42d280f1030007540100241c09410000718070304044003117048161a00a01c0340380000724008204845958420006074112409181c0310042d1506414441c0d07407028000141d020a44560900300241e036010010181000d01c0a072080c4650404c40120039405209404040c81c1d41d42030200740045144980c10082c2034807110344a040c800d10f01ca40c00d000c01024170b00e000b640c01140d0012040d01140407841200e00030a28030902690b20030440c50901c007002a2540700b200b03035088034160303000018190502d05901240034801241d6580c2c580c20018a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 233167275 1250 233166025 233166029
    0x3120327020d063b03120703181104050f10050f01030905070e010617010305070e071b0b1b030c0f07080d060308030a050115020601060f030b03420402040b010306 71
    0xc030785007142583c050310000b1079242c002c200d812440454920f2425404d140c240051041c1030154000b042180341d03e40081c4451900591185800034034440c0036840244000f00401003501d22512410032695245081c1c09001e90110606001048a00f445104204000c4107802017510035002c041480310964800d62003031012603040000c0b210901e545d6804401c00840030700132180011680e401307400700c0c010841320050480798004000c2c141c8a141016001d230a00340909102c0400050310f4988500e208003020a800003800b03805608241d0514000c9010004070000c4030f160841030a0007000340803a10103087d81c0080b40c8400d039503940c581c41460403800903c40c1c1703800203810506d0b005000c8103002010000e07620607406e24004101c0c9988400381c5040e00c45118181d80011307072018005001d094864050322405140c1e604000c07030064801d20000c1d08100600c507440c03044621014501040c0d060a02c510038007060505007060300c02450741e1200c15a00001400a0302658030b450f9000e45a074401c1c0c0c40440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 233168525 1250 233167275 233167283
    0x60906120402010e0904030807080c070f0b01090501080a0807020d0f0212100c0305042003030d1802130c020706230409020c0c030c01020d030518010504080403120327020d 75
    0x6a920411003544024100c160340c141e00044900c40380310194208a8291401103806844145896a42040031281c0c0200141003907039401040c803017600044e0102c00d4944045104814013881c1e9810420b25004940c0b0580c407410113039000090000104018204550060341c06131441c900c915180c0c100144043d0014900a400000d000e0070600d610b1404504140c40001810082c80044407280c41101600d90544000c1c3c02640b00c98402e8041480e054100403044501500783c9040c40c10b946a0f0a080359400000200803c490b8980c420442c5000407042496040c3c0407410801c160410000070359624a41c001d0100303104010010055400c0c0c1d6940c40e140c02c14641c82e5841d52191203102c24806500300140080c40c912808a91030710528002c80d500000c0343c01a030040800e040000011000340c00080c02c40b80d4141d038035000031232070b112081c0149445a4020301031155a20f255191000e6079511403d40c039010035141241d40301c5c1d4200314041d41c00346000440b9004d1652082400007800c480c1103000020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 233169775 1250 233168525 233168527
    0x112805130b310905010902070b0a09111c02150316050a1701060306061205071d040e19050709020a0219020103020c0a06060f0e010b0703050c1f0911030a020310020306060906 76
    0x490301c40b0001d45100e0075036890706420b00c890707640d0391007a00c20f034098081d0050420384107400198500c140c90f848048500d014620400c24940031202052420008051389240c681c91200024150b00b046113400080c2141c0d299528610704d020003500c00425403103042c40d0100040022000300e941d101d050403800c4d00956402d00301207541d440034090001d01180c420344001c0344002c11200d000c0012031281520507122902c60594100d2a45000e00d454000403044e140e00035500c081400c0e12a10401c450100c0c03d001d02d0b041041503080e81089482c1c148150b0282c40018010824080b4003540410340d08101c06d50104182c141480b18401607029000d4200100b01e2407250358a0031040c404240c00010444841c6850564007a0720741a03c240c03100d0003409000b030410030400c0407a0009202e04014902040f000c010348100c54291000c510890080d90030000d18183c0303811040c014014802d400c400b50f013000320020a00701c1c0036a400b0a1310b481d40d00c42908515a170101c001002078940c0412101c003208010201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 233171025 1250 233169775 233169847
    0x10e090121050f0c0f0d03090302101103040f170a05150601030f020d091407080303040b10030503040602030c1c080a0903030f06060c050705090601080f0406112805130b 74
    0x80780c0d680c503d910461703104006039000e07055281000b10b5100e0b0b00503059602c114289055800f070120500101c480c500400c0082c441c1010000713024030162004c2e0079800305403036429117441c01c00d503c2403600010250082d00424043c0340059000500d80042c441d50345070030452542c9610050f40200103044071814428000100c0f5039400019031b1240c41468483c45019400402c601c0c1c2c040e076510034900030303600c2640c41040402e001c82c02840155600a500a54211038562256981811030b0002e5201d80e025900c040355046601d0700c1804000c03245030542808085954040c00010b01540300500501080740e52203804006141c403c1c0c000c4040c8802001040c01720b40d941e041e0040006030402b4081e0384900980c01b0106161611100c118041c1d44169228800b0791140210306002c48000703402142c2d1140d48114900b1011107400c041c2042c1c0c030041e01507510042c3c840510108001c945010b8030f080100c2044020f03000740c4a180010155a01c0c0c04805844110302c24035a0308000c29400f070280f0f544019841 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 233172275 1250 233171025 233171053
    0x40507110316030e100c0b0f09070b0702030c06040605030a05060402130506030a061e050103051b0403080c0c0411030906090d0522030206042d08100e0109170a020c010e09012105 78
    0x16030003009200f008011001e03503400f50310040c0748c02c0580d041c0002d608848000c101d02407034000034100540c0001e007078449600c1507200055050340650300c0303140405c41c044204541e01442d8402c7c1a408442507070154a00b900005605800c2000360003094800c4e06c001c000700c1d44e0740c800c580c06500607002da40303040e101d02c0104440203c003c07109440350a00003800d040020300c001400030800c445060458800074201421595004035540050080000074814028200d030726a0750741c05883e00003e05e034107600d45d50b400c01821141c181080100f43c10040d40c0700311071507150a030b448412219880351201410f45410b906075000e0340c4641050b8000b95001e6008034000c41c5185030805a100401c185155a0100c20012500ca46041c4064401c07401560046070803010354110b10380101c040078150000004200071590b550102c1d0380710382284d29501400200303407004400e40400c58958894001d00b0290f41c201d40e141e0000e60000014003407071064604c0b0030046c0244c00c2c800e207404190f03a035004040e11002c010b1194 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 233173525 1250 233172275 233172287
    0x9041506091a0a030209060f0310060b0711060307080714070b090c1822061805010c03050106090506041701060308180f062a031c0209040507110316030e10 68
    0x442c0c8400709251111000140c80c0c080303107078411030b0750203080c259555454904009113040b0440c0b031160180a02c025004151f840c51090402034681c0400540d01e600c01c0e4101f8101c801d401c2680103012700d90030014041c2c142d802603da00d038000b8035480d08041c03070b2100800c482528019260f00034100204041803040c10310000c103503581c040b842551130740f1a4080c00d9500280c8580240d40903081443c2202c44078a841c100354940360f903c10f00400d00861401410220104007a60054081c4e0f11650755545241c2000e51500074135005101c01d281c03c4003264100400208035104e68440d6011002090100d880b0041c400c0d00103a00443d00710041c00e4454005400070b0700c0a23000340600510454030110001c0c514600078081c0d62049500032040b914090075200400d5462010f00c001a1240c482881a048200710b10307120300303035803125120025848840000a1109035072001c6c080c3c0c0d06002d01e10903002160103000090314201589080d110010480604003521042c40c10050150458100c01080d00720a0300f2403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 233174775 1250 233173525 233173541
    0x20f0c06180703031b2f03150c0a180f1d100308070f03020c062a0606010c080a03060b03010306020903100902010503060d080903061f0602030c0c0904150609 69
    0x20782601d02800c8201419464a05074000107000c91044440000b40c100700103d10302056100d083c007002c01d503110301910710b120198aa80102282d603980040707461404c05010014007200d40b0b1002913101d05001c00084907900a03114501d04000c0c030760b9214503076032183c07240000003040148015441c0c99154000001c42105208095a2010318640413a02c0d41103010f11403000ca0b0340018402d41050900c0c2c3e00d004031701030307031210940840c4504d560320b482d03a0f51040014072209001403040d00c80c2002e541c04064882d0003181100040350014410490070342d800090701945a5032100d451039854809038015002040c1c0760300090300440000c40003008005140e4010011042c0c11800c40d98424844000d4078151101d00c4e10080c001a42071022508500300441c1080d040e9210300310080c1040c4070400448d01e000700407124040c4030030800e0158241407280c81502c0c0050002480910729004c01243e00955032101c8140041c012200c14000034144480d600943d00c440030b64001c00e000b1559036400602c060f102d030b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 233176025 1250 233174775 233174791
    0x140414011e091701020d0c091a1602040b03150a05090f150f1e0718050904030905130603050f030307030c0f052205041805010b060c060109020304020d300311120604020f0c06 76
    0x9d1000d01c44a680102c0a8070619855140c14607035054040d802c1c00054a840c2d0326441e0180300352418100701264a01c019032040202d1800003030306240c0880c055141210656405090360040c2c045e1404040524003141c0d4844405001386405403100c003e0070064013203401070014590f042c40c003480840f907800045036995646851540c20240d0716141040301010042e680100403502d5202d0030080303400d0101010944403e08a070000b00e081c0d5035140c690500c0100081815250400010400100c0c1c25200b250300303924a62a2040c420781020f64043c1c40c610480d038582003007007030045590030203000e41c4a0b041c020f0000035100b4000c41802680035000d65031450341c200ea40703509040110b0301310304003407054400381680c182c020324540e440c041c1010000c0d0b0000d04180e8100b41103815140c040b815004a0300d401000211781c04100154450740c101c0300c4486580758000b0541000b02d154003400d0001d0941c0c4170141d030884011b01390345664001800074415484c00144018010900d03149180380031420611954036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 233177275 1250 233176025 233176049
    0xa1401080115050d09050309030307080417060402130f0902060c011e020c0a03080408040e0903040f050d02060703030519060803040806090c03030a0f140414011e091701020d0c09 78
    0x200d07011090707800c441d00007071000120f0074068541d10a00b40d130800101c00e4084d900740d91038041c0140201e802c651201e9001eaa4101d0009010080c1e5100b51120010050032100500340d24102580007851041160020f4003c441c0c68030080d8204841030ba001d20b2074150300401940c0d4811708400319501034514002c1140c1000000341c00060465114001c8441c14202c08001d0400c04800355002d40d507a00000d4401e03520001c0521000c1030908051038140e00444030f881c000d54590380307400700745840c0f210300e900403d004000b071035400c10060b00c4000513180c2556050601151682c2d5441031414842030600c0700003903141c2403000c006048030b000f00060065422080039540543d0ba440c3e02c4136034440718030181c0c58140d030041020b4100b8030f00c205400629110b8600c2c013006031036094901082244c0040d0098010014180c80306026982c0041c50700844100c00d003480407035500654009041c135601d500c80d644e224103202c2d050a280380f00a504441455454002c00c01c07041c00422030081008150340910174500f11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 233178525 1250 233177275 233177279
    0xf020606011701090c091809020306090d09090b0126011d040203060406050601111507081e01030201050903100203010909050c191406040302090405060709050406060503240a14010801 80
    0x4414151120106405442c48071143d2a02071842c005141021000007040101b000100340004003440e424102000b017000818000b84c54010141090805018a00c1c82d0303200b559503c102030307080310184045400503075000846062a00069410807407080c80c80040c91a0850a250711001d000c60403810303644003084188c000001100312500540c800d6034040c0d419032003000041c001910300d4002c83c2c1e01c030381d061401d03141005d041603140b032500f0b55140c5a92980c0c8215010868981d5001d00581c0d403200890380c42e140c0051035216140104101808087e0401c40005408002a20100b002c040c08082d080011956582e5813200d402c0280706400e4100c4160003040d080c11000d10305030011640c400c80300c260b0511803030b04c0c184c01c1d4078007902c00070035aa0b001a0244400800750b9600341560f8491400b43c80030b001286050500205030307181c01d030802c0c3d10840c5401018010568041d00340e9502c100f16202080f8a19030b0002d222030f000c1c495000b07043c1c0c41010a1b80200d290f1100900052214500382c0b03900805036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 233179775 1250 233178525 233178527
    0x309030b09010903120506030f060117010506010c030e090903041e0f1d070c0f02120607030b060a0e010305040606260f0106060816111617070f0b0705120a0f02060601 73
    0x2a074181c001340000b880d9141e8a00e00c2111580300c60381102c4020200c51003c0c180c15410381c00d0070400d92102c15103071550750b005680c8010a000307481c0d12070030901e4060f5100d1060b40e0f014050042c00450030f4081d0811400003503a03407404000300c40107010595042003820707000f0044140b0411450007946526080c60310001000d892014400f1800752000b48074454542d00d58504850500401c20203032140d601d21490000540c840c16003060342e004a48024007800c1c031781008090103481d048088507029032420400300b403601d540800c1c00c035a0400c2c246808500b41c0ca440c1002000f8208980140c4100340e8684040e415071503009041e15142d8248400342c400e4084078096490807140c483c8620340c0070404000000300c1d02e51700318894209105844c108400000e0550341e0b01e5251007030b812015210304410100500c04443d0940300f02d4881034142000700b608604142000a1003400b40c86600012140845e00e0805c021051002c89801d050500415480f00c02ea4400148088601c801440243c0160b00101d8415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 233181025 1250 233179775 233179781
    0x40c05030f030a0e09010b04051309120e120a030f1d060408070303080a05040507031220061f08030d11072901050306100303140d0614041b02100b060405030a0309030b0901 75
    0x862a01841f68200307840d0805003c2803201d8011007075005503503000034400042555503010920365180d03a0780f100051490041c4290b03414071b04804841544038041c002e0000e030b400314450031940280e140c0100142d9100ba100b1148640b5010486da00070800724001c0b0b0100c4000030514212030095a844a26440300c0317a40d10300316001070320003408642020f50203102042000040c000810058500b00b00c0040702c0114024600010003e114070a4011409000d03400d0720340200740c509000c00c65914200d442c54156083d50f01d20032900c2d026035441e1a0f81d501e562034208282500c403280c1d002003440ca114040e100946083d0034540000707191850345000041540c2c1130000f00e1034031030440c019204103500e00350349003038031541032010b1100034400081041c1409090180500001000c20880c000b42c0200610108000d80d0301d22030100d04000342c071440c1440034650000e10314004c036401850018098000030003185c4c40e482030341c10864052213243c01c16003c040d4081c0b42071084a025522a400507158000032070b0a03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 233182275 1250 233181025 233181029
    0x16031511040f03330515011419140a050a1b02090601200714040f090215030405030d060b091206100513060f060c05100b090a05040c05030f030a0e0901 66
    0x42a2241c14144000380c0013010401542111420403401004035040d15000906010508a01d19840d842440640e03030f600d5604034000102400c080c2c400e41c2c004501e150150140c102e03092404640c0c0c0c0500601e0fa0b028202c84102800c17075084559450300c00400180ca170b41d10218144000a4101007003640c1a5688151a40200d074010407141107074680c9001103035503140340e000b000090014866403442d8005d040000c3c0d00284138461038220017440510400c4200c62041501d503e8440c104107070000180e449005a080d40b54140002a40303075159030428a1071400b41c00740e006002d514148011035640c801e940542030840003114000c100ea0004101c0c50b441d40e600b951140307842c0403400c07002e010038a441d103c0d03a24010611040001d105e030751100f446503c191583d004101003940c0d0f81c0102d062140a200d442074074040402c05200700c03500703040440d001c11401130001c0c0907a81d0700c0010608001d14441d0020007000300500f1030710209035400a05490780c5c003048192001c2803009860210704e090a00e81141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 233183525 1250 233182275 233182289
    0xc180a0b07030305070207210303061a1b010e06070903050c040606050a03020d020f0301030f0201170f0126010e1608074208040c060c15020c1603151104 67
    0x81480002e5070182c014120142c140390550284100200c2e00138900200441d8240c80110004070b90089420040d08a50f01d58000c4d15007600d082c1031240c440014482110706802007000b103089074140552006004080907a0101c0d0203004803001c1c00036460b4418051001e07240200c0503510440f1014081000312266031041601180c030522014200500981c040c085204c2c2d040405460300c4110301f820719036036100760022905104104c26120555030b1200308070b030300300c003401400882e00d003008002c04054110510a04450f09861400f0b015105601248580180c0d00ea500030301001391540712140c1c9400030707003452490a02c03503c600081c12880004041c01150644900c00601d500083c15050b08030900990242409500d5021809158112890900d00e01c0032940d03030540508051510544180641d8000b034100180c0d0102c980c0416010b041c2e0401e0012004c0005903a2205002c15608054840c200710808146962000003886500703508104815428a01000380402c0045450701600a13402462 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 233184775 1250 233183525 233183527
    0xb0a1517061b1308030a03060611070504020d0e0d0c150935040906030c050405040519050708010e0f010c03050408040e09031b0a0308070201181106040e0c180a0b 71
    0x419000207000a91100524403001c50700e0000c0000c00e070f201c140010707070005000381d00001e43c55064a030306d4810b4038082c0060703107886082040070207483d5a071078549024582c031491307001070350368210000c5501203410f80c40c1450603a1290300c200d6101410084003c8000d90320106134122607024804584189010580c0c00030203281140c109070f5070f030b0f602c60019a8105117103c1400380352000c07204031280500020000218089409400c0d0700d01300c4490303032080d4050307800f03141824180000120b0114034001e03503044000024174000b0321030501a2601400b644514101c9d46001c4440c0c50044e40450401c541d521000002d102002050404504548044170060301e00c41041c401400101094090361342c02c04455800c5070f04007a04513440382c1911400c44420981070b0302c0350600008040c2c001445541c0081c1c540000c000c5240d101d071015070181c5190000030003c2402c00340c918000d58845c0180c8010340541401d01441d0b29144c00c44200c168011408000d4920480204c6400e918041c10a842518040c0c9003503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 233186025 1250 233184775 233184781
    0xa0c180603090807020a03050f120f03010909022d04060b090a15050408011b0f0212030a020703020f0d0503061302030712020306030c03060a0c0306080a02030c010c02030a0b0a151706 80
    0x841c020400c0600c00c03641c81000b0001c96000da030304c480c0c0140196000b24058409a041040024602000090315a4204009110600e0303a61142401e0340e0440e8501540030501041c0c501c0042c80c0d2000201001c510280703070315030740368012190088070710006d40103440821071300c7d8a540098082c5d006000c0c03a0f56100d0300f03046080c0718a0402107180b020a0202d810420b050a0f26401c0150039034120048c20702007030204241000d0b40d03c0d0311a00c04110b03a000b50002e440c01d0008004445500d00c0000c00c11044141c0003d40e403010107108100054841c0000001d503040030041503401016588280e0f10144181405400860008410b10840e406040c0980394042c12052405080300030750001010160306001c0c1c40c500000c00c3e102071140300d1140c500c01d040040c0b42104014040c040f2481d0303400000d01030380110300480042c0c40c0061800c51010007400d019240101600c0000d01d01040034000510055091052000629040d0060f2506c900c200301400429a151038401c099080000c5030294140d02039004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 233187275 1250 233186025 233186027
    0x40b060412151b030c0f023c061605030c1c060510080f010f08151b0703030c03061202130e0c030a050c0f030606060703270803030a0c1806 61
    0x61000964840d41030408202195400030b000c40d8000c10008000b408080b02c992140c0fa41813107600b509031954200300f40c140380d1110b4025a102d21515004840c480c0400d414510b0550809803011400313a050411410601788100c041e4071503030240d440d017800d504440442d60501380a0415244120b101c0282d59040000d04061006c1002c100503400c0f1103561f03200e001013450f0300d84088003160380c0400d4444400d0703401e0450000100c0041640281c0031806442c02c01d20118101003824a011084141c02c421203860b81d1045009006d600f110720408038400140728000c26405410500719486140c030100a602e50303400c80c0c000301030320405000b0b61007265040304005a000c1540700445880d03044081710860003d01e00468a00084003030b0650780d41d03001e4a290034041c5440060142c80038410707409807295080000200d941c40c0150b40e4014144a582c400e000c1842400320140c4c440300c2c4001d021501d28035541e1607510b46961040c0e400414203400c10009800450203240310046421040204a07111032400c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 233188525 1250 233187275 233187299
    0x15050306010c060204060512010e07050d36050715090b1b0303010b041e0b19110604210e100e01090509010b04170d0504050904020607050d03020405040b040b0604 71
    0x280314107010810301c0040200300b541c40074102610711601d83c00d9a44081420000f00840140d0003001c80810200421145540c442c007502c1c0e50718410f01c030220704c1e0170310140320090b209640301c1404000090001406000c40e080c01801402c40c3c01002955982902c4031030840d80280382c603039070102255424808110441c0c1807002444031641c04010b107020b1031140301f0719a0441c5e100703030311184c0d40e0900410180030f14100000080c020070800110445440d20f042c002c00e403140598402e2800c60f00e84d1030748c1c01541c01c0c011840c00d1500400a410780d2500d11307003440c04071a600c1051540443d030100c41740c01d0400702ca0242c10340b12101640140056915443c0441c100d400b000c4001c01103042260200b4000792540f1205150380c06030903682c01168031a0704110108041c5c074000c01c049105035010079040c045058200782103400703880060310f01900d20b40e218000700300144549032000b0410b04c00c484440c508694154041d0090fa88200c0742440500840d604010030344103917002a80d40044c00300010001300402039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 233189775 1250 233188525 233188531
    0xc040e011421030405010219110607020607060f09120215061212040311090c0f040302040f1119021b06120604150b03010905010f15030e031b01060e010b04150503 71
    0x4000700846007102d8195041c0c0c1c950100211400d43c4085800d022039a014031540a4606280d0030359030080006894440d00d540e02c2584850080d100040c4440a5440e0b000031990300541040003032054100715448640100044c2009856074580e8112140c80d880c03001c01d0700e01e6030300e11580c2e0710754058440034100301c0c000040f40700c00d107068810702d4510a801c07050f01d13018000031802020401030030400c11041c003c41403002003d0540225003004501e15181202c000e07182a00d406030b400140c44e1620b02d40c10001071003912041607001201140308a0924100400c0340b0400f00c043d070079a00c002540c8010000c0d48420f02c800799510000611060501c1e07596006403d074404801040840c00c103616900603c0c400049810001445038000b0041c00102c85a0180c030340148080d8078891589460245002c5014038800b56040c20103803101d07202800c4841c20401d8500381d56465507185002141c0b44210b9000308210321401c2d0300449940300009642000005032800c8426018044002c1c20604504640540c002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 233191025 1250 233189775 233189779
    0x60d03120f02190507021002010e0703140307020a17010c02061608370606050304020d03050c280203010b0904020d1403041d0603190201120f09060c0f080c040e0114 72
    0x82c400e030709454082d0402d0b22403c0200d130b00c0b1503958841c00c0c010701c0900ca4800340c512040da030402c010f551a82200244036011250007203c0764044074040c40e100e908500c41c03080301035800b6451210220f01d440103554201d0210010b48001c01c000d04008a059841d66000c41e0a181004013150400c0e0307500303024600b800d5101c1c1184180c1d440750094620400c015904584a10211004038072268001c55074501c11030000e06414100310707081d449c0c030781e00107505a2407444000342003060108140307070107400406c80034130f05c0311956000360800c41040c583c3e100c8a1241c2c0e030341603110391300b402404011402c1022405000f1074010b8182145c145450b110790702c200d11390390350aa40030b03c010800020407200d8080180403c1d0400078018560342088803c16143c65030b030340e03030038200c462820000d00c0051b84c1110607086907554620000c190064034080c21b00081034050700260845042c0140103034030a500c04680c0c0b0034042c0c191142101038030b40e030541c00042e0056000c1c02000d5000304e001400b80940d400010384000f640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 233192275 1250 233191025 233191027
    0x11409030a0b042a0f03140c090a02090420040915030b0a0c030e06071e0c05010e03120709080a0f02220501171f09020102012a08060d03120f02 63
    0x3055462082c1d25004940654400003004c2d203000e240d0709840241c4181201c0a440c904200d82400951039041d4854070000f0244d500142030701e0030350481070091602c20400204455210b290400403400694000c0520520071450b140d894515030b60175182140d12050200350302c1c0d0401d030030101042c00415001001100c1009048400000145007a072118450781349000080394040c0b0148000d001c1c0e420070840f01c44c80b500007900300201d15500255070300c6912200c1402c0080b445a2100540d421444048090825402c10222100c528000402006058070b1008a220b01da03030703000781c11a29164140030340c1038590080c00718040868200e0718041d80290000307201029400d5040160070307020199a858846468a807001080401d000303c56200107000c8440103400c02514070341e09061042c0c031b20350348020032696039404442964401d6114110048200d00e0001348101c1c42040c2500403280d01030480b0001d1242c0c07001a815042c404a61143d036a41078690801d4500424404009040d5801c417001d09154 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 233193525 1250 233192275 233192293
    0x2090103140106030209150403030c060507091d180d0c060506060405090901090201030e060601021e0a080705060a0b01050f0f0307030908030109021b07032301060b040e060310090201140903 83
    0xc1107608035402001103480041e1759003100c206000191041c00d0742c4c00907094080c0820000700c0d41020311010382a511000c00502d647e905003090301d400c8030030742194020290310490000c0d0000600c000d18010500c1c0c0c50201c41c00001e003158203954010380c5c054500002c89100300600000d00d00d03046182c001d02c00801c1c0320f0919803604045600810304807088000c50303448000c840c0940d40c15102d0280900400c0019018601c1d0000c0040d565203002d0f0001058000e00d500860400101071103803282041e4040800781e650b9010f4140159078484c246c903080040c924020a1040c2c0d98051411543c210140c50003190508816400c20340c001c0c1c0004000758181a2100481c40010b4a040000c50181c0460100142c64001d410080102c071400c05010003c1903000040038004a170f280b40d03006081c580f6214400d0000000c0c051b88901400d8a9030090140800c0403c01042c3c0c0600c16044030311500d015021210503800e40136400d001d075614200b0280c08180a5014203134079010707420080c10100740260071160111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 233194775 1250 233193525 233193551
    0xa03020a1506081204090506040b0922020301050c070215040305060c0307110a0305210108100b011e02070501080f040b06100507020a030804090e1c0518031905070803041802090103 79
    0x100285040f204200c80003d411b0015444c0d6229031600034109079001c000440d04240030039804c4401424450360901035100085d03010302c43c43c2001095540c00b400a12079810a01c8003031031113401018080340710342c2c00c0b01650010304003004281c5040380e40140c000c090f00c2e15200c100003103950005d0191410031440c03410752006e5100400c040d0015521035601c0c40d595411a1100040c0102c1103640ea00780b002c9000010080d103400000d0400b1049a601c1d030000b030f0022100010303100040781220400070b03162418070525041d90081900b60880e40b00703886215407a51000121746080d4400c880090030002c0390800703d805410b0030301d90001c200e03609050592502610b500016075040c1d20740d0040b600494005400c0c80904168000e411020640000400c44506529021b48d413840392403041130100700011807000d40ba150340401c0340340b22000c054180c4d200d800703402c3c5041401c0c486d09802940c6070310030b01d400001d4419002088034211003162a00001b003c014103880400780d442001c0b85410551220850a001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 233196025 1250 233194775 233194783
    0x50c12030f071707050a150603030e130b090906070807080f070f0e060705011505030304080714010905040e01020306030f0d0f050c010e06190c0302040b1b0f0105190605030a03020a150608 82
    0x130398081d100400c501d20f581e2415110b001d141421482c0d010341800d20800000390840040008107408072a240380201c48001c0e80c0c00107104d103100c032a60100001c014060b000d90003040140c000c40043d501c154680da0f81140070f590500c4241c2d00400488180800a11039034441e1000380c860903031519046820030100f4000502642010318180c41d143d540d44985410162111680d41c001e20081c1c000e036081c58946291349444624500c42e220145010007120078076a07124144c280080d140c000d0041205018200146000f034100315001c600a102e05035503030400300d1000410303038407100c95035940100600e0017000845203600a205c801c4650f6403909540382c030303124090202031700c9840d000001040358201140c81d00141e814095450091610400041c0854a412030880c1c400e1030301241070420440040c0215490b1541940000c1e40381e520700024801c403000b200c2d1034118200f50002003807190a44a404058035000020801400f5910460060000901114454080c032841500009095179101095414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 233197275 1250 233196025 233196037
    0x405040c021c050a0801140114030c09030706030b040b090411041e02072405040c05010503040f0507060329130902060d140601030509010b0d0321110304050c12030f0717 74
    0x1080e008140b020b03041ea07210307107058010310701d607070001500106110022700900c0c001e402580e4212000000140c0320b20204088904001c0040c040703030b2699980343c000400a142c400341c00ea2055040250810107891f141ca44140110341007074000104002d070360100700c010811500600014001d41c1603e0180c5903440c40502819802a01408609101201d080082030502103a0006051504050001080ca10310f1002c060310801e0900ca0703643d07100c5003005001001d010400402d07500c64a040841d0300ba501d0b0f0001c40c40f40d852900343c01a107401d418291740120041d014003580010b08541c0032400f5000c03d42245a285002500103071030050745141b41d80070780e00001c400b605c0d44103900c0240035840d6031500c1110b90081400c0001c005a800e024000385040b00e0403040542003181250300f540f50094414000184c1d40c10400c2d040000092039074000d001900300321026142800f40d03150759801c070704103902c5052040c49400d0255251040400074041c06410103002500c080500c03100004c11f100f148030003091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 233198525 1250 233197275 233197277
    0x905010b04030b060303070b01120201090308030916050f011b081c0905060a0b031b06040b04120c0b0405030a08030405071d09070501020d0f080a020c01060b18150405040c021c 77
    0x1e562400c5041034540c200c1d010342198041e43c420084140403c12803100241503801c8045c00c0586912180012074000c0c2c026000a8983d41000003801003079580054144800d100068641110f00c0e55502048100c0f0384014019000c1015030b041103410200c41020f201100f03105101c0d441c01d0005c40b6100030f07a0744480c80421880c0c5036944c841d40b414441d0400c24250b10440940b030920140040b0000b090f101c0c5882e000341c50018900c22001105a80c600b02a100a000402d92042e243c59645001c50801c207225042612217828041c4041740c1d01d0194011241540c0c4007a0090550b110301d5074622000754801081034506006100b4042500024004040c03031307999510482c0352813801c100c0856400c00c00e581d44158103660058840310f205580141c2c0b000100146801e042090fa83d4192020010b031040340c0d0403812a518007030b8041070014003c40030b8200115074081c0940414804070500145880609604902c000144400c00030751909400c035502d18085803040e10485d00c0c401c40c0c201c0ea10780c2204e1200d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 233199775 1250 233198525 233198527
    0x18040608011811091005090711010507020a17070308070f02030f0a0f200705060702040605031507090b030106050f220321020601050f10090317040e01060804050c0105130905010b 78
    0x1400f4021a0041da0301c1c80c02c40d640003117400c00c59009581c00761a8030500d4040c0003840002099036000d40e02070403000710104000c3c441031401c024029180c400d400011a102080d11442ea02580096400da400c09549a01d07103400f1612562002d03142815000c84640451008101c241c07020008c0501403d0303050115254480310a40d0000007034824403c0d8480f00c000380080745d030720711080350001603514221034050340c82036076400b1140081405002603030032003601403140d80c829401c0d003920240124450301c0ca980e81e0709001600d40a0844461000780b04417000500140718002900840000401c454140403070510b45c54015440a003440d80c0d02580f05880400e405110401d10034607444030f000003440035201401c00d9604010018401c04031000305030340a44141100240464050b00b00600135541000c07904950034124244903981e540240190f21140e010780000203640d60155070b10300e01940d0705c040504601e541900046a0582003800c0340440c1026a83d00082d580c5481d100701d030301810560804d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 233201025 1250 233199775 233199821
    0x13060306060e011e05092706040b060901150f0314090705010908121204020a050303180a091107060507210603020306070807050301030b06130c021516051804060801 72
    0x40031090b02c05a101880c0351541e000030503190b84088a01105640c000c075840b420343d0b01d500038007003160603404418124000110781914600d03d40015120f11552140c000042190703111001e010140c007007031160703419001070308410018103070003262401524000c9185c000f52031401c0c04880c90001c00140c90740d80903904514014841540c0c03001d5518050079000c00101081002c2d180749050921461110722004010100814110b50750a204070000384001030807a0348802e00c0180d410109039140204500c51310188000240c0d0100328003441c800284a070221500741380403901c0d18000742c07400521703a10800c40c1080c03c602c00340c04031040030002e4030000d060000e1a18203510501d40782110143c10181800190b00400c400d20f070b030200c200e03415240d00c0341b441031080e101c2001080c0200d03889800e00034846e04011f850080c5d26400203030f0f80c00b0403841d055469500c2d214000b840b4100034200c00c00bc00040c03410409001d0492102c03100d500881c40141001a009030745100c103e0841e0b07081805680400e20b01006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 233202275 1250 233201025 233201039
    0x70f0e091e0a020307050904020c0f010e0601090605040b010c0305130e0903070b01090509030a0c0507180506042a2007060f090b2503020a02212407030504021306030606 74
    0x29099004044103002c602c1c40c01c5c4070380003800e0b1340900c1c50200d22a0b9000903180c84160021701044085803881c40003032000703030b41c1c0d10700c0b140e00c690f803d01130f040442c3c0c030b8002d0014283c0f50034005ea101e201e0381a151810010107d4070f044619900c0390164005079840000300143c801420b4225030300c10a07041c8060b5032540d0030303858041c0150320b06034090f005a60130081403118400300481100d00300e1003281400150b46800745419800c0103900c2d402002140390036009107030000001d400883c440c80c8102c0b010003181d50b10f0245103100d61841005910703144c8000001c800c40d18010700003403101541d003040c041d8084041070600e80c80d2000a03040200010241d5800760700345a0000d03168000f91091458044c20156000c010040580100b003401c507580c24000e065005141c003c0c8089480142c01401a440d4001c04903001903144190318910402c5200315001001d001000101c44200c805285058110035101c0d41422000707810080c0c403d903071042410062942034003042c07060b0b8009610030100440d0003854008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 233203525 1250 233202275 233202331
    0x9010f17160b1e0415120c090905090c1309020a060c03140d0e160602070803180f0f180f010b0702030a15060504060311150909070f0e09 60
    0x40031825a4054104504884004070754041914810800d0703945851000c000c41070300c2d001074100000307103401c00180031a1150181c82182004055902c07031040410309200a0030803212821200310019688000602142c07096820054111203d1012110103060a100040c00d45605100039a81c95070342e42c220300e0460a1a40001e0010951401c01401c0d00d1026103001e40b203c415860003041048000881500d2103046500c4460a01411300c2150910220f11070118013540c014007859002d4416180c0020ba00d8500004880e814900151124a041c04000034014200d01c107031103840d070180f11025140707072944600d03441000c51900621828000d0a09802d60305040c00182c10000c07420100704001070151b180042c158103410b6210303201d0b180218281440320020401c640240f81d200e400c00d0000400c0c410300c4042d139072003403508551000c4101102098064280300d568406900506240001010a0b00504000c51300f40c805050580c0d03040c0004001900c8040c0031200d080001880c0c0c2e944044807100d1032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 233204775 1250 233203525 233203559
    0x80a02040501050301090c090504081218070b090303070201030902040f050f0f0114013606051206040903140703051309020c06060d0c09111902010605011107050d03120b09010f 77
    0xc1c00030400d80d14540ca4000f201c000c48c0c000c42c070a6a07282c1000c030b810400440d08443c895480b0410408460600610000c280c84072034801c007880c3d12944901140d03a072001412038016000040066141c00c201d40c0c019409090301c1b4405a921503030b280c040c01c134030008074020b00303114812403202c8282614000400130500441a00044410012043e01c11860390700510395500b6003892040c0c0d1031080c50300aa0b00c01030480c8103200168400c06804001841a8001c80507104401c0300311103002003683c4040c180002c0b11203a000103000100199030081c48040c4c03800c02400d0003406031030214500789840024840d4020a907100740140e41d800070f402120b0010511035a60030110407507400000b00f160b0f4440030075640c8140280000395a46040200701000040122503081a4060100c400c0d1003016038080c0c020052423140038085070406d108460705010200f541012f07500000c01e016490f8240e600c1c2140c4a4103045885040140c0c9c50194850b00e5684010090081c10400b030b100c41d90b1414a07800301d007824421 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 233206025 1250 233204775 233204779
    0xe07060302030702030f1b120903210703051b03040305070e06030307170c0102070b0f070201060602030f030a0b04062103020c121908130306141b0a080718080a0204050105 75
    0x18014065001d5001c0200c03010481c1c5201120b4447c44459112606038803800a051030342d1003010095500f111046010700440d01c4102c080e14244011020300d101882c118040c0c010f00480104410000240603e001d80800002030045102d442c07400c82c4068a0340e40305400c1910350341c4c01803d080102440d00c100083d07105409401031400c100700c1d99154180c981c00350380020800e6a0200e004d8600c22401d6041e20103007030b0801110082800c1114894040c11401c1e90780900650a00c400440d207a4000001c60300341160010207a07103160354003540200244110038050750701c15240c000000307072401c0724040a050135181c001202c21010306440d01a02e014a804600c50260b0450300768a03180e450045840e500c0000c035444403244290152802c92502e00c14180c0c100348040e00c608012050003019401284007501071404442162550346800590529024656082007003c0000e04840340c402c0c10007540040c10b50600700000703a4070485031640000950440f107aa540411050019442d141c040c0c54018481 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 233207275 1250 233206025 233206027
    0xe0a030b060603043f1704030c15020a11070b07020612090111040605030f010f0f0b0706110714070509060d020f030a0204020f09131404120c0b190f0507020c0f061902010e07060302 79
    0x1480686000c3d800001f08003500348088200a07030113110356812544074880708010b0856a4130241d2002070f009032404002c00f80c1910070788001081002901c0c085400d41c0340c00804040c28200715900e0204004402004041c46540701c02f035031000e08042c0070240000d40390907100d0f2130b100d00d0026040380000105a000105504036400104041d400084000c41a0b40c403550203981d460682d81003042c040c00c3c08148010b2000d20026640301800f104d0340f46120102c0a00701a10802c0b90b81c3c400304054880240e030001d60158100c04020014540344101004006018041c1c803024400d90300010202d1300081e0343e003101c09400154400051500c1c2d0119000c4101180c003c00c40c4584001d02c8428401c0b0090005086105c1d0707051151041d070183c85190641503010038180003d01d0068203240b01c05901c8071035440b1450400d1260461000d15002d6103110324004e43c01040c0360160101013000311172004440d290000010080701e10f00c80b00f2180c1c00c5c081030f0815000442c08503100350b4802c3ca00880c40c0d01a10070588 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 233208525 1250 233207275 233207297
    0xf1e080706051f0b07050114010f0e010e0411040b03011806020a0311030c0714030c0106030326090d03050a0b030f0f0c0d0b01050f040b030a030f0e0a030b060603043f 73
    0xb400c0303c19501550701c0e203140c407600d614442c030f0102d00400001e1028080011458000215030081c4403d4000340d4030386651500b066642e6901259210350103407030050030601c0c403c2c0300380c0d418202075100e114500380003000880c51241d140c0c11800e094822001c151211a00000c00d40c0000740c250090341140002c14820341c2c80c43c6001c0f10000c81c10300170b000000f48000e560030825400450100155480124048000c008031070340d0349006050400180d204c2d40300b0202500c101d024060403040d403280705144841c082c0041201c114000c9005140080c42941500e94540c14240d440c3c40030004601e581c1403140c01409003180d03d00303040b440d1581d005400e902c82c0d640b41c0c414200103910310101604407202601d0800700039850b00c00040241002c00700031174062048140c400107050b40214642541c84880d280c44801100324401d1142c00882408044c0980403074030003050342340c140b070401191b00070f00900299900c16501d1070f02d8040d140b840942045034182d841d1074040f200303500007200340b071503ca107041a01d00304d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 233209775 1250 233208525 233208571
    0xa030e160b090904170d0e0d03060602030901141303050a0203010b10051801091a090111010c090303050904021b0d02060c04030308010e0402040e1009140102030907030f1e08070605 79
    0x711500d4015400340c0c844802207010803015098500c0824451022691100c0c90014202c0042c80c030040302c0f030201e101c0d510f23034250f00d41c1c000d2080c6810b03a4075590280d8038080e00711006440c0300c1c500400c0030000103020004140041c41550124028611400142c215015030b40101800d5803c0142e00c02e04c1210742c07a00050385643c101080703803800324001e034000454100da280142c88041d03050380100e05000030070b00071010b00c4420b00010620036000362902541440c40f130320002c0c200e95003a52480089020342c2c03402c1c40828040c2c400341810b9500280701510b0503031010841c0200409807405800c142e030040c00315820300364051240035030007042c05802031300b064510b0324018030058061145800c0060340303401003800c5d9103690b00b00e03003000300c1c2039411180c645c7da6900400d0000d04000d90f02365000405041d43d9400140117008a03401446003070020061542142c40d00b402030312980c801103c407400007054070244100044040c0400328000c0c10000e4031200141000005d482d002441c242c43e100142181070402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 233211025 1250 233209775 233209777
    0x60307021c11061f0e100e040807020405090a02030619090c030803060a120c0b0a26071107081209060409060807050f0f01022a0d1401141b090a03080a030e160b 70
    0x12051020814040e40302c46c0c1c5100f00310907098100c05036012604041000303101c03810f00102041c5100b034400304210364404004a403100c070001002980340e046200441c0500d0400316103500480c592041c00103500d68259124244000c550340308850100c1c01108119861034580d003002c00800e4450403014a007181d6070b4500b40922414080c9408560022403804c0c070b83c0303100f40c02c0d01c000c944500c10480700070f0180680c54606500100e44c0e80001035812005a100c40c440412404115181c000c01450552040c5002007012781140d5442c5420030801c3c807001400250758050b100041042c03c001d08021420031003030107558041c2445950091a4000c80580541d90000f651300412000d06040006031080f120711300340314541c005030590f00005038500c5006205020020b1040c0941c814000c014007003019946240550040313415070101208a540e85400c242d004d0020a01500300900c2c100041d13440b59039103050f98001010b880300081c4d0301d007150400c0c1d480410503941001101204500b180d45440d102c9195 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 233212275 1250 233211025 233211029
    0x50118051906020f0309070513140f041406041410020702010203120a111308150103020d0b040318060201051b090a03030e0d080a0210140f06060307021c11061f 70
    0xd0501226820060040075415100040784c04540540e0340d080081c04155100031500a0520803601d00009640000040c42070090080c0204081c501d1659901880600490010000e403032000b030a000f242e45001c01440310910540c81050301a80031105529242d1030040c10891f03080400c0d104110480150ba00001030b03821400820941c80c803a076a480301c50b04040c2c04c040e5a4410314645c04120300074842d241100345800d42e045641100d411200e508201104a0407e203c0039401183e0058010b002c560a0008643e22602904054044298098030b400b0000c0c16584031000503590340d0b0a1122500000f065440c2c1e0110300c280c158144421070001450428061000405000c404090361070030f6200e42c1e42106032a900410000e45480b0002c0d8080d45410340301c41030a8501707260256407061212070003880c0740100704000d07400d50301d03a8980c018081590b2020704a8000c1d8490414181581a0b40212940c04a85241d950000c40c07015a40c8a0b4617101010300040c0c0d040101d22008880c0041480480c42 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 233213525 1250 233212275 233212303
    0x3020105120601021e01020702010311040b12070e0a0303270303050901110a0507030c03020a0b0a0203190c0507150f0203120a090c181505060304150e0f030d0905011805 74
    0x4034a4440c8801130786060345140d4580000400445035a0304a0810b5003c0c0917200d0007a00c05000b03004002e40408414496800385d0700104509114207019080e181d449036a2207815818080300080d10070001580c00c0c9010f900c1140021580900e01d03d00000b03122000c0c10120744081d88000b02c6040d5613010303100340190441141000300704646440328040030441c0e4404c10b0b40040545804c0c0d6180d0800d49050340c9280070036800f9140c0f101d0001188212102120b004810b0759003c0c500740030065803511500c2000042e03030307000c1011540359400841d0051042100800e501e0308059468ac0c009400542440400040d4405540040c88441d4848003090380503540048401c20000f000d8a15207481550025140c10404014501c0c2030503005c5200b065214961101c81904910102680d6030104070003440211402015289803501064602889400c24108880c00c3d40a03281042c8000c0101403840c0c0100340340340425038031514074809104081c450301ca01d400c0303450407002c820b40c0e90740c54285c1d82c2c11199220030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 233214775 1250 233213525 233213557
    0x509061801090c031b03080f0316050c070b0304020a0e070c030206060a0815091204080f010f021603032f2104080304030807050d050c090a0f0f03020d020d0204020f03160903020105 79
    0x5e040c100b103040144091648005085c0e21046200040c6005400882d00350840b0010385c0a280c3c1e009025009640344010300c1c100920302241441c2c21031111350400780049070480800c4c140810000006940c03d4404d1619680e1100c1c00007080c10f0003480c2860182c41180585034485c800e002e9948082800e10b406005e20401c0450b540359510704170716003a4110342500f0709100119000c0b42c0040c022806900d2003810100070b002402d1a00c03103c41c00c17031003000030f03040c00701740b0181030500024000d410204c1b0f0f80c416a603611104489503003031101c4001d034201145985180000342210a00020014400c122402d0806a0700c2d900c0c00755500c038800d120141c000f609000d0041d000600103846401114001258104140030700d080401100455070080301c031091003240140b0300850041511200d9504032520041180b1402e031030754081c040c804850080076078004100340c2040001d070301c0303034001820302d04c41d10304016550b45060707140180060700410018080060000d41000582e0b8014252560410281040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 233216025 1250 233214775 233214803
    0x4120b060621090c19150210020406020a03030e010513150b0d030c1a1618050a0b04181a060c0f0a030206160e130e100509061801090c03 60
    0x3030803809103200d914080300c0c01c11070740d5015400500070280200220000c44035001c2d1010104400c072213040171007543ca1981c40004000000044102080802260044c8c0e9800b102e00443c05050ba80b19401c0600580c0c40f50311680c04060b0300d03200e242c0c1c07a4ad82150082000c0c1c207003548000d82e0b90f914000058062415208601c0a1941c0c982c0b00f951034010003000603804070024503014140d4dd540c3341d01624440d0540c09400031010031840c50324410703203003404e43e00e43c134015281c41558502016464443d90720504980032401d900d41c21240b0020301109200719444034a802490418550008082d03280c1070305001e646d060200140880c0351003500100c45e116143c01014901030319103200304040590360701c0740c0400c000c141038000c40c00d28090f05a062161400d4051600c0c15514056500002500318800c244c1036a060b6506034011701410f5120b01c103a840c0c400803400d1003820741381c040e1801d13a07050304000e062082c00c3e001c0ca0720700e948117a90340c0300921030b419903910340c0f540101c1c461002401d17405030800c2c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 233217275 1250 233216025 233216029
    0x3110d020105040e0906010510050a08070513090f0e0c0a120f080c15041b0509011a040f080d0f2f0f15010306060f0e1810140412030204120b06 63
    0x43c0c801410750064804824070303160110b41d42c1d419084c4203050180001c4600d0702e81c2d01c0c3c424001c80322a40c0080e220f20001d52502c100880b10b81d03020300301703860780034080b448041203015590003040750003012024041081a4050b44190804011042a61044158500411941d6850601ea10a40b5007141161040075654140755600d40314030311303420311103005280d003802d100610500c00d02d000d03074004c00080d212440e26107424030441c0d4003800b0361b683c0030048200400c08600082c10180102081500d03060400da918540c40c001064142c11841454000080024103603600c00c45071440c2d03118a240140400c52480d2501000f95a203c41090020700301140074821007004003d0040340384951422204404e601801c0d0701142d080078041100c1c5a0f0502500044003440710010341c003a614054000700254661048107207030b42d0041d20700d21021340946000071a078410b00e84a081d04030301488039421254506440c0c4000003a02800c44d03441410710621081c012410340102104040350b1244020080e5159000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 233218525 1250 233217275 233217277
    0x1203020a020a020a09020d0f02030705042102120708011b08010b180310020702090a0212070c0606030b1e130507090c170405151b03221703060f0a03110d020105 70
    0x650004d4500d900004d00c1107640d401082c0401e25034104002804452300c82400703901c1b055400c000001c0b07050009111722020481d82142c414032a03c0307002d541e41c1244e80030454812140c00540c2154200305000c0000307400070b0280780f10b10799070000c402180c0130410780040c21110303041c050b205081801040030450040307070f03101507050500000e044403840c40b00c02410f080654800901240101a000085641800180292410303da0803030000e03001980d0365042210b498000a000b0b4800070380321034000020640d83c81c03817103008043c00f21410744c079902d00c1c0042c0c150842003c0e0144070242c01c07071324040000c598041120802d807103200501050301c44c002003080302c0c07001c0589078412280350404180b0042110000e101d24001580c080e90312401c2e940c4034000d24218103002211500220b040000404582c001005d20584083d443d000c01c10349203268591100031020084403000e00701c400003d0000c6482e2944441c0011001201e0f44000d00e030440e0340d50710003541224000c1d409407040b00180411613011354 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 233219775 1250 233218525 233218543
    0xd0e030114010f0812040b03010515040e040f0b01062f010e0f0a02040c02030f0315270103050c0d05030409020c070b13050906120c0d031103071407121203020a02 71
    0x22984409584801c150785503600c1500c1842c13040e202d1100b04084545142d400e9074115901c07003c5680c02c682c6414140540780001c807a00d5010040b00308008540140c036950002e0040d0301803c407030f881c846400d1a0011400c04184c00030410300030691a11084018180180f0030142a0991154803000b05400458054403043c40c0607809400782c0e20864598050000e22025014000c4505005180c41d824041c3e0702c900c11700c8e180401b000c008000003002d01309040ca044001d9440600006c11402d103003040e4048400494070718681c44440e0800400a11004100d040c08294088501c11041100355a44a60f6031181e4826009115008150752428100900100000342140c440703940d40c401112803852802c8008d8080c0a2040d909480801e40c2c6040980340395015001050040400350201020801101c4521400701c0400c00354140c030002c8000184003600100d8400c40d28068040c0c840502075040a0007504529101c590120310b0602240005110b041644a035080c01a42c070422400c0c00c13070500480c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 233221025 1250 233219775 233219801
    0x140312181c32011a0a0e0f0403030c12051f150c020904050a0503040b030f070c02060904020d06181a0d080a0f090b07030914031b190305060c030103170306030d0e0301 73
    0x80b200c4c2c9800300c0c0c2c80408002e04410200c0d80344404903200d501e120f402020544a8030003d0105000103400a400b170383c460343c038014841c00d0035030301803484031030301e905451040f50460400141c02040c0d018042c0340300c0b240c0000c0c041031510f4044804203c84000c112a4104502a00c144443c0000c1400d004081c0034117038405420078192903540e0313121280c00300c0b130780e01c103692500a20503050b001801242c030615108440c0340c0e00034085071820300a0420407000e9041900c40030030740c6a840900054070340400c001e5402da0050010007086010b072030305500155102007190759002c0c1c502070142000041403602160a111164104640140300350f040440d280000e81d003092041140004510b0207050b0402c0d2000c0403110000645401c0e0162501803540b20300c1800c003480c0e1107050585030380082c0d1401203031b2030034103403c1f100c3e003100e60b1541c0351100383c608041500c40c132007a030400100500c14020b46040c0200e000303a001101341e181d0709040700400d54650b80d014100c0100301800981021a0707030203401001a014003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 233222275 1250 233221025 233221031
    0xc080c0715020f0609062d0108070f08010209060d021b011509110703090911070f11040b0d05030301050108041a0f180a080301140312181c3201 63
    0x4900101810507501d00c1c150000d8030031045400c070240c0d000103150b846405101d001e46201d03120040350a842d001d181c0c02c0600c0c40300c0c0d0503140302074034040801144d0003405000001c1c43c90034501001c07402100d805800450035a4010400440a41c07200400c8070700c44030b514100165103403001d6440003071159030003240d04815400c02c054036000d48404c140140581e111000304012440c0340d80b540044502ca0004024040380c14044200160304255011150580c100c02c2040c1c6000c100d95102c1c00300481e0104125090010800e00550f50300b804e21404c25401c0042c0d40c0e48411512544406c2d50741d0005204450400440200043c10000d26100c3c06410400010041c60381c2e061441c0301441410080311840e00d01140c007521f41c413060300005106400d15810160036440d5900b021001c1040e200200c55554240c825040440038041c0c0040052900254500340c410280c20000c040001c80d40e0700050030300d100503c4003a5a00410040038142d4503565580d09450691198062f1600c20241003294140035946 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 233223525 1250 233222275 233222279
    0x9011409011103070f06140f06010c03180608180c031b010e0d0b0402090a050c070b040c0e0403050c010509150a020a030e030a021e0d0e15070b070509040c0e030d0c080c07 75
    0x2501c0740f105e06005c0c07160000340f1507070880440450483c14200c6020305840c680101180b101e50040754000c504501906e40122403001418541e03214031a607520020010304490100808002c00c1140d40c2a8880c0e01d002401103030050f03900281d600c0041d02201400050082e14928040e8041c40c8506180c20380609614030006072400c085001d02e90441d401da014104c0c0000160b81c07404607205a500c030b40500010719003040f100351200c080301310008000b00d5140c0080c020114480f12141c0003a8800d5201703a4a0350703032301c00f041d0000303030f09641c0041d205070625408010b074140c451101d42001a800410248010f841d40d81c10803048011f007505801501350b0f400b0000b40c1e40081540451a51310285088510060070304013001202e58415408141c0d100064100c422503e0b245001092490008505001a820203000362600310350040103441c690003040001034040140c0c2000e025800c15032465080c00d00d0319a00002c042501c43c04042d012104121100003118104030000f820340d500803000c00c1c211500c640d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 233224775 1250 233223525 233223533
    0x50918101406090403080c0705010b03030c010b030d0903020916052209200f071a07020a031205040515070c050a08030a060f1d10080109051e030901140901110307 71
    0x1140108a03007036100420009842030805850044c041d540c16903841c0030642d100310000080d41c1001c40212181d54031560208481d41e0700704094008072101d5070000440f00d22110801d407414038a66030100600c03d1400007000582d5407810b40d60b80c404c80d008600c1580c181c0d6040d04a8843c45940c00d15641d0654100400d89000700d0442d481d41980c1c0040410090603101010814226410003130340da2000748100b24030000b424440c005001a02d11440301406103540144624031078290450302400181d010902d02010300d0750140715007030f003100004130070031590500e40c403680c3d1210302004540021900060100380c0051080f4040e0304001c2e0454299211800d0368030f80f90041c1d61040e6595a0942e04000c4085210a4080e481d81c080b03810f04094608860130301a0984c80810008010004103c6440b00000301d128003805510320f40ca10070f8010b4188041812504d0001e041881e40c0341c030095100f1f00000344541d802501c0030302c0340000000c0842e00c03a58050300403203c5e0203901c1d01100e154040419600200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 233226025 1250 233224775 233224781
    0x1051e030723070c121b0306290108070c0510020c01050a0f0606090909030e04060306050f070302031005062a07080c010f0c0b1302060408101505090105091810 70
    0x544030069a244421001607007a55041c00b40034405421340c0c0c00c003030b0100312801010356042c074842d01c11245401ea4020840c0f50b00e0081140341e1060315031b640c840151002210808122008a40c0a010300711100c4d4000d80000346030042c028159024800d00310550f5051160401c401c2400041009040d56210610400e481c042c003410359900d1809810410420070146246c01290280c1d0840d0f43c0b210182403412088801418a000d41a414858165160425506c0d58081c200145000d0500492582000d4020700e826003401041c1e50101841403040c03058110070101c070030b011075600710b80d050340700c01c1e0144160407500014020700c1003d501168100d15000d001049290032134943c0c1c4180d0300781b801c035078006540c0c0d0f842c0c024240000030300909188000400c000400e6030070022a2a00f004071485a50108000c2e5005802c042140d0780456145543c010081c0109030303840130303103072400402c95242074003140410300107003c4c9911918060000035802100c000f00050b001b00c6041c22510080d100c0c040321402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 233227275 1250 233226025 233226047
    0x7030203011103160810030f08070209130c12050f2e02070c05042a050306130e1905030c060106050703110607020a2006040906090506090f0601051e0307 67
    0x2075080185082c0d4208800003520b2084010040c0c0c0300719110a1402154041c0008202c00509603118002201007003800f240780306018450200c03140d84e40340c02d004101c807a003001480b00140d1078000d480000007030304035030304c00080703c00c009201d148081c2685004d074108040f603002450b5600c94000c203481d40c031924050510b9103040c84c062414013a08903031001e0069204852011300543c200003000c001c03a0806174006440c1c3c4402c0d00c03181044688181c00f49614101c401c4005c00000c901109100720351a00b511510b5202c84c65480420420b20b030103242984030300a0000340300b00c82d68120103800038098107001301d8111803520b90075140c1d651784070b4502404a4000403425000122501c0440818520003d0007a0260790380d41c0040510800d84d40e2901c1039104004482082c010740340024541d203440e07210142018100100c4049100350a1110030000c0f80c0300200b032980701d80d0160013401044640300a80940000d82860115500c2c5101c105d00a821198111844020f190000070052102c1c1d06c81030102c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 233228525 1250 233227275 233227279
    0x60b220f0605090a05010623180a08061e0106110a060b04020f030a06030b2412120a020f0d0206240307240806011d19050a03120e01170c1605010509070302 68
    0x1000c180e5040100448250318440485008c404201c80642d203d401c68101e184008000c200c0e0042544804600f070400b0020380d00c400e840247c0164031101404100102d90141900d0700e0a03410004a100c400d0303039545216100a8003840d0355243d1101252510380440f48030f01004045203989050981c5200020005840240c86404104001c02d004491403c0c0d4400050f440b030300003000c902140e504002d840c140c0052001c40d14410f50710001820b256920140105040640140800c40045a409030509110f10403160071900030404011aa01d51400012510b084001521001d00303a1000480c1c0780c6103036600040c0251542e5601c00d00c1981281ca10602008001c0d43c4030611070301d4080c015540701c004000030b000340c0902a0700c100c006060100078112420094041010340320303904c50214901030f8041e0010b03105803485007034000595801001e03582c9030980030b20b403400d13501051205a00c0c0300a0b018001d0484c002002540c0214000100d440840c1d660704040204410304110b0b601c1c1e42d40e400203101c224 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 233229775 1250 233228525 233228537
    0x1b060403080a0f020d050715020a0c0b10030c050303130608073b030705011d01051b0a0c0b0306090a09061b031a09011d040f0c030b04060b220f0605090a050106 70
    0x1760074440c030103a8003115401000d001c10b500301d14001c2c1021703400c0031001c0300401400c100e41c040030a130300c4828a03000700e070040344d00212641141007080d5a40f00c290043c6009a00030018640706000310020402292031034900320b0790b15160b80100b00c49211151146e09002d26200700200314019230b030301c5002d0340b580d212003040200c041c01005054845e4203d01c119408034203042d1110b042041080d40d5800007a80514015160a01d0a0b0544000103204180c01507141e100f0760034201001084a0b800c405404000100da046160800c00209003010081211089070380f56950341007042400c0c2c10041c004005400c0704c00f50311141c404000d0081c00c00d036180c01c9030400c1d82d1011254a0600c801520706888030399480e0361000781c607440b170f000e038012018200700c558641401d802c10104040c2054a80030354420007052241d4185410044195000507007001d00ca81b412260030517080039031150615050300b0400002c120354655900500c002d181d01d510454022881c10108905c07007040b54803880c160744a688400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 233231025 1250 233229775 233229793
    0x21031909061701090c0302251407080c0f0109031a10060e09041e05030a030905010c09060f08040c05032d0604020a030f0602190c14030307021b060403080a0f02 70
    0x8480074a0700125860601d40642e0040c00005825000441140b0300760401500d0070b80c2c881448644181d105094036841951860310108000c0061b000400e6862554000c02e11681804409505e07800c4054007640710781c1090b8020b800301d90007111443c00868109040031300e2616804822130820b14100c1c1c0c41040c03c8154007001c80d10701c4c082ca00c030035101d80380a0185101642d440c1d582c844158204500c26040c900c0d45c1050b040010000c000510001100742e40104405056150490070741d180b07008460144003154005110046c3e10124041a910540c0380c00b04854655040864264013036405c060b03050300445844044059007039189450059003c2c401014414007100c038a61529001c0d14001c0d407010408a04002141c04095540007240c001c00006240c01c0d200000c5203105986004c4001c0814080d900c50b50071300000c03d004050100720382000d5450751400500003910349612a2311104c024403c0e040915150700c40d50305035809154400a05542c0d1440200003410803a40201c0c242c005209841034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 233232275 1250 233231025 233231027
    0x180c09151305070e06030a020904020307091e06050702011b0c081509060105012c06040306050f10030803060402070606080708030c0f0f070509280e2a2103190906 71
    0x42c00d4410f201c03541e6488a415600e03002c000b00356001a0904414903000d100e0454560b4032072004502030001038962464091900820504004c0040302c1c2e4a0300f11015034041040b16004401c684110341d0918000d0034040000c41162102032450401500c031f50903064001c25012000500520161036147c0013560036030350080380aa646e00309000d150b0000d00c20b004000d28205401c4000740b954221151400e5a51180f0300c04a03070070350003943c0140c91094840d002e2006181c070000905030000355800015400c2c90075622500f001c1e01c00502050300850303002034a2801d01001d0750001010b00444002e0300c0e40c82c1e235607404142e07aa40150103140c000d4010030511113494140000c150855000041c0034010203481e01041100140b0300605d00001d07030300d030b1844c402d01048840e00030001a4448020000b0001c80c07445181c0d15246054001400020704180d0184090707440e1440c0c0001a02c048070b00c00c05001d80810348012903070640c1002c0c0610301c000300314a400d0231000c001840c0086095542e4462565503840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 233233525 1250 233232275 233232281
    0x1206020717041802190c23100b04020a080606031902040b03090f16180e0102030403110c012f01090b0f1506040302010503040b07020118050102031009050f180c091513 73
    0x20600c400301c410f17814110800e070150000c0b0340e18a014410040d90300c9008075641c0c0049022500100766a0062003186500d01200e02c5101001201507030210300f421040000a055450080d1840c2d01c24440840018813004441755042c216069501003903464651b20508910150001e42d1020424010503c01170011900001c817407421040c001c54030002145400e041421421b6541120071142e41c4910303242c50b000100740000c41c0030b40d1182e520350200c09240340b80b450500d0607010420781040b405110912000035200e50108070145034000c25240c010440d4015401800b1080c001001000300d0307000c100d64140c0d405001c1e807159008810700c440c05420701d0104151403180d0700000707010480c02d0002c90b0201c0c48501a075075010f00d15000005001c08441a01a1000201001120f1a0f9000820000f0101c50026464028180540c051085003000c4400b004d41e103100a242c1c1c0d190100320703807403000d045004001d542052000502104602d0401c4440403000c8802185494040e106c4140002d02d030b005644 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 233234775 1250 233233525 233233537
    0xb04121106090d150204050409051e010e071a0c060403090305010506030102120f0612060a02130509010b04030f060b09010b04170604030207050d0c0305030a1e020111041206020717041802 82
    0x1c10b000d006020641d04c00f200c941070751251582c4d5640c00d00c004036072a00ca603c51415900e009400400c40441546184800130080721507070441a4104001050650000608a030a5030203028214000a1030441d0445d014001c115886429125841c1803006054022800c0c0050703c1c0198000d02c050b07950141818207038070600c259003000d1078100f00001d203050a1119026000780000b4041c3d21a410322200c803516258013980c00032a8036900083c02008030640191100c01003105a42141c1658074002c0544024087c1d84006003010340c0e040c1d1981c1c20071071103a100e4a01141c00800e0040c1e5561988000391140d04140100002c0041091500c0d00005000a0051140d139055000381211400d04084c03150040c0392a00444014010010100000e541480644008021a038682c54250504040032144028000100e03080da42b4006820220140c40350803101550030390328510612802d546480c200911520b44d000d005400c0b006000b100310700c0f10100400403160b5541150b13540c4143c01c404030080784118 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 233236025 1250 233234775 233234779
    0x10501110616081801060b09130e250e040c06030b01171b040305010e061e070212090d08070b0615040503060103020d05240603070b03070e13060b0412110609 69
    0x41c003845458400c1d811594010301c4c00f00c081420424000780742e0b00f952211740203611903050119134218a802c0415030030707840c0021440180100092300480075100d0b90710100304411703011100d4000211400c984000c42c003d0042d0041100149400d060144000d070303a900a0000280c24040103140a40c4504c206c00022585590318841070b44401c4c2038450980382d02031410780754490070b00000020031021b116400315400f40784040c01042c50100c4015443d2095410207100085d00c0c2c0050100181d0300080040b10540b1101e52503079141c44140002d400d08072100001880b16100040310010000041030a5001e41c900765852440c060303821005400c0c60081c3d0003199019441b02c001040503203004105403040900450540c2c000c3c6100e0b0048544034058800b424409a807460140122401c04000b80c0001b000030703106060960605400003405280c00d11b501030300c56903010400c1200c904043e807144008041c80e107100c0c0e40d40e070799a40c0c0f41c01d010b558941e010f50740f8030401074206980b4208801240c10f11040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 233237275 1250 233236025 233236051
    0x30c031103070c03140a17060913030309320601060809150a0207210e0409020a0501080405150108010f0e0c030601031e17030906090703033002120105011106 69
    0x15028112241c0303200310030680800441704c40c103c10410f800001801028203943c1c5103c290840b0094070840e0f40b0b00034180a0240c0d926804015030754251002d001c0034650315150201d406c13590340c10320130311840c0c505c02d0300442c075030311448ac1d18581e41c4080150120404c0715016909260399414060f148010200c4141e006ca820000141d042d01780b0881100798428400400142884003946407003c00101c030804d480030703400d994081c825480ea080208081c8010003100d00b03001903c01507021600e042070314400c01d03043c00507120101e401c000d42800b141059070045000500c90350f0703440c2e9802d4060503e500761a1006898813403a52034800010600700d04003040500240942e0b480c541d03801000cbc1c1010042c4048440c80500c028001a820f8000703007006880384a840340e12810b0410002c1d0401c0d8000d068094a0351150000b0800250080c1c4a100003807000c50008844c40044600c2c813040b10300001c81107408a06c0021300030300700d202500240b4141c1e1002e0380c07200304695550740455980c00081e00c14292a0702 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 233238525 1250 233237275 233237281
    0x806030606060a120c231c05040206070204050906010f05030a08042d0f150c0f0b06040b030a060c0915091503020d02030901090b06030109080316031d0607030c031103 73
    0x81c020010b1903003416515100c050b1800c40820002180c1c4002181c0c0000f81c0e4040360031140d401446c0c0254080c3c00b40103102890952044000e40001480c0d084a0080985600c006010365a0743e006030b800f45900a00b01340010f2404401054035007009000e15580700180880104003401d001070940035283d8030420041c51309083c52991400d58491980c0a440c01c198003000381040a110a1840b005000c01500d400d407550420040b02a00750071340c1140001c1102184454001c5415443c25051107500122203880e1511000049006401030302c81c826094031410701610104140340d48650000303940c5940b40503400d1f44407414581c1808103c0d00c081d00041502000380700b00c850a0701d080d401003000d0306005150a0700040c080f000d036001226880c407243d550f00c941c901401144070503960301400460003086108140e41e10900309002c00f42422180030004030400362040d009a1101c1541c4012070a0307003011f0f02403002c42c296148400c446074000a401c0072180e50440c0d0003801380d90581c429120b4a10b0440e5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 233239775 1250 233238525 233238529
    0x61a070204050a0b0d0b1902030408120903090a0f03060b03061905191a01140a0903060b0406030f050718090b0105060306010201060b0a020304030c051e06030901060302100f08070806030606 83
    0x4007034610b10100342e407000789103c4c1c0d5980f84000c1ca0250b108105c404180d14084200c1444070804488640c9018010000c00001815240484403a030b020600900e10b42c0c0c440400c00c619501907109120342245402101160f40b40d040b81c44c000883e4407404c410f02c07045440303000303054503143c0a49607541c0f22030141241808111140d04034039400441420104608070b100e03200e84041d80c2e03000924142440f40c000d0064410b59000f000c801c1c3e008240741c6584e140c1004900028078010b0240300180c80280e5603079081c911942c0e65081403008603001441c007402c48c650b5040103500d80710944602d156480c0700d4003500e14010028080d142210303030800c0c42080b0303503840c1005104603940000c007100c2c1155070703480b408203c3e080400060620012558019a00e89043d85891885086940c05c41441002c10089140300c2c0084101c844e1b400e08810341c0e90079146e444001d9410301401c81034100030340c001081c030720401c18142d1003000840110f007241d44041064031001d0003550807403400d8070303c1500740c3c11100006001e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 233241025 1250 233239775 233239781
    0x507020909010b09190c141c0209030a0819030b0603010b0705030909010e01060e030f03040b0901050409020a030f0516020d03020a02070e090d020d051305010c020103020c030a090306061a070204 85
    0x1241500c1c001148580341a400110545412036426514512240ca0541e003211240b00380581014641880d511440c15400e00516501030b150a2075a0210700d00300070001c0159680517600745c0c40000d4101c403819070b907514103104650002c00000036035000b8240500381c441d109000e10105148003920361032942e420505410340c103510001c000c5c0c40c1e81c80100000e00c41a1102c80e50345000f0815495000f00650412500404616260381d80c1403195005021101c0d41c92808004c0300e04440c0c0408540384c1d14100f080042c5d81a0080c0e41c03101240500c0410401183c3c0c2c0c064000d441c8400c0049020421980c45155014110b0924048180140e12010720340510600990081a80c082540122201076a56011440e1040d00449444800760001c2d110305107101c0e0104002c0042c0482c3d81001c9050440080340d85000020500c512410070090009480540e4040c0e030458584615201c196507407034a00f40c0000d0000303a460720084840750300c0c00c40d00007060641d82c0351060128a00702d400c9803508009800b00005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 233242275 1250 233241025 233241031
    0x10b0a080c040321091d15030c0d080c01050106110c1e0d0c081207021f09090203160e060c120c0705090103051e06060604180b03030c0708160605070209 67
    0xe016007080040301003501042c09004d0810701514030502c80c204c070a001804007070180c0c4488a071b22a0302d07900071064240385072142e60100346450480d10684250700001e2a0501a00d40150006068604003040c402100010038402131504003c0c49640d07070b9400101e45103450329036080d50b2500300c0c00b40e03503820b45003038045c000b2060b03040182c6200110740000014000e50151200f107856242d04081000f41d94000d12650f464441d0800c929401c090301b80e00828100b2083c4805100c01160165032409124018840d050103441d503408115101d10306400440c070444044102c1501103118040041c106141503c1100c81042d042e002070804142d0495111015030005c0801e04601e026000e03012071036466185031071f070085000f44001d00540400300b200d4202004114059030b0380e078216004210b460f0300d03204201d03411101c003015102542051b4400e440010465501c00591502000507005441080018000b0903242d406059420320200b4540c284813001c201d109010116100b07100100240c5130503401e442d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 233243525 1250 233242275 233242291
    0x708130b0612070617060a0f05010c2d030e1207050d05070e0405030715051b09030a17030105130204050d14031309021c0c080f10050a0306050108010b09010b0a08 71
    0x11808112901d10b900b0300352a03800600009180c4503650010041e1800425045001550032110701801c041c5214103401441c06000d0602c0074200c040c504020b00410400c4404051781c1c0000c105550080c6a0710110317407403d8040e4000381c20707174080b0708040ca003030920a070a0f815881e009011152500080c0148000b08880569050084a03000511400c0c001c0f00070340b150b48940c020750baa6050394541921403e8004c80142c0b500c0385800100300070a1050311101c00f00c108615100d0342c4403120040003a01c1c01288123001072541852078941e240b5481e00300003450688034225050507092001c0080001240038a10070540d110600d00000c41c08510300e807800c1400f02170040d080d01c0c681800c0b103c0030310182e030603071740401c0c1f841d0b42c00a40031000104810710200403030702c0d050302448001c010080c0108104009801c1e10044c048030000b01c0c107580d500004201c000c000c0030344061071441d81c90501d100203003802d1060391415400d09000f00356900d00110001c0c169440e41b44910704004181c0411501d05800600140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 233244775 1250 233243525 233243539
    0x906070f05070501141006050406020d0327060b040b03010b031c032403050c0f0112380306131a0c0904060b190503150909010204050603040c030b0708130b06 69
    0x100c0420802e00a407001716101042c68138650400701c0b0303280035146d8658454402c04c0420f11051140e80c0e404900c40100000518000c40c94010485040403000051100300c0240340680c900f58007001456000412120381c00c8030104041080c1a00f403600b0b8849003409140d06402c84003400c11001446003e80036200c06503d00010007600010703100d180c10301c40310900c207000444207400704104001000348031180003041c1c3e0107881c01c8645c000040d040f100000b500710074140d01d03000100710804103000a5000c1204110000020082d8141d1030642c8190303c10794075019004a50020b510328110348014030840b503000004005200280c60000c1880d50054034131100c0344001c01190600381d40b203001d480043d0020707001c055620003280e1000c401c00203141400000f840428402c003c2e40c2c1c0390080c62840c00701c100750385e01e005541d1803407070003402403080d80c010a0b844903012042c042400418048a41500e11078000b0b400b007a100da02003540d99110803640f02c0440062070142c0310024500391030f01a0442000f61640e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 233246025 1250 233244775 233244787
    0x60d060f02120403020708101109040203060d0507090b04051e1f0305070e06040e0705091506070b2503020f03070c06090b0103140c0a0302030c091317070303140906070f05 75
    0x2c440340b401c0594090700140d0001c40c041c0103032141071220f00300003628150300300185d0090800d41110fa00540a0080c4200e6020002a01d079448603103100c000c490f802800d40745103944456140b0010701400d03100da8011450b10000600004110ba021a00612401e1610025036034609080300107105041c01e078072801c5406d440000000d0700410000006e0655150280b003580b80810a0100311001d6084050180d880030004000545682a815401100301206640a01c42100104d0007920076940d00420101401c010031100d090b030307106524001e040300007061840d80c5d1811400c400360700540c40d5170400b02070100003040070b035400780c1d03c038a0304180310340d0000c5881da000d82c031220780c0c0b4142680150b401c80701070590040c1d202024096400100b0040b1145900507040d500032079540c0740710521040c01804440c011840304071400300051304c880d41c4010910016070304e0b0f00400800ea005280c04074046401c04081900d002603021a85128014040003800300380c0d9141e504840700f170144030082d800d100c010450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 233247275 1250 233246025 233246047
    0x515040b0d060317120f070309080f07050c1009050d0f060c120509010e12030c040503070f06030c0804020915060d090b0105100906080a0c050d0c2105060d060f02 71
    0x20307001900312440700003001c03459400c0c0907042c8800100ba40d400c400040041402d444240318543d500143d03041902c071615514135905170700074a48100003410000707000c10155148050300004098040c0b14a06903031151107a6000d00070702d00344408040002c05c0340a80107102c50f06101100706003190190703c5d0b0043d11074040d21498112041035204500040000d02c56244500c018080c454002c05c50000030004844200c90054880e00170b010700303103134100e000000320f40340b076107800305603409040010180c4049680e1aa100420b1140074810140420f0034405003010b101c1c0901d001c584101d030090000c0b81e040e60ba05040c00368904080d80c20603401035080c000c81145035240d1044400051107150450070702c0d41042c04002c0300042d80b400c12820042c0081c0140b00ca103500a07040743e008882000086039945c02c1e920142c51a00a005c052140a45405040862142c1c0b092191600003200301000d10621442c503901d90550314111074080e00060701c17a000d007000420783c2d88140300f4030406110050900c1030200c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 233248525 1250 233247275 233247277
    0x50703020a0b0103060b010e060405030706051c05190509011b110109060c1808070b0702062d04140406050a0611070e0a0504050d030b01020a2414090d02070b040515040b 74
    0x644c0d00686d034407510119542c21408016075141d045454a04152030800081d80e101c03141c0c000d0f02c04210f408a8030f1071010001e52210a8180201102803004e0320702818801c0310a103404c0b080e0031403142400d0200702c00c10410710602c046d520404906d07813007140440700e0541c0c52103001d215090f03941d90b1303034035103540865405e20810002c1900350303803100300b4403107003031020b04011246410800d496040060200072007050082124100c95054941c65120340149403045084059032000e2150b07110a44104110070758490014801d0b10751295050b400c0c4071200061004071030860003201d400a50307a0b48140714043c01008074080f9940781804030b4840c1070700e442c20880b0382a002d807903d004640d2901d0600041005c00d04c808040701e913241ca01000380a0300752000030b58520310148050152040402d000313800400820410310354042a05050001e07041703440744003600d08030403220381249010769030110368000d04c0850b03e1011208bc0c811250708050034503040083d4940c030344080150b5000100f20000380d2854402c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 233249775 1250 233248525 233248529
    0x1806010501140c010c030c021006080c01111908091c03020601090203180f030d06120305041809060203090c0307060906050706021b100903020115030210080403031508071401031b050703020a0b01 85
    0x146e40440d103903999a0003e4503101c045441141010f052034010b1154000020b02c60030b50590902e024110691299a41800c01d90007a40d030f0104616001c022000b0700c218040148089801a100b58a40b0644c803a00303105189001d4400400580040b401000490b120307401079a0841c000200d41110383c1064a4160310341002240040015000802c0a081c1d90980303104a0005124503140300300015102d83c0c0082c41c03482180280952500442041d080000041c0d0120300394642c00f0000310350300d080285000350386140c10900c2a1092050b1000491240d101e8401d01c003c403085610351350f017084040e03502d610103500a1000d407000750342244900381c801c3d0810003911440c50090100000d00d0b10326410000e00307460b515007062505481e10305080006031070f15076001c2040c0c1014a4045001c0c0c42d5407800700c015168598a0040c0400d03005800700e8440d0000c0b46107000c460240c00e00c101400601c00064084c2d4481303248008240070740d099082004c40c0140003d15040f8400e01c141c2d410714845642e070420225080e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 233251025 1250 233249775 233249777
    0x1b0c051809010c050c030d090c0b12040b010501091a0c0c030304150801050a050d03030507020703200f100f110a05060103031709120306010c0c05060403080702091806010501140c010c 80
    0x21000e01855240a1181160031107262030400e00e0b02015405d440e03902c1c401c0000040301140c0d00c4201702d0078007520303103040005007440e0020550f0312019900048141481500c007a502d41d4614000022079602075000c0004580e03d101c0380c00203000a01e016500305420504482145000e06091542c10390341c140010009410000c2c10007484801031000100f203120305810540c01541c8920044c0031641d01c141000240692515010511350f0724510b04900b07002c2c0a80c80207010218181006a070360074002c1c050110000c050790407207804400b100c10001d041002c000550040b5403000c10148000d072141411010442d82c890403144000c03042c0c0d840601c0c1400c243d0050300018070941e001441e43d540c0e4800d0030b40150115004211b1701d0211402c031103442c03001811060501902d00441403c203c40c14a6540040100601454446541e810700d10a140e0004108901c9150007100007445080c5070100c0919046240c4010030b1540e090900642d2001c840c01c0038040c09200500038032403070407001d0017002408211 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 233252275 1250 233251025 233251069
    0xc041a04021b2b0c0302030714011409030d0c03111801020a0b0a0f0c080412031805010f0603020301230c0304020402070203011503050606060c060c1b030703020615040b011b0c05 78
    0x10700d50000040d010005a03004c016813000d2110219500005a031300d0140c0103102580011180180c4a00403d070a42902e0031404001e807c01c04140004005481000032115040c411405010320840c1107890500161000300b0080c0140b0441e660700e2400d5900f152410700441c0d04050309900d50000800080b101c00144e140c03203440c1105044041c2c080c80251a10f5428455514102640d0b2608106001c10f501c10405646110484c01113120421031030446400800030000140d01c00b180e04003808942c00709034007d60820206c200003100c00f031150031459868500e00c01d040d80354035402c10103560000c2e009a900603020301055016913000c0c406d400d511190800007101c59071030741c5000750130f02d20001e1400340704450501002084c4d201c0890300c29800002c40c0c811958800d04a103840d4404108111403070840d103c0410f81404154001410346d0090306185205004145a4010001591050180103000034090740d03030800c034214084040320340d0a10407a03454001c540c0314808680c0091801d1980104060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 233253525 1250 233252275 233252323
    0x906070f060b011106180118080c0d1806030e01061a191407030305040c080d020312010803090a050108070c0203120901080c0406020705150408070e0103050c041a04021b 74
    0x14410b01c49503074801e00f072041d011544402c9450712648000c0404000006110301c0300d00c041000c5d41716040028184031503500c9a040c41c201850306070004407a55190b8820b80f04d0440e5400c4c000c610320380700c0400058480071603509001049000c1d044c41e41a4800642d02c440e0007058102c0140d050841580d4802605919001071140b00b030300301206102140f0500090b0040300c484416010111421a9018200404d090320355142c111800000c680c010595030003500c4002c004264080018103105100706041e49107179803240c8602e0b03100e00c03507082c1460740b00c100c2e01d00c01c12140d4000c4c02d0325584a142410824125001030f004681441038008194042c40400151041e03e5a000300d880e80d001907803c405542050300b04600a5600c1040d4001c0d14880c3c0003201035205441c552504580152044c201901d110943d9121800804882030104481c43c1c0140e5450340200c1c20988281908240e5109070b840b054281001800002d600400e1344144c500c000d00e200103010503040194542c00e24100380101c200f12 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 233254775 1250 233253525 233253533
    0x80c03120420040902061e0d09030e0102070611100b01030f0609020405041404050604060e0316110f0303190e0303090d0f0201090515090105090f03160e070f090b090301020906070f 79
    0xa07410000c1d10f100720300d083c660b03a000d6200c41080d14088407174400006c000121072140b0000d00d02865165528a41c02d281c080c2c01090391106001d04001c0081e02180d00c0180c0314581a13403a011550010500c80e40800031244551940340c10081040300103040026020310440499810f56080d504a4510303590000f03001c01c07030f40c1014030a01e040c01d202180c42c0d403074030304141d943c0d0b68561001030005030046803210f901101d400c50510803921544404c1c168246481e415150172480d12005004c41342c480c2c00881084201400c01200300c80c80220711994400181150302002e94120000c501c050b60140f00521800e2480d4580151540f110390142c060078610a41d148001400850913421003402482495000c0c0e05500c6000c0039154011000d00300140c0741c041240220300340b4801a540326500d40714001d0b0300c0c80c42d0f80e6004c48034802c1d60040c08900e042603403400d00a0311103030587d141a100140c01d114003040a68548000303480c01c0b690003000545013054110010303040e13800a040a850010701c900c0c28100300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 233256025 1250 233254775 233254823
    0x90513051602030a020c100e120c04050c0c0a06051f080601050415060f0e1503010e0406050610021b0315071101140c07030e030c060c030a030b1c080c031204 69
    0x1403007081c40154600408100c009469950084a29001e0400300e80c0304d0991030301400203810542c101529090380d1a90031500b2039551025847d030315000354a0000400c00042c11f80e8120b445181001c002820380c0c0085541e49002820700405a000300d81d0001140c5007881b404000080050017020002c141d20350424041104548492072150b42c1c1040d80071042000d1034020040d6524025a800c0429006e580000072541003e105400310f00600070010011845074002e42c1c1c51401f85000740803c00c407985e102c005008160f11000c0e00d150259000c0003130030804183d40d01003c2115000030702034420700d000045946c04401070135245040440c0303c450105180940910400741c401007050382c4280c1d00d0400c03110703215140c031640ca80034080041c5040c9000c3d26407000c000303240242c840940400e9035020080d00c0315403244c00c250810800642070114503040d44c90500011042940c2000c038015400d0030300d95503903031581d00072030103009103000910150b42103024004a41e803145000700c005085540c000c0e4003082d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 233257275 1250 233256025 233256061
    0x305090109081920100e0d080f1b0a090303230306040b04110310060f03050411041a090702010f060909081603180e010f081504020f03011e02090a15050706020a09051305 74
    0x200d64015030740c00007ca81e000503030541250001d41c44034600d44400f08490300350201601b107c082039000180c8109495481150301c821680650b0b199071450b04030b100d401c204044444d5600e4180c01044c0041900d0f8900b5600100300a00000c100180401007820f070010703141c01c00c4a8503031004601080421150350007480c941c8820744581303020095486c10341d60f00f0058030f10212400f8000c0745d413000b40d03003a42c3c0401c07404100b5101000f400e50342a850401d4009010f041c01d14400e10881e130030b185000410100900490902c00e85c800305490902e5503610388040d00c81c2c0b1400c0140c0c10040c114a04201c1c003504004410003500c1ca141e0ba01500b503051117400282d92126a00513640366001c140101e1858003141110f6412540c1191042d003c2c0113240c00103809440002a00c10100d15102c510760103020450b4010000f055003a40e0460401d076403403107800803003000000716a020803810441503000410340e034000c000700e05090a004640b1511800410710510000d02540c5040f95108240201e01c5050074070711f41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 233258525 1250 233257275 233257301
    0xc0909030a09030b040804080a0b01091a0a090c0e0a03062a0e010c020a080f031911070306020f0d0914011a100c06060504090c06030509010908192010 66
    0x101c0e00c100c07004020080c032141c0c40041c00490001c80403400700211401100d004192400844828044504205107081002e102e420301c607610b8000d4209070300080c01881c5540781d10040c9580245403a14101034080e08007640b1680c20002100f48664950741c408001e034000d50301035800002c640700d21002100c1020180044441503100800400007960343c415880c000f481420700c0d086044136100d10100c1c4902085410510300c40c019065580406407002020b00b03000401040300c40804009a041542c00140503c001c0d22140c03c410800e01c041401034008010725410160840c1c0f80c4200129080100c0e25522700c00c4600c0b201d480c3da407601040003401804422070140701d00301d10203207810780010540701001c04030b2428842d0005819051141d070707900880007041c0142c420700004245143c148103044450003003c010900d00350101d403032050140305003014154040c0c2414a807640c3d81a202c0850b01e03d010703400c1c007007040585800505403034111604c0000600d01004042c90150074480000303a40306a01c07044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 233259775 1250 233258525 233258527
    0x2706061713020a290406020d0e1f080705040305030304150b0f010203030a0906020c070b07020a0902040f060c1104150f0603020702030309040c11030a1205010501020307020f1003021b0c090903 84
    0x740260f9901c0c1c08500c201d03400d4183e81c0c82e41051400e400c49013480001c290340d100050120300016440d4012890f141c3c0c1e9422541c0c0e112820301e4403400c011414802c1070a400044081403044034416000314121500003216090550805940741e50b084c0ca9a40100c0d0308035040001444c8031202e1328034601908440c4201143c06540450800000039500d0100504081c0480d0315102c180062107a554101c0310850718050030380300710369200c401240c1a40e015060807030081100c98800120100a84280d07410382e4144141d2084582c50610211150002d442040e6100c4109140c0c90b0034560b41d1341708107011515140010b000040c506141c0d6034085a6aa00c05814940104000c50050350040f0840d10603880c01c40f000120b0300314844e030455046007000c2c60502144400584000c92541040b00c94091500001d0240032a81e215001280c4a0280c2400290090000c0c26402070518140d0701890402d2410700d8010b00b01915008850041d9101240d69903079500403111444840c100103404c00c0d0300c00b540b40025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 233261025 1250 233259775 233259811
    0x20a1e06090801092d0c080c01021207120e042405010908070303170c040b0d090b130503070b09120a03060801060906060804080705012309071502030427060617 70
    0x3605a02640d07400400b950940c11500102c0c2d11040d1103011005504440340700310310354841142548c0c40040d04e04840c0035100c0d444641000400841c121070306641d01c0114122645800702c4250b0300440c08440c8640d0050325100801c0d2040e00c0782040850707500400c3c860185251608001400c84c07001e0b6003204443e070300446030500220760081e000c0f400c001e5280100c1074203580c42c01540307095801150071500c40094006007680c6020340a03005107110a0180083c40780b642c45a9041c41c00c20403c905004045400074824031020403240b00d40154082d80c0c8009031542e10b032400e2444030300ca50151412501080d81c1c0c0000340a800000d100c0c0074003820b01c0802c20042c83d4100100036060042c0240002d00501d00042c6120411600390080407030180c4001c1c3e1400a00d8595019011641003104d1b1f02d5003030b200d484da00240d0b502d20400007604418968010310300c4d16003040b270080d015240c1000c144e040380c0c010390180780b5041174510681d401806c1176540c04085040481e81c812014201500743c11b95035210a180f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 233262275 1250 233261025 233261033
    0x180a1b02071d0c0706050405030424080c09010207170a061b0c0807030c020415090c02060403051c0b03120301030506070e01021203061908030c15040b01030609020a1e0609080109 78
    0x300e1080102c0100007200640d640c2611060300348145070004020700e043c20180010801c00201502c02c0e00c0048004140d0300c0c52044221769105455403040c4005030380d00c03012414800d0500002e001004040c41070381c003400d0303e64200658031702031221141642c2d0f018074140000d00c040c52044100454a0a03440a41d00901400042895440b8000078080c10f00c000340d007404140c0580140b25800e60302a1050004e4860710b81d602890602d2442000106401d15400342c000900c04a112407066038183c0307586042c4810190f240011107001c1410300a415600c0420522968080199008100d01c41529aa40b50b06602d4403034200301026103500d0501c2003504082d6450380c0c01140c1c0d00c030542c040001d0720b0b840b90346400005002031601008455403049140c40803074039000100040a20300e02c48012111a00c03500c0318161402401250060286030414005000144030343c2c004280b4240002c210040d1180c540460000840390b40b10304040e0410ba007081001100e80160700f01c002005400000c02080c180d80d22 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 233263525 1250 233262275 233262299
    0x2040e0c042a0509011e0503160503040506010b030604060302041415090f01051012020a110606010e0904060f02040815010614030c0d0b031204060315050604051806180a1b0207 77
    0x2852030305000f004180b0760580d07442210a200401c251042040c0909484200500706603c190303800c190880c2e00511004401d406001180d008550010040800340e1a04480e88a1904007619071648240c0b81d08002003d603a55000f00c0000c131140e10038070111400c02c0d030504600b0464803459207002e90702c454104034030a81401c40841c1183e0042d66212800310741c0e16800c54041300c000c007200d01110320201d010b2003041c1d8041482a02c4002007401c40c0c0c6191104001503034002038011a82e5800510140010006149a040a210b03000181009030405881d0451113050007070100d0380050041c01c07980108031035544990f001c4e0344da50b2100d1000b4558107001d034456800e881003e210170625511042d070858591003c0248641004d640700010782c480d521001c000f4041c26029500340484a00408041003e1414074110303000c86030700515101004a500c01c0d41079066800902c1154000f58010000300364141c0108102d22440c03140100151080f0f6160b0391814441ea40c5075071401719845403009009060610b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 233264775 1250 233263525 233263601
    0x5040b0d081b03160f0209071d010c1e151503021008100308030a020a0801090b06121e0130051b030c10050c0d1d01030209010c02040e0c04 61
    0x32540300b2000e030790b042120b8034511401254104a00000fa40f02d018024001d4129115602c211100c3c0004d484040c0c0880f091068050070401030301d002d0368120402c2d80130341c0942803901c1c030500040083d081d001d42686d07100d1413001015030f0b001c0080700702e08400241d54030442c4008082850305800c000d056401041c0080f0100c80340b101400a40320201d201d0007a21001d41e00103603400280301e0f60b03034940714040c82c020b034020702e40c50710200e0160300000c074828920b4000c81a000340040c02d01400d2016a594008a1507006400b403401840f111007101c20391008466418040c001c1215400300100941c05544252596007400b84111401030301c40c18002a0081508102d01c2844030041a00ca10f0300b500281c00c12440e40110345d4052141c00411071041d4016001d041403000e40c60949001d40b040510039101850848025508504e900d110b14500e03600030360140c09440c50615128050300250343c042001c50b400203036211116070100030171001915050190203940c140303502e040030000c6403e20349410088802 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 233266025 1250 233264775 233264797
    0x1030201140d0e010b0a06140909040c0b030c0702101803150e060f06030c01020d1e050c0a110307140a090c050f03010603090201092c0405030c0a080405040b0d08 71
    0x21075104812a100041900c0140354106410400100c6031941240203142203002640101c240820009003280100c80000041034000c010a00d0080b4040400400c0400148110f800030038400d000304030087d48502440c424851407500f40e645070601c0c0100250f0614038144041000f1100910703143d0f10800c0c1d0070840c01c403a07201d0b5441c4110704a1010f00e9001d8001c1c9014003600c1d2241000700055484501c3d5071502441d81a415210034114041c01240c07030300d0340d1503014004600000c4542c00103001651115440c0c514500e4950304103451410001c2c200102100e0503203808421030608005840c06101d90002050207002c2e1490350800c90022800c0000c81e4440d05004a68a00481840600400c1152041892180099944c2d0f03102e60020300242944541a4006055450003243c0803c50303021420b40c1c0c0e14544149560482185818100040010003c07686030200b8071560449030f0041041001e01e0303220708080c58880f4100800d100448042c3e202c624481c00a01d0b5641000c04c40301c01c1152207988403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 233267275 1250 233266025 233266037
    0x8040e0f0c0d090203010b040f051b28020c090702010906060902040810150314030d1103040c120f120504060e030a02010f050304030309050a0c0501170702070b09120114010317030f01030201 83
    0x12900000b8010300c03050600f05c0e005424031803090ba500c0c403540d00052080356642009000b1001c032f2045020701e0300600813282078924100300b0058420303100c0348585540508510450310011303107032030200740f9140c0280c0304080541e466007594010410540218400b41400f208114106450510420b56500782031102d202100ea46659800c0c59003101381040011315000604c3d07407221340129403110703a030340e0140c080c580d6124039003c42003000d1000841281e0060350006070b00f041c0c8a062131035017150300101010450314452840c2c400f0b00000c0c003803c46c0120394001601d407e44c99601c1d010001d000541c06d100360520907000100da480050781c020360031488041c1503262654680c1c1c0c46150070f8004180d000000380c014828540c04408006d90400e1440c140c880a9031007264488100c121880e0610090381d0450260300284018010070202c8409002e006400906110010840700c0d146800c44007a41804070101c04004018018080450280c02c242201455102c6c42c600e802c90f0901031000e8180030090402003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 233268525 1250 233267275 233267291
    0x101209031e18080703150b0f040e01020c010e0601031203150f0e041502120c09043209030a02070b09181e09070506040b070501090b0408040e0f0c0d 65
    0x44540d040c0d28010007852924209000044000381554080d4141e065100020346004242c3c040e01007101c204a0394021200d01d134142c0e000e48501d020b861400010754004001140c461442d95440c011020464032000006035140644504035003035402241000c44140d00000c010070003c2c520001c0014080701ca442c0014007140303071350540d080c800255804121101d00e180804214001044030702809a4461101c1054202c0d8100faa4800c1c5d0003a088048141d6040c440010b042c8240c01c0020154008014170010b450501c1e400c1d0341d04842030300e00030143c2d004500140c1ca9129040483c0207900089400c00541c00c182800c58020b6a800950080d030b0007c06000c1440f880329283c0d03180b003548525003040e0410b861b2070141d0b000c55003005000440ba0001d00307034001007450044049810420754001520980c030f41820120002d9075948882000c5a080d9a108000340200303490ac001c2c01c0c02207100c0e604035540d461800c04807001d9090054403080b194070025007841500402d580803613504140040f4045907032a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 233269775 1250 233268525 233268527
    0x503010b01050d1a03060106030e15090a030c020f131b0507120e030a021e030606040b012a0209040b0f09010516180305070f0f08030406050a0c150c03140610120903 72
    0x21300143e1425425104e40d034000f10baa960590080810070028030f084445052400e82200401c0780d003521000c0030394002c5204100440e00c2013030040c0741940054041a1a2500c1c100440e00040742126804a56551102d0a180d0541058000c2400703a445240c10b908180c3c060b02c8415405540300c802e00107220910204441075241070143d07a030f1041d0001e003c030031814a0880c00303024000e1401d88092003070148400144080ca468400c101c0100c0d01a510801e600c0104800309680410385000c0342101011080c040006a076000281489180300e00d10710803c5e030415541daa4407041d0007502110040e414070381040007040400324600384482407840d00481c40748203515a400c1c25841e640002d000307801140f001151201d00c50b03440130100e03611040711410565807821480d850b40103078012500011010000461464482c0da009180c0a0107145990700d1030080a00003004c0710040c1c120b5401003034071180d0140000307107000e02403540013500f03850075010440f40c204014203a42d641d03010300c0b0f00660354010800a01d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 233271025 1250 233269775 233269811
    0x1617070923040c1e050907080705041703040f14010f08011d13060624081e1e0a06180b0109090c0e0d0506040c0b0408060a02090630010503010b01050d 66
    0x20f1110b404507008180050300040b884c11002d004190040b8203080c0820310062180d030065104071000d9551904017405c02c030b140c6a00003d458811000e610080c8004980d40982400250061040e10481804c01102e28000740041134040c1003034090084031001000030041252809003180150309070105a55241840044000369060300a8205c40c40e020001c40c014040c41218040140700350700c00c91403641142011119800221000e001c010f02c210360b00d00c9081841688540c11803203052004644580c00b1700720f540f1182e41100c80e403d080d0344502c0104400b0b45a0441c0c64007109ca141000c1c07101c80ca0b0480040d08485980c8204408140c0c2c03461110000d9102d20f040c40304c0c051005140b6031424105040c00303175440c4030a0340c0540391a079003010b0010310101a10115400c64500002a0002c0da8480e0900002501704000741c64001c1801c0100710070106101c100c070600c5c038030020340111105101008412010390140c1009010741e140c0740003000b0603a003000507038042d120342d40c001141e2a10140006000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 233272275 1250 233271025 233271029
    0x103090305040b03190e0c030c0d0f080304030e1302071221110403020f060304051213030b0f04030f081504090602280e0f090105121617070923040c 65
    0xc5a9400f00070b201210312240c40c900c0c10300b5030780c0354144a004261b2240c1921200003000281d0f0540c0000c01e0003099090000c40598151b00034008491410119215400750754011070b0101c0000d4030604010349603240a407002e140b030480f0618210700380402130343c4110380443c0f0501040184003810b6a00d03a2038444000680ea015051304105001078009644005202d8101d130208030302c94000418041001e007401801c3d00c2c0320316000350050030551445c00c91280c8982c05540e03c41010350308002c000c0003007002002c44a02801076500c121801b8038040c1802040207a41c1d080311020400c0d401d060050310701814041d620a98401c481c000b8050f100d83c941100244102c810300c08034603074102201c0078480744900803c10000c07000e8488861100102c4108072000b070302003d900d6402116900103002506020982c0c801818251048032400745030113010020100f9294024103880e0300741034040803103410920407072000340001c0c04140206d2090286428901501c2c0a030044000c3d1103400090522501d0300003440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 233273381 1106 233272275 233272289
    0x9021305120102120f0f0610230c0105090a0b01090902061204020402090a03081b011b030c1407030c1a040302100c030608031b070803040311010309030504 68
    0x341805059040e03401503500b404071300c0d0942e41070349140b801880340e20600c0c0300750300e00402241c0840c10010706850080000d030f0500300303009400c800348106088103a21400d03921045030000071100c3c0180760140702d06600f06400d02060140225591584600404d034104c0c3d5a171b2038030300c6a402e80341e480000030b4202900b00300c9501440281100250414401071026140c00070540014141143d940c2050721200c03c0080c0c0c050015140740003020031428408001d02920702034282221003072401840316401d05446907052440d05224410607042d180e90030320141c6d201c501b142401056006e02403c1242d8511041000c00403a4a41e16900742c8501e2303044d4000d1a01c0040038070300c60b021f460404161000d150700c0b0741d40451810408e0010702007043c0d04e400e8850545034440840c500c4d00d4030304d80c411035264208105c00d02c081500000f40c0040c01ca42800c0101c0c4491b00362130100c5e000c2c403039980b00d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 233093525 233273381 := by
  have h0 := BRFrame.cov_init 233093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 233093525 ≤ n) (h2 : n < 233273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
