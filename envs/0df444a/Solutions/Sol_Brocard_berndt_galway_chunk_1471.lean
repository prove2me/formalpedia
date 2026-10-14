-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1471
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:08:44.257236+00:00
-- url     : https://prove2.me/submissions/026c0aff-e6f4-4305-9b29-5df9d73c3c38

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 264388489 ≤ n < 264568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 264389739 1250 264388489 264388507
    0xf0e10060f050c010902040203010312031d0d0e03010603061401090e0c0f19030206160606050411030c0d11030403120c0305011802090105270324040633150302 70
    0x1841e424401064144100490300e903500000030740214500e10b500a01c21981d03503840b45062140070161110550001c1e1034070000042800c6c105001e00b051502c960002c1c100004c0ca087c088406201050203260503549a0000000080300c500605819480a00c0c02400ca503050080b41d5040711400a01814a507004104c040c40980380c04002c40c54660042d5555055105400494a5101c0c02944029040751000400c42a0500040d0500546520415003400320300c2d50ba600300412340c2c0001c16104101d24040000c0780300203d500700200741c00d9000d40800300c0d0450702900b11342120342044078164003280780c01210380d003030b000c0510942c420b2044a040c01c200c80d506140000900e0b000c042c58080c00c5070341c0003e00c0c40d145d038080c00a6580384070507040003015180c0140f4921004041034072513603009104d8085909240910a40714130b0080d02084c0c403c01e010b030344907120100030300105030790840480305640746c1240326650584000c0b6170811020107540100e180070380d07880d100000701d0f010a00b003505c10300807440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 264390989 1250 264389739 264389747
    0x5010608070320160c06050c0d0305060306150d0b010b12160206040605091f020406080702030f0f03040606231207030305072019051008011d04080906040f0e1006 71
    0x8480c000340c088090f04c0303007501d04d10140c0c81140094050320300407481000290f03040e070103402800803416602c1a03401c45200500700394161401542c40c1036250700840c00040065041400c3d00000003c000c103401502c40d082d494140d568082a0414854104001038014001560507000da810060021140c8641d05810100945130803010308001c00c04c2e0b0300c078408940740045c208001818100020360807035040c041c600e514002076001d4032848000c600011300054400b4004000e030749020021807030b1545881c09500e5218141d81c4000c0045822594582e40030808100c2428020000e03c0c0fa90000c01c00c40038540c1c100022003401d0541500c15074086c2e0000d02c00079030320a0903201030701c2c0d01c040d803841085650030304940340c02e00b604031460700071507008907801c0c450415040c0c0100b12682510002108000030808540c2c8034000d01880594000e00f84540b0015200c038546958130070f00440c042400c10640c1c00c00034031a50720a40c06500c00b005011010700600300702e51000ca400100201c1c01002a603e0020050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 264392239 1250 264390989 264391031
    0xb03092508010c08040507080105012102040f0203070c020a150c0803040f02090403080703050901091101110c040f0b0406090c0219030e130e0c19180b0d0501050106080703 75
    0x1211000d06140c46000c492504800c800140a03104001c2c0702081c0c8141d4010f000e840d0440341a540c6100d5100700082145040c410541600c0c858440c61322001c00a1810303c2c89030140040880c0c02503501c4c00c400d8150405031028602900c525584d680e680308903401000a0038000c1e42107140080d091301048041d07903400c42104525542c1c00b000003a101c0d601e6048c040041135034400040c2d0080c100300c007000201503001c14900d00c20740302620104455103c8984841c00c8500005009040007840c0100f4181ca6010381010ba5120304a00e04841140b08000d01142c1602d140c8088001d40d00c2d00c038103010515107880e004102c05494075403002c01150b026440002c1d0368880a1031055a481c10014401e81031510500501c08000c01c0645403800c1007244840300b1004010761444c0c400c4501520380c10001c1450644001986846850148071040d402d002641c01d00352099010a8401956901c6483c0c031707501c64507185504c09004800009103589480c8018001003401482072007094a00030315501043ea40e180c140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 264393489 1250 264392239 264392263
    0x70f0f0905030c120703020402040602060f0708070203030a05091e0c040b090f0c0901020a0602160303142e1707080105070912080706020c101e0e100e0321060a0b0309 73
    0xc0300114516139084d01305a035540029411900002e004500b083d00058014011260b00740d4008065491290803203010f00140c1d10034005801c1000071400000b100d41144c0e0700801101c0684807881c0151081410340841c18040301b440340c1041d500d402c080d00c0c1c10b110b841100d810035200d1007454900748260348100c500080c491102840b01040380340c001d0344208020340d04298400400c540e204074138241d108010254140840c0005d003841c800c1d120020070b114169005084810584001360540201c001869005002e080090350740c03075200103020a0902444070b1006001000390510905008100c0d080d101c0040107403051105101c010008000035003501202540c0000711540c580c4010300c1c082003e4800c2d03030f58000c600e2180000b9074010710b029030300c1820050180103039007841d0340c14840007806071104030042d2280e03a040f155204800409075040b044111000c4410780b8540981c1189428101000d018000000c044030403c009160902c524064058218014103906515000054a076510108280 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 264394739 1250 264393489 264393499
    0x2030f0c06031305150403050d050705040302181b070b01080d140d020901020106030215090301050a0b03250f030305031602071a09010915030f05060603061f1205070f0f0905030c 78
    0x20f030800b803100038800d00c85c1083c80608145010300f0b1a044c01852900595900d40200b0702d400041404240036030101e6040701d170302500c0788101035040b4600f00b96407000104090a440c00c0211ba005514200c20000d0000070b03c14120300e9042e50510600303600d441282c40900040c045140e10303030900307808400250390144140c26005680d074104036004038007528081d032000390000840c0058030703841000d13803024142034103055000304038039a05c50740b540c415039001c80d0b82c0700e030076030072401320408141140318200d290352131000024a83d040d95101e01ca107400b6019401600010004018400c100840141000808025200070718640e403c01d00c020101081d100031780081c003040090342183c1a405207401c800100b82c0c00b0141c80c4007080380704014000d0500c203000ca00c03900740351000150407850030707005a078002c94001d0001c00c00102c500c0803170741d0030410a4217039006004041c407a0410066150040c540304107919616445d1109411070094062101d10440c9001d000600d0700901a90301c0000d29050f00d2074041318 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 264395989 1250 264394739 264394771
    0x509060904151506210c09090218090406051b090102100c0210090501050a111201050108040201120e1f02030f0a05060103020c0a050d09081f0203100e04050a02030f0c0603 75
    0x1001a0003005040d43d00119040e10010006140b40c04c8090714424858001c22100e0580f000381d4600103d130306084444000c140010f0f420b11400b040c03a8007402048000041400c2e041c1c80d00c0e0000740c0020000c13202107a081cae4948003000200e08100c103285800108512040d41130140c1500040e4883c40c40c08504d9601a650707100e0214454401c0100c1503071a0380c0082c0070800070000b8103160f40603000850700312012505000031214000030207070849103d600380c0808030a290b402c120044a03c4100900141d040020015040302d1003030b920701c180062440014018003140c000d0100c50940018401c13102d1038181d20600810008103100582079600c80c00455000940350394000040e00280034001f4516140d220b1014924104540010440810803050311030450460f9220b8a03550764060040b6141c84014840c0412030600419030081d540114440e0b24500005898013804802c4c41000c680507140c652000700d40106508090000107200c90f4a107025242404051021541c50f02c4040c10b01906540000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 264397239 1250 264395989 264396023
    0x1203040f020a03080304050109030e100519020a020910030507050f030c040903050f040b1201150c150204050414160206060d020f040608010203100305010608010917030603150a0c090509060904 84
    0x800d01003e0359200140076183e05107802c040e4002c0c00700c80022030205428840d00344007440d01d4903c46502500569445113092004208010b0044114040300c055116030113807840141d5600918500c80c1c013160b018003c2c01441d42c10041c0c9040c22960205000e1040702622120a03103011a43c08442c880035100490002400e05d0103c485d403184680c1960341c1d140105000c644021400c00404440c00c90384009581c07a620b50b400728240b100d81a400b5408241300440140025891002101d45100b94240040c24207030f843d0041415644005054803064502500b0002c050b01c00c140240c0301c02030248000c00152900401181c1c0290700910041d1048024038140036140d561500240090711030300c0000c4d912800c1c4004015221802da00049805500340403000c100301380144280342c038098022440021000450180d6001d80d4005010143c040c011a1006580303400d0080750940500b2041c1c0b000100303807036002e0700102100c035181c0005108a07002024800c00b80e5a0012507070b040341c4c11500da003404103140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 264398489 1250 264397239 264397249
    0x4060522031709030f070b1215060a0c02012c0f0d0f0c050315070207050d110907080a06050d080406051c060806011505030609071b02060d1a031203040f02 68
    0x290380024086810b04051040da0852000500401e071403d4003100c1c42c404e0000a1242c84020b14044c12001200038017040c09a501c0c900605500421108503a640c60100400400c1140e44400600408204810080380031541c0c0458481d0f030b0b51030402030704444050030004031181d038204001c041d0b20400807000215003d45d200d156000d00294003074002c040c07482281c82c040000424502c29a03102e805402a60300561030649607181c41282554060840c150400041080e060b154040c10b40e084c00302c40c11102816114002d006003c5d078040e0701c600010b407a110300004141d6100790030040c09907180c901e4117000a000d800503142940d509041842d2101c1854418003030016510076980c901500701140010100c1c0046a8941030b1503e030304403213500219040080c0c645120654100fa007000e00c220004d02c5440c81f80c1040c620001d0640044400c00300103400041094220102d0040c011360740f456100d9683c200c04007030504154042e4043c001e42034090303114084a001c001c01c0500800348440007041103503a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 264399739 1250 264398489 264398557
    0xc0e070306050909010902030708030307050a1808060907050f0301110d0b06070b13030305070906230c03040b04170d02060c0304080d06060509040b0a0b0403021e060a02100b06040605 80
    0x1501d494481e140c50701d131560180480080c00d1780640070708000424412004021a403003142680c45452805844d0081140c442071501c2c0071584140f80c0c14400320349030b84280240c600403042c03003008060581c203020030000c155182d207041074440d03854000c410312501400015078201c14000d420005200c0880f2010566920030a5002031510303802c94100a01c8441ea06124141503000b0741d01000a42d58852041d20540124051b80c40490b00142261a0004919511401d041c0d005000f039420810480340d40c51554204d60800b02400501040030300c0b0f11031290b840c600703a041c11100244118901d11801940f10300780a010b401c05404000001000c0c4001d030f5040f940c0021200404010066441c0c100801c25041400720610079810940c51411910b00415401d05a0741c00070200c1c0d2805140d503082100d15181d43d00300d11307100c000b2001012542c1d07079040054640140c0075000740007002d6070342c105007080340c0c26950060301c148801c0c0018410305902c032b030680d4a9480210074100f400f1a24004180000c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 264400989 1250 264399739 264399749
    0x11040603120c0b0615120402131d0c060a080f040303060305160e060a1412100908090a0617010603090212010507051c0204080a0201230a05030f01050603040c0e070306 73
    0x100d01420071002a402403003480124000c8940b080030751500300400c02c00301c28a4403200a011410712006100d4400c281500d0381041c8014180403207a01000c01050a13940d401c001c03190300c2001c4c06080e0012500a1050300f44051003201d01c3d0380b401e12403041c0030f44803240141a29980314040c800080405010341e0040000e0354010044030300d80d410443c2014800c402c1801087d15101d1104003052a80c10200c405d4419220390800d0003066200200034088206840f03160052544119a4188514940d9100d02e007030350390040482c3e555031403140c41401203040d51a400a4200100d1902c807180c01140752803c607042d11480d00d130118640600d8000a40045c2d03013107003506815460001808003403900710004110141401c50740184004580f02c8100407401903100310000383c1c000848100040d03100702e2a5568500018002c0c415120b050154040e19421036804a804294000240500c900090301c0d11030040c5402c9541038510f01d00f66881074001c3d1740d14403615803401e6108000c035071a10b009800c900c010f44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 264402239 1250 264400989 264401003
    0x1d04020d0f020a17010203010501121e020306130504060903030b0d0b01060503060a090f0504060c0f020304051201020f0d0c1704030c20030102070818010e06041505041206020a02120c0a11040603 85
    0x13606038004500070361003845202e0108614011041706510f60740620314850b604202002585002003910801940c801130540390301c0344d0031342e41d05640701c11a445154021030141900090100e100d20740541101c1a10300d0141c80781303901d00d0882d4001015100c206040d510f5071302c3c1039520f0b80c944d100800c0c038101c0341e60880300243c1d0070010041c60120076503103c030f48154011182403110304881c140c01d44001000c0d410303000050300104414012402e018490a21a01100000526000c2007c01c0610b050700b0030005010342988070003111004541c014031000030071907060b0022945050540e005840d5018038540285010b21030004440303624400500d080241c88007400130340d5166014a0700d220b43d90b00241d0200640301c1005202d03411948928074280d80b003400985a94079044c18113025803201c608828682c0100a410030002c1003103102503100070500362103400c02603124541140c02a0501c207000341c13039a845200070b105100c0141030000340d00c2c0c0344681003c050390785800d4110100d0040c1045820190001d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 264403489 1250 264402239 264402269
    0x13090609150e0c0103020c19050304080d12050a05010501050a030902010903050d090501081608060d050a0f0804030501140702030a0e01030b0607050d1e09181d0105011d04020d0f020a 80
    0x3900ca8101a000016110680e0341502d03c060041d001c80c0103200c5010403a601210204050280180100c17118a004000b207904241e503d14a40d4079242844407244c1c0001c44801300700304071621501511760030500c207910034407280d810800002c20324000c0c5041c070004c243c1c4a0300703401d0544e4040d111341009503800c00181c0e4401c00d96018090a0180726100312400070703040500141404003800d590084e5030001c0e03500c040300c80c0c43d51070402058a000c10029034440c021100c501c400501d04491000100303100f903034641d403180c0c0307541809800c41e250480f408514030310340810088025400300403140078401a01385019980380b035900403001031020304c80705600b200b40002c0704401d01c90300050825112070b171a40c8486112000b50b2100f8a49401212041c010a011542c00c0c490b50100d001f4200c2e6071003803800009200d410110b8a84041c0c8107107403030001c03665542e5005110140c1400320301e10000c44000105d0300141480ea020400d1103a2105001d015111441c0e001c0d4219a6051a944c000b015101148212 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 264404739 1250 264403489 264403523
    0x50313021305040305031f0e132916170f150616021f0f030203360705041404140718051608040b2403070801020403050d080613090609 59
    0x40d4070a8444030362000a100f050001d81f603812160308140c030840c0c11100855103940c00c02215803505804111800400290700184040f900d0785940e2846110349120310490901d801c071000c0c003c40d92003000c002c10540c868114060680000040d400190950071644c840c3d9400c1c003c03800720121400c03255404000055001c4010303603020168002c0310300882c0c6618502c841c0d3f220b90030403446800340b91008940c1980c030040c0c00d103019074040c1d940f211107003941013a00450480d824080d16908100e01c0388400703c4103a0b107280910204240c60184c1410348082082c400c0380c5070840004d05004100800b101400d001240301c860090211784000c00c6400401030f20780b04140d00d55005481e00700e0390341800b02e0041410112480c892642140103507001402e00d07007951101c1d41952028100040200c0203050301402c060100c2e107040007041e0040c07404500060300c0d07509501d4903904010906041340200202e40301400241d54800302c3c00d50a1031071100d0001501003551801001410b0070440c0030340300f130500c5110449 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 264405989 1250 264404739 264404747
    0x20d0e070e0901050f0403050304020f0d0302030c1c0207091107020901060801150201050c03070804020406150c030905030c10051c15080c0301050c04090e07052809020702010503130213050403 84
    0x241d505280c20108955a00120b0034200d03881207809510486040340480c000c80d018000454100740007800303c1301d9047d801404580420005402140141d000103451390100343c05000b00303442254000502c0113a8441c1c0b0500035941c00c07a0380200c102e05a550000003061401c60411200364580c054040001c3c4e42e0340c0c11024003008400d204014111500c620200142403040c403070303140f066400b0135a103410f64403150030031100c0605c010001c0340c020f80c0c1d500c00403404000400c1e00703010a6a403a51407240080192800401018450303000074000d5000791020b2140d070b6184141c2d40454043ca1500540341e0520300200f00d08000310100c0010401d29108103500d0104000440400f81c44904007117a0504600d11f040c90700300c40084511401000040c402441b031082281c1024044400c2801101d9249880d100091032450f80301d0080d400c000000e0764000c03940d02e4000741600080100340300440c180420368001a080d8440144400c810303244040c0d242c41150703500789078528801507821007007240380b9142c50058 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 264407239 1250 264405989 264406003
    0xa0302120106081803190e061e0c0f0a050c062d041a120406050901090b0f18060709180908071a2a18031911010801081f020d0e 56
    0x200c04c0e0000354010950b01c07a0000200d0f4215040c106014103c0000d40f0310071206030541c107108035844001080140d0359158104483c0e401045d02410269640070b034840b03c249803850a489084180c0c1041000001144000c50b00c04850070061311565514050007104400c0c6804441000c071109000045100e0520761580c06002a07038000c241110b1404003011040c620fa0007180c2400c900162482c0010b000901c103a000640c1003050703074001113008907050751107800e000030890308045448844000c0140036600704000d40392204612000c1c01c0f03d401e24290042c4400c1650283c90300180c0d18908000e007005246c6d200610150300a843d031a1a04405d252901c00792000c1084992101419400300710070364800481c0706040100c0803031548041800c050200407580090451034490b20401d00740d801c554800f403000c0e100c50f083c059800c0c8c0c0c04440d0b81c50314040880f000c85400e410065844010b0160031800280c5010309004641b030000c501c485480f045020344911720030074540360b04014100d5100300d030010b816 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 264408489 1250 264407239 264407251
    0x301020c16051305090d0f02070b0a05120708040302060c1e03040b070201051005011209060f1104081203040804051c0c0b0901110c09040b04030e150403030e01170c0a030212010608 79
    0x1540f20a07400911034195282500e81e0171480d081941c00050321402910540c11110709030042c0ca0159a070303540201c080b900552050700100d20001200c10440c9140240e980d44a506400c0808560034141c81c000d58400000f8038850220400040c40303940d1605c00c2200000d00c1c4440c66005942c0d140c94034042a1160701501d403a0702640c00c00c40851100141d03142c0e42c80564006945103035400001c580220013034010a4016030b0030594070400e003441c00310f10740100ca491650b270300c01d00c0d40d8552030001614948501007103911071010b0248207100008095004031400c80710121501c41c007424608040d04070324004200014050403802e440020481c2030307040941800c0001b41c03607800710004075840445e10340601001d0140d010241d00300113030020300f0390007071a0340060207450005010032901010030071650480c0043d17800c421022500b0010180d0014124a6000083ca0054803480d4020f45252704000041d00207908500c0119520750107034400c0e070688005200c40b060307109595a4420025108c0300c02030340d039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 264409739 1250 264408489 264408499
    0x106030b030d0c020f040c05120921040f1202010e100809010e03130303050f16031e05090a0329340206151305071710180b0301020c1605 60
    0x382c18114000c5400751100c50300900384000d680c1040082000800042ca10030080c00310520460583c0501021920b10641c4510f0041c41005820000d500c91308a1240707034015401c900300810301140038200d40e003608459002c038054410310098801600d403400c800b49501c1d00010603601c0b40d50f80e103038001d488900884400303000300400304403040c2042d143d100701074a4800b0704103100001c0001a2182006000351000000c00900300780d6100b84803595003495a0098002595810900041b0410155010400100c6060451a080c58240814207034642e070700c009085407040f250018101c1da541d000540141019003004500c5140113141350380d00155011072980e8201d070100038000703180c000918842c0320103900d0300142442d1b6642c2c0500101a8402c840c0d0b140c0010883c103001402c18014000c46004020540b23480c52080c08645100311020f400400080ca01c2010310342c1000006010620f07102140280200800c2c07051070a408a4064486e012200000c0d209495001e100740a59020940039980304503a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 264410989 1250 264409739 264409753
    0x1e071e110102070b090d020f060301060201090b0112120806060f0705060f0c0c06010e07050906070809031006180f09240c02150609060d0c06030603020a08030f040b07050102040801050106030b03 85
    0x1281d0303d855900030810344150400c41058603291441d60084010310003090101020640b002040c0243c0080e4481c00250b91681c801804000590403100d000d401d0780199490360b82280d0704d85000020010500909000280c4041019915400e0494008215490100e59a080a480c01c2951042d00311141581013400034041350300010303040c2c2100e81c83d01240c00146074a03424001d91034138402c0d011344185c1c00d0100820010007542c48540241c102c050085407429201c072694418541031a0b200048040c281d03150030070502c81d030001004508034032060030703400152180c00d418030800103041907030025000031101c1c0e1403035240703580858040140e65811a000e002c0d007107180700c1c01da80c0c2d044101d07216100444100c0015647e0304010040a0b4000f030020039a000c1d000540c0c40e07600da40207464001c0300019440350030500941c2041c48410008011242c001e500e0825040e005003928043c40c05151042d420006241080c890250143e9004d89004402004a0b583d40d140141c01040703503007c8540039000f41d403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 264412239 1250 264410989 264411023
    0x702120f0c070e01030206040e13020415030204150303120c0201061d01060f0503221109070206061c110f010c0b010e060f06071101120e0a05030a11030a051e071e 71
    0x200c0f0700e4101c1340e004d03141c0d07418070741000441d000078140102031a16007004102d0180140c4e4880c080c18585c0c00000c0045d20440d808c50050105883c050702910b00b4400c2030b0382080000a901070f01c0c1c0d540200924000180c035112490b4220302401c441d034042c251181e413412032000c40064201240d4100d400648442d0f201503201442a91140400c40b40d881088004001034140007034030b0024014040d05c15008181180d60501c00240d4540094a1078801a4848810401c490a01400803c0d071041d2a140e42e14a0903030300c0e52400c1c071905000185a0040e82d011801c3c3c8203507402181c4203181f803a800009100c80d51786034641c1208010007180d045104910f91003269100d400c08008403a605900000880d05050031038005551120450203210307200c03591200c41c2c020702c0609001c14206035116802465075003030381c40ba0050403051228400d813015082041448030298000e4126454084420980a807400c14018445241e010704100505004220b103101e60b520108603034001c500034440c2070141c680c2d103184 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 264413489 1250 264412239 264412259
    0x905060904050a030302030601120f0507080619031709120c030c0a060503060d0201120f020c280b040302070f060203030412020d1d19030803070306061809050702120f0c07 75
    0x41d01c01901a0b00907900a5003c280309800442d1300c500c040c1000c010040c4c000031800704581d005200854180e98520a12030b2482c0e00020302504440c08680e91001000d8418821000c02072074480140310201d0103009128084080050381c042c40c0c00101030440c5100c02e600c40300d85900b01d501e81c0034800d00482ca0080d00a162421020090390b50b41e65a1500f59a5048180302040300103200590500084c8800300981070400d000300b42014095001c0941c84821460155151104142001c241c1011044000b08803d070144000c403000c9810141c9003100f0f07101c50805074101000e64002003821442d4100c042103550f0008029801544901c41e0031400b18030404e01261039001006104002618000440746d07810b80d101400031800d80004e040c1503901408100e4100ea50986070701c100d40c2900044100800541c06109180080100c2c0c14071002140c2112244c401e00300c810700070030200580e9000811040c80c030070805064884a00801a6a180400c1d220041540c100c04a404001c1c49102c102042c043c240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 264414739 1250 264413489 264413491
    0xb09010308071509020301020c070501121109060a050f0301121a010810150b03070e01110105010311060a0c0f050304081e0d0509061306030f0c0f020c0909010e0a0c09050609 76
    0x10000742418202d203036983c1a80070302e048540003005515070ba4104050ba42c280b00900d5812842030003001080c0ca0140090302c44070507100490070152804091a019a48640c125442c1c0401191a40c2d503407112140184d0f214000d5040b542400c80000c40007040e40f424040d96031550900560514424040501711004105401d004140e020340080140b00342d8603950b0b03004041d88020000c2c082a20300d403519041303111900115410000621103c040702d2903560044400d01254410700700a0040d98150b0b01e50400c1c2d48440c050741d5005000c0040c80d2441184140540801c0640c0640d0400c0080324508146640c1d40042c0a0b01d101c902403864110004c0014000c841107200200d405460200303103059094426801204003150007a50400052502025084000014121a46000030856811440305080300c0203444040240071918800140c610740000742e1502142080796040d40070b90350f1138549405401001481c00c0244161400c03941000081d264000a5031180c9030100044d030b480400700311050780 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 264415989 1250 264414739 264414743
    0x3080f030f0109090c170f030d060e090d090506070602070501050712271e0804080102030108011109030c2b060504150510092307021c02030901090b0304050c1f030b090103 75
    0x45010f400c1040e40c4421021b12040c40c0c024007070340e0400f0501d2089509550126424a00f80c1d0364942090240021041d822038100a104000b41041c18144101803c281700c2406801e1080c40042010700030415103404a804040e03101009001606144401a00341c0080080340103005040c48842055440c003a0810810031000399180721598620ba205c143c0303c8032100324069031000c0e4507401000803c1c20013001700010720070b24000503565898820040e0071036444089414041c50104080c0c1982da500040000701c2920455090760300458409121601d1101c000b0110703858a00308100d00d00b44000341e4000c900c100d000f99203444c45010403403403000489008407004640300004401c04d00103040640c0c000030650207480724104140c0442c0101568a490495941005902c0540031b45200304003c081c4007255400c6000450900840740c0010b410034141e406458070780c0700c001c0300040070300004005811112802805a4008003003c02200012100710700364140403e0803d00014818140703100340d181200d07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 264417239 1250 264415989 264416003
    0xf100302010503061801120512030c0a122909010b040317030705070c17010e010507050405040902030a020409030801051008160c02030a050d08010812030c04061803080f030f010909 79
    0x54110390054502e50006403810350855501944509080081c0c80140e0103414814080e000f58007951405078900584510005000101401030003510743c183c0064031810601810103564104503500c018000700490388000c2d06104e5203044029040e6041d0b00b90340c11000c0b0517039040c0c0300380e0307211a100c0240d882944001486d9a0ba14807940b01a1000302002d550007502600d495450b041541d11013000a48258029900d00c1c007040d4443c20b04030300c09110380404080710000a01041c80c0035070380035050307018600c40d03240201e403110b9400302159400c1c00080380365079005004000101d41ea04006003544424020381d40200240005242418025130f81c940c401c1c0c107804003d84400d984800d0417250b8803041c0d402280c0500c03800c1480800180c1c107001c048408805580c9203c00da6140105039854030584208401c031010003081400492844001145d058540f10704160f803015203615207501f0114000c4c1d002070032020780800c1039034042c2040001140207900164100c20f80340d8a13500900700b1160903910040400e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 264418489 1250 264417239 264417271
    0x602010905060c1b0307030e090603061506031017300711040b18091c02031b1203040804030605010504050c0702040b0a090f0902040507080c030a020c0c060712080f 72
    0x40155600078a0502c007650700070344c080d44036081114515005000d0071804038159200e800d0060510170015035100004a0003000c4034100600314501c459407c42c039a0303004420000000d42c1c006080c0380908024040c5100303d000f0b03003c103889055241c2c440e01c0030503410344007015180f00c60500031225180640244e01e91262400d590765a0340c20424500c0c01d0002c8e00640c480880729010759580030100c4240042118890385407900c41c00d203604214840f080f002d01183d400702c00c0f5030400d40c001f05a4203a6581d6a64040141c80b00300d509526002d4021400034240364000b04103c100003031440503100703c031710804003408280d8952040000b41d135070440c0e043c900c0e03d80910a41c00035140c65000b4914040340608208610341c0c5404504041d0307558405151040d50300da020300c40850809100b1958424200d00d0040c2483c1000c0500f03019920028007450f4602d5000304d01064481c1081c45071009007040100701c0c50b80e400e51441c051170200380d8240d8030000300d854080060781c1504103106007489804400c0801c408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 264419739 1250 264418489 264418501
    0x50f18060106080604090f080306010315080a06050c04080f0d020d090614160203250905070f0503070e030d030501150e061b0703061a09011e032003100b010306060201090506 76
    0xd02c0c00c009010b0745c0c0c015143c00d04440422041540106614010f00b250780c1d8901d000e500241c269006840c841d102c20b02d102c5420032900e5000304030b241c0000c3d031002020555490b14002b07401c06010700d41094541c0d002d00320b4041c0b81c0700c0c80041c8011900d903d40d029034117900fa40b80400e03a903207222031181c0004588038403c4100e50a040b24010603c1100180095600035016008a450544244400da14081c610080415620140f50302c1800070310542405001c00e1070100401010a2840b02d6140305110020000c180842d020314140d0684440140072140c2d020710000004000d40004e11680c00500c07014001c40d6441841860760b201104005413880c1d01c1e20368001f0103111564941c2541c0480c50140702c03804030020303403d07016184881d00c001502d80e0500c0c56490802070072000692041c0d4003007460103424802210004c0220040b250000c120190014008022349a0843c00c0c0b14015030500500d514402007070100c0d1301120855000b079078104806500d503c0c00fa400c8820395180540150300c40000502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 264420989 1250 264419739 264419747
    0x406080f0403031e05072309012607120506030a11060c0705030708150c0403030e04020702060f030f040501061d2a0d0c02010f090b150105130603050f18060106 70
    0x203000352280c50300044100d03400418841d1691369400989030141c51700c0c1405105903202c14640c50440404d40b807944d13a589042842c0d6924440d41d003160b414070110a0a0300c4100d260101c0b2005e14104d01c0000b15058075111a00a04140d00d071070006007007600c0c05010540c00d050000e04c64a4640e8400f149003031613514003080048680001c421000365216a00740440d43c0d46081c0702d0b220091103618010404c40700366840941d13a03a8001443d131040c00000380020004607501c80400c240c000300030799006941d0001400800d0b2030344940324504907184000800d010080441c0c0181d1481680030360000c20004d41c4440074841040c0010905442d8040b0801c00300b00307281d0704401c0c01164144074540000381c200080980e00165040f01001c01e00c6250340354455000c40f0b40a006854902c0703071100081011211685c0c8d45504550003419441020078194241843c0c2d034010002c0381c0241c038000010324039882d5a154000d014000840300c03940e5004180d00410031110b44d4043d074019990624014242c10383c00e0400c112 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 264422239 1250 264420989 264420991
    0xd0f1716200a060203070212010e06071209121e050a05090910030212060f091c05090a050901090e010f0c05040303110a060c050a030b150313020a180204080f030406080f 74
    0x4400c06040301c030910060ba840552142c01482c0c44d030061a103c8280f4010004058003044102c1280d904002240e00c18140102e8450340c8100542401003500082059010040001000c010315480603e45171040c402e8102e00b4544a403000000300f00114118403c0440c0d032030027140d8840380400c00070b00c501c3c080c1c0d26042002c598004400c200c295540c513507980003d80d0604d58407420b142e2701c1c3c000c0301c188100402d041c12a281d102580c600108513a000c0c1007081e41149550361b210108000c008500b100302580e03041c05000007000000d02c422940d5848880c810000c03d49003030701050542ca0480310043c410003900400c0348030f18103615454100707031443d102a5289401c4c2d1079030091600905602e04000381c2e2520860090303c001c0c0d07950688502a0390b4014080702c0380c06885510801c3c4a11024501c00200d00850303502c0b151060300c107681c584003031003c0790349024a078028101000010511907414880384d030151044500c2d0f10210792451b000072030156183d118170300600c000134000b900015108102c42c0261 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 264423489 1250 264422239 264422273
    0x3030c0f0d0501090b100914042c010b03070618030206130812120f0907030602090607050a1b0509010b0403020103090305070210080105190602030316030b0d0f1716 72
    0x28600d070040e10100d180c11100300b60004203441d03503501d800344800e06241c1070f511a81c0c000c40c14a0303410a4200390800440b0500d84424030711031600e840c3c68403050170600201e454900e0148142241494415030000d0103411601c920354042e1180301c02c0010754520a54050204481096481000740e04640922119500030888046803001916000480303220422403100b006103849486901c078591112040a080006403251650045070818480540004100300040b00d82c071800040e130f1036004001007107040c01a2070007e0000c0c02826004002c0c03041d41018048604840c007410030402d80c0301c000b0400509420301a014103d1400e02c4244015402a03000e40300150003814140d06242c020f80c00100603240b40c040d083c000401420040003942403204083d060726000070000440326041040003035590000402450180525054281c4124000d81c4242d43e000c0d0041c103200c0c4022040d052201230401d1890b811103140da51203c81d00c60303440c001000e44240d208000709480d480c1c14030340c44a24034203e6801d94 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 264424739 1250 264423489 264423517
    0x21201090905161e17100c021c030e0d020118060504020102010f061509060503061320220b040303080705090f06030108010f0b04020a080415020c01062403060803030c 73
    0x48241803c0c5800910307030003802c5982c04030100b04c4030074140e074284a42541c04500c041300c00c43c1c111000802e0201d03a142e243e0340400400124010041012031a00150911000b000c03a292a4600c1a80750300d600311700302c120085030840e40031840c0750800320700b202c41e0340c11200000440040b4440c0054a44e070000b5070464014400820b0068842d00480f04a45060b0311080d02c0c0300401d141c0c01d220340e03000601074008041d0750501e01e080d4035040e00450564202c5680f00207040d41e4618100d030718440050404564041c41c91041074a442c0004007818400901840d1407860713070341c4100000754501a503011181500d6042e50341d1025600c40d00c0042c0c80a4004018541d480600a6887c0c81182c5426019500030040e000000c9880061014000111007a601c0814001c0f401002404032003a0400001604140e2200e20546512802a0b4400c000e00480400c40129403d19400041c0c0c04500c843d41d10a801100301c071800c400c4000c103015001c543c0c5c188101c500d04d40013031001401c10740242c03003c1c1004000c6211 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 264425989 1250 264424739 264424753
    0xe040302030a050d06090f1b02070f121401020a0206010f0e07020d2a120e0103050c0f0307050c0604050706090e0f16090f0b03040c0b0322110d1113021201090905 71
    0x6010040d540c0401144804554902e0400e40341c54000d4080081c08c2e066002902c03041d8288800203152180034000c18a00d0502d040030078041020490b100490b02a001000b19101d16040c10029100c550070300c1103c24202c2000400f059004440c1c0c800d0b07001c1c4029400400c88072400010070754820251052822080300da5807143d600140072125202c107840d11506c0b41e0001c03042c410001500740c408007031841c2e0415203014200070b0f04614110840f5003c2c026511360544942e98580100d80320b10404540c000c00e405034000b848104600002c020040d034119031140125a40c2312045008180f40484040780c2d0101030f40b011810302c0d90701d21006606010b60b46410f9928a448070195030305a800c91380451280a0004200000e0008140c410009031038940515440c50411240806000066215500b41004800d200d001008030802c08090800002344c107950b0402c445040c8804064211807045006041c8100c1925010f4041d100312040c0d0655008054401d17400c0089860081114000490b51441100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 264427239 1250 264425989 264425999
    0xa1b0c120605040302070902040f1a1c020a021b0f090c13060e09060a0501080f0a1d010504030815180901060806104e02040c02030a0206010e040302030a050d06 70
    0x503020403969030090801050604181c43d0007445c219195000006191041c40184420303007070428034404031459030345500c200c01c000c03002c069030603c1501207001542a284540d51401c280d182c020f0400a112602901e0452040c4056000350303080000342c07642e0202800c1c410011610b401035171305801050210485061115034140d207890000250001000708043c180000c41c5403800c1108994007200a64080d2586854038001070403441c07014145121680b0340d0b50000d1502d200c0c0b03038014518828040300c85880c0c00306000a0a0007010142d81c15800110702e00c0c00669540b00001a0454550001c0c081000740340034202200441d40340500302c0300d019521980c001607580e00401401d4001c80d000c0c0540c0300014900b02d00802c032000b28588040d4400c0040741c2800311800741168801c45200c2d144c10004942441380c3d40b011480700c034520025400b03450640c00c10103070381c1c1c0040944141c14494088400316600c646000384528001c450040050380104061110f403441000a001190b00c40c20010800980750 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 264428489 1250 264427239 264427259
    0x7030905030a09050a0b04050a150302090d080711090108100c110d0201050117011a0f060c01060303030203180307050a02060703090807060e0108070e030604030f050c01020706050a110a1b0c 83
    0x3504800207000b16805002c0ca20300170801c00010f22004c2683c030315040c43c000200d02c4000c114800c0b5044661341c0251641c0c040c1c040d4040b184480c7c802802c031007162000307141c264040c6c0c024000a035131440101d20000c4490820445060681d0b02550013004840c03070100360a409026000d14040c100140803d01d401035100c204060443e960b591b8002096660614448034001000c101c40003070281c0c1049080446044c0c211400364103014262130003040e1001d06004a401c900c1018540022580b03003000000c24158564051401041950503203401030001518240d0307640120365001e0080e4100110030001450010000d010481c4681028506551380d807003aa0300f000c0155100c01c0200310511007c90696a0102c2d07140ea0164075410f06103070000200c00444c3c1e464a00800c028217000800f17040380c1845004005480841440d40b001f503560324100c1c90420080d05e000e8510001580c100042c1c4a0015500010b0714201c405590350b14982c81031b0010000810114007100340d07091135a20001150300c0d910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 264429739 1250 264428489 264428497
    0x20c010f0507020a0c0e15030d0e010f03230406060e0a050405160602150403270503011a180a0603020603040605190b06070303020c25060201240306050703090503 71
    0x100100004025120a01240a03a040100181c086401041016000a02c10201340060700c2c1c0c0c40110f01c04980e00c41d80180e0640c20030450280d4907114001000401592100c6c200358010740030307a52056070f2020701d01d06030241c881c1e031200744554400703246528034803402c0b01d200c06d80d0281c09000c1c0850751961703900603907508510560740010500d466004200502604208014207020404c00640205103043d000075110340e481c0307039034980008401f00403c00740740c411001a0001036100c40d8200f07000300100300d80f0b031b040384080c803032607020354246850082c8604500691360020040034200300c02c04003003000c00c024040c00003400400a242c0e600030102c00741c1c851101462080d0f210300c90009150400d8a00c0710341c440e03001c80c0700e60050360604692152948a52041c0c0300b80700c1d4103090143e04c811043c0c0155040c41200c010319103e0703c540020050192285001c040105c81c01d0350020003821184040301609201d28400da1b03900e41002150410000d1180d900155214406140c0060600d0107595a1030a6502c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 264430989 1250 264429739 264429757
    0xb030112060b1f05131e060e0f03030409090b0a090309060c081909030b0a09030912110d0506040201270302010e030f06011e050109030f0807030207030b040f152c1002 73
    0x281c04204038030600d13070a17170940e00980070502d482074450f03c204100b04010741039030256600700184071410001e0380d140c008440b122410300900340c0b62140c0c2c9820101c1c4c000c124801080c0c03802070182010640100940c4511025150140c2d2120500741c1050000d842c51250080704648841c0c080140600d106c0200c1a004848086a550703121150324505000c00100400303410600300510b0f1481c26070010b074000303100d1811a4100500f4800c000f035281002c08601507030b0103031160000220351680b030400002044052046200343c84200c460301c200c0341e08040c1c0442c460f408501a1110300818800b540c002c400b201c8100c180103045656841e45242d915003000c00aa0004408030200c081c11025443c4002c02c00014107428a0328114052440c0c8501c40b14003100203014210342000509030003410320030700110b8003071a0042544151414145001d040700704100b1019105100c007481e01619005039809008410340c0324070254862812070800e081e0000f8803400040c0c92602c50711403042002d5800d80060b0800306 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 264432239 1250 264430989 264430997
    0x304081006180b090403140f0705060402011b120e0a080f070609050111060f04022709190203030d0e0c040f0b0a05010e06300a150b030112060b1f 64
    0x340740012003a030703818000d000b0744005428218004929103900704071070f60094151503c5540204454071902d043d1084140000f100080000c4100502a000840d10f0140e4801c0e0b0700c10305000c580c40c0b03003140d8004440c0c50042c0411042480050103520038201c0d40c0c3c020500403c61841595103151561a10b1040c801c06030890300b111008000490304a040c0300018402030030f08850a200c1c0c0509a620344600a200052540d014401300b01075458841040ba4480702e01c3e9031190fa048100d5449020f10b40c012514440f1500c620300c500c041a04441c05000e07140ca90250055043c003030440458400342a0705860600c5510640205108a9483c0c0c011150101c40c00c002c0058035000003c140603038080c1a030091414040f00e00441982921010100c030082100f000034010075540036400d034002c5150701c0c05c07403400c0aa150000c2c400225041e5100b61110444101030005003659211107180501091103136000140540b030108003c01c007590800d00300100010701c40c40c1268100702192030b107800301441004c009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 264433489 1250 264432239 264432251
    0x1a06040624051c09111203120c0705070e010f1d0609060d05061306140606040522020a030506041401030201120e0f060f0106090e060d060207050307060e1b0d0507140303040810 77
    0x7001280c240d80d0b05072041990321010203203022201c03a907244501d007001e02c0d0659110b40066803e09c00c11064902d00b81d4841e003900e500c1071b5500000b0704106400e000700c0300c420000d490009900e15080b000e50440c1104520358050a035038032001c00100100c002c00c0b26400004500060300021000e00407113100719040c14010103160400d003030880444141112107002011000c083c000d81d595800d0642d41200d8007281c8070201030402d20180d050b41c8804a4103165694004550050460b4054214901c103040541c2c0401c50111100a1a51584400c0c88064081130586054680c2c2c4480e5800c049a0105800304031403920098000991910302e0484025060303403600001030140c2c50340645540e0041006205418003810002c000030354060490100a241c9036000940004000c0b090050302c00c440c0e0404400c10882484e850425107480750040310414440328480c1c038101502e031662006816542260052600d542040080e100c1c0b84a9034841a92600c000d00001030803032010802e03546c01c504054004295 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 264434739 1250 264433489 264433493
    0x190906030b0109030f0b0405030f2a01020313140c0d08180312220504052403011a090901110f0705010c0c0803041b0803071a06040624051c09 62
    0x3101d800040c100e04120a00d4010004030b21121a1000a181c101c2c0240000f51203e02d81030346548154019481c154001180030b240046a80c020f003446441c040081c0c8030024400c15126080f0b1200701c0d07510008810a01c0e000000c100300030725040340150070108554000c820600001c3d07020148242c100d481c0640004c01c1c0115451030001380ea50990f0581c0100702d105007007420032425000f41900d4604070064040380503089040300a84c0801018080c0c8100a0360810885c0c1e000c1c02a04440354401c140d180c00300556041c00c0501c50341c0351514102c010b18034000054800c10400718030141400705150340750004410f84036140001000c504071300c00a055580c20580c6003642c00c1d81c5004072050284520250042d011400c9003040ba588150f10042010252808900d42c4044c0c2605400c50511071002144034410030541d140b0000c1001149450046c2c0b0343c1d1381c1400c01045d6141c0d030246100006445040a5416156005918080581c0d05009040455122010701c0002200070102d018035164118002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 264435989 1250 264434739 264434741
    0x1021602040b030307030c060209210604060e030c0703061e0c051b0102090906040b04061a07051006062312040f060509060f070e030a050303070509090702011512020619090603 77
    0xc882d0740c00d070007940c100000c0e43c5000d004c00201d4440038100310340004508100e40d030390007028811080c40b035109510700c1032840c09140d540d80c41190112401494910224a810340000980390075210380d0005094850441c1e4442015004404e02d003010b40404c0e5041d803203010600c0c02034400468032036980a4851080020041c402ca200815012880e441044100d56903100c0000f150b03400a0305403030100d1801c0300080460024045544040304d0100c0a04240300b400e40b0b90401465901e0150040b591101810384040c412075055100b40004161454041101c001c0f440c041c070711003c1204030300c0340e041c01c096000300c20305110101c50864841d8464440c0c8400c000030751140b20341100c1600c0080c902450410031000c5001c2c03000c0d1600e410310850102d106080d031740030449484615031000550352603082224001d82180c1046004910039003018000400c150302c140700d05003030103c1303070745c03080001d10310f0300307980030140100940145d8000f0010030031030315141e00a0087d5400c02c442030b540e000c006854100d0041c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 264437239 1250 264435989 264436001
    0x6060503040317060a03030e0d02090a05090d0810030204150b0d020a080a0216080c121b010605010807141303060c120b06040e0c03180d0903120f02190201020f0102160204 75
    0x48100403c03031040c0701c0ca07502c808000d1415258142018611180b2850001d03144002c1000c0081d84003c039070342084840d00305070300203500804100d822a41c119402c901c0540d9807241c1201d22140c48078a07282c04002520f4190082c1e40f083c0d02410919142c2071b151311172909150300c540021a10560001070280f1010b500c041c10350360001c0074100440c28404500b110804240c45000003400b0043c010a2441e6465024494040100459014075036203007040800c401c440411029664070b08d520b80440000c88d54007030b4004d24852885035031181d170707042c6240400466030b030010003c00c0b0f5a001c1e824030100010782288030f40c405681a40d01c5010503580490440c0090303420501c15240204024002003001a03600d6a50503000030840840c0e40d1030399210640e1404010559413644136078410945a810240c2e00300c03208070150b900445090150144500d01646c014944c0450100164403113601c070300340561008040f60920b8814410f469105003c800418260703004403149002c80003055010b1f204526203031190b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 264438489 1250 264437239 264437267
    0x902131109031c09151e0e0315010f0608040209130f02060d0e2a010309050a0204140405010506190501080403090305060702030408011b0c1b050a0f05030d09140121060605030403 78
    0x242c16017044c505e0018103034008861459600072442c505094040d000d4003018404c0000501103800036000c040340840405030a01c61850030003030001000c981148100001c0c3e1059030003405d104a01e0f1907060044032518440343c01a160300020050705001644d03800014603509034801c1c03012604c0301840c0000d600304201580c00544500845030741014a420024000c5800c11003424001940c3e4420300b00242060b649000080d4072921b4190417206401c080c0180600603030180e0001c1019503104400c0c4040030800c9031041d0f1020143c2d0104221640c45092116031061007031400d4802e15030353741c2e1200e1800c8420707035610025800100f000e00c0244000d1080c107100c024500c000454500129401401101c103204c4003401c4800001560380101340b400813120300800011300405004c9688002503600c1031118007500e842070044111091150784554041810f58010b02d04c04ca420109120054400c02800c000301c90302600d07034000b04640d801403485200018400c9864455480c60700e031400030002c407085006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 264439739 1250 264438489 264438509
    0x903080402011722031713140a0b01050f010c17310603050c0729130221010f02071209050109060f030506061b011e0902131109031c09 59
    0x821108001300c2070031907000401c811205480b40141d05044901103100d500c4809648894410b101d0300000b07515007034841c140100c01e102c0180013011a40c60701c5052041014150719494801070000c0c0c0740002540450340340504249003580e4095442220f0b00442d2404205102c1d80801d01c0325a00d0040c0958100281d8180798a602d01000c41c40d920806107514001c0204140c0d45000003079040520104441c0021381161008480345081038a1106022140d0350611240c11050040740c8014901080d0f030761010380c010304800c1450013050440e5608031150b42003023020340d01d510010407860b10510040060a02a44040031805c1034814040c202101550040c0c0c10010440302c01c11a1039400984c1089001c182d140100d41a02c49000041d8a4042c2903640076901c101140c88800760807055120b0040f9000d10050000500003480c00c1208075883c3d030711701030b4102940c0c6000170340484181c0c0c42054403007650501030341030201c100c0220b03140425120f804c0302203a004488810980d500401e2040c006e00740500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 264440989 1250 264439739 264439741
    0x60504060509151c0b041104050c0a0305040303180c05030106060f021c020703170a080a1505010503040f0506160806030102130b130b030705130503010c020303011e050409030804020117 81
    0x208205070001441c031190320780f860200501c1035032100d031640001064900d03141032030180c506055422440a840c121502d05030300c41521081d003070500480d4400e5888030714013400c0250590081e0043d00005204900305980c59940b0001d410304e810240f400c0c14050724010352960304000c145400c48a50790029002d204946030b043c01c43c41c0d0b00050903058110811010f0b600001c02003026072401030303540c00080c01d1048041030241c12006200c041c0c5107400d090307500d2440079200c8e10f0140702150900280c403d441c10f2014010300043d40508021500103120f0404120001035a407500c50400030b0540d40320341c1c40200b40d4000310345a030740507044c2904254114000c600c0c0091060317040072032140302c0c403d9500c1c2150100c0c0074890010320000d4040200480000c482c3d4920b0000d00082c0540e10540c001c1c41e40350400e0b0390120b46414140301c0e8000b940840c1d0000c51441c0d02382031000006d03088001d24200880601440840e043d1954001e01303101c01e200740c07200001801c140c03002420580d80c0d000f201c507a01240700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 264442239 1250 264440989 264440999
    0xf06031a0d080f0a050c120705061602100b011206060306050102060c04080d0e01020114181501031104020f13090f050c03070804170c1906051006050406051c05150406050406 76
    0x1500315150305400c040482e54403945410117481d24010400010014064000381c03105900058000303040d45803140c010341300c3c1c0c0d54801c1e0b030300704090180100f910010303440071034109101d040030390180300140814100141c032640c01c8840c020a481d000c1e0031404c0003039100c800812040d42c040200c65040410b024015050906207d1503507500e04655049604100440640c082c084c3d00179441216017101c0c1203010300031131400744107a104809801c0000e2029102ea121518031501c0030440c0e141c180c0340d02c540065402c0c03980300304000c0650010b103a101c10502040094882006545080400a0003003000c007044080e0700d00c030010110fa02c01006805000c1c020001c11050b1a840009554495071050040300c0300c1608041c591071a0280e100b40181c40c0c0710b100030087c84403000c942c40340c180c0c91142106001c0380d500c400400c05401007074400c1001080061000f405410300404c0500a504042c0705040021942820304106585d001d8642d40e08560307507449113800e503050074060a00601410340f02800107901d04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 264443489 1250 264442239 264442253
    0x605040b0d02030411042a1d1504050a032f100f140c010207150b030a031110050a0b04060501080606090906040207061e06080d0507080a03060f06031a0d 67
    0x60107264100707500100180c108203401606800709400a04100002801c0001282d0240455203450315800403a1200a100600c0340074450302c000100c5002d081810303000c20034003030b444072110000220003005100208858980c14156002180600960001c08850002003500c4000d00d07040050440035816144d4040d40320002c42c0843c02c10a860500780c0d03904001d60440300c03207002520110b1000c1000401c42c80950054015021103801420060f40b070840781044038045960030380d400340e050342000d090351010a00440c20742d861300208905542021034400071490450300b04840c0384c00c0181d55100c05942e2800e00c0c0c481c038806810b00f800c000d5441d0401c280024554002c1c000f8442c401c00c1908002900340c2c40b2501072320001d0303a20010a2010701c900000482802c0c80080d403e8464914140f03001031505400918200d00318503680303d03146045642e0300e54040c030341c4c49100408181070711007500046480704098a03e005044943d4000303200d01d09443c3c417007030001d90ba80c83c00d880342c468030300030002240305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 264444739 1250 264443489 264443497
    0x70e0f010801140307090c0e040b0f031c020a05010903110c1210020906040306050709031a01050a06030203130c0b090102160e060d0507080703030309060b10020a120306050312130605040b 82
    0x2003588020481003080006454401203420a0041905210002c10030310303040a8400003480c000c889c1170182d8402d0206011030b00c009004503950541c8944809803900140c407951000d041454415980b5480b0729072281d07403e44040724011000a0b03001d0b80c9102c1919001c0c402940c62101c05c6034081da41e071040c0107070070380e91320342c40c0c04080c41696000070a8022170f81d448080714011503100d001482549084000500600b81c0c40c8806d070b5021000701c0394607602203803444090b4180da00040001c00194240f5030100c00075000107110390103000764201410042a80d000001c0d000b08240c140d05503070307041c81c90300090802c0081d9800c00740d42d8145500601c4660106410f10b03500040070745920700801004c3c00d01500e4060f06a0048216000b04400070003410b5241e0442d60b440d03030050805002075218482030000040318042800c0042c5c0019046000045c0300030f60300000003030f1070300d00420071075101c40000b41090310038240c1c00111007001030440301d800c00c64070503d0b000346454200241400c4c0761201c1a682031103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 264445989 1250 264444739 264444749
    0x106020c1008060604051908010b0d05030301060c0f061401090c0f0207051314070c02010f0512040f0510020f12130210030903021204030302010213150c0206160b0708070e0f010801 79
    0x42400240c50b0303204c3c60181c900521000307004040c00411781e4144815001a0701428401d542000019000c505054840d0740003540d00c100114030310303031a140c03044441c01004203040714049040704d41c003c0031482d5030140d00e045108581052400d0751500f010f02048911030106501031100200312400380a0b00841c800303044550a5a020384406410200c440040c00d8100e0400600710250381807010f2268451702d1400b01038400e03252090307540e00103482681c281c000c0380f2100b030020458a000030002402e841d02c00c0da00c50b2099048810600c0d0341c1c080c25040cae8200c02c0b503801e80b01001180d02d41c41c0c964110340c802d400c40c0310010383c40308180140d000300700781c40303d0700100c403041c581c031502c48004251003048462000c2c028400b170359880d00c0d01c1e403800901035400310b00c0c0b03080c407a11100030101d1040d00c01002485013001d2501c80d03040180c004d50038003904d50000f014065180c203c254209010611620017540301c1c458540c0c0f900e14926240b00d0280c802042035042c0c5014400d03082840401d45d820161990641e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 264447239 1250 264445989 264445997
    0x904150b04140d0c030b16141b0106030501290a05010f05030c07020a180518061b12070c0b010902040503151518070306080102131530050106020c10 65
    0x40c418002044200c9600f030750042c80c8004003071002007030000058046000700030014030760400c005220800c460800c42c407143d0b62803a0b80104804243c009a201c00c0c3c1c4a540a500c5c00070070320a650b61a014211928150b00e107a8541480000c040310740d202c00402080d130b00d011111030312480d0420b0002894546440c82c90700c280440040450551a880c000f03841030f059009102d10101501c1d141c2c540214008000740c4480c15040001060702c40f41401000d40c2141c40303040040295903100080302d03098002d4011780391007141c010002c1d51401c8007004010340c40303809c1946414605501d00c1c80d00d0b490850059014a034030a1040c0402d000d01d5a01160070710303007030801803081c08031a1204030744105a2800c0d4180c1c070780c0c800c6c0d000d01000c04030030080034841e2180c50f180d10304000d40703a03852004900340d20402d0107030707000c1d104240024483c0000214113000f00d0042454403d200d5480011114040080e00c003890628130f002c0b42006480d100640240c0e4054002e40c400b425020050102003190702d409844510180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 264448489 1250 264447239 264447269
    0x60e060f072307060e0f0909150a14010e04050c011112090a0b161401060e0a0908120703020d050601030c0e0f36071103180a0315020904150b04 63
    0x1820b14864400d81ea10481e01c2520401942e40d070004c0d1100700400f4180b409041e107a245400c15151034811188201000d102501c8541d541101c000490b0100400e4280c40c50f5942d0406800d801810010a010b4248000c0c1c500c118141414402e180c00d0f100c201c00b42c1000350002001000480110b2144400d94690000e05d845140340c80014591190b40d40100800b12000303d0340400c6184600354400815005100b400140026020f1003800d0710310a015000340c051400022039510406075100c40340150160400d05d05000080e00c00780782d4550280e5803080044d401003000415058140319040c2c020b84242020000600380d20741c003030700654070411242e12401510018a20315250107485010309143e4218000c0702d08400c2511030130030000650f00480035124034001076000c83c020002805004031020003181030090018074002c0f51082d842c0181c0e00312001040020000300d21200070502c161180032b0158580545006110440301010f001e01400442c0f0b87c1c1c2080008041c5003100c09541c0c00c0f02401d001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 264449739 1250 264448489 264448523
    0xc030903040e1003061e060902091806030705030a0b07020607020c0d02040b040b0402031f0e1b03040606260114010f0b07051e1f0207030801060f1215060e060f07 71
    0x58504541c07000d04000e0a00006c0303400c00e02c41240c41c6480307004d103c0e810003800380c44400a03001c17070140242c8a0341040914207550b003803450300742e211135104000408a8000b284c80b100841d0400d021441c00b2141d83d4070b098140000c0e03a405000b169402031061001348401049000005c1c8001007510b4040c0c0941e584266044481d01c4503005440d0159000e4800e56403801d06905404120040040740e2410000d50400403da032580700c0403041c0981071314040003a00400c940340c2130000b07038409401120f103030b41c1d200340000300211045088242084007100700c102c40044d15800c0c034291060b004048585d42d42e02c000600a8070580c01c1003906550040ba50240c0383c01c05454490714109513080d0905803038090140702c54001c503001030502c03071b038400118094201d06180e603084010307802001c5004022401d1200188185c0c2d1003805241c0c1c010085180c05044c08805035040387c200e44901c120a22420003807042440000c0e0020390103455241d054030302515046413482c11681501520074014400e45800c08880c0d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 264450989 1250 264449739 264449761
    0x20d05012a03231e0705270607171207020c281710020c03040f080d120906090212070311121c0302041706040302011508060f190f060e0c030903040e 65
    0x100361451003044c01d095090139503025107030790007011095040385070400f0500d003071402404242100c200003038203442c20b200321540d0350360002c00c140c05403a40b011424084646447c16240c400b501501c095000382c07014000d40340c1400900186540446204803003c0c00f0540311219200e40d8130111482d825075154018482c0c1c2940341841060101020440c0c008280c00d4100c88000c40100304484a015100c8a550707072301c00e800b40d01c9841c3c0e4441c600c041400014040b4080d075494001c10440d5205d03407000160040143d000443e60b5440c03c031000309a40c080c01c01441003024425005011041c12640c4840030000b00e121560f41d001d14240040212183d9181500c000d40641c040c3d82c05005e034808800e41c2090943c840c159a040704850a400642c20140300f5950010520810b005a41300c80300a008141e0790102e8103558604040c22401e1400703100c0ca414000007546110f0034000800c0444042215032410010701e000800187c410303031040f1020818414915000000c42c1c046a03080100c0340200d80d10800800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 264452239 1250 264450989 264451021
    0x14090f090a020c0d120606020706020a17040509040605061305150618060307170105040207020d060b01140f040303110607051207050f04032f01021009020d05012a0323 73
    0x4020740c46980020101325400c61000c07100844002c004112003591604200d0342d40d01c0d03a101c0c000240e041491010042081c0030041d64002c01801c0d1070710300c0d140d80c030300c04a401114111410340d9455902c90900c0312505d41610805020740c00c0080a108030700703100c80d07042c5c40d6418511406105041c0040c80c1d100d0300c0004441c1445442c0b00400d0141c583c0b6015802400e0340b48551481411780f5030100012400346494401d03500099000b5096600100442c2e81d19002452a50304940c1805040e203c01e10b00d007901c2e41c008000d1181c0c1d1008141c0c5861941c036000c0c204000c1c29a02c003181d0b4021004000490394032000f078500700900110840c00b60b03100c3c440305075843c8c40340540d403448500001a001c030520001254a01d03060014514800443d100006000301b082080d26000380183c20901d070a44040c001074010400c1c8900043c01c2a44880d1503584040c21514030914858012030084000301020708041080c181652450405016103000380b0301545100407544020701c1c050711814040746846000c041c0c0d10b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 264453489 1250 264452239 264452257
    0x30903020c01200109050c03061f1511060a0e12040509040f14103611030c0301090609030206060a0f0b030a14040317060105070b010506070f020a0906050114090f090a02 74
    0x1c12905c036060400b02e071101c498013030f820700030b20806000c280b4500b85612120004d0300c062580d00b130701904200a4a845103401c81b22001000000501e0a04100d030902c686406904403900c0001c20f903481b0001e003410000481da00c148a440c0510042003181c0b1040941d50740142d00210112404207540b81c52811a00c1c200b00021152241c148440d030281625400481044031041c2c0300c544080410700d464041d1900401000108028040300000140c0c42c1210000c05401c014191100c07400c1c8040400e00711081c404058a4a46d21030090005240d01803003d1500640c06aa00b0600141040e8010564140c9807040021030080000054a040305a51003c240e401c000d803c1c0c14883d003000c1c280207268030100c00c0e03010700f106880d4000c203000713600450840c2e00069100c0c441a80c140c0c81c00080203101c0e008040180c64003813088200b1001a82c681c04008045c0c0702d08440040c2d041d080a00052461400c900c0d40340d40d0030010042601d540d52458250000d40200312800d441550740c08250030701034044c043d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 264454739 1250 264453489 264453491
    0x110c0703060608060a0903050703200a08031806040503070b040314120402040e01020315010c1103010203010e0a0c14090607240902011206030309050d050a0b0c0301090b01030903020c012001 83
    0x20100c20046240c01c24011141d076074040341c1e01901d4440c205012282d041e070700200410400c104403000603000341c0b40d44901140074114a007081111744141410043d2600084a0b241c2002042003009600780f0120708642d903080008080600c1c0c0380d502c0954038401c40c42d0162500b0000f0300014105489159203a000710b40d04d1480a403600461224044ca010702510102cac496406d0403a1916030400510a07644207030030000451508900342c0005484001c02c0007029038418140c00b13190f64058509000550080184c4078542d10070b0b1070489615003c40b005088001d04200c04402c4002d010200c48040d00c240c180100c072019a900e030399141482c1c0034504900c1100000f0215580c0d000040120b51108035801d000fa00c50742442c101c4006e41000301e40311804020003189001000b03002a0401034009548144100701300c542400041c2c8076564488030032074002e80c03102d10001c010300c6050124011405041820308043c01003500ca660043c0d01d5036400c41c0318504006402507010090408040315110159a00c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 264455989 1250 264454739 264454753
    0x907030f1704030c030b0f10140a080d0c0c0b0c06220204090c08120301030c090b0d0602070b10060c12140409050103112d1005041e0e0106030c12110c 66
    0x7510001d00040c600c02540d842d44406c00040010914040c054416001c091000164600300104088091440b01e652904011001c001140c009000c1002115900c0141c0b5444454042442c04040802c065081032988503410b00c2480e00305880043c4c11074000c414800e0b9070011110074039100e514100200d4019601905043c191418005801410301c15103240c03005580e04503030144884109807000f80300050644200c0c4204102800c841d0b8084c000592008015180200141d11960141d800c40141a00c0c410031440500203615040c100d6000100000c0c2881d0b8030703c041d00d40356a4000000080c0030403d0101809804400d080004112009403910304410007865071282040c0340e13a000c04020341801080d0004410b580c84c0c5001408500f242c0c0310710341c03414007070032600d06014403580350300903082c00d005080c0070200c0c2c41c2c00030f91428494080c2c92141c6a02091070500c510300c401406a028005040c600042072a403694050100a165400c0240200b043c41c6001503c20b011701c0b07204e803e8081d80c0505d0b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 264457239 1250 264455989 264455993
    0xf060b19030b010f05060403020904020f0909011505010e0315060310090c090c030615030b0103020415120b040e1e030c01060e07020d05160605100801060605071a0907030f170403 78
    0x1035514065a0050342441c001d6a01d5130205200c504a50081c0f44d030011050004000524080c41410350292000d072111100134182000300d00320490a0340c500e080e0703944450383d4501c81051071a22000800d82442c00316403146651002c0781d201c5040302100c032004e000c007a000488a807400c00004014126400d41046581c00034100014900d107103000c1c0c00c0e03029003415450411217100340546401e540007000d498a6110200754107800a1071840d100a0616400340307c0007900c42103640300c581e00c0d0051074640c03041116240d44401d00325021585607510451603c10000030300c910005007000050315840340421300e8600241e0f0146580200110030509600307041d008101302c2540d07075205025107030f25003c58540c00603072902600e00d8080e0300040030f411481e068800012507240d4004c6038011013040c218082154844201c40e0950740680c1040c008602c0000c3c04008004400c1c4901c0e06004000307020380c1207814409a81c4d6201c0302248009004200c8958610b0184001180000780c909400b4804545d85c0d5924 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 264458489 1250 264457239 264457279
    0x307020a0506070201050a0f090b120603010f110a230412140106180209011e090f050a0e130515011e080105130210020c040f05150a060c0f060b 63
    0x14104a000c0c204000d00040d00b418003800fa034114690507103c00d800c00480980481c2c0e4150b40e003641e5001c00500e8800081d12000c403000070b0a880c0030200b400ca41500d4600145803d4607500f400f403001c01c0b45405e4126054260b04015142d00030400c2c504010750b040c0c01034400c9076441032031044107e0307a0000178001454500051855200a1044c0d401003c6152000259402c8070310034801d00c001c4010724500020519041d900030f09144c2c1050402c5101c0103504030910200885800c44c860114000440c240401680a11030070b00030007045135102149401c10001d03500c1d1170405041c0c1d1100b8400302c0b001e20b00300201070081104000c40e000314442c040d1f95903182007000365071900e8110340415106c040400c5a15040c09154850020350052044500d410f509118503113004404240440c02030440f00c0d0310070340d10360107072031818248440c0120f00c505040200c803111165840700107105d992402700410601c0d40104c1c070300c0601c681016050520100d42d05110303004d4004160a581d0145170402d84c1503d051003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 264459739 1250 264458489 264458497
    0x11115011d0105090708010e041a0403030507020f0304120609021c05010204050f0a060e012d02010e011109090408070602070606030f050607020c010c0212150412080601080c071203090b0903 83
    0x48512103a0712a41d0f1441072000d05102542c803100080c0201006103c06011310790460340040c07045030b8035607045010222450b00ca01080e14214006512103080c04107490741008040d1654584101542c901803501120f501d28a60003040201403d454940890075551805c060b440c45452501040110b490380c0e03d4154000d520900682c1c1c030030f1728011501c0401d8208a8414000e4842035182c1d201e945c1850401941d5004c90301d80c01c882602c04000081a07400b03400e0520701d1185903107030004a8059034001103542075442c40160300c08441c1c410f00108480b66a074040d52900725801032020f0340d4a41507030030468040d02c501c4030040d0802e070420780c2c0002081200034004218502840c01e48400d0f8441d22400c0341c444010424441c00504400d00040251034414154100d503220b030303001c440450b0715441420041c5001114141c0d1201680403220041c070b50082c2019a0004007403030802c0c0d41d4640450302c18114011864050030800080c420704030315a0081d40f20f2242c440e00318102a41c180381010065580b944 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 264460989 1250 264459739 264459779
    0x70b0304031202040b0706091106130e01090207030504060c030c050109030c0209060307140402090d0c03111003150306020d09020307090506030c0315040807050a080409020d1b020c01111501 83
    0x2220515141c0300041e503c20741d016600d408030007a151130f45a8407030101424816500307440002403640d8240d40d035911803009100d400c00c440c05000200d4a0725000c0c0343e0124050340454012801040b544000942c0141220142c520604124640e44d070641011076a1010740c800041466103090381010600d5002080e021072107100f21800d41c1151b440381c080c0350b203880b0705104081c24038843c0402d040980c9010b4001e061001d03006045c3d51881c406548524103181c41a600030388116a00820311449030401c115551103440c2c0c0c1341003c3c02441b1031f80c40c4855080300c0b5444003802455000c01c04203a8001560080303080a90010101c3e07030829280d100c120020081982d000307101340318542c00907440b4200821100943c50700c0c1501c8440942d0b5179107940c0c5281d80310007002c560f5070150b02c603564001020034020b000600f011040c010785500503484600d040b01d501c0017a81200d00c240d102c064104540c00244100500020310380281c00c090100c5c0101c1c50100002247c544104480c000411070603244404011400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 264462239 1250 264460989 264460997
    0x41503171207030e060a02090d021507050c0a030b19110c060603010e0a0f0803130209010e100f0503031c021b1b061c02070512030c0304030f02060721020c070b030403 73
    0x2448848040e4102d6500c4000ca40e0349070042c1001651b6107840c0c0d4040c02c21510098150060f5015642c000351482130b16904440f203000d03011840b0b20600100f0800d20f031401c41c050741ea4070340b040d0564558060702c00c1d00074148407000d403480c1c140176031404c0c164100f1080c2c180b81720003681c0c40c2c1621442d141d40b540002c54030540250301c1e20249425034140003c0e05000181c001d1140c90381106140ca42060b2584028150400b14020000c81c900607158410010700804240c0c07662185401d00c40049041002154000d0074030010311750040c0115580801126013841d0940310441c0881d0782074207218040d02800306940301d5441e0000e4541c500f40b6020500c014501003d200d07413400181500c0402025003d82c850b44051180c40d600031404045007a402000031500480c1100e41051101c1840000c0f54030841d01c01e1040a400b00034081090342155220b6034080550010b01035618045038010301d542c50510200000040c1443c1c03100882089604549076200700d40b00b914031054586000400c035a100343c408a00107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 264463489 1250 264462239 264462241
    0x150e090112140303271504080a0810180e2b03150b0318030919080f1506010522030f210c020d020f19050f01030b0306060415031712 58
    0x440040200c0c0d11039141072800384103041c2c2c0055a0617000d1818200ca4410340b02e80002d01a0b851050090b01d8802c030b20030820169a00d68000009001c140c0141c203200481d05184401e100b603508150780b0006480d000c40c1c0005080001c41051403030194041810140c0070b40c0c8290f002d01d150500c051000004c030494400384034165084101d914800b6076482080018035007031000c0f070300310716039051103c51070301d43e40003143e0405005000041c401c3c00d08150040f100c0c56a42400c1089900a0207002c3c3c903100c2c136401402c00c400c11508000803582c8001d04c500d04001c0e000408617a42a80d140e80c008401590041203403e5549030b160100b91001c054505075113031260580003a41c51182855045100005992801c089039443d9003407182c0750254079000c0386c0c072070301c00801c0c151242c07609c6910101d11000c81c485000d60500d08424006480001c0b05141e04041c00e110643e216034900042c1c10b43c120006840000e0301c41401241c2e0030200091703810007000b554860720f0a448244c500d030044c00d4414246030388001c0b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 264464739 1250 264463489 264463523
    0x6021c081e07083405031003060e0703021002011509020c0f07080f011b0c060518061302040609140c0a0207050d1101030b060903062e0e04060b04020310150e090112 72
    0x7941040130181e1a800c907514151200d924030480c007540e00480910003007a90583c0ba55a1042500c5022240202a52094004009521300b1340c0403800f8682031400208502610f03040c1c1401d5290850003854461900010a035215906c100040c15000c40c020003a50f5079a1746402c4100d8450780500b904408941c20100aa484004c040d103590080c0a46074468081c01d606c03656828015000013840d4100c81d1750ba03030440c3c6050807414404284914140c20915900103132070300c1004111501c5410403c1c0544c1f80810b04961130860404441d003140c0c007181c400d5191003000308201c0c603024481e00020340161044003110308200d44108041d8105100f600c3c18030083c00c86200b0b2107002e02410388080d606a1018021480140704000c6280c860f045000d2030030100c1d8428005081c0c00701155020312849043c2408000c2808000e202d00840020111810351440c24048151403045910380900750f200e00400c85c1d0b054889008401000c281680904400070542c2d4464560303608010038041980d80c11041d01c26254 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 264465989 1250 264464739 264464791
    0xf04020d022236060311090a0c0926070b0301031106070f03050306010e0306012c040f02220f2903030409090309051f020706021c081e0708 61
    0x58901c0c020f00c1c080000000100501e4820155081614001e100c1c000c2200c0a8003500600000d0350066141125100381030040c40341c0210014600c44603140740c000315003001648000b6001c22a540b071030501565200e20071306a00e40c4494100d019859200700d0340c00040c0340d820300003d18101c80c081c9046598400d8030a05014491040c44d00050103841e00d800040d00290040e8040c64200e841890711042006040c00846c1c607105082c3c000d000c03240b44041d80c40c00284050099054041d0011100d0303410350070302c1e80d903440c04040c080100a111304800d41c00d180020010b407604e4035103410010018007101c0201a1010000e20070b003801241c0c00021000c0701006c0c0c88c14907000005030840540190b16042c5003141c0305000b0300c01003000300c081001841001444c0d40d940604603407480c209950708e10307104c2c0d21003801a1400600d68801803d40d00a400990002c80141c3d0788881c0720340f45420443c50355542d03901001d0b00841041c0d500016034480000344502c065100a040d0310800c0304620703100f1100380442d9698 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 264467239 1250 264465989 264466057
    0x605090603070507150f0b0f0102010b0f01030509160603020a0e0306041703090f0a061508070609091a030a060911010c080306040e03090909010b010212071a060f04020d02 75
    0x55003090041010940c640c0c4280e0080c41113901540e01c01d03001409940000041d10140206000ca81c0c0d119681c01105203480020561054401d0000b04150341300d04c004641e80501d61036481d4141555940051003445050240e68881d04140b6001a901c0b038482c20040d00a400100000c1c000880b24000e080040c100040c1c031602503600310300f0360384102150050002c02c035031004080b00b41a000f21459050070710803c116482c40103100340d03808130f804046860002030f501101d9001e09215403001c14100413041e0400b41040a031000004046164441e00341281c081e6220044419003500c02c60450b0814404036a0220070344500c60219000c4036918800116011141044d010701a038a0400100d641c83c50141e210203950703c01d07a000c2e40e0030040714000040342054211520101a5100c0c1c00b80b0310a503a05001c1109400d283c50b8456007481c010340c440c4400d400310f201c809400090050080703400e0b0f90f9688080a5440b0000300259070307a06d80d608031078010703400c5404d0f00c040041c08043e4912401c0458040301c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 264468489 1250 264467239 264467257
    0x120f020301080c0d0303020408010c110c010c030f08100e0f040b060402040b04212312190c1103030f04051e300304090e0607020105100b0c01060e0f100605 68
    0x1440c1c03145040c8100300404d281c00200300d007815820040010089802c0c01441701809680c0c4070141d03490040c1c05100e003040901560316042001ca4283c41300040c1d000046000140c040c1c0ca880c80c02a91000120006801c042e00302d100400804020083e42314165032805114902c10101d190b160740b241800e10044e80114010303c20121020300c01807100503c00302c1c030071134611010718946c070102d410703601d03445e03044400c0c504400f214284810082c038a103041003140d11040020031034032500c0e1160840c0c1a500901c20a1092810003c03003500040500807540d203081700d4038074010140c9586100c06521f481d0a41d005114040c0500041c00800c0d100c8101384403216100c0601503c20b46180f00d200700010f6210203c1014540c00d240b200943c0c452403582000640050810808001495159030312503a00d46403006002c101160b04240c00c00c00700480105040085407424171000d521181058000c43c00341040c0d80046065a440c2010840402810320388180540c04003074080083d503450b007001310f40710f105181d25 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 264469739 1250 264468489 264468493
    0xa0606180c1719020f0d0e0609030403030905150c0d030506011808070b090604080307030804110f0d08090607060905011b02030307020309090411062209021201050d030c12120f02030108 81
    0x1503075003016940d003843c010002c01d0014a044804031078108503810400300c1c0001c2e075a441008419200c81004150b0b001a4000011401c080c40c0d40d5005100c003c0340c0c025180141110801580d02c00a03401c240d42d98003c0940982d5021465003200400505048801c1030000e2010405d0f0b11401203003071485420b55211001a0007d507050085a04450380f0410006c0e821040800c00000e18440620142890a10903600c005807410b00703092032506488400702403032080458940c1c0c2101503940d5004003460551003e400c3d620383c03446c040050b046009140010300450b0038042d60400300401940075510b00203c1d19980c81c450540c101080f40c0d03c5c0000c591000150b4010007507200f9a2400105490b0f20611800018121010076008200e41383c11070711031031008201595180e00a0404143c091020b0800c0040c210f0800d4003860410404120620500c1d014900b440509400d040c49400810754494000100308150850242c00401804415521206151902e81c5600ea079402d04d000300c078102c0d800040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 264470989 1250 264469739 264469741
    0x1101050405011707140706060e010501110c090405012009031209030a0f051009080306010815030c04020d020c06010b0406030f090b06010513031226130f050a0606180c17 74
    0x1c0304890f5140c000c0c2601003804104010780c2d0914001200404106d84104800702d40549014a900711000040c1c104034140846d5110324009010001043ca2403a08201c940c20300c0d0791194140140181002d910b440d210b040d5480c0ba890b04e42c4044e60003890718142c01d500716011081d907600180791600540d20090381c5900000c410b2004225803580a601300c40c0504260b440403e40785000104946100208880c01c07480407040001c69038000e0705031684001301942d030002000e09000003e860721000a440d904c5036601250511900c0c2050341511585801c1074125511381d42c6172a541000c43d0400c1c411940080c0c1010482e031072102c0a401003031021a1b1003984007a1a4036044010344c1c817600000c09110740e0400140001001c2211084240c0c0030b0710540e00d644c546901400070441c14840806000500003200300305100490001600000c841d90300081036007034420340d619040d03042502070b40c0c000d4009402e000b030200d80811407108145000c000d4280420040091a406864042c0082c0e03180704c0c900000d00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 264472239 1250 264470989 264471017
    0x7060605060d202d0f0703092108030703181704081207020f0103020702040e060a1d2b110d08190b0307090c110f0a0201030c021f020d0605100309110105040501 70
    0x754051308071400c0d03a90b28284035941c15541d125401002003540003900e1a00c00b0070682204141c54005803804251101c2c0c20302c115203907210a44009007001003090752311103000c40b03480401d084078202503900c40c04441003d40e0b0003105244a4005014010250180000030f080940c2c1341011610305903030140041e02c42c802502e005400a4002d03640a98105444603c0840070441c1844418810000804005500400903001c42c004807003c0c2c03118a041da02052090100c40100100c051500d602c103018880c1d00d642c0c03448215210081f12035401d083d4880d440090500c19000210a48a441c0e01c140c40b04011701c82000040580d0f150744182070300760300800014002d80b0300b150040a1004610700b00703141c4101010072020b1a220000c40c08508079000a2130b081e0440d030b814028031501c0c6a20340300070150800030440041c01010960544007500342c0c0000c81c0001d819842d080a8000c20380102622428412010007a01420761a40112503500c441c2c0f442000369805007040d00c05a0b84182e6450354044803203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 264473489 1250 264472239 264472297
    0xe1012111c05100e010e060f04020604050d080c010c0906050d052706011d060306010b030403092105070b030123040e0124080106030b060607060605060d20 68
    0x1000d04641001d50407180c4100040e00206031080d2074859401010303222503060f210011070751454224100c43e418490b40c1052100700052485c0c215050700c00041894131140700040443c495039000c6504034444403401000d000d000e001900d15245904002e009c00250740604039000503c50045d40045802440200c085984580c8081d500c003540d0051a040000050303070440070300d1420910106140d2048005000e43c009082a00c410380708040d58001e036a0402c81c00281e20340405020328000c84801000041c189441011084003e007460a40102581070a2116243ca144400403c0d036451088100008541030024116030403540c0b1018520303d240c2040742180b100c084400b008592254640006500244085c0301b07184a801110488101d20200783c0d01000742c3d02030030b41c020040350b45800b50820104072008035650340310000f00d4140750b903910300303140210003054190449a000711000c00c00d1031051415500c44940c4103d2822103203201c0c203000e00422a03d00c1004050148098000c03c2002a8140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 264474739 1250 264473489 264473513
    0x90d06150305010213030201090b03011214031201030c030b0f0705041211060d050106080f0105060d050702030c0d020d0207080c130b0117040305090901240f02010908040f0e1012 78
    0x145040441039140ea94a4403401da070066a01080158040d140810843da000f020000080110b03c3e5601d08562401e00072205000e40041c0c007800c106900074480d0741420b400e0003114003203101c0303003402500765859081404101d2114001106e06040d00404220082c803962130082c4900307829510301c2d00c2d09042c191150b0050700f9204080f1100441c90082041079900c800250082e4058840b00048239850148020094003020b400500400803410051020303845200c1151480e090060307021440da00c0e1044124a10f2040c8513100035540212004038282541c0407a4260700842664201c803241512203000d5a1171b20f01c8a00e9180c1e01c81c0c1c0d0302c040d26444810503000900458014189416045406844080141e4088808800081f80001c021500d403901c038451a001d080b001000c01907240100e004c142401d8040140d520610100540180005100350010222a6840800035407116501e52480311788200700e028811481c3c030700000181d40c945050020328112640001604012025500c4940c40d181d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 264475989 1250 264474739 264474761
    0xb131d061f090b0403080a1e0503010b1812060402041b0215100e0702060406200702010e1c06090b01080c090a0207150c0c11010e01050405040b030a06090b010e0c090d06 74
    0x4100d80025050a081c02410045d4000c000c20307036940d100e142000308910700c4100d00c3d99091070000351344114241c0c81340c00d482c15101c40c103402540c2c80402c164a881c0b8050101c40d0030358414201c2e91103c90f607280c04290700e4015442618240a0f01e00c11005220514048000c000010b074003200c07059800103000d203030494104001041c1c461a15845440c0402c03e40c03011203c25016a100200380030030407441c4d119a406056500806012511094213819424031404201078104941c03449440c20f591f40c2c1c061012140b009070035121032081c4040ca403d202903c0c3c608802ea40c0c480220700000307040880400d4811206030020000304050351807460aa00a400901e000e50745e9601c0e40c0281c811008040c412a0340342425611140000c8055180848500860580d03182c1001841d1001088590300a01130790242d8600f02d8001c11410b8071500800c0c64140020000390803030b0304141c08070003030214003100e8034180c6180440340e60490307486110502543c421008601d411605141c0120049540c83d0b0012100302e03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 264477239 1250 264475989 264475997
    0x30b1c02131104060c0302150c0a0c2301060611010b0303070206070c03170924190201090b01030f12020a030503060d1b08070f2711040b131d061f 64
    0x40841240c06854005410200c0803501068101e411301d034041000d2110350010070403c850390b18186200c501279005012108007808141c103020020003464148907032210510450b031555803481444070724042e005912424000c0340301510491840300040c0250704106078064000c501e8500c09a0a0081c0c60384110026200c021504a01000142c0c1300384c00382101581648100392503a075074108002c0d03220398180010340d003022440900c182e110764090564a40101c0c403030f41e00005181440059000d05080c42e40185a99000000402000710404040718a40d002d07050814000e414a0300999841d054440054081201440001e845191032610540c01c07912400c074040c5194034049214900c032800b5048000c2540002406014510740b142c6540020000307400c0c49000b14041c01c0c00c14081190700051290701549508001c24102c050204443c010500b0341480380d83c4422098070810348620500400c00b2900c0c0c007416040100c0501c92045005200c018580340c004104428002200a441d1000038144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 264478489 1250 264477239 264477251
    0x41109101202030a0501050f0105070c05060c011d0106091508070e060607050d0206040605090a1109101a0705070e01210c1203030222060c080c030f19030b1c0213 71
    0x240000340050741c013850084c000442c41d941400104a126203034407155504200b02481928045000409413030111101540c4040e0741e01c0d030001313940b400744c492040e241c1100f050301550080845015407000041b200420020804802d0400c0fa1383d10010841c80344002c00c2e88141420b00c0200e0410750300c2a0080740080030b103803810b6659980d840c1400381d85012400036070081020007090042c03134021294045240d41c05014461295a162a10802c044400c1130041e502c1c10300245028a07440b030710340080c1100f080543c0c80b000001034146400e910038a003ca9903406000070000762000080d0000d4142d4210541c4004081c00380300d04038080c48e440c564103903000d0807101400600d0003c0340d03080c00160341c0203650151707496803100b1040c90b510348505921807200c03843d100c0400c81141d20800c0140001d611035130300e0ba0b8551001400b80c1c511701800c05180e00204000074100080c81000c2d1031114481910340f81800300c083e03000e041102d0707150b1044003c0e42c60544628554014a01240c691004102400d400540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 264479739 1250 264478489 264478517
    0x20601180204090504030509151e03040c030c0305060412090e0c070c050a090603051207050c0909012012101401030c02011404080a1704020f01031a03010c1d04110910 73
    0x40c4e61003a5000c1d0007058001410150a04020100d00072210400e021240303041213580c81040400007210b8078076602d24000c00450208006074804000940d000b802a81e80240c0740d0038042d4440500743c03022601042d011b00074000c2940200900e07000c681410240200b00d03a281820700d0081c0c0e018681c00c8400d031880000208480e601e6204e002d0141c21b001d84001080c5045241061820b0018450554480c10a00038040010340009044406940a0711004807684039070b018a8094102d45040501c5a00c3ca210313002c1200d55610007a0540000b500004841034503000c00c4103004013014020216248511020782031154002e40041251420318800040c0030004032541a03414071055808803410301c000100f000050b503015048410f052030301318000306641444d0780007801131244261240d05168aa11114000803c1c04035010301003000580240168002c200c402044c2d0600080351008032182e80109a071303903080c240300d0f1003003138150b80c0b600c9481c1c03032021020810b101003401407403030410103000704040c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 264480989 1250 264479739 264479741
    0x4081306050c210405040e2107030306092c030c011d06240f0d0602120a05070c0302150a02040803040603050402090f0606190203191106060405040302060118020409 72
    0x10050030203503200d64551a0395001e5904181c050007202d0303091901c1c02403582c404000d850856044403403c070740000f581212141c205081001903041c030840306e40132018000c001e100300c4000303042e42882a9000c00c00d20341ca600b5404122914080602500ca50140207200300300780c69602c050a80d22071001722424641c90450791400e60f14140d24030724800400c41741da04482c0108010894004081c08002e80c0c05140150004000100f84c440180c4904030b006611440d94a40c40c00c401d0b240381d04100f007955500010000b80c994007109507000d0000503e03000002d02100d2154002c49401caa155000d40a0b24051001410780000c002e000d040603240d0070400001d03010000c000420041110b92400301b00780c5040d00412000400003854000c405d0350181c10800580d07105e50481d002904620411011440940005c0b07103507014500003031600b40d900d42605052207403c003e840d103120700c101045030392680e0740c1000e0100740d6402380c400902503807160b0014012000b00d0351070110a800c203800010f0600b40d803055000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 264482239 1250 264480989 264481027
    0x30c090d1b180c0503280f020a180504180605060a0f030302150a0c050a050c0c0613030203060a0c17071e0801140103090206161b031208070206070807080408 69
    0x31900515a031000391070b06924003841d1904015401e2440c15841d10112142c42c2442680200100760004030003103a003141e096010403642283c2c00011510350b0b600ea0b8002e0500c01000080901e40107112000142c149010700920f016100c10440c001da118005a54032406808041c0a0b0b0b5404200c1c00c10100322031880200c8600158040d900a209618042d042034860a10150200d1001800e0800506840760031804841e03ca1075a86481640d0340c090101041c10704802c006902d81c80b400000b200d0000002c905030307034000c3c1ea000310243e030300c0ca4407151008000c0311180059580410302d1103140007801a001a02254444c0940c10020b01c10441c404618155007081c10100c000f240780d400041c041c054810f901941203000c00e003010031040c640c80d00040d005002d01c008481010030804003400c00c124594543e00f42000000e085042419140c4c135104d0280301c000c14014001030002c03030000d050a480020107a000e08108d0319070404603160380001319440f0400801c159200c900821403403540c813504c81812 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 264483489 1250 264482239 264482249
    0x1051c020d0221090303040b04060e0a050d140405090f070207030f06290d08130803070b01150c08093a03091a1903150807060311030c090d1b 62
    0x59643e80701402440302c0c2c1801000f00044803920000700060040c2c00021260070a8014050895640d150f00c2d03c100138000482c4010028040e800030f2008010000414429201c1d0680b1f50755a00340c01607920b100c1c1405035100760740d44888208041092290082d0728550031100d1031044e41c00c80c07130b103a80310a55411509101110810b0b690540040d180c020203090440d603000e00f04d00b031081003079840700142480000210113010801e00092010b074090300741d6070101c004c007951700c152a160035181c02c0c55803220200740300d10503030b6040c00c80b031507283c0c60701c1001028842c0c3c0d4011401802c00000c0418402465100d46108480f94141103650281c460b03442c840030701014240708510001c502a00e00142881090341c007a00d4406280c41b00400c90880000a41c0c80800c0980a180c400c484101c00442c05000c3c41000c00701012580b02d008600c0b218003181200035254591400c1c0011101c02010b0b11851004881d0f181e4082000d100d212003034986005001210382c0070341c40749046603080c415002d0011040e5480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 264484739 1250 264483489 264483491
    0x14090d02032e27020f01111e0705031204090207050a210e01020613030e0a030b0103030809010507021f02090a05040c030b01080a0c080403050a050d0c030606020f0105041101051c020d 80
    0x4049050a280240c900b0340050b0b100e0101e0810f58220794a00b40080c201c4002d2082850142100c0c2a0344a801d025010305019400c5694891041444540051078065048042c1c01100b4021815003070000e030020710f042c20804414038042ca002581c40003504040d408580b0350040041e0700c008904851241102c030310f03041624402c25078a510014044109450405041d03411050800c80498200b1011030009a01170505080c0300128800140e044810f03600020b107100c060500100505611448491194914100030489070320340600030f90707844038085284813000360007030820341c1c1315140c6402408240300c001e0140c00300c10f0b45980c00903050700c008040b03503000240c2d1030780300110540c2d000300220341088225004019005841d000104000710042c0003509004000540c8117010703200e5001c403405c140041a0801860045c800d000300580b60b0f43c414040103206614000086c0001031107880e000343e91185490001842c03003c015946504070608204000740c0d158562240e07420340d07000500c000e040d0858 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 264485989 1250 264484739 264484813
    0x6030a06091404030e0f0103090b090303090f03070f152003100f080c0402030613020301121203050709152106380d06031e03090614090d0203 62
    0x11403481210010844030031142d8a01c020301000c40c0d0071034000101c02d80c1c217440d00342c0340418140040c0d005e400c0030724004112442440c100410a80c003c00514001c440000035200c01126400740329940e401165800340c0703047c4000d007600c00029220f0580a5611080b085c02040f440a66143e07410640741c0a4890825200000100446140c070b00c0c7ca800301800070f220321044c840b400c200c0300d50303958002010003034000e80c0d000011405959642d49807166103400140199500c0d1703107501d00045083e810100072280314a0454882210b24000d000c3c10307214001a039207802e02c091912444400d111204c07134219091003040e03034110300c5107c60044042d2440c1c0e1034040c0801c1e642d1805800114070105803c006007003050b405400e40800858040000030a1a005013450711040550004001001980d2004140042c0e01192104018180d507882c9451800b80c0c0380c65114a40d2500180c440c078a4601d08034014002c1000301169a1408a0b14403010074000760031601c900502d0750b407400920040390b0202c074140710564 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 264487239 1250 264485989 264485999
    0x53070303021e03090f0418060b0411090904020d0c080304032103060503070303050d0f0612150213030f060e01020c0304091a060406230f0a0e0901050607020108090c06030a06 76
    0x1100051400c040ca80e80c0b4080089040203030703201e008100a0700e2141c20b59100b8a17034aa6616001422000c401d10034411500445160440061218a014a006a0400842c12304008245065506000c006010300c095aa181d50030443e402d00314200c00c850b084111900170803626020806440950310034021415000c0e00250b81c6514203140c0020324040504289003400591004118031084940c1414001e0700da0b81000541400340130300305032407886945058000034030181e02e40311143c546030061140030b40c006440b42000c0c0c1a13108901405942c45140001000000e0304000c0c80804140030320340024040b1003104449080e41d0220082d001680e001280900091655100743d44403071003005442c0341086801c05c04a00d00c1e004a00c1404203004840d240780102c3c480702c50030000144e036072048850381c07460501c02040f00c90b0820340d4003200040580429460500b4850b0b105030690b8801483c107400c003212179004444c4080c00905105440c0600302a414003078943c800558000e4040e400b011414504013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 264488489 1250 264487239 264487243
    0x80a0c050f03161202030c16051011210c0a0303090c08010606080703050c07050706020732040c050c0a03020d030507030c0e010311040f0902040504065307030302 71
    0x5100520000d80041103805003035240500c0103680f10b548960412020030700700200703078118051100c081c14140a05100c1010105409410354145c8000700c0b50050101d04014003150184400700001e070a6034000364103510b0006c2a051407100d1100c0c03000300d040c5030609440c105800c04c4038120341140800e880350f503603104001c40e000303800c0701900103000204981840c102e0f0041004101520040034141d41d10040b6101c0d02e8440102d40b0310507001000c590b011030352142d00039510803d91150240c0c8803005d1344005c035a04203800300b00b07500240040781121203000b02e0040200034008204040c0030301404100042003950140310f0411502d00940180c0703265410b505c4d014040e1100109542c007094500f010080c0b09507082500d4014078038083ca40003a0310703c41001c0c079190300d11454010302c0020a0452000500f02041e0b0010401d540040d1070620000f0b0303485c000150040c90100b11032020017600843c3e402004440030601c070344a081012a2105240f541d401480e2058914501111641240d041072082c1901 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 264489739 1250 264488489 264488503
    0x8100b0d03020c091003020405040506060f01020106030305040510090518010305060c091f050f1218030708040303081b0304050307050d020d09060309170a17061503060913080a0c05 79
    0x36590200103940ca5940252501c8183d07650603c14240500800c54201050070b00101850303000c0d1040200b81071509001e66030781d0045409511801c1001c42014103544180038079403c5991549038581050304110802059058064805081003006440025190f5a00d658018469040c503890020343d41581421030074244001c01d0140d5505041020b414251120801c117650b103d029808507181d1480081c0c100c5062242e92092240c00d00003141043c070300d0b032814003100d020b0301d411403032404d0303000c0801200da80702d00a03d400034007281400d00041021074060841d1a90201c9408807917100e00241c0200606a504103403400d683c039600104006081202c00c000b04488000140010704001c14800170050024245008080c10151100c0e540c0c410400440c1d00c1d482c11360b428403c015103c10350308070018100d0440c03440d05071014000d0004100281442d12702080c107801d44104d01840c2d9a6a074050100300040500091010150014000301145052018011a22050356040e1002d00701e41085464035013 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 264490989 1250 264489739 264489761
    0x180b13061203032d02090111060106020c03060a0507090b130509070c02180c09010c031808150a05070f05070f0f060b0f03030f092710090608010e21090a0810 69
    0x4420070703143c000c1e0440301c8240384c0c1c07100d004100540e1714101c090040314200030345440783da503500c2210008034039150040340034051000d055007100e0300c40d170361101010305940013500c6100214125881c24043d48020100801140c4001400786400c5551280449e900e0a011105600001c01d1007801c0d108614200500c1c181e0600401b00800f4141000c000307044846c4908001d050505c403c100c060b10400d03018410310200e0403040000141050796030292203450390700c3c210705040c2114040e1f000034a0342d400c900c2441c0c0501101c0d62050316480e54500160340b16440070307109846001e5240c01c0c200000340b140d80c8100406104c0c0c08003050107034088090240c02d511401c4030620941041c0321204543c0c0030f0805903410400110f890712841200316024903d5280d140001c403014070980001c005880c034a15260000b243c905000810580e640d500781a42240c80c0b111104060340c1103c0030402d0350030100744504200d402a0b0540d603182c0f25441c00040c5811000b03502014240d000101d1320034052046101d0034000d05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 264492239 1250 264490989 264491021
    0x22401090f0b090a020d0b0306180f03041d040c080303090f070f05151e0c0a03082d0c190903060509030a0c080f09120309030c0a180b1306120303 64
    0x140390000003020684014900b07a00b445c1d01160b415104030403900903024401d009016140305062603010380c04030300b2100b02500718601c05c035081d03440d030320400004031030403202441844c00c1440d10544c403e40702a00301030026202c00200301c90100c0c007a1424402140940c0c02440245004054404140c0c10045940d010115070445480108100e40b100c1829052698540c1c1132507a035031640c0c00c60404058505403032507650b00740215650100d9800040c0c10303041b090203a04c40c0320640d5100310b9512040ba516003291712550518101075038070441c80c200065001151600041d040c80d01c1c0018203510f110580c0c04042c001a000982042400800d02c01c107600000007401540c905040703460f02415405583c007004040140015681d100040c440003910702142d002010010716000c9280c00b075a03641c103e043d225100b4061040009201d01d811603c5404844100c681c20078190100402c000003442c3c8092007580000c000b05401c4412640c1e031050300058400c40400103105041030030010304640f0061000070b021 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 264493489 1250 264492239 264492251
    0xc091d010e1e0715080f0903031b090406051906110c010e010c08040902280e01021e190b09070b130e0a0212190b0103110712022401090f 60
    0x10700d1010a5403560b04086030b0b1445200784140b80c56914244196100c0c072401009943c03c421402d90008145000f100565611004c60300d9030401c158030303488140c0c0c0140750041c0d141e00514010320b080d030140c00103240007000000c2d1540c0d90340c0455508a030511590120068183c41800101d40190a4400b682d85680080924800070383c00640700100c0080600d0500036030f25000301c1080440c0045a01a05a02c681591981c000003003520540c08094800382d405071240c0740d0001040d03c1242c40701030740c074016402041c400c10122005000300643c8419400e480c000c044541c01803000c1540c1c038285461041d0348000b5949030801070b03d410132410703402c040440ca8007000201e0211403805100005e840b00746004442036101e00143e00300038811101c80008510b13821042119182800c4440600072024640600035202e14034011002c40b40301c02c42e015407100041c041403000c15941001c04943c18498012644000d00d1201907119101c400000e00c40d00130b07603020040c00b444207103026076003146410107014080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 264494739 1250 264493489 264493511
    0x210031b1803030513030602040b1b1b09090a06050408032d0103121b030c02040f060509130305040b130501031835070f110d0b0c090402070c091d01 65
    0x7101481d10015040000101c1d1a003e0502d5842d00c500080d0b0f032100e0115510781e076596600b0440d130000b98901500840f06040c3c21014400800d2000012542d9140c02d100348042004103c020300e03001e0702d40400d0380b04075074414001411511803503002d41e0003410141e469150989080b403c20075544140400c0034400c0e0706070040a8404080c0c141941e070f210400410354540c140301200e20440c2c1c480e5940c8401d0702c1000120074560010740b266400d500035501072107060191560304054620500c2003d03001903072400045c4042604200341c070070080c8a440c04618155903000c3e604c3d6684c024005020f03884528031b1040006680611411085c0f170782c40f80002c50f003590291102002141030b00c142034111030001204510368840f04c0e0700e100d04241081026915001c0604041b281040900710888001c0d00c0034460203100c0c64000c40001c1082c0e4806594480366031021944a540e800100e40550450380a100602c0019540a040c00180226900004030b054602c101c00346642804030b182c10a0b03034501440110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 264495989 1250 264494739 264494777
    0xf0f0a150f0e090f0d0c031716020601090e030403110a091e0b04090807020f0103062402061f060c0f0b0a0507080604091101110307061103100f0605070b130210031b 72
    0x30005d5603040800e4070384601c0c103096503040c04d090306400401d40350400300207440c4541c02000c2a55100c1e6401c607840c5030f0321450184110f450300b020b25440c5d60f01c14041000040c0d150203d03100e49000180c000c40c00c4640c1c815520090f1101c8440e102c00c901d0b003900d004404241d20b403080d0300e1254411034081c0905940364907074030001e01c00c004000c1d0045d01e110b0841130b0340d17901079003040004240c40300003c035080c030f00850343e080710404500700e00e0018002c9002194070320300c80f0344620208900040741000c226290003400d41d40500c00840440f0a040302c1028000851104e02c0c24038410005820045001e1801410040072218000c2c80311748a20300c0c219016000c6189070151810000007170034403150641301112260b20354010480002e213840e0034006000c0c07030086c5e40401380d4000e0b0880007d01e4105511040c04c000b03002250300030300001034410b100ca0004694410321498106080c64000740210304650040380194622281001c0480e07107825044880076600280c03c2c40a5080386040a40610100d1a00c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 264497239 1250 264495989 264496003
    0x1412010308070f0b07020105160c1505090f01020a090f0501020619020903070305030f0706140103050a030509040e0d09031b0b0301090507030e0f0606010905090f0f0a150f0e090f 78
    0x80d01001000c82d14404010303400d05410034154101c00400d04a02d01200f0090107800d0480360050708040e0340c111a40e25500600c40307085060b9002107030480c1c06880080c45d2009000040c440c05140c401c4240000b141c0c94288001c2c0120565590f4100185080030740f840c803e009550300817411580010304211100030010480840400050f03c0907a98803082c60010740b408540e600058114040080c0d1340c03500044d074000a04141344103800c00e00c034000600b18801d003142c000348005071041d005809403a00080c4580010413001714010800611a840294954900801000c0c0d281c04280000700600a0084e05242c020f101c00c03281c040400640d00b42400c104481c041885640307241611840881c40d010700a4000002c0701151104607105400b40c03205030b980d10341003900c1e5540440e42c001c0d804100d9081441c00d0520500c44103011004940b40c1e900c4802c82040300030281c00106035a0903240c3e002c0b41182a114000340708500111500c40d040c101d01c680c810384050014140f6074081c02940000e180081600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 264498489 1250 264497239 264497243
    0x1b09060f0b030610050d14010314060717250305040303050604061401080901061d01151b0209070905040609060f09140103021e0301050106030203180105060109140a080d0201090314120103 82
    0x45000d600d040740003a1958000d00c90805086403c0841c451f41d103000004445040b41d008a0340000710100c3c0307412080d202c5a050300c060000950051032202e4007070440c2c40154210310a4403071042c40c2c0d007080089201001000e4103c00000e030700e440600c0181941800341541103407049404000c200e103449410752020628020079418400700c81c1c0040c06410f02903015400030282c4002801d40d020242c03120a0031101c0900501d61230041074040038003000d00c40c03075800b5011303000b114000801d041550204140060010180401c0100401703020419803140d0040d180185031028011541c06e0034070f20b0b111142c050310341201d584146405280c040210740122503904580c4c0549040d03004049005044400b0043c03100001d40540c02c000c00040c0c0c2c5a4154000c611886070928009105240304809900f80c4205544103400030b50b01030000e000c0c80000e038005000d0520002c0c0f90000740b82e6500c6115041800310003400000d81d54a0f00755400741600007581880b42c0482e0841e0070b2600c0810655100015018000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 264499739 1250 264498489 264498499
    0x305180601320303030709050901060f0504030605181c0f0203030402060d020a050409060b040e0c0c07180f09120e0916030c0302070219031e032a1b09060f0b0306 71
    0x6081e090054400512040700c2d4050103403940c9207070039800036104100300d02c82c070303802000a08000111b040c800c0704070b4490440d1a6035050714003440c64950314085c0001a12a280800c21807052506040081019403043d1050700f0020101d0000c03040042c044010012141d0705540040080000595440c000c480704150b00603001a2a2082c941c011a00c1d030013540c201608441c40d18402042a008000180c81101e44020192580340c2e00c0c0d03074604c01c0f540500382e0a001c065100300341c280020014403008003903030400c043c1d000402078218074803402035034001e100c20303105402c0c944a0100f5071a401440860400704c260780c00e0400741000140035a08a46c04108541059682c84100c100f685c82501254681c940003403400501801c140701044200e0f00c00d11046a5070381000d080d00610000c0c051020703403695019150000c8841e03050100094180c00c800d107000108694600c64000511550f8108043c40c00c0502503d10b00c6d0700340842c0c10704803020798100a40e0802c2510080050b5030300302e8200e940c08441036030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 264500989 1250 264499739 264499799
    0x40302011d030d06060f020c1318081324030c0c0b0c0315123f030f06041b0e04060b030115021209011b050703120305180601 55
    0x14100c0c01408240700414400c1d4010364099480d0800101034148804680010854169200015500440000d0020000d60030150f55070b6524a4022410b4021900052020a17030300340d82c141c10b03042c04082c841d0890383c40001203407a1581c550035481d10070140070003814111200781c1006060341c4960b05502c2160400d5140c0e4140e000e001c0c030481c258503080f540251a142d060400404550040c0c0040f980132010344080005a9040e107400340d0040c0007000200054807103c600c0030320101c1c0c0418942195244030302241c4d072403080303400d00a81d03044451040da50f2407a101c0c100980c44440340180906602e120300c1c10940c00807100b03000f00d00d44041409a40c100b81001d19541d034003203005015a980685445003020000140700d602c186824010019154203680c450402d60707040d0010350040c2991540000d40c00312070041400180d0004400041c000e070100d990042da03940c0c801c0003240c041e1180b030700040e444505000001090696245442400c84060f009940c1444a0211007801c0d00120410881c1c001d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 264502239 1250 264500989 264500993
    0xf05130207080a0c110d120518132408030a110c0d0501050601090b2d0c01020c0a0218060f0603070512013c030201030f0b04090605090607020a03020604020904 70
    0x3030304490030980c0c40798002d81c03103200740388020b4501c2010032402d8070450740701030650200740381c03002c48901081c0c4c0c480c5072107001c04001c0008458030740006006040b00c1d04184101140780e510450f80c5029a9803044002c12410728054501c04144003822a0000702840d055040c07200385400b0045c1d1b203010b5000e1408008084070018000d14145140160b50f4124442c0743d80502800819005644034100030380702d0141c455035402c0004228441c4d4145000e60b01c2070000149040c0c080c4240d050800c2c410300070031508000130004058220b0f80300ca1044182c0d507000c0070400046003001190724440d0f0300810203800c007625000c070119500d0064032500f240b20300000400500c119028006942d2010421051480f2940c2c451510150300c2040940e80c0705201440090200000c44170405c0c20f056111110031100382074555401540600084403800300040c5c2c441075444600e4641d0f00c202000207009440105141c18810400d509280d0003900780304c02c54210003075400c0426000101540c2065058031020040d6482d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 264503489 1250 264502239 264502241
    0x504020607230601170312040203120c101505130b0121050405010b06190c0c030b150f060307050703050304020f0603131a040308011503140c04031403040f0513 70
    0x3180080003080800c00e80c01082c09032100c62042e15105000b241e005980310b0180c00d50120444400315440e52080105606101040c0f44140d003051018049901d8803044010213501e40d000300c00c040020f6170040284855070f950340d004140c1d55014032400054054105800700c0c0c680341145603481e14040d00c1d042c41100c01d900c0340c40c449440c0711401010a02e15106464508040d21068800391442e60800380d060a0f589803040480b45203c0c4c8403071207401c0025a0703440564400e00c24042c02d555885007290000042850102d426103c0c01c104540188680300940800c0b004201d0906014020042441000110303034018080710202509408e010f92a41e8592000940750003400326038540010000c010302c0410002c28041045031741c41002e000c035600c101002c590456036011107000d00010510801000500c0e0982d104a0281c1c8031703841c010441009800c1444650340c4103941107401e81c000000c0c20070034080310b406006c00c05480d01c07018501d040e160014054400c10305008546c484c1d041a004c00b0140c82c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 264504739 1250 264503489 264503497
    0xc1605013f0f02040906241b06020a0e01020607020601032406080708031c0b030d120f11091008060607080a0909050c0702130209030a080901030b090f070f0f0c020405040206 76
    0x91030800e100c8024192101c1000c0d4000d48103400f007080c10000081090b8110b03807a600b00450344d107102407d03100c003001030803521002007000c00e90460040d007484801194103800140941e80d042e850704d070225001e5400081c5400001020302085401a40c01400065805210842e800541380304882e584482140004028801680094141d101b8520700145541012004d0b090b100c0350150302d910564141303c1000706880a072150035925070082c902d440d1245000d40302e4a1041d4a40c0714002828014240d0094222049119904004000481c2210309454112903409000c1a04e01d040c2003141000e101080d503078007400c400182184000300e841843d8600c9805140e00425a490040c49a0304007200010344541c05604103a018207034141d0a1110724170140201c410380c00380500100200c01d8070740c40d81121600868011070425488810f42d03492a84d4040c0c050b030065150070b1040c402c5091611019041a8121007000c05201c02d0f103001c1c1c000180c205a5941001760107543c08079441d9250300c0011b4183c41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 264505989 1250 264504739 264504857
    0x905090c040e06010512070b0702010507081909090c02030c06010b0c0a0c0f0317030c0d0e030906070b09010507031503121e0c0b33030a080c160501 65
    0x464580b0640b5800b40014003039048030710950310000c14002410b06d064030f408040c050201d0300b4100304040c20040d441040104070641c0a00780c0103003464504400c2a043c095840c8881000a801c0030081c07245035064482c0c41d0901070680019480d00051110300c41c0c556005118600002c1808104460014001e01060320010341c08219440c11548451044070708128900042d03602c80e040c15800c0c04180300311812a0f02a000201c5d0260820400c0b51444004e802c0e403410301c0042e4001800091695100e40d001380c500e0510a2081c1007440c60710214030b6007103aa00420348401c00d41000d040080341d800440300381040c0c98100b203c41c04000c605c40c83c10b580b20a45400c900120f8403441e00000e9500384e10481c0c40c241141b0a00c202055a03d91074049e484c1010b0000b035841000c540092030303902008025503030300c64010001d01962800d07245601d41400c140c106801c01d07541d68002c0d8460030180200e20705520007074002400d05641ca01d602400d46003855905041441c60a03049011007108640c10100c10b4000d41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 264507239 1250 264505989 264505991
    0xc0310030602221e0504060f18060302100e120111040314012406081b03010b0c07030b040c1809030806120f060403120c05160206030403140304121d0a0905090c04 71
    0x7590f101d8107003282e801140f0240c07513038000900f8041102c1c80c00d40620000c89040b000414040c606014003208209511040708202c144c3c4d4580c00001030700c1c2c12012520001943e2200103162485206000c600070080b442a00035074500310140403114142e000b99000c0e01c1d003101c04800c1070030f000307040d440c010311908460084220100c1522108903111246240940c0e0301a51446010f0b01c900c8408038441c1031100c1d4039840010107000500411000c0c00c042d01c0101e05400031108001d40d00c1e00e40144242050382c094a0365900f050050210441032800c66100101c0000c0420110416440080090b000500390510801c000010606160400c100c400c400041c1203041d13070070b142414900901485c581c00c4001c030405040102c203051803401603082da2801075000240021819282e42088043e0b88001c00807024000b803680d1500c03100c2084006548a5031085c4001040007141d080b01034090384001c00040d10141c5012020781250300c60210305000c0718103450010800351a001c00050803d020000016001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 264508489 1250 264507239 264507307
    0x40e010305030301051305070207030213090804090b190602060103110a032406080703020303030417040812040303140a0e0d03110d2607020a12120e060f0c0310030602 73
    0x40700d0080021412a1002c940311080031096082c0c0380207841080343d0b04005600302c1a020409402c100501c25040c0b1605140015900c00b04c0c1c0c0d40c100590015081081d24a540da4440c030f5490501100c3c0c601c0c0b02510192002c80c0503e0700304020340d11304050000070000c284036815445103403606920302000d5507110b50f1548034100341014807203820800140d41d0001a091200c006041840803503243c0c00d50b600980610b2640e0b03031b9615905221981610340880314007081200288030502072007071214440c8c2c074000882d41c6a1850800810344951100c00c0d6100c1d4000300003061206420840c42c40380e03a18240c0b40341d584000300742020703031301445416404215070042d01c40c4201100c0e441032030b00080e1005001d101c001420f00c540d18107180c000840380c0718050391044220704041030100070280320740c541c42e01d04000c99825820380300c8180c8a00340c01110140d4412021b201001d85c142c0c500503488514800c481741580f50403049982c0803070f400d1001812a40d80069a485120344031a210005c0100300703900c4a40c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 264509739 1250 264508489 264508493
    0x1202040303020a0c173c0304080709050c0703120609021602090c0315010507051f02071e2d08120601020f0d02030a0e220c12060305060a0908040e0103 66
    0xe0303c202100480302c40011503c003048040003c004000f074180030340000c200c1340729410304a102c848400c403000009141d5400d42907424400ea80034003a560ba0f640c00156486500c0c1c01800f901e000000d800c5156182d0400080161100101040d01c84198141c5802d00030030200109080081159811034850580000359480003070b00d4034000d13250440d2081e40c850b259641d90001d001014007042e40c1c90390050a0800550034150300c140c1c0642011400f42c03090311440110030710003e50302c03052000010007098002c1180d200388648104030b9591900c5030481010600e01e281d0b01d22184003c00407452030300b00c1451480700c9081d001492114001c6a010b815965591038126448180050880b040750052050500d00141000003045000460003140c00840c18290f000c4025036183c9811024140c0052464a110320165414640140f11002d404000134880d141ca40d8010091101408140000b50400e403041001034400520710f43d1294441c100040d001d02a8a09984948a1030b0320542e1605442800801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 264510989 1250 264509739 264509743
    0xc0d0221070f0c020a05010e060d05130c06020c0d061109120a0b010b040b07020904030c080307030f0b15030a0e0705060408071404110d0c02030d0f0608150c0a0f120204030302 77
    0x1001e007449448240c5119100d10003103c60b80b0100e07100035004614401d042103554004c200c203c3d80c2d100300516503420420490002c0c1c04071807007200c4030407429400c010362105004401c81120040c101c248040e050203000240071a040c1c01c41414000c100f103a44000441c81c00c005101540d00c03148004127549003550103404010342c0d40341580000ea032038042d030000014624100a01304d900312110b402049040c007040303400304848200000c0c416000d0004c0105d0034400184014001c500c950381c60348001a04031404001002124800c090442c046d61145c0b65200704015800e041d2a8072a2040038041510b610061186050551540c40550070400c0406c02040e801c0000c240a0107490200ea1140304103036059017044161032110340c060705c800b07030100261640e480301504546100005401141c0ca000c4904041008a410040c031940405130380d98424090814103004020a100071080741c811a400c1c41074800d582d80c403481d8411001d00401154100246004407140110382c81c017684119103980c0c0e01e040c042c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 264512239 1250 264510989 264510991
    0x40b030c0907050c1516020f07060f0309060f0e15240d02060a052206090302011d0603090a02040609020a0512040c03061416110607050d0209040518060a0209090c0d0221 74
    0xd151001110426800280b001948080c9000301d4001809c2e01880e200007070b81c00100740710242d400c1689400c0c10801103440c1c0e001e0140006128100040c0006103503003820308001481910324200040c020038004425035801550000702c040c070440c1e2010103400400613202640000000390030140200391005565045001f07444482c42443c0c4100c06400c0e00b4040441c400007500030640450000c100c20b1015500c1440c01c04d889500302607c24000003103101c002405500100d9180b0148c0d80b10114500c01c40c141401850014410f4030029810032145007000350140c02040040c880790030400c0005003d010001c08048002c40c3c0211081090782182200c840c0b00322000c0740d1700e010b42d4940701d580c84603ca2013120311840c0c821188002c1c044035200c003142141d850b4480102402081e800703120125095a4921030715000d52000c0c03a40d01d605000c2c448010b400c00b54002c0021a200f0b10500103d24031340c031a070700314a82c40003404e030242d40c2d078070002e1801a0090141c00c0c0c1009111079141d06030812503404403003035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 264513489 1250 264512239 264512251
    0x40905010b07020a06020c0310020307030f050108010606020d09050a03060b0310050901020d0e1f0b01140c070303030c05030c040b0306010c0515060112112d0c1b040b030c0907050c15 80
    0x3204000e49a44007642e4450700c1c603190070b4040c0d1002e00272604841c001d5000d9a0081c0c514940800c0000d0080c2418040d1042a0007541103a5500c10040000b03540400c91400200310b02c2c146000c000703140c940011007100540c4005441d1588401c01100c040c2d90a115540c04002d10403410805824070b104050f00079005280c4640780d40c6e1034480c00b40d0444400040c2c8405508001c800b0145140744400071002400c06c00e07040701d0512100490081c00c1e03e05110282003a03101083c01040310502c3c0d41401825100300344d00c04020b010b010000d202e05461004100d40c15152030b940c1e0700307981c0d403103202c01202c00c05000f10b0003030121700407246c9002c4001540c540e868001e08090365454100300500c234101084480020480f82082c03010010580000c1d0303858545210306000201490412811801c401090741c40704011031880e8218560312940c0c180410010302101c0d5066604111040c044404256501811034a180c403c0040c0301c0080c44807841079041319101d03007050007980da40f10025030f010403e002040e00c41e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 264514739 1250 264513489 264513499
    0x7020d2006040e190608070306020d0f0203010b07120e120d0305060303090303160f022e0207140d020a080d092621071a010923071103040905010b0702 66
    0xc0c0405860503038182c0e0107a902c040040d90b0720781c64200c0700441d03801840d028003200c2512401c00290703481041c0580802940211400342e51208417044200440301c0b42440090024414001400146001425074241c103900007a00c2105c0c1e01d9129064441000c864034843c2c0c40254040540070300680480c0c803040918054806005944420040648a005104006806600c10700820042098000b000c82c0350078028003444d0580c00c01030f0080341d03210340103850b510800030712800d070640311440d440c02c2c0c1d07002d9082502c050031001d810441d00a1001c0b6203000003a1280441d24040015541c84042c064000d20051086070940490030401800c14482403203400c014440c5c464800d0006065060b011140c513800102801c050b0041d0861040074003240c2800300b00f00e61040c000100022211034142c40c1c4080c860008402075850271641100b0f50f04001c00c3c0000210410240d0f101301c0300560030306134001d401814407042c1d1105606146155011302c0d80524550340c1803c0002800c5103417840149020390095238 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 264515989 1250 264514739 264514793
    0x6021201030c030308341101051e09060c0301060509131a0a050108040b0103021c060221071701050609010c05060c12010b18090717090c1f05040b0d0207020d 69
    0x210340c48418494030303443c01885c1180090002c2100000f8031030044000d00e04101f004d040301c00e5040c030b08691084699101c0300c811144a494804034500f00c650f4000e0841c0c2c000d05643c900403003590840d01041c45058113010011903855003036070340c1d101264107000c06d00303030208086c02c00340c10441d0100c0740314030903540500c528000109095100d142c5840c070407900070040d50b0381a480c640c2809072004400c00d0003a440d903401e82e0104c0020303140e40001c00c10074400035203042e03d04c03a90441504031081c020703103603001b800f400903400102c170040c004c8600c0c1150400c880c2c003500c0f0341421005035401c42003004003c081d4010001002442e599542c05002c1300d249400d00f0b200c8980c3c907400044514800c1d131941c94203240b428043c824603403402c0c1d401c180e809107840c9400c980051028184142204090f6045903803504501c000314110b0810f11211281140701c000d0000c03e042480300c004c0c040d442240a0054090000110009002c9050301115010b55010b4001004481c140c1401c410344075110781700000f0451908 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 264517239 1250 264515989 264516001
    0x3051503010c0e1216120519051e030408010f020c0f070e04061a040e010b191a03040c08120703020c03060f011e08011109120601150c06021201030c030308 68
    0x442032070b0206002e525a0311005114104001240041070a68006881030824080e40070301d054103001c2c0240840c24101c6a41400381ca40301c2d05100e4a03a06d54540511300c2d1502a01103080050307001611800007420810303284960400724214412500075100960801002e06252005a8020080e03000c1880a8031002c0e5459580d0039220f418074400c01c0c0710720401002040c040b9540d07a100700341441c6c40ca00042010400c1a0100301640c044808910700d5954448041402c4d0034226650000b4165480c01903040b40e0910340001c00000a0860350380c0743c49c030084005802c020704080b039140a800c180d0102c3c0c7e8140c25528500042d0343c41540c0840050240c03207151100303402c0001d460350080d030f400e5070700e08100e0303081034480c00352018524400c1c00b030f150110030000780c403000030310441c4a468402c020240c0d40d0f80101d0b0a00c020b00c40704140d001001d0b031040700108080350b0703014540d0a02000c0b0b840c0a0030354031168103001001c1c2c0140004007801c46049000002044146030040080340e20030381b41c0d450720340d480b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 264518489 1250 264517239 264517241
    0x9140d02120a08011802070c0e010510110d050a020c0303031f090e03090d020118090f1a060a0c0c0e1e01081516020304081006051206091b0a03020306070305150301 72
    0x2c21410115001c40010711415007200c00501d11100385910050038041180c031066071a60725a8010000881444014419030401c02404214580182005042d03008481c6000b5035504031400c44c50708000d0081403034880a0303c28440015000c0000301142e4907810006845984418001c0900880100001e00000c100b030f05401100c5075600c1440107541807a41c11003d01604209280080303040095580c04400f94091081c4128042e240c242000964611040c44880845081c16100540046074142e442c049964801c112000e0f07030558544440c40f00d8143c9404c62500103da002074a0400c0c0701c170104503800e03a04c1c0e1000d4084541c0038504041c1c0d641e846001e1521510b80210002a4100650018013194140300b8039914211752441140e1900e559101c0c1642000c2c0c03444108000c06440e40001c115500e0440e4010140080721405440c05051048500b9920390760701c0882542007044c00020090b40d560312829400542d0080c0c155281407070030f5400180206810bc0e480c0c41c82d80004640c1e0b110324141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 264519739 1250 264518489 264518497
    0x507080603161a0928120b010b0a030905070b07031206030201020a0f080d020c01050402040b010e0102070e04060209150c0105100b09060310080102040b1801020c010504090f09140d0212 81
    0x456060201d41c10a50240e03040d06440d15044252081000014519100c0c514030002c1e242100d1840100c800380645d05600415107980884040344400c41d000012422000311103045440304d1300c6199131810451020303001703408403950162507401042400070700760760a4801004030602c66a80d0a98283c98a4010001c803242c0e400042d006078048212600000d545c1f01d092145903000319071450600c005516600141d81c000001c02a069440b02c007400110705080c00380004880702420b00031720504e62400000d5658603180301d40c2c5034000c0fa6101040a00900d9411209844e0015080d014a100d5286900c0141e078082507184206600e0040090442182003000c00203850b0070402c614070744030342d0508001c2a500003030041a42da01c800c40380050050001d10040008001c50100c40d0385415034200807006011000c407400e13040d07402c06c4640628580e80b18003101c0c10303640c4d0301c44001000280c08881c500203181c444030042020f6207140110a402c0340014031415050440d40c00c80b4696103075000084501d0007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 264520989 1250 264519739 264519763
    0x5030c0d020313080d060611010c083405091e060a0c0305040905040c0302090903040609090c030e01060b0d0b0d0230030d1509020a0f050c1501090507080603 69
    0x42444203a4a06036103400558100e480355188100d50710311501c0d5544507074029603800d9245652a60200412030300718107010075140c140c1008200c20715a07800c024001c084014200728800c580544280b00c00d11034011090322403898443d10189000d860b08026102b03038880441c1602c60146080a125940b41c850158411100054403460030042c102a041d940508802c2084080c440103000220b1030a40c1441031a101d20f0148507406101442c5006000a50902402d40c0d44207800400050090507001f4640c0d00440d00b041100203920003811034110020a43d142800b0029400e00b40005848024040902500b0444560401074126000e003004450110000029000a03112000600d2401603008044a010040c580b4007000030550041904540c0200c070140764060f500c0c00c24050382c850151004010f0000600d0031403078005200b4001c0c2c03070800204500c204100001501d90710104050080c461341140f609140c01c1076585602c1e600c8041c00d01160320200090403080003400d517103000078441d11010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 264522239 1250 264520989 264521011
    0x31a130c0902030a02210402150403050705101e0206040203010c0306081213050d0501022101240e03010e0a060506030601060c140c0d0f02030c011814030106090c0903060c0503 77
    0x345401d244101942000300601100c650034000101010403004e1241c40c01c0e41c0340000d041c040d01d80340c81005a480580e1013142030303070102488240002240001d0315000d40e01c5c1100c0c90b82c50306801e400111905184000c1400048007501d4140702004d030001503041c0124803c400a00c00c02c02885002c4085401303900c58080d0791390040d11061052007543c0010840d5070b0b210704805142030707255070100d234400c0d6215108540a0b0350000c1c00c1c4801d40100c03281036600011008002c031042d490301900210385598021303900d004070900e413101e081a40c080d034100ca01e86c1101800a11a58150850680d200c3c000350200342e414038100f0780054134501e4046010340c1a86d0885d26400311080381516091900406030b116035040b0b11074500c010000d0750300c059500f15440d21448559a1081c2e50344189824943c1c6005e0352070501034030181064032074a17607600322804e9a2010140e03d40105503800000d000d000550321030340480c0e10b800b206c10019940075078001e080d6806030000340200c15991781c0c03c0b0703030300c0c0f104840e116010307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 264523489 1250 264522239 264522263
    0x4020307050d0b0d05011419060303090314151906090605060301270501030b180111030604020d060e090106150c0201020c0d0219090c030c05090307140d0c031a13 71
    0x800306074040000d209000d40020018180c4e40e4941d0b0031210010b06410741007070300f081003044421807032440000e00e040c6003a0034400c0b149165406441e10b80d4500004000d0501340342600004a02000094484041d0307030310300040c0d824244814207826100d0f040080c0b035203040041c041209681c42c09100203c400150819156030f280a008111031121a110007080c8072004a00720b8514142c0e01500d030180d03002e40f9226106017081800b2423521504403038040100e90500345a040c00c40350580540b0303480b00082d90050303680d0341c042c003660000b00304903004045041c1000d828044035020540c0305000345c5091100340304c80000a01400d90b04519020360090050740002410302c554141201c00000c1c4a02c0078060300321000c052041540c0d5442e450304004402e56445560703104c5c9580c58010070b1042d1040c2d04289203000c48040200352035490380d016040d0b185080c0040600c0d1a2125007942089a811501207640991a403410046403080c0c0103400101c0d0208501064802e00000010001c80d50300c0f01d519904 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 264524739 1250 264523489 264523507
    0xb010305060306010b1e0c07090b010314040b090723040e0610050409030e06280e0a030b180d050307030b060307020607080c0c0a0503040302090a0b0a1403030d02120609060402030705 80
    0x9038051018a1b20b4203038503002c481003621a40b00500900c8080f84040e000507030411200303108403000000181d04050030141c0301d002450b00320b0b84954000e900040c60180c1655030034a09840c109156211903844000c9034110720322008041441d0300600c03421203041c401103401c0c0c0f40c115a207010540780030528a100e80020402490b142c1d0011042e0751007820b0090019001c1000200c468001600a40703824403114502c10311800c1c42d04203034080842c54100250304040001c0480c03204211400300910030304c0d8401c08604140280c04d40c1c8114035100004a4602c0c420b90000203010350826038045000c02c1c10008620103074603003d801d0b644100307480e500034800380e550310004450b4958080c184030320303081080041c04161b2038248081c001950258004503a91782ca14410b000c2001c0006000b1a007281c5001c030b800c007181d910300218204a038005684001580b13000700c00203086105101070300040910020300030030034407004101203125174000c035001d04807542d43c1001e02c001d0784000c440200004004100c03000c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 264525989 1250 264524739 264524759
    0x11070c091121060d06050f0f010608070c1506030c031b0509150603150312071401050103081207020c060415080601020f03030601140702031608060108030c07030b040f0506070302030106030b01030506030601 90
    0x340c440c0c3e000340101060240c42d165001114802c0d6140f41800c00c84a0402c01c285101d031002e580104982d01d02004035107800c650080009441410042004031686600280700c0e4083c0c002e036000e10b03040b640d450340040c6e0f00e02d0094007148070702143c5034004094a800007143d20b00519030910501110300c00c0e04c00c0d02242c9040207150341c00141100e078800001c14010311180c804100041d140400c10050a968003003c1c1442803809500740c214800681c100001840012480c1080d646589944101304003541c442d070209a06240500c80019004030003c6800211410603500c00c56441c2155101c0d0ba586032582c000490301e0301c85540954000b0741c010408900300b9403040d640104000755000107a410520540e000038101079610065001c0b28140f410306111060f8180203060040400340c00940c5010084841d407502c40f0300b684406801c210308080004c0a210156941d0803000c3c4d8410280d0308145082d11000d0300a400078050318002030302c0e22200d180b01c6c0d4000e20419000b403000900074a000c0e840d044a0407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 264527239 1250 264525989 264525991
    0x905010f27030507120812190e031305040905030f0f0d29060a210b04050c0405030705030304060c0b1008030c0f0601050d02030307060902011809050114010918050a11070c091121 78
    0x40e0000181e0000000b40c7e40d413140b0036a032722030000950ba540c0408070021b440300e8030503003205106518200100700001c0c0b0000c2101c000d08183c001094860400011803011405541c80054034181003030200d8260b041701c403840044100c15105500c096661003810702c0a54000c03401103801185420f103c4085021b44080b01703480c5a800c051000c1a00c1120340042001d42d0303401d4400c0c601034480402c05000070714050000c00041c007000c1e00118103051030040000c0c182c46d02500b000c0e05544400c00480c080d40c543c60b9101c4068844035084030b6440440c101d96a070348400d040c81070308031405401d001203190310b0300c070042c0580ca03900180154200380c2552141d00081822402c100d05101c241c0602e00042c0d120750070140300800e2031000010301c41d0b15210a60f0403004014181030304101c01c103001403110000d030f401103081c840040200040c0070741e01c07109944020804160340a49000f4003180190070064180c0001e000d645403544c0500c00000006054000350181c0d0009041e20004c0d14204070380308181c407543d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 264528489 1250 264527239 264527251
    0x9060804140709020703110d02010b09161b050d1404050a09051509010e0f010915170a0c0906080c0609030a0813120c050102010b0d02010905010f27030507120812 71
    0x520105a030783e1100328203c0c0d0085000b1400b080c945410115420010300104042e1041800240082c0c9910fa000901d825001070a6007000360241c94440c240510070314103074200401118148000d030909081060743d9100304201c0b040003031076003120702c10601314500a40741240c0014140340055130a00352403001403c00282b206001c814070a9044400799500000f01d4001d1201c8920302c440c0b4106285416a0307040305801214865040c00d501d88040c903401402e69080310300d00942c110154000c04040c0703080c5040040301422503100341c103010820311020340c064421a00e0007004c5481602c881c405000349401880c00ca654503402c040d01072800f0134203140040c160358400040e00c2c6025a251444004130001640302521007090502d403c0c002940c0901c149100c1c090304446d51030b40d42c081580024a10150b60040c01e04014002c0c0454200a0060802c81c1000b040658441118580701c11015104003036440191043e100306003000411029040034808415003000030a03181512880c410038070f0358806818 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 264529739 1250 264528489 264528493
    0x190302010f0203010306141b1b0a060c03050610110a0602130f230d210e04090f171c0c050f030a0501030c0b0a021b0420030f01060906080414 62
    0x4010a071840d034801107000e18482c6900098005440b4145d0b0f00030400103049010440c20649910041b44060301524807904100c1e01d140300d0948508001401d01d861500000c21a90410f1000c102294144e000f40380700b050700303484401045460031001c0310303c6000c80010038642d0708042c0d403c40c08503401c0d8000340308200140507603a02482d56010a4500e0303a006521142c0b030701501c51000182040d41905071000c0d0300007100c8884400800d030b21501042c094448540807200d075140c03250b80e01c0900030702100180440007031040080c2d9641781481c8071003100e00c80d0215452859000b20a54100b0020142c4d03000610001444446003040301e03904004040a1540c907042c00001c1c040c5440c2941400011840f82e0b40d0418040f41c554918500740441a020350401c2018510a1010030002a40040d03d10744034090040f90740e44d407038190782c0071400802510328510707014420010710883c2484002c0040d8001d900b080d103201070580e03880310100c1d801c0c2001d01480000070590808103011840340084001003c0100d02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 264530989 1250 264529739 264529751
    0x30605070c030813032d120b011b05190501050f010611060103060b18010617160203090d0f06050403021c0c110105030709080d020109020118030b070c1110030509060709050319030201 80
    0x1440b071545200d0b040c0f0f106c10182c0c4c0f0b8042000502c0d0700c8000081200c8244c002800568680000600f68107071101a0b51002000c500101d420300c0810810300c0c101400f20007840340300e11850f0420034081c01c2d088a412110360312660001402c184645242c103080c88144020b030074664215503400e000351003030050cc00c1e405403002c50a030414005203ca220300800341e58070303080c43c1046000c3c108859104000c05a041100f90f80b00b850a1094012045890094040303d8082d82000070b072030140d448003003200028214074606400c00c010190001041d4401108002c0003000052607550101c6042410030402054107e400303001042550080d0302071900241c09052268030b80761503220b06031600d460311403100e0060f0344a001c000c007556086000da100c2400441181e00709181162120b0001440c050b0101c400c2000744007062050200c0c5800c10a22004002d0441d0018458560000c004d4141038804d03188901410b004280140d0103a43d1410440c0d0001d000382000140d40405c07103619034041c00007601555242c01d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 264532239 1250 264530989 264531017
    0x10903201807020d0c03091a0408010c0905011d0d0f0816200405010b0f0a020f03030405100b03030310050603060109050d0803040b010f062c0613030605070c03081303 73
    0xc204880080c0d0520411007403481c207204020700e0160221904001c3c480c00039504400709034090001c0d01510502800c001c406440c041ca4041141f09982c0044055482c00032600c04a552107100c02c004c8540c05d913100e0303003603d190804850b016018070804035030128417042558001001004182d000d80e004c1c40303566040c80e66080b48407a25500d494000c448003a000103806108081c0031004d00d43e1180d05450410440d81840d5000006105103000c90216080210310004075920802c81c003900d0b40310702c5094075140e041501d00141d407404200030800c40307141041055229400c000041e0f0344507004045440d2001807504042c05141c2c0d02c05001541003201c040004940b9403152150b505600344600c503a03560340d28045c1001003031080180c100043d0034040c083c0410800368000480700000c1c1c4504012010300d50030390303005c00352354445440e0f075a04904040344010b400a50b51603c0f108481c01401c1c10701c0142d40c2c40008548110043e40700801090b160300c04110b01200c01da205040e09071086c24a21a84040d00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 264533489 1250 264532239 264532249
    0xf09031401060509070315050405060a030507300506040b0711030703050c150915060103023a02030903040e1302150a1205011206090c0e1515040501090320 68
    0x3a9101085070345440c010070440c2000700403242d0006181c6000c20403481c030002100c5958416105452080381c84002080c4141d03182d1b1140001194440308591606558271806400c0100c00507102551803003d640d5000490000c680b00303880d951b4046d016000594513030f40c40e01c00c850000f50402c010058441041101580b00700001c01a490280d02c0340350301c0c0d000e03042e5164a841d0720342040240c4140313880140102c81000140e0300c00d40b581d180503a1841a0b4a00303004800038090b03072051500d1007422440340045015503020640e803081c904100303107034070784040b4040c981030b40b000b500c0303107a034541c81000100100d1000f2401d2903045441000200320311162030f0001480700c110188150404840001e00d8800c0380c0d0080e0a03108107405a0106000d69071404540e118110140003020303081c2c540743c4c1c00007800c1204000d0a1030240001c010701d5140750510b01940c5001e800b0710090180a81800c40310003107074000780000d0380e003141c40513514800c3c0d0905581e038000140015055121030240624070b420503545e21 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 264534739 1250 264533489 264533513
    0x30d0201020c0615030604020919050112021201091e0f0c080303011d040c0302090915010f081605060d150f140901140d030f2d0e010f0e010f0903 64
    0x16400580c444030703001c1440341005009018a8800402c1c070a400310503840c0480d400341d01580450b00010565501100003242c2e05584044036405490b0000205036140003030f0340380c600c49009035140d4820a6004842e01d080350a90b10020300f030072250320145078400c640545486010b62280307018000f41078855880100c503050580150980d60070203c0188125010b081c0304a0403102800a544030f2802d042d02c030144084068003000c2d002d90110400952080030800030308000711001301d0f050049680d078009802c280125070040c420140102210b80ea00f10320300d8111201a10340080c4690b2400540341980001041c4100054524001084c0c00265194150072400000d0105240030050442c0c0c3e00e0400c040210140c0000304400c20400c0710000b10f4640035891086a0b9050030450250582d020054408072002c48002180d022400d0229840711202030141e6206242615000701c0300e854100103607219543c44540c01c000a460300310500c1c1c2503125110140301c5d1001803d0007032885403652964004440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 264535989 1250 264534739 264534763
    0xa05091002190806010c080a1b1407170328020708030a030c020d0525080d1109030724030f2a080901020f0405090a061212020606010c020d150b03 64
    0x140b80007095582102107254840800d10345452206800e996111640c0522a1301c2c4080018075500c11070300c60911aa5240c6150304403198190704000802e0003551400d0a0098071984070a158100c500003200000346c5040e06206401440003000700b0903040c680124200b20b070400c6200706440002c074408103000a00d50304107113940105803190600c801030b1410385003800e40c408111b02004001e88200c4030004050b24010704440600c681603441c104400940542036603805c01074034080410205610400091002800580075a2010381e601d1740c11454102440180e80380d84800c002e801e0032903602c40d522008800852b07120004000c032041c48010842c48030000400b80d00c4170070b15070302840c10b43c0010820b2750040810707009600d0144144801c0805008030f1040d64080d41103000480e60141d89504000081c00d010980508003848a00704002c1c140d42603003c110250040c40c010070040e51040030048003443d0041c10102d03103d10165910082035402e1049590351998814074004165401d03c40c6a00447d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 264537239 1250 264535989 264536017
    0x4090f050a0308090a1e03090308040b07061802030a0213020c010912020f0111160f0b0c03041e050a0206090d0b010602030301080706080108070b03070212120a0c020309090a05091002 80
    0x22601c0c1c030b00648a8a80030348440c3d960381c4007044142c00504e00c500c03500311010200004000c0b8030040c0c039054660906582004107408004100804e4030300509000d01701040c018503050003500c0303501804d0003e9020102003e03402d03821032100400541064900c614048600105c0103191064010701103085910f0081b00716450503105020507246075041094500525480c4020072401e184880480d18510503000380c1206540041c00c1001030180750b1a000040301d401c5103400c1418681112105440d038400c560480d441216000a0881c951000c0089460070381d100c0014030840a81e42c003004825048270b280c043d40007540f0060a00004d0022144500030111500256140e5041070680c6050107042d0304010108208000104054100040e40c40115000d42925540e00c0d1036000c012410281e43d40c02002e4800000038210b040092000001c07442041050320401032041582012600e070300c5881040c592184080c000320b82d4003611903201c50341200343e079001c031000c144000e448030050780c102864441e041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 264538489 1250 264537239 264537253
    0x30f18011a01030506010503060a0614220614070c12080f0706050f060d0209040b0405031b0d03060e04210203040521061003080a0e0301090213090215090f040b04090f05 74
    0x365070540074660f0840007d08003e4250300c0e10f41d0110780041c14038407800701003010000d1400001c0a010003190742d0311954582131441c41c42840b039541240400b178840c403000030702070710801c0b003086102c041034a407603503845440481e06524010040700c42c40598002138441500130429202070140d100c0041410501c5805c0200300c500d401c003014400700c003006104a019404100d44000107135968048190300c00e5212480d03081d95141c50912034550300551031000c00020140f030400c14800b100060091401e040c9540503c441600d50800703c1d095841600d0090100aa204c0c014010358400303264602a00d4651040724101507468000a00e01003101005c1c40803281c0035880411030381c0040c00000d41c851680d1010441d03d034510b540d00b480c00d12480d1141000c00c0507022182207555001e400044803a50028004100391111004e031100508845508070320030141c0380c0f90860100e00a50581d0280c00006080007013209903c0701f404050445080c6595100b55035110200000d2080415100703000e0060b0014151 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 264539739 1250 264538489 264538541
    0x18030308040c08060105010219050c0414040b0a15060509040b0a06180902030f0708070309021306090c02160510020304090504080a110606060a0c140d1110020c03030f1801 75
    0x2d403810b10b0704015800e400001c01400640d800040d003040d607004c1306032a001c0c010201c0c101142000000748805500c14201115452400d01424140307016602404200320b4549031094040222122004604810300c20030804202c480e001c0d00141401c2c08020b000410300c40c9060700024041422500140c000c50b000b240821080c11a101c148009030043e450218618108842d0542c044040200300504000d41c550016803000d1180e0002864640e02500e0101140d224441802c042c00141c011428084e117000000c4050620010b20081c500d061010805442c50400007408000d1059052101c00c3d40b10400000034811451b12910b8031230b1340500038154451444402c0182000c0041041449591018007400900e946540859070f1002103824000c0c1410802e107030010850081002d61a2140240840500081e401c08502c8012400d4041501d4804020702c00b00c1e81203000d1220401d40640c003e0002404c000d51b5404c101d5040003851040911111100d80002d0030348440d0b41c0b544001704420001608 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 264540989 1250 264539739 264539753
    0x11404022b1d12090310020403111e1807091205010204140108070905100306030b0405070501141204080c0c030a030f020c01170f0a180f0c060302030705030708071803030804 76
    0x10342030601010704040a8102c0100b50380c4090401c07079200ca007400051034813140c3e5000c100101c04007000e01011741d01c56540c1c0c1400710141102c4d8250500801d440104c214002c1080460704136200802000e121500d06013055610011301c00915080c1131045100300410000301c400107141c0711600c90400175036500e040040801c05500c441070118180004c075014441c40780d0704080b002081c1c2d03100f5601031100b0460003104030050280f030707031020b0726800130a014802801800b04411058820131f032121362070300404402540203881400f2010007009009404100001c0d251401081c030707030940c0d908840100ca03e0f900000e08110010360100c01261400d1070700f0300c82540600c0b4034050f2490034200032210803642c108082c1d007035070300400c11400ca0115000280c1c4c1000e0f140d010415101682041c4003c048251810032512101d0759001d5540030701004001480903c00e0080380d22949050351814150303120300002b5901007d000d01801f00340014059501085644101c030900214040d0b0381d4a55035041c80e0030140b0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 264542239 1250 264540989 264541001
    0x2130305061008061923010b030603010605030708101d0f030a020106150c02010c0201020111130302011403070915090305030703080a0b0d05120f07060f1e020c06011404022b 76
    0x80d11381080303040048080c4c010f0300c81840084111800306029024019192001c580b426444a00b9001c4030700101d140d8082101a61007807006400822406480e10101591250715100e4421280e0100d8845004030b130041d000b0501c0f2244900307020403c0c0c014205c03228100001d194802c0c0d041d038000305040e80141d034240211001000121400750340c41c4100e20340180500c402e100b002c2c2c18007401c1c103c41c030f045900c00d5000d0300b0342840500102d030300c8007040190440d1103a1184002d90000b50289409080f001070203084a004070803549900c4001443e22a0307881d80b05900540800c20300140901c0000855800d000808005100c1c0d52401420b262448103030044960b010394107401080a00510300004a001a90311041038550f0300c1c458440903031050007052845114001483c09040200c0680b5103252900b04100c1e0905944264201411032010300c0101d000b5602507450340e5118200422218404030615102628050405490007034803100c0039051503118426030101c25000b0000144070700300b900c541 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 264543489 1250 264542239 264542249
    0xd061401020d140f0a0e040501081c03020f07060b0d0f120f020f2d120a08010e0c0d050606090909070501080601020a0812060a050a03120921060b0103021303050610 72
    0x12032180e070906030203091030f8054840ca1084203a0001500c11140e0300030640341b0b00c0400024024000d668503804195200c44039121156144a00b980038551000c1c028000e8a046424281b0b0240c1004030f661107a42c05032401203900ea40241c548100e4801040200000c2d402d8070f130162b401e03911000b183c02001040c4031458a084021134102c0c14903129040e01c04126190448003c1c443c50317224609148180d2580e100d110b20014191103100d0101400c140464060300885003191600c1c2116030b40c40d605038001c0344089031201d604d204200800309070290f40386d100d030750482d0000d02041e06110110340403a0000c801030340c0000c0030b0b500840701001a0360b0702c1010349511040a10150104a401d5510000a40a003241110794105528009034440e240c0e41c01c080003d00000300030000300e95807420901c0c500c0800d13550010002d1141341c000300b0814414401c0c910b15060300c1102a0300d5a06507200c174401000c8076035600d810035408005080b10f03c0201081360010318080c0016182c9030400c900351080c644115800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 264544739 1250 264543489 264543497
    0x609241e0c0a0b040c171b01051612020102070f080c07090b010c0b06280f0f03020a0e0a0605130b030f070815040f05060a09150b1509060d061401020d 66
    0x624501c44404900507a0040d80421184455161464913a80c4c0c10b090341c02ca090060920462840c501e0400250300114005075105442000c8002c00110390911442a10190038100c00c0b5505000408040c042030f4410143c3c4001424000d255070f030900040e02000090341d45030f0004c44d81141081e000d0180500600b06010b04000144084d40003034401c1507004000b0b01004c0d00380001480f2500c2d00c031211182c0100c01607200e1001c00100d10f1074443c038030143c020307103080d54130048000c2181026011a107040d2030b002403101a4492804800400c1c0810003094010780c19142c810005090302d91046006800a40f0140410000041e1040c5850300415481c203c005510500c0100551240890b0a04030384c1c0c5034821881d00c5959a0403c424480e824040c010102e208407010440d00c00290341c8890601c610419007070b2809004480d00314140c074100c024055100c10350400d0107200c50303400d10040629541c090300c540d0904445d007032414105d40481e442181000c5911101181d95a41440000c41c02041410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 264545989 1250 264544739 264544747
    0x50306070801050a090c021509060915040218150d291005060f1b06160c11010e010e131d0d05030703020d0e0d1116080c0609241e 57
    0xe80207912905c10001603d64441100360400c0c400c1c0241502c40c0b00c0c52680321114105500802d80c0c8000c200c820301c1540c042d0410a184000600100900a80d0020050504280801d62003501080058141002da070402c00f40d440090700c407a15001651030003402c0d680d03401c0f440c6455184803820481500203150846400700084111020042c40c162081a01c0107a200e900141d01c0a2183c400c5442c06c01e41d00010a4081c0000070780001c0c5140b084c0491902009040b25407502581c03101c0c0c60b400000c0c204283d045601890317522400001c40c00c00814902a2035000c00c50000c0f4600d1072a80304c0c076051903511003242c2c4c00d4000c0000c00710f0b00c481e100d07907004160a014000e0300420b01e0201803d072404141d00082e0300d60f0540c0c0240c208074400c2c0201e1098032428044020b02034803091482c0d200e03c0c6d5a00540b20312044004208422004644140010b0301201003e04108030f500d501401006900500004043d1148400210001a104060700005940d01d49100904200940f103102011604600300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 264547239 1250 264545989 264545999
    0x9031202040b120604020f0c030306030705040b010f0315090c021605060703080406090303020403060f021b060106090b070f060e2b090e061503071206140a1503150f050306070801 78
    0x100da48030443c80180142d02d071a240c0024000c0d2245051005520b200071480c005410030110041d400b038407040341101e80c4a035551003444151400031104501044000055117891030094200080344002d8100c1b02d140d681d01c0712011421118000b5030040141e0004000c00405d901d10308181c0c015140880f201418207040e0382d001811000d00402c018091034a42102c1c4007014040d8040d20091688400c040c00310105144441009403c207180c2c1054442c00c10402241244010594506813503c56480384d00c201c1c01d1140050b86d913440f07454102c4070603002a03250000b00300e5501c160505003c0481c040e10b40c040200001104201c840008200001c1480c11502c210980151000e4100da091261140240d541c581c00100c80840800c11140b04110010410100540c01821010309a0050204200d0552031340e518403403104003c41e969420024015050203941403a000190a40d00f040c5800b041c00e400d0210200d00c15040395100c02d205005880041c04940350500c00c0c95031042d5141303032400c01e039031400f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 264548489 1250 264547239 264547259
    0xf0b03010b131d041104151211120105060307092307030f09123905031902060a05180d050c030d090b010918050c062802010903120204 59
    0x1845800408200080c007180c285407403100c0b220052400c0c40e02815108001c0f20b69540700f0390119003c07500326010300325400c1a0300d041d01c030f0300b105541c802842c11216810700d107200f422204003110540341c0d040803004e1603849581300c1c201c1c00481e9142400105150606105151500318070b40c00100e04582440340c0d01d5040c01c03c020740d650491a000b06800c1303d0b51203c800c254005c04500c50164510707400e04120406102007020340c400d050301159120811942401500e100600e00c030841065400300701d10b0a0b250301d017040c001c101081c40c080c4044d06d14110f201c4032107005a2030189075004c09a00400100005003842d4401c0710b42c0030040065103521102e0600e580d03a181c40402c2944814850041142070b03035200300f003003904c036003030204842000710140c14244004500400d00c03842030b201d03091201c1841e00b01c48103460011100c1c0d01400070005580903401308003d6801c460251540c500350580c040408240c050343c1000c42c100540c00020f1405201e04005168a0821484010440c0100010800c040207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 264549739 1250 264548489 264548491
    0x4030501051e0f061807030c09060f0c150e191106071a0903041503050405010b06090d06050402150a0f090608010f032a03050304140906010c02060307120c05040f0f0b03 74
    0x14603000615550300d190004e112842c8145c1381c51542d0102004001035140c0580c8804002c2c0f0441e03e03031000c6169241011500d0038161000d030000108040140000151405403080203088140d40c0402e81e15441310380e5920705079100030444807404010540005100584000880340311055800c5881e18025495a040e200c4c906203150b41d0344003e070700024032503803410300076980900240750001030544c0b800000113004e4502030310203950310351800c4502d00c80d5262000c00c82e44800c40242480380c155002d502c810005180041c42070b60481a0700c9040c82c01030310401c00824001010380c40d203528494905034010091002c0350040b2040c0300030500103205e0401c0740b0800404980d03010105010900119500c6e5890550450540040ad01c1c00c0201004015012010b80140c0c4c0750740107103041c0325800f58100101100d041d28024041001540f4040140c140700b40156031201381c0e414880c194414402e0103804a60b500c81d150760024034041014403844111409410040105507803208881e81013120101044c0301c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 264550989 1250 264549739 264549751
    0x7170d090605120f06120f0d0206010e01031a19050c0301230603011208070b0702070302101d010309030c1a0a0c02060421021c08010e010b181306090e0304030501051e 73
    0x13084000401d0750380c440b82440c1d00016164165080c5a000000003699510fa0050060143c09054004103010034240e4645040340d405c20f21500f0380302c0303202c034490b1007644002c0c200b05601400600740c40e8000c1e55a005060003104480222a0381c0d42c5440c400303079060040030450072003d0091000181a0303503030300000c0d41c0c1502c0031103407030b5040c24090b072070316001c10711039140020b1023200d000303081110340307034000c508041224000e076a6641c02c1041c0f00030403203403540750442d12800e4190104d000c1c0e006510a0388076581e82c901c6810024500c034a03030388a07c41c1001c080c4800e4034012120303100b00604a40280078400031100329000030082c0382403a0390b9605410020f1801286020b45502ca1141c000384200043c552114807900400e0703407110846001441d00d1030900450000c8660b0707030000641c00c6540003c0700c991408e2400b8003854080154200f080f8001c100400e10061603c80310042544511031249013036201c0c0300782c000c6035210310310725115081d07900c01044202c1c10b070039a15080880c06442c1c0354031940302c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 264552239 1250 264550989 264551011
    0xb0a03060f0e0109080901020d0206010e0411011101050f0406150e0a0510030f111f02030306150d0c0201020c0c01020d120209040207140102090306010b0a170907170d09060512 77
    0x245010420401090034010a182c19802c10703d402d401d0040440041c081d404083c0d098552001b465503041e41d583d0020320811000540041c0080c0c0404d510a0031f1a45080051411644404c1c00300b0181f4250707001550b407005003498007010300081000f6032140000d500044403000110340e10740040e80c4407a210040c5209046519040010ba46013000f21464010315401443c0d0207002007a42482c00d80c00d040025001e00131070703540e030001240440302c8682c02e5484889074029460340d60303031506010b012101c4024180401d0341c203019014840e00d03503004140c02000300340d00058850702c2c1e142e101440e1020780360001c1d041d904400c4120700f20a03400340e0484004c81181002682d07071803400300407500030702c1118805003070340ca9140b50a41d2100411f400401001d4070850440d44039036240c00306043c85200390310f5644040341101c0320310110560b1701e6449a030300250302c9080d01d240e15640c0ca105091040032800ba40030f540c0001c030456000c590403001c10380107410035182840c1072001e40090300c80746600141c800c10b042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 264553489 1250 264552239 264552251
    0x1512050106120302030d0e0307020f01110c09090a1a070503041e08030124140306040c03090503040e04152711130204050418020d1101200303060406090b0a0306 70
    0x44002500018010b201803640c459481501c0d00f0000e45913009000112006070405041c0c0d180d071003001051301d94180c0c000707000d081c01040300c40041d10544070140c13048040c0e003c0c0303140c0001c481e079a60800b10300c510ba200000e0400f40d102840d1042c0e00c01c6c12003a454500c0407901d410301c03a44583c0b0070240c80c0d1007684a00111544003001200c20090081c40718018080d2600000200c0d142c200300c107207407c0d0442d01c001d40c50404200300c003040c4c4003540c0ca511450b4020328140300050b0759103070071380040c0c0c43c034001403d001945c0155500c8503801c6030702070b400c81e1142180c0a4148001c00c5149402c1403040380480401f00309102c40010540b0001c078443c130f412290792118039011403d21540002000c02880c0052442036029040e550ba1030181d0007910801f441245010600700c1c4003002c528103030500550040c14920f46010990f00d0b00701201c607800d0160304206035650300b507040034004030009140101c00e80045841e440c0c80803c00c41645c00c60340041840c6401e0945c0c8840031f844900b0790500b81c9034064000b040e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 264554739 1250 264553489 264553493
    0xb06130303050f0d0c020d0f020a200d050a08120906090604060906022502040b040209060d1d03030403120c0c12230f030105090a0612080703020c1206090d031512 71
    0x16034011302c2c2d960000b5519081d008644282c0004041c09144543d44420721b0005a4400c1aa00c4080064002e000d001402d1051401c41018245031100c0900080415503915010340315a0b00d42040c41d4411a06890001180803020b40d1020309543d2240c0c0d81c0b0300404c614500f8542854580101030f10080003191179925001c02c200041d010341d0741040501000c1d13a001852020010b88540b1460816800f0303501e00b40c0032041300d041a0007203030414500036003042d290540c8642480c000341440e0740408824510302000c845090414001517010360300035507640101e80d0400444c001161402e01c01030003404102580c0c0d000090703014030402000746603401d0501e90030401c4800603200314040000c1c00d40e402c2c1d0000f0b120580011501c09581a02c0095030000c1e965943c07005110111445801143c8a600d40d00711002c0000c0c107440c008000c0705110307106540100350500042000c410242c4140145501708600708400e000040003140c1088400e440c040c010001c0440100424034014001c1000d9540041d080c503003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 264555989 1250 264554739 264554767
    0x8040303090b0705030f0a050705041e120b090709021608210108030409200403170d02070c0503010c032901020f1501080d140904051305060711010b0613030305 70
    0x19198100620700384038941003e00030402e510071192840b007450300501007440d100c2c903442820301c103d8441d22801c2c50a030900c2d404e42d01c0b0052a5801990802c4a000041001003081c600c100740940f02c0c01240b00b40f801c1c401e901d982440d6264010340b00f413034411b12403d04605a5910303c0322204c0d40081e15141e03208402c00b010690768401c880707040c040d0110300c000000ca0b04800402001201d0868008011003080c0300f180801680e20300c44a580c401c04c0521080c07002c0307044c0500340200e0480b04107015140c006d89118443c241c3e00a420b040d1418164030008200740c0c2000e0060010004541c0346c10400750050440410390300700200c103801195075500341d07505e00f164001c0006034aa00481d900321805094402c0481c0c45104003402111480d00403800054603041c00750452195141218040a003048040c0c1c0a220003014000d0840c0440d0075150030100c00b04a046c89005e001c0c0409958100324440c1c000c014500f581da02014450007494100410604910383e0300c04d210590b03034185030960fa03400022803120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 264557239 1250 264555989 264556001
    0xa08010e0c0f040905011b0e030a0b04031422061116140111030c0313050603010b04061b021c03030605010507020d1403070b0f040b010f060e0f03011503030e090c04030c030308040303 80
    0x40007586441c920700718100c50140d40e02803410342d45e035491a0908c021030505859841540b4002d0440e00030102140c0001e0007030743c0c41c00300d034942c20102e24104155103400d15200d1000e00d005a43d0a00120000d0001c0307540414400c54440e911f90003485d07000034458442c0da4441c1c0c075101d2845c4540c540e03800c40300700d0780c850700b031a000030183c0e02c0490fa11289400b001c030340c036075024450082a00c05103280003d800e081885c02c0d84e040b291601041814545411001d40c0c000300d10308404031420261303018440043e6200e1740f0540589960a0000c0710004030391501404a42f170640000741841303c10b1082200590f211810200cad05c0d82d100141811007210310f4078041c55070092020007007402390401c0800c40102070030a09079101c0c2d03024140040c1c15999811139201007001070b00034240010b0002c01a40c1290800280c1c10706106000340001424880c0100d103000015501e400460008100ba4200201443c1150200c1c0d0001202802c0a150030724660307900c41c401c0b803680300040502c13185600040a15010342d00035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 264558489 1250 264557239 264557243
    0x272c03040510030f0c030513140118151103010b22050d050d0311130e18060c04080f01060e060907050409021c0507030c021902040e070906050a08010e0c0f0409 70
    0xb4684a5a0000019002e004400341c00801c0f649000804003495101e40183c6001c0e0b54004030031a0200401d403a40040120200c076034101c10340d2142175801003180d4030300c68414686e001c3d07020070b03014844050000040d079102d40f440f042121024001480700c0540841191415407090180c0f207011040c011740203040b940d00d94082681b205040c4000c030140040440d41d2040420980c0c2c04102050103180d20580e50f00900c1411100400b230103e050012200480920390440b11699106085c2c0000001c85842c0c204100c401c101903800104c3d0402051400308540400094045c000303000c05400e00b00e0346000d41c03400070140c511402c100c20100385418001e108440141c10082d0041d562007134000304005040c40c0c3c9035030b82c03620b884c50a00090f41c41e51080c420b8920030340c401d80c041c0114081c0d5000107014a00c0200069030305c5039440040c0f81e043e5504005035002006100408204e0034500810410340307a083d0340c0f100c0e1903030b4149404103a200e0340c00300d40b650205404507422021000003030b0110740105425100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 264559739 1250 264558489 264558499
    0x12030e0307060f08100609030809010201021e040f08060c0a2a0305070c060c0b070e12011802030607110c0904061404050c09150a0b1b07272c030405 65
    0x70200d0300c0c0c0d43c0400c0d02d40d0710074000c0d11448001c4d20741c8100c034040c01005100d24000910302250910016100707030020f0901744014400981041f480c101c0900402e501c850200001403000901000804403c0450310018101007029041a141c0005844164030440011404100c401005501800030000400d000213010fa81210400510f503e4050200c0e44900c45c251034402222400040c0680301e11981685550f002c05900616112801d00740d0b11040702c00d0500d9031008000c140000c05035000d1240c50034046401f81c0d01003a804a0340181418140050011801c0080c0c1c0c404400c051080004c81441020090781c5200c03050399141000f000070312540c0303070b20701102001c80240814007070000303151045980d084a1a224607140c0502d0b40d4540300c0e030410b2080d004008103000f040307035410510140c801200500d82c00c6003001c1d1040340039824080c55801c02007210350180400a240c071444812400210b42e2203000b0841c2d032501c11480c980340061003407800103101d400150458920024000d440040c6400383c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 264560989 1250 264559739 264559753
    0x1020106120b0a050c0c0309040f02040b13140103050c030103110a0b0a0302030601030522080d0204030c030309060807030c080f040501090c08011e0c08180a0c03030e030d0f0912030e03 81
    0x5401a1200e00a82c3c000c4081c90800b00856003200c0a182140e00c1c4407a4180118601030584c41404041c16030221104041035013130000081200004008201c030340d80040300f0804881c14201449250004500040c2c1098546410090000510021681980d800484680f40556074500081d00c0183e1030704001205940410116561074154005c0e50041d6404d0b01d05003d00c1d03843c15126580b80c1c4900066204e90407242900d2000f2480d013400500403011389150140c03400e5100d44803508950300c542e100f200050620350b01082440e90210710a43c000f0381514040c0201c42145000903c1c03600b0140c11420b00f1a86207022804101d025800f000c56654001100c520456032504214020700c00b00d440a840314140f001040760000d943d01c1082c0e07084440341c4a04829844034100b00015845000e540d00c420301c00d5220070404511205400c1d0011446550342c400c03650191014141045001d480e800d00b40500c0c2d22800d03031000d4006824806840c084a02c0d100d500003030742005c0b01d41d5181e0004164243c01000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 264562239 1250 264560989 264560993
    0x2a070209181f2933040308030105100c022101090c0602160f080613150501090911030303070207140105091c02030f0f030409020f04090216050c040e0c040b0102010612 73
    0x280085050714410350f4204400489007036080107a07010180c0c0203070721161442c03018092807486401c0f8070640c80c070b1100120684131100c011102d070b41d110382c00681e90b100021004001910704a00044d07407035a07091820410044855005c51245c1040704009406110300d0700328403203491000d41c00034101581285420aa290751100c2c080c0d20b9191480e04090200c2402d00d01043d14001c0300c01c0c0300c0c2190941d20041800e640c4406101008012040040303448000036582e4100524080c0641e038042d0080f01400540030b10b4526081e15141c0348a81218040d42062080048298000c169242110101c140800000b84040c00403905881035510b80340d4488400c1d40d0410b282c120003101c903034000e8800c1d0212151403050b5030400341d40c0e4449118002d00350388100b0080c002c0d284c0035005894030103200c549042c01c2513121200386050742c102c0c4102c900ca0170442d40e0b031001800b504101d50070300940291000c0048000c1c035003910745c03541c1210382918041c0c1d0b19040300d03d0b40b81c0d2007540810020060740c400548a42068 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 264563489 1250 264562239 264562241
    0x614040609050c030102180904081201090f06170d0c0311150901050c070209011403010204180b01020c01080705070201260f07020c300c092a070209181f 67
    0x250781c0503611480ba5400918043c24140b089030f0a1010051205880107003a00802c00617806c010f20032141031500b0b02c9050101010320012034003802c16000003145560302428524220b821507403050080b080706001003c4008804100b80140c03244038071741240000d2050505440800261046103800d1049601d05907244402038405800344804d08004e110580340d40c0c001d050540101c00740603500c800f454004121519011a10500701100500050700341b0b550780c00e05000c52a07421126900094031420701048640c1d0502801e0145442400c090b096428520301c010030a00800100038180546010b54085800305004a4440c3d2601110003418510744071220880d028010703200c11015104000c400d01c81403070490041800300c1c50f002e200051160468803030340e0b00b0306c0d0f2a00c05041140541054000643c85942d03810b48a0215440c1c2d40901016801150b41001d81505080000c010148070420046e42c0d0889a541c02814084107204a072282400903418000e801c43c05d884450f4018920320009002c2d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 264564739 1250 264563489 264563501
    0x1050a030c09242c01050a02010f021305090a05010e010506070510020a0207170a050a061a0d050c010908030c0c060c03120717071e0f090509240607080d0906140406 72
    0x90b41d03d132a800c206900c200c0100c848040920300002c41c03e41c0012007554402c00181480348006e10020034500c144120a10403a0b0022682604120314110140401e04140b04550b41010f041700302046550300d006250440060180507462040c080003403e00c1c180a402c1120301d00341e0f8043c113800c540c2c072418480040d550742ca040c40743c0c00c0080c8010810020703039440803451618003500080900440100742e0748079001001d5050385004000ea05510b400c00c242c40d461009250144190010040b0169190001d0701e1000641d2154103a64400c1280313448145011070307014400300b4151031042d00d41000031501c60030340c018440d1440b6441007060800141d81c1d13025036001c940c003c1003111070359035031185c100403511460180c0c68540b03159a0128810009446000760050710060340ca40066241d0b1540002103c4410a4540c07498242280314044082c410301c03070004100200407510549010082c8c0e0b9079015900600c070100c041c056480c007081090051a411081c0c400351804030613019803030302e441c09030006d282c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 264565989 1250 264564739 264564809
    0x708030f011a0408070e060a08030307020a03021c1b020a030b0c1e0a0c030e04020c0109050312010f031a15101205090102042d120803010311030c01050a030c09 70
    0xb145840114141005104807015200c03800043e02c116070408000c010700d000e0150020342c014240740e000144c445014006907004100b01da000d06408001420300a181100601250100341400851100e20b44d4010000d83c2044182900e181c9152050f1b00004600d18440e600c0900485c1c0390500308841744c410310004001055110000c0c40e0082100c9800d445240201c46010020034800144200420701450641a1891004101500d490b8000a01c507081d95403160040740c45900c0070a01c4030010b60802c280f1405046144c05c0c5805d241e25586a10700c0b0304032040e1080c0c0400c00ca0380c0200c1e81266426108145043c00901081d0803100e170843c004040d4080c221021006d949000701040001c0b1060023283d00b101d05481c1041c28007542d030101640041c1501400e2000d412010b200003a4060301e40054084c8a80980c1c41292a50300d103042c5110080121081640300fa0407401001d1003c0e0f803c0f00540da400c40326441d00246500390b0703a000b03540401554010684200034040500d65800d40c01d41b00140402c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 264567239 1250 264565989 264566009
    0x7050f06090f060f0604090c08030d0603020108060d1106030a0e07060c031701060e010f05090904030801030c08150711010b0a03080a0e120d110312010e0402090702060f01030204110708030f01 84
    0x1900342024161140b00568880b202c5030b04131404104030307250a4100c10220340c02002c5050005036507920180c5140d02c007418254a498480c0c0d0200190749e0050140707540040107075401c500202e52540d400b003c464428211501c00e60001c404150802000d9012a04c20005142110111610381c0c1010340041134540046000403a10036196500c0035140d03804c0c0e03049031800e8544060041c01c050042d070b80c0a10462404041007030a006c0c501ea07035aa800c035014001c0f400380c0c444414650540c1088030343c0c08030300c0e006205254800388000c41400704080595a0040b0b251504680c014422190725014003c0da645580c0c0c0910b5101010003846071100c010420584252074050071701c001441880603c100c454841c41c1d694210b80540c1426034041c00040e8400032000041d01e2070002003683c000c0e5034040a07000100c15040a00400c01103082c44182a50001074500003400f15180c10a1003211041e0140030007070003030303881d0154040f0740d50880b801d60f1030840c1e00c0703142c2503160b140500509621503401d00c10400c0311 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 264568345 1106 264567239 264567253
    0x50d022101050a06050f0319020f1206040b031b1203040803031303120603020d111507030201020717090303030106050a1e030e01060e240607050f0609 66
    0x944200d0680480c1c1d414074042c403802044503003108050010401002842480700c80580e94131031000b00920780540f148450f41c0000e80948804100d5210020484201a0f0031a016442c403a840030f590411001c90803004160b0348842c124034001e418001014408030a040c29444001220b02034812030b80360903902c070380d44d40c0340d90310449016101d41031300140e04d410181d202140e240c0c03400e0301041c144444c6040d5000149054040340d03000303208100d10400311900b6219450000350004000804580320311490038064080e62045000301c581c2c0c0401801026028580c0040e140601e401800071400c503820500152416480f500044003802030500c25140110000e000501e403403115942c0100d42d10b107000b24003509403070a940100a01101100412801c40c103480c84204056014001c229205881c1c02c011503200d1282036405400360141e58071001103d400040c68a015400c000121034030 = true := by decide +kernel

theorem cover : BRFrame.Cov 264388489 264568345 := by
  have h0 := BRFrame.cov_init 264388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 264388489 ≤ n) (h2 : n < 264568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
