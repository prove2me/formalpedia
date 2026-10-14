-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2347
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:26:28.050163+00:00
-- url     : https://prove2.me/submissions/76630aa2-915e-4b0d-b4d8-486e6cc3f344

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 421942446 ≤ n < 422122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 421943696 1250 421942446 421942459
    0xa0215040e0c0d0b0d11010e09040b1311040f0f060503010e1c021504141507200a02060714060901020702010c0b100b0406170a0c0905090709050d060905011a 69
    0xd81d0802c24080149074044441c1d40101c2e0b40f000c01400201c101c13001c84000d40e82020305000528041d070b07004814040220088802a005081980b203601d070000c402000800c0388051801c0c00c03400e2201040c094487c5803c02032042c000d07c58440e2404020305600201c0540e16420f2042c045124079043c002d41c0c0f9181c060200070480f08440030035580718175981140400550007000d20308421080d050302c10380e01c070b24000c0311004081c581c1c031030002d46403503516190007050f51821020300c040c99600403200140048942019a5840d03800d00d20700e420316035941f00080d4090000140301c0f04120103220442a19641c200030366030326a84452450b802d038840c1c10700080c000703175244000000140402c1801900b00c203a1441d110176081d100d0110703e1944d8441e070000800701d402500d04543c0036107030420a560010355020300b44140c5c0002c10010300038041724080d4a00c6034080c0c40008494a00c41c048090080c10001c00540295800c6d0070400300030400a0016611175007880c0400b40d801255509480c0d1594018100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 421944946 1250 421943696 421943701
    0x8060c18040212061302070203011b18030c05011112041202101d090a09020a080610061b3504060e0303090a090e01020702030a051b0d0507060311070204020c0a0215040e 74
    0x800c4040c071124180500c0717941d030a000100240e1024840d03c4000c0304550201c0b210000c2c0c4000140543e20b8426a00c40c81c660380043c00d0001800301d0003407804450b003e00348403c00418030304a0a04050080b503d0700151000458005070301c0201c0325603055002d0017903811310f001c120801c4046510700040b5031000b9000b0200c5c0c00f524107605040132403da010814a00004178402c940c2c0c00128660318643c03040d8219030000c402d00074803e0303201034001c00030441d6090465100107460081d00c1c000c8082013001c0c0050091003d202d041884a0111010320a41044018045001200b03038005035046802200000340108226621034280041281c1011400802c1a1400c81c688a003110141c540c00b020542c80355000d00558006803003c00c90400030600c80c0000e4a40140840207050b950091544820b11030301c0040078580229101113911019102c00c0e24001c980c2c009042d8003485c41d44100e400094102d40b0004800c0181103012440750012407080f9070700b40008280c03d520010900941c002c213030394603412402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 421946196 1250 421944946 421944949
    0x1050108040c12030c0618110904050114010b0a03050106030b061c020d0c030e060a09020d080a0216170705040c02070909020307030b0c1c050708060d0c08060c1804021206 75
    0x10125071103803081d2010300029072281c900303a003041000070003100030401c8680b8480030024a0b004001d8070140c1c145030a4140b219607103400c840451981141030045940c3d80115050000a4000c00b4810490350705040c61540e48049281183d8002e01000b8002440c2500101c1d500340b1900400e00081402803642d0304029620805150b418041d410908071980d080007a07101c045078500a01506101e1610002510743c01605404e04203030004016244a920300a03503040181d80322409034031400d400c02a015220032000b00280e01d04141e115210060780c0240c000081c01050030b4a0000034000c00303205642c040386d521400e2000b0703185071180000c00341e0000001803051421070303841001c049000800f22841596243c0300da2082c490240d607076010100d000038003182801d5400c40610302c0c000d1070f801c0801461030100c030014108070303014190910072606c032410202800748003003189025080b44402c0c0c0b10700d42410228054940d1100100750605c04401e80c0f240d5072454148240c440440802c0b401c9011030340c5800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 421947446 1250 421946196 421946207
    0x703030f050f0f1306180c0f08150a0623121b010c0816060209120606060712030e0f010b01020d080f070e12010f090c0b0720030c1201060501111203010501 68
    0xc10a8980c85030720204c0d0004603006000340700b64a070030a00c4541460005051072600710110307401154048071071400411210000090803200440d1041c070121041d184c0050420281c030041e4042c08600c1000d4840d544d01d0b0343e400d0360180040d001150510031080c000407880d0785035011240100924103844281c0c10843d401003507507101441c49240c14a24002240c0c81c3e505424584250a80d80b03a81d000c01c004d0703c142007500c1180711400c0e900d80100060703d411000580d5521500e00000c2012408455101201d4005c3d000190303d69000010349142e10300c0103001a0007018110800d80c010310400c110600400e004080c9c06008404016060160703503150321040d40c084456401d03481c2c11141c5449030030440242031042510400000e60041000c040b9414240b03c0c42e0700541245103640d0080041c9000541c0fa02e030501c2640001c900000e20507075042001a05009030b030b07802c003034011030003000740310000d5019071256041d00c0007600c03a1815110344624950f5103134078041140c890351a00b00014005503010701d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 421948696 1250 421947446 421947451
    0x5103201020106080106030503072f0d031209030c05011a0609060309122209052202030c041a090702030307090611100608010510051c02090a060503120703030f050f0f 73
    0x41c000890782c036980b80e000c00d08495541e8003e075690f0700b000c10348000700400380342220f2a260024010b404084401140d4408052900303400511074518a50000c0426000c4c01c1c40c07041400b40d1040820030003d40c1c1c240a82542800501150154646440002c134a41c201c25070440302980507118601704905001842015440541825220b210311010403440d02010001000c3c3c4507517294102200001c14280f0704005246071300140794150805080050760400303d4501c203140b05a1761443c2040380703800c0c0042800c1c0240e4001c5c00384c0150415200c15801c00c0300e15006504c600081d28084100ea0305c58500320384900083e209100021032000080284a02c5902c0b0200c500300c640381520005004842004115085540455101c0e511801002107402510a44030001c00c029204006030128a16081c9148140890001d01c10103145000c0390030f2808561260014281c050200d481c944031001041d0200e8002c01d80c21030000b0b042a140e04075002013800307210301035141d1b02001c003440e4992031950348070803000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 421949946 1250 421948696 421948699
    0xc0e0d050703050f0a030305160e0402130f0b09030c040506090f251215030213180804030f051e0303130515040c2105060106080402010909020409051032 67
    0x18084088007142c028010a4942013225005112000c011b103805401c3d980e0081c0030604110b5589070350380b84250480340c094458542101c0c01a5200386000b1014200724094000020211000b000868050040b00042c030307900d00304404407000304602000b00000e4480440304280c00400c114045540fa10068000030b402015180c0002240400415890800b01c1c13104010b00008540c204041c0b03500b141445264203104101c0f05100c80c3c41d0940e00400c040440011841031070340d03a907a140c040e40c2c20000c10200051a88140b0725541c0300c0c0cae80e0034082c0400c2c407294002d642d1030080c0c480f4009031034000c081c9000c543e07058402440c2981d9802003420102c450511007603801340505a40140c0645021000c01c0c4114410701003040540d04080c0c04482c99000c4c582c000e4980e001e41411500890300c0011011704480d45490225465625440101d804e40c1c5154840d5030030314000320f8003141c00c08094100f00d114411060604100c50391324002c500801c808200d140a078a40c5001216400e00c0025500e500300560 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 421951196 1250 421949946 421949953
    0x180e030904110d0c05070210020f1203090703170d0518070b030709030803160f0201090809040b0307050a030309090b0a12060b120f03030105040e070e010b0304020d08120a06090c0e0d05 81
    0x80e1103c2d0078150380c402e01c84c510020340009400300840c0380c032402096034a83d1a20003080309401c000c21503641c1724405038a0205440c0044001650704074200901000755038850b001d0814624208501c02c0150000095200c03401e040400003055041ca00c1c0c00e82c0703449858a0018000d55191421022850b070000c0d040408100320441c0c040041800080207502401a4050740c484908524a0007043e050680c0c0c1004110390400c511980440c041d18252150000c04030f4000900120f88000030b41b42c00781c01e90009801c003414040c00414190003d605408a0714503002c1441001001000c000e184c0245004142c150700c6c420b00c2d4880491030325800400044000340000c200c0c80a212115403a00312010703681c0010303a00010060109041a000d20300d003c11111004000c06420001c020418010501801c4185400480000c044d03548500188010a8014000541e241244010030080020480701e03400602c0c01c0c005c001a014000748500031210b289681d502c4180441241048440303c20000d0640c0d0910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 421952446 1250 421951196 421951207
    0x90209010e100f080c0301060602060c041403011b231c050a0f0e030702190e011a130e04140a03050a1209020910030c080105040221150c04180e03090411 67
    0x111083c68150242000c3d800524180602c9002c1509403085c0b030b08a4011074010501b88060100c482023502c094840c0d0380b400c03190400c454070120b401800f126620403070240e841842021242c0d04501100848401006028a40d101d80403107081207220705103c4070410448101140d070300d44a268000c83d000100028040b1b05e084104c03200c4401d03910410362030382003a000041c103032086150200c0703d030382051b0204200000d40c0c1d1410401078140c003c14424642e181341d450f202014180c20000840301351007007050154102689820900c2d407184400c89080700c1041d44210000114540000e0000301c441e030556a0900d002c0005104881014000802c100b5144e01c48003003d006130b44120304984070f100d0301011680240d00d5404c06181c13800d81c0390720072038241c0d00d004207010140e00d42c43e40b80000176840d1011010750300301601d10545401c2030729108415041d0740105001d143d0001400400403501c0c0e000100340090010900142105c3c140000b10016078400c00001e451410550421382282c4d02c28900a410b04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 421953696 1250 421952446 421952459
    0x70e090c060d0e1e1504111002120706060e010605070f030f0e090a02090301150605041a091806040b0609010207030b06040e0304080106050a060c0503030a1505060f180103090209010e10 81
    0x2440c0c8640445659203008002e0030341c4c4402c0011104e8080c1e240861030480c01c040d00e61280800c100d85c10300b8005e802c80c1c41c00c02d1100703008110104100c0e80e0f45004035560046800d002004000b9800340003003883c802d00000504501c9201926055600b14000150405099405680707011121031140e080c030880040c81d46e800d60701d045456114218206025945003094400c05085550080c1c4015401c07140000070b01019034400c094030242d429407080d0101e20498549001c0702400385020f190360045001b04d40c1528180300310aa03602402c0240d07810b11011014504020740c60003000c3d88140160300110042011901c0d070041507411103005800050b1140c402c070b06490031070b40180c004c811076a44604c006c11080c2040c07640800100000d14112400310340075904d03151a0300c00602240041a162a43c41042c4039524500400800000b820035a4443d518156844242c000204186468144100085203940a0b0043c3d4120a07070080c81d88821380e003800d00b035001c84040500f642048484c01c43c004640b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 421954946 1250 421953696 421953703
    0xf1501090b3c07030807050f1b01050f011a07080d05010305070e0106050f0a1d0a0801060302040e01050708040201050a0207051005030a0c0e03030904020d020f0703090503070e090c060d0e 82
    0x4219031003006020002082d0905030065039104015403140200c80140e800d8682c1e0b100980e0344440d031628002e2001c0d00c5844040b82c180c0118042c100c640000055000d14000b0b14001c0040321240c1d00c0000d1001d0ba403040fa0032006000248104410010b54211014450034054001c10f10329100302041824403540007118021101c0981089803194022441804440510419140105810303d8541d00c0c108007103200315594040d4841d6030091002c1c1c0c851800e2050020380303580d09420b80c0500600c071107070350300c42110303003c0c0240d44003d90040b8542980c3d80c0c034140060046520070b03c0c0d80d40355946a0703100d66004480603803040b00d04a00b1402000001305690b07a42c2c02d03a1811095540e941e098680c101a91070000300c2d8000d01482d414040c40c850200c0071510007209a40c07008804a400603107400000071240061322403010441008071000410004150300506040c00303541090b000c80300f441d611080351031381501c0269050749013135004003142e42c2107182000050440c00780048020804102c0400c2c0e00c1c1c80c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 421956196 1250 421954946 421954957
    0x705030715021c0203070f14090d05030d06060219120c050a05060703050601030903210204180e010c1103030a110d0203070c03110a230c090c091302030f1501090b 71
    0x41c0e0a400190b5000c50740c3e1840d84080b40048190780851a5040c4804060280c0c201c0c25441d0040c8a440c05812282480c11015520740079000b400340303244480b0500d0469166030100405c001e103646040323008101c092000a510001d030b02c50f2012170349503402c0340d160315980740760840e500c070204a60a80d0300d40c005103041c80103c5159115070010701113400c00341005030580e407000b0541410107140c80041d0011a60141c2030580c102600700b500505942408403182c00707803085130000510040c041d2066040043c0d9640a109201c8546001300020840540d0884a40d150341000e41c00a0380140089030301c207803041d0b1102c041c41d140d80044a1505094841c5c0c1c50a90708221200c1d404a0391146d088802d05400c02003030201018110050f184a0603550b036450300c03803021a40c543c0d071031003902903c11080340800c0292080280c4010300c052030501d4000d1185026030700a0315020b005103645c3c1e2542810b21424001e89018100e039460f0b07054a607894010004240c1c0e0012906810011031101c0001c50b003529000600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 421957446 1250 421956196 421956233
    0xc0c03100b0102121218030c030705061b030f160504180c030e0f102705030d0f0510030f0606030803010b040f050a0530060a0203040b0604060609060507050307 70
    0x1003410769200003a09050340400100030002c02044198201000c100780e007580100f0559803040d4078060208640c0c6103008202800d1518807001404000f4030a000810a109021490f040002c1c4400e25a0001c254041a101307205141459000b0a0748492100303074031049103d803841c055040c40e0707a5513242e800004640f440489070301d5071480300903003095060060400260411005100284440210581d82c684103d80b01c10165900c9859400622100d0b0100550f800440c0085481130343c5414150340b6580514640c00d1100d14081c010b00070703180903000d09840f852100c460005134a00d1a00c80c0c0400f000443c100300d0ba4566944c60100024000c00c014501030800c0d0903051b5241c0341016020b100c01c000340e0300708510641102000700119a15030200507903c40300c0b01da5007a00b400c030700110f2650210700761000c164036004101c108140740031664055032240c0d02860003001a41c4a801c240001ca403014014800000c041c000240200b41c01000140b01e4284280708980c5894055100c0200003400c10590f0ba = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 421958696 1250 421957446 421957451
    0x14030f0a140c1f030b040b010f05090406051206010e0708040f0f050a12050d0f050603060a090c360c02060a051b1602010305090d051603050705030706050f0114010210020c0c0310 78
    0x78105981d0505c2044204981614104100b91244001070f190300000c4d4046020443c000600b03040a80722034020000504002d01500c814000782c000e250389904090113803903040314000d00024440b43c802c004a03030046400c02d42c45940c0804686824910a40044094804c0d10482c81003100043d141c0700c0e040031059445c2d0780c160b16000072a0802050b51045c000075000d03242800e084c048076a0740441c8042d04001c442400180f01d200618003011072070025440601c45404084001d00c101d844807050320036900c007070301c00f00c6207500c144500c150407544030103d60b9005901200004403200c555500c169000300d416020480da101454141885543c40b00b01c0103000e1904803c0755100f1541c05002d080d800c081002d0160040c440b00080041050144a0214050203002c110010506000c1c074201e84095030004183c0b9074a04141c20914098201540c0b02c04c03280690600010b04607030070005031204040142d018250003950f080b0900080c2d00f00c10852103460007000340a06407a42d00b004603004040022002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 421959946 1250 421958696 421958749
    0x30e180c0f22051914040c170106020c0f060309060403030921050d1104053d18090c1209060b0604080601060905090106140c01090b090714030f0a140c 66
    0x1c0c0020281c4c910070905965808640510100800382c82a0400d001c06075000142d000001e403013100c40b212080c0000404400700340010a41c1d650104041c05044000e491f0720b01c40c100714405000403032004640304c00705508001c0100700068403903049400c40c0360180d03190524058103402205680882e900f015008140c00050342c003c442814020b03020a0003110003e141030070300d00404140c640d14291000c03080e0300c0b01c5040400e444203141000c0303048100b010301841c810305042c2c02c014001440c0c8411400140052180008030038406000304800f1034080da941458101552443c3c00242043c03000455202d515450b0308821a101c185c040e000902d000c0300180030075494402c0140c281d6415800081c007a010400040c051280c203c2c9007050742e03802240b80306551f02c004481981c010050008010580a00c0d102440040d01001400b4000ea0b400c41e803045445031018001c00d65540e041c28100364a582000c0c42c0c400209040220505d0101400c6041e1420719134a84002883c00a4484c0020801d40c2f01240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 421961196 1250 421959946 421959949
    0x304031103030c12061009031401020d1503020f22020912060a09020a0801050c0708031503011b14280c05150a050705090904080309070902040801020403030e180c0f2205 74
    0x1400c0c1c100c0c0040e00c0d00401b821002030005c0564109000140c05254164900b0451500c254100d800c0c40201e404100442c05805000090521043c80281e01c1603204500b00850b62608a1001ca402408000502d03099280344c0e090340e010307400590000364025201d03856031200900a00901b41f203840c0400300003c0d07100030f030310400c5801143ca4210858582c5800c040003116501e00701119500c82d04000e4158499980e20f4160359117209a04040b9015402c100c048a030390701c2c0130646410942c40503180c1400d84c182c81c50244650f07008000403041d02d284482d018000104218150381c0c0d40400a00e008401b0301d0064540070310780903c0141d00400b80040d1010028041020311915400c50312a00c1d04c0d501c1c1c50031000000d00343e00400341024000010002c08551800010004d202c01007074640019500c9030f96405035103000390858402640415002180c2c002c940c030f04440a107030301034888404048540c490100301030081d04056010702c0040c0d0100154545902c00714801112124a20310f5064464140300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 421962446 1250 421961196 421961227
    0xb070506010911040e0c070602161b09200d0b090f0f01090218040f0e0d0c0506130c030b07020102041206021305300c060715050127020304031103030c 66
    0x383d5103601c001071109000c11030940a006400c202040d040c25100c0a0508100001b4030401c01d0f442c01d40d50001d240c24042043c9000300200c00000c42c030402403003a0b0396540c44002c1e1001078000f0800076800300c2126081010080140c071015030f40c00c1c07000072003031100d04c00f103401c0180980d0f00c0e03a000710f41802080b0310800700c00840c40c090511a902542032140644090a00308085030002d032149440d0041c0300b1615000d0ba211001550b1000122190903403424005454040134810a683c03034061030000828042254070840300496121444101c0300780345450310325104a001e8480c004554003040002601811888070010003402080d0040e0f450f001d041c80a0780f409429404140244548107141c1d1500ba00025800011041e001ca600c0e10212501305650902c280364548541c4002c021941c0402d00c00da400c2c5014290210f1034040066980350a0304001407002c1403504944c0250902024200c030b030660300a550000d2082c03d0a13545418110105815a00201c446819050011841009500ca240c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 421963696 1250 421962446 421962461
    0xc09090309050105031803030a0902090a0e030417010e010f06080d030c1b081b03030105011103040f150e0d110f0d0812061804120f03140106030509070b0705060109 72
    0x11501002050800e03900030300020707100e01c10035050000200015100a484c10103c501c03006441c401e884d500d00e0100d54440050404c41400c0c0d02602d60100002d00e0290b840c070541c0303184420000150f041900c0e203084d1255618420f1500c1c072455482c3c00841c1212007090186c0160f00c001100c01017215401e041b1802c0c50514220380010807d4140520030f0300c0301b40c03c0341c500e620148076000742d4041c0541600b40310300c0910980811a41000340d01c0d0700704848610100196041c0c8409a907516448a0115580303952802035000d1101075414100f0100400c4001a080303403000b4046050200c654451080051128141001c0580e203000310081900028078020a9002404e5011282404e41c4289521030445500500309201c4107214610b02150310f5541d4980d0800d044001c40401e181d480c580741c645648240340c4540300350085000d044118032160301900031056001e202807804052a0300c0d10700304501509010746810070038003c01c41c01260865583e401010300d00e0041000b09a00d526091040e01102c486 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 421964946 1250 421963696 421963709
    0x31605030412211d060a091206050a11040b090603061203030f250e120102090d12020712080726040f140a030b240405070f14160209041703010e040c 65
    0x80002c81400c60306002c5002d81159419103250786c990300b4040c1c05840181140d00203c110481e514510020020306400540c0324075a80c8c0d4080c0200c40c910030307014000c3c1c0103d01a107050f42e0400d1040403140c1c18050040d540c0030750020084282e00c5484050700d82981e000b0f840350000d5805010800c848041400c0310000001302e00d00100306c42180f984801060b0a00710b2180500c0741d041d152a458105800350103568086c2c500034000a0400918034003130a08510006d050000341c091084000350050711051038041c10303a000322000746400411303aa41a00404180b40da8185070385141c02d81e011072601c5801a10142044001c0305000304e040810a082c400000046948580c0741d0100c148001900c682c44141c004500309200341d15001d800000000f0a40304103c440e400038601020811999808409540801600d84800c0090384140319896140e1145489041040b501045100014240721440039846401500d0b0740c0c180c14400c00e2000c00950082c1d0000e080c1c840c244080c002446a40200080200724 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 421966196 1250 421964946 421964957
    0x1807020d02161205010b220507090303080c130911040303110307030203043303020d140907060c11040c030506031203010f2601060306021b0f03160503041221 69
    0x200d4030300140c4426654043c0c1d00c403c444000c0d0b0501040303070941101c40071910040140d075001ca9048a20300c1031281c1a1b1020a9080c100b902207100580902182020b881c1c06035070740d081c25a1896074000d501d80c8030455201ca04181f00d480021038001c0e61081c410003000e510241c030340c1d6a15500340202142c1c1c4542440286030820000c241c0000d40000c116070485a56403002002c940003c551412400d80b001c0e0009a10305075000d0318103410341d0640c000e220241d4506802c12580c800030000d401c0c1c14170121003041e10382c1c0c403036401402201c4c00f8003043c0741e003588204012030018140d040480d050310544200000402c2e00c5100f400064501441203090910031a80c41504640c58044407226038801e61007614680d4008443c2003034295402001034000140b401c0081c44520358916001c0025840000040b003c0e406405412850b14004903250701c403014800000e40c1007421180110f416040038000c120b0b130034031042100003451500031032280011401442d4000302441c000d030b00d504c0c8c54145042c90000700709 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 421967446 1250 421966196 421966213
    0x260a2a0b0306042406030501061e0e0405060a120804030c05030a080304020f0d1a0f07030b01023c0708010510031e050106090e06150108010501050301030803060f1807020d02 76
    0x30100300035a54402c50840d40468a2404001c507951400c0c110308100e20f01d041c083c0c2c00850b42c0f5405400140c101c60342643c404145030600d000d0300b038060f844100c800b40001c81d0300340200c03154075094100d20f420400081c0016002640d0300408550500101c4080343c001d42c01003410003e0003042c00c1c10318001c1100390060000242140c2c4e035507000b031200910080c07080c941081c3e140000d40785d101e041816035130700200001c281c00b0309510213507020300100d42240d960341c908000111407520a0140f0344142d07206070010902c117100b007003a10840c40c41e0005c0200b81014034082c036000c3c040c04030000f0b04030940350780f01504105040003000b40c2900e0340104580a1000400c40400000d0392003484207001401544c1c3d0712955400607e82640507042541c0800e800509104642c0710100e40491a20b0141c41aa0940c8004132003080040d1407105017403080c07902280c81800100042400103005560140004000c036442d00c0800d00014000c541962000b000060104104801240c0410410740e115a450005003c00c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 421968696 1250 421967446 421967459
    0xc0c1e060f0304050106050d050f06061203181207030f05010b060315060702031006150e1807110c092d0c0a030c0507050118150510260a2a 61
    0x1803150491240c0720000000005051202c00c0d4000c6000d088020000343c0070046d00d0400941d2107940c0041072801e03015440200b005441c1041003001c51000c40c84c0690300f0501d00030750300d40606140ca0303c040c0d0001000082030b0384010301407024402451280000c498a20440d080403809c5444034425903002d0716042082c00380c44800710386401640013040750f20a549510510100741400c10400204d80c415081c00800308217144060180c0d182c1c100a541e40418a003154410041100201c40712600120810400303d50791a2041501440000d0800100e4607242900c0c400305161020454542c5041c6190764059454a81d29040c0c8410780d031f009541c819800e080032f00343c0e048d0b140b041001c010140760b521010781c0003450095095402103600280200040e5980960503154007601e903400301c4000e81420701201c034408140c4649401895104610640355007000c01040181043c02000c4002d0b009420921018100130410b04802d240700d204c511014000c524440c076a40b007000c0e1850f0f0300344c5c003e840050100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 421969946 1250 421968696 421968709
    0x140708070204050c1b0f010c020303040b13051c0e01030513020108060402030a11040311010f1704111519020f0703050a06090c050d080309210a1d060c0c1e 68
    0x2041d0100c60025a41e1914840054944940600500d03d202c24120b8074036840c0020a8000f040c00340d8400034880700795004001ca880c0e100444000f81601c81d624085110300ba03080e08144103d81c480c8089449044c50000020788070140301e140300e000900c08802c0741195580c1405030319080a203c0914882d06e030065400030b010030000904035070042d540480084e050040390341040096821140c103d42c0c2d10740c6c4034103002d115030001c244024041003426004403444c40c03203510749020300c2004112607101c581303441d950941740c180440700880c0c0c40515036043d0040d075810360004051403c200b40a05413036100d01c3c10003a0411194011001d22504148400c2001c15008140a90b07000c3e880b02d0b0009402c40c00349060481101aa00000e030000d81c84211101080441d84c011400b403014030003214010303005a50035920b118905218480598018840071000b18080d00700402c015000021261681082001040994101004081917a0320092810145041603031840c001c010140900b404000c4800c1301081c0c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 421971196 1250 421969946 421969957
    0xa06051f03110d0e0c04050c0705070608090102071e020a08030a120f020d0603030914040c1706040b09070c0b100f050d06020906040e18010e061611030703020607140708 74
    0x2410345841030380203803102100480d084140507082c02c2000d111034251a03a41c0f14a000c2d0740700e000380e2807c000303c0c041075405402d444015074884010300300181486003c50702c01030301500c0b000c070b50364081c04038400003032003010903c0d4080883e8200403801840c50042002290141e401183d0540041049012290340003a54200d1a40180400716074500550010300c0244103000d025401c4502d0302401004069112042d002159039600d880e40c143c03d041c1c01008222a6116502c402160503505203039910211002d42c00e0307001f04010800101043c640010522035007049900000051203180068104083c90403501e402005400c490021141004030545c0400d9048c0610b503c075801d0104a5400c016080d01110040f4001600264803030756a07801c0e40701d03000c5c415542c84100007440c54000c00f01000c144642c0000e0728100c40205055250450701100094061403094200100000c03109102c800c20001003050300d2080d8010501c900e000c1100400045c101100304d62400010402c60010540070300a450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 421972446 1250 421971196 421971259
    0xd0206030112020a050405090d11030f03070e040e151e040c05120a0615150804021008090c0402190824060f0903060901060603110403170906041a030a0605 68
    0x650100d4000910700c4c800c0c0340c1c083c0e81d0182c03d0a04002d0202c1c00881d10069140031a180d00700c52406602d03c558480c003418041c2c80c0c541a040c800190307014030031211a03a03540b102a20000e52821a003500c1c504040011010075117103c1c078001800109503180d183d03880e06003100c044072185030400c0d540b041400071052142d1071143c0c091001d0350005110074403100401c2c80c2e010304104000015140c4808600e00303c0d01c2410114082c00508020407030064004500c16640142407031080000c440b0107550485002c0c10f10203251045180080140c0c1740d6200800c15200f0440c10081141403e800c0245607040050542204d07400303129070f071098561045000c01c60b102048441d00e0300e5070301c0e446801c413142c0101150183e0600c50602481a2942c0660250b800e0300e0183d9070a014240d1a404011050722030340c40300802d9a000070003c00c01b1039988101811034401c009199a103850303500c00380d03081d1000c840c101e80c0302e0103003001050200c2c40406104681c010202515228401c01a054811301109031101440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 421973696 1250 421972446 421972469
    0x1200616090b1801140703030c09050604030302060a090c05042d060501050417030d05151228020a091103011d07120f0b030706120608070308070f030e060f03070e0d02060301 76
    0x561981e000d0070040c1041100017611036120080d40c04d004000d009141036520200701d40c10740214503801c1c8181102c05881d01600181aa1303201c2c003a075480140801e40d004d4034011008800455180c1d1070340605407103154040000020022050003280000c111406041d040e545002c10400099030080e05403002c81c0c025450303c0303484902504429041d48525080d42014a180808110601c022100c8041a9840030780c0c5003410050700c84840c41c0d4582e01071202e4402c02c891f01100c06404101c01039040e4042d8800380200303410744d07900c424460580e141d1180b488503c190110050148241c401403001c0c0c001d8148850350124201650007a000302c941c980001c25694560446903080c840a4002046504019045030341040d035074440203101465080c0d8610032541087d80c00904060b0004102c41600e80103002c1500e0251181d98048c09100c001d8001c03000c0c4100070070481956550234014105102074500210764a14141078024401120808418441c582c042c8010380543c0f140d205880c10b40b007014040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 421974946 1250 421973696 421973737
    0x9090b01030b07030b18041202060114060c03070605091c03060302060904020f07120302180f03060105220c020106170d08041e050f07030c0605070305030c0901200616090b 75
    0x32005800101312040e0003880706100001b102c4900405684214060300100c1d0108504a00490300c8003020312500300c000700c4904003900c0e1458481d00402448600700b040720703c0d01110f5134038401591811140e203415908984000494226952003002d1524420b141c2080b0a0f42983c0c001006030191a100a028560210310001903824803c1213421031038019003080e4822500d508000c02075408030b03c144030b212440c01c48180c070b00e0902c881800102500140a44603983c00c1c0028004200755290f8060301e403503004c84050a00722028410070320166896400407511030b0510502c04014004102004840e501071883ca0070450751042105401560010341408115a02c00c0904180280f161018100e0300a5200e040055100010340208883c45012080b176a50380d03130036054465016092028022510404c00070301480c0003a0001c124800341418aa2910000d03213032080d00200441c020780ba000d030700450a02c1800d00c203400c1c800792081340c286080c400c0745085c64190140c6004142d045001c581e5880b40c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 421976196 1250 421974946 421974961
    0x109120c21090302043e07080711152d030a112511060705100203040f0803041202060a061401030f0f020c0d1e0f0e1f030f050109090b01030b 62
    0x302e450040d81c0040050144000d03107000c400825800701c051441c1c0d8241d8102e00550340418040418102426480700c3e4106440c90b219420107500c81e280c1224045070601c01c2480c1562101ca010410b00702040115485804a80c4a550080012403256a07481c007500c0c20780d0101e0110a040700e51044440c4800b1030a408120402c60b07041c080d0f1603407000300002000703450380182d079000000c01d01580205400203a002e22001484098400c050002d4456048640b2012141c000c80c1c0045800600c11050013840c9545900e4049458009403411503198032025580d00020783c0c10414035401c1101201c0801105182001c94404214640907081c1810346440840f48410159444241d902d5050041955110200c01d02240c4920558090720041844024240040042614482e42e070b14426101c01310b0703003100031105039040606d0780000c9500c03070740a00787c015403500c001c030b82c15500c1e110030348022075032102c44407141e400d50b20144c200f05203c3d441d10300180e01090915401e02d04683d0030454041c51ba032600035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 421977446 1250 421976196 421976207
    0xe060108060a14120d050901090f05010f08091606051c050c09150405060a03020403050f371202100c081e090703140a060506060702030c040c020109020406080109120c21 74
    0x59070145400f9172100701000300d40000c02401c45c3d000980c0e5140701e068454114200c1c2511740e020303082c002211b034905d0b03000380ca020b100c411742c00c041404101d440c805061140d9901d403940c25000b90700011008540300d105a813140e13442c0402e0303411464081c0700518102400e901107000b04941d00d8404e5a0b900c0455012150b00340443e00984005801c0e10b0791040e40b260050040e500a12007184e491040001d183c7d51400302280000d075220314105030603c0d0758100800507130b080900385405040b00806010400000790803040840c05401680c01034004a80440c4184048464106c0002c0c1400075aa0421103000100d080742c505200c4001c41040c544e03201c8811080c600195900001c00d21400e030340400d04241c0b40050340031000c80c825035050042da541c8000340011809041e500079015030004410b850b6625140d08100a400e151f1320001607845c030303650002000e8030a60382c415a000c0e5076030b12181007032141018402c08041c19500384103002400c180e46258116190300105101c02c603919118100e001e200d007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 421978696 1250 421977446 421977469
    0xe040b04091b0e0c0301060c030f030e0a0308091207030806190f0801091104020c1b03010b040f0506030712150b13050c09030c01030605181009060b03010e060108060a14 74
    0x3103100802c4030300900e95594800ca583c0215990900c400780060100034103541100d0584906031b80d40800d804240c0e038150f544441c070758250000e040c0c5130348102d2400b140800c024042c0d1b5000340c0d96504e4a040c0f100e4041e081465555504406a00404c0303e0000300317800280707154101100741c2e00e008400441ca5807129a076a6190807510b1401009080000c423081c05400905446000b02d401810949071402004100c0c42aa41030354242d1300000c10601c2d001e450102c600450000c0a400410b91000401c0000c044802100c0661040780e62401400803a060420495025180c0401445880d100b5501c440e14020081c2e4000b02d10182c441c82c40b00920740b641c1b03a50803482031301128244080d081c2000300390407580060031010f00034420840f200032a5071090151400720b41c000380024404510403940303c0e5189000030007807014034800e02000a80c0c1e1a05100b11001410501141a102d505050030800710780c0300a841a8100113811092203032907540c03074440404a501040c03075104800340b035902054180401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 421979946 1250 421978696 421978703
    0x10c0c03080c0d0305010602060f0103290a021305090f181504030302220b04090b03160602060708150f0f0d0b2505041a0903030d0203090109020f0d030e040b0409 71
    0x10800000b488030010b40e1240340c101a40f42444981c0c0c071010101d83e10201112a41d9204684000410104a02e8100d40c0881203814540c040c3e542c4d5000996200c0c440207646409420b6400501c1841141a40d46035001920041b0b900002e1410100c546800d14100500f84040c02c2c02c2c105181308400000f00300444c05007144032039010580c5402c0c1800b170001e400070000d41c441401807449642915061703249500a540c60b011a86052500303045075000101600300609406224592803440d80342d56955603403005042c182c0c010030781854140001802d42074090b14207000a110025680b4459841c192048124141070320f82490441d000d40000d460f241d00c03108040d0000854009000702d00c160741011040c40c1e0381c045444a94011404c034110b0b042d10a0344283c20f400d410a0601015180009004104808006080382c0c00c01300854824000c903401556400c0b09a0740d640d10341411070501c2528102e100c4c90441c0c06108901240d2400381443c44078801244c42295902030610341a510742c2e00540040d0f40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 421981196 1250 421979946 421979963
    0x180521070e010e01030204050a0c1e02070b07060c0f0503090307030c02041d06060a0602030f27061c0c0c0201231605030c0f0c1c031403280b0d02010c0c03 68
    0x2550b00020000c40e10031700041c5c0c000e600b8140003e030450218042c080780407070035554154441c01e0303040300030044000545280301107005070b030400a203080c0460040d000203030040b00c0004100e403031904054801c00d00d43d1030341d0b01482018402c101101c0804015200c000da05814004118003503480043c0082022044040d21070060fa8603865000c0700000d291442070505680030845d040d114001680e0701c0c055091549440d040800030031265400c620891035081c40c1c01d810030465800700d4000900143c00510803102c0812000e9004e0714802424090300060760851b08145800c409603400003000c40e8982c1403000c240600c8074000031070444d1941d084558103250003000224007043e501e4401d031a03500941c01050107105214050501510200780d070701002c0c50017031003074503400111142c2158803e5054010340c180503151400381d80d001e4100006502c1013001000503488552408401038880d0210742a29180c2d07440d10040284ca03488540200f082d064090900070704011451070200b04136842c80e00020207081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 421982446 1250 421981196 421981199
    0x90b030108031206030304050d0609080f03181219030b0d02041506020709060b0a080c070b0f0402011205040c12020622170f0607030e030712050a180521070e01 70
    0x100880030701261000074044240603104c1c071080564a001f24001c4d503902180030184c500006049034058207002d8481c003d490301740300ca1102081d200760400c45801d01c03542080908a00350800510503030f107042d440101d6007401d15018010364140c00c5c200500d18018141d907905000c82c150ba60310700ca091000d80c0100203004090140c40c070315050701882d2082c080507200711000030403030380ca041c0180d07025a00403c0f5228240780c40005e04459141e00500910380da00000c100d0b60022a0003201d042d07100f480c89052081180c1003510004204411050002c2c80071444c100034040021001c4078410120382d4155841421528140001003076489900e0b0410062101200c4000c03e2913076060440007103444a0320b182d5509503107490700c0381c0c44d8004149143c560341c0210700041c4e12240280c0c00f03140030021a00840c0c0c00c00503103644580d07000c0c0c4c480301c4400c046900070aa020007240d01450000329540c00e44d55540c0c55a160101140e20f05d4240140405580d40549220315000d4007002824020100300c2c8100f80c465 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 421983696 1250 421982446 421982459
    0x60305030d05061216090e010603111c15140a090b012601020319181101180902030a0603120f1d0325091103070c24230601080105031c090b0301 63
    0xf1407483c4540c00c141d0b814501c0c107508887d41840340400b20780c1c04c0004801c004444204102c01d40d500103006c200c08101c2c43c1c040300040750711203c01c03150512070031200048103520941603104010b4000e01d400c60a0341004650030001709142c1945044490751140740c40c00001c0501d11010b190075119030724200f58404801c000c007240c0750080c4080b0721840c0100410134944181030311801710f0121388000d040085580740204840d40b052580080086011600060050700c07840e07044142d81c416610b81c0c1c42c0e56180c1c1e006005000c81526a0400e500c154107100702010032940300a00140c407810300035014082002d6075070409860900100f4510800c034000125001913a208840720201e0b103018504a00386014600550005100b04480c000e12094a60001c80119940da0581b29070752040f12994070901844501c1d000f05840c0100e1740401c00d401c0b600203003840c14a024025051f0000d00b014100540c4000401c00b0741c80c045181500c030340a142c40c10283c02c4540e101501c24560940c0184070718070002000040380e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 421984946 1250 421983696 421983733
    0x201c08040b010806040308010e06040207020604120605010b03090c0402071e0b0106081f0509040f060f0902040e0604030503190b090f07020f0601080c1201111b10060305030d050612 79
    0x8074071865004145980b10502d031641c4e0f00741110001c020a0382d110040c4074044414036290740c403540041015151142d9030b80810b00d0344e0881e42c0300c00b404031403001d4410108456030240c0c0d0b0151142409982c00c40c5000c082d200c2c0e8900d5504845805668005001414000c00180380d400c074070701c0080901f941c0c80c06440c00040140c07003441441d000440c07002c080b5210b01c407544500140b030600540300003011814101003011a003005082280d9031803100720000b000580318000c00040064035a800514000540148001daa408000c00384442e0403c2d0200400240c002090701e0b0030003d4448004840f408421040c001003006000d25079010782c021b07040107000261190b02030f1007010a0350030f03102e040c1202c0c070749030340c0e41c0741c0031f001b41241c0ea00b0050800c115820445895054103030400000300d130041e02c1c014406050f40c401706550414401052440384641c0080180c2c2c2d050188015041040c0703131640d1200754503402100c2c0d0501c20507407501d02080d1035556803003001144c0741c1c8410580e00624003400c040c905 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 421986196 1250 421984946 421984951
    0x70602031f0e07090e070e0d060522050706050913020c03071104020702091906031403130b0307020607030506060c0d03051f1a0f042102010305130201201c08 69
    0x5a4003148408980b4805401d003481c02a40345844440080e4107000101001c007900074100c3c030402c040e01062400c19a100154011480e010751b00014440c2462040150705030130801044101d03142102c005c07000a200024100f003114614540661074074411030020b0b603803000311481da8111600118880d01e88a5001c401400c0f001d01c10180845a0a440824002039004000000e940030381c1e040300040040b50b260302c0b001c240c0621035000180d881c1e100d0380d4920035001034103070b196141d900c04240300c41c03502131511050001d420f06420300b80c20740c84c2c036150080d91464000d140500701034649010451a40f030710000da815a840300c4081d034454880c4580c004006142c100c034841c8880102c5203240490540a0485900342c61060000c5c908160300030300420a00d5014200032404031004000006d0072813410002540103648140d14907014441c98000181a02c0c00036080c4118000100c400c00010307071f0031040c1020300104240845084072802d9101504001030b40e0f240030040c2000741440a03811303601400030352 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 421987446 1250 421986196 421986241
    0x1b0717010f060531150510140f070303022803050a052e0302150304050d03051918050712020310020c0d1211190e01023007060203 57
    0x48510242601a41900c15074030034513402007180e034502a9032400c01c40b260714003810303640e420100c0c8001850501003110001c1d43c01d443e1580000c1c406203d9440d00c00d81c02e0310b185580e8a0f1850700c0400d01c09244e541441501860402c00c44005403000806000350141d40810b04000d5a2650300300d00304c00100c0000307582c2d0090a000030710b0b20001400e29075192140764065004041040c83c0300744042c102029101110f42408211959440b00200607503804c100060420f0040f0150f40d12402d251404500c0c26480028140c181410b040c208882414851140d0702402d82c15540441c90300d04a030084d0b05041c2e14a80d01411900403c100412402d81440d003145100303100ba001c40300e441030103940d07110803030007981f4070000d840d00100c0903090308030310800c084107070a4180f4a0002d000500ca42405226038020a00b001c401c841d06018013014641011030441420000c1c0003401d002e0031010044113064108800c011400c41d10340e0b012000c1d1300e00c90400c0e1207120358404c1c8115920b040c00084a1140700d074004004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 421988696 1250 421987446 421987451
    0x6020c06071a1f0e07200c28030602040602100c08070804140d030b1c02060a0c080c0a1b0801090506270717010c09030b0105040902011e0c0c080705090c1b071701 71
    0x302606e403200004150031035418006000d100521000304002c03403080c0354400340209043d01a00ca410000c0d032100d10000d522886005a03110302c1e001c40a03042000705c20540400324600f600c2028003613005900ca69100720301d464030400569035803420400449510309511050b10641c003c0c0406103070035906c441080401212101c500511842100c49213a0350100001c1d0040c80c18003424403a14020300181c2e070303410320501280741806920350002d4900200d04805441d01011200041000d80c03006100384064141180240035080b1180c80e0981d980c1801380c06640410025030f034044101510401d8103002d00d400700c0c213440e005903440381d03408202d11217200343d179696518102c2c944000ea170081352500e017101d920142c103007240d0386807004010080c81000b40c01e0703040c003800e1103407000c65590b80c095820302400280c071210108070a6081c4808a01c0392a003054080307500000f02801560b44441e8425800010a216a0b0b5240d04030b502131a02c810b03c031090650300f445071000214110080c502080d407100b5096008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 421989946 1250 421988696 421988717
    0x7061d06100305102307022113050f06190905040c08010f080706020a0f02010203090a180b0405070c08031005030a05030406030b0301060b0403030522090606020c06071a1f0e07 77
    0x410b0407180d01440544d05d030903000f6241000c0d4020444a15840105030040d1064281c4c04400c0000e11102a07403845900c1400140511546044c080074401901d020303546800c9525042d80446e485110b05d440d10303e254030096103503c7e4000d00c10f02c0d40c0070142c031010b04107100209482c84081d241d01804e02802100344003c89011481a00000d10b003001c1380c00c50b03401088258003d0b1140f804845c0d112205a04500bc1084007540686581c20804010105034400c00d4a02c0d880150000480d07041c802c2c1644210304000a02100c6a801042e8460040e004070141d40d80340c0798828440e0381c800e07591b403001d80c00d4042e1201420a110010001e0811a11030751001c3c0140c2c03000c20109400c0315110702a030f0058200511060000c03038802c001410460360340b800540c0b20f00b000640b5030b4424902c4d0764001c1c0d200d0b41e10f510003032128a03410300c80d0a200034403d1f101c90342040c945907210b481024444d184074090004407000561501c035070f20081645003030100007801e04951900d005004c40c0300200c52031008248402c2c071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 421991196 1250 421989946 421989973
    0x302150708060d05010f02120a0b10020d0e13060e0f0106020a031223091b010503040f06052d0a0507110706030e030d020408101103090307061d06100305 67
    0x90040c03040c11141d03036200c020741d10581040050903502c0d0702503565650300c104421081d445403000b085003507849102510b242c5001c24481042c0c818804505000e00380c094510541d40b50001038180b4440020308022401d907613010041034a20941e40d1803101524140f40c0d00041b0070503042c0340c990090040e1b00c2290280d80e00d074030003a40d98810b4440000c00044658200c030781e024040d544620484451510000107a0301006400c042241c0240e4141907039030007640c2142244144000207004040003070130003a00303500e010307140c2030b0400805600141409440b800007031500241802e003080041c00d204500c00084201c491501144031040740d03146007403407500c40841d002c24025088030200b407241d02d00030001603043c03101c110054101c0309010007182c88107001090003001c1c180082e00c040d28401c8014003000080c103000106952644002c565a0641001032050000d80401100c10068101c00d020800001c0c0c0b001d40b00e00800910042602030060314184880f0742034640340c0c18210790041d41215480922180c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 421992446 1250 421991196 421991233
    0x1050706111e0c0601060c0c12141c050301030204020d06030f0c1e05061b0106180906060b0304081602030c04020309010c080a110403030c0f0203030703050c0609070e010302090a0b0a080106030302 86
    0x1020f801103a0100c07004110051240b811602000e2194081d059040d690f0385840c2e1007030070300640440752405064503030016aa000c005201048203094003840c40e0281160000d010341c4010302010b4051900068032803048503141d00180011640605d9003078803034000d030030704650046850084800005e1a50f10710050340740040a4072040e50b000a00e024580b50f0300c0170034022400c20400942002c1c3d502d07003c0004007281c4816001d046107c9180d804240c640035407900030304448141e000ba08a03c0400d00501012500c1c60b03040d10f03402d07518825090f03851101800086d2070300414040c0250b1050001003007010300a41034210340341c0250b0030f44a03268940c4801c00d80c030082d078072a07000d02050381078180000c0000c17074403170350b40b01d02168050450440d62440310b40200c5c0c2141d01100059010030b00008032116000780070424254425502c0c0b01038183c0c50300b07015800e441c841041c07102034441c24004000c0b8030f1616159100c0c2d40300007030003811460859910014540602000c0c0b01c03e40240c0603082004001140d001d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 421993696 1250 421992446 421992457
    0x50a210816120f0917010608101a030105041e03091e0503060a060303050f09120609010209120303040510020c1f0b0a0509060f0105030403181214010c09090b01050706111e 75
    0x142c44010707000b401d203031140c050144001d100c030011b5074035004c1c0000d51450501c040c02006051300c0000c02c0c810040ca50069440001d004070078000c0c0c2c0b50100300408501510110911a83e5900c9050b10030309890600320358540058010510f002c82c11002d07160309020807a40d0b201194403e80686405540303580c49101242e19074480070b000300300100850780c00704400c84010070080c6401402010710004440c3d4052401310101c650036800c0e9400a541041c500d4202c415003103d5550000031440c500c0c09030754554803501a03580d121403e41d00820320303000074001400981d01b20300310034269490b1540d84904260140121843c6140110f807000c0700400c4904125500c140701e1003015011000050000d401100c82d81e1005200703070104403030700000c1d090442c4e8549640c0014191a21601104680c6043c042d0046400c2e459917512a890b100c07525006540081281e1b080f0781ea0140002802c91001005960b58842d1040080c4900d00e0602d404c2c01a00c011070141c1080500012080e22091001000303403002d00c0342 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 421994946 1250 421993696 421993727
    0x160512010311130204030f060608070b0f2808040b06010207032102031303080d0b011706012717010b010e060d051504051806070504050a21081612 64
    0x160018804a400e140c1c481010900c050704404024180300000e60803a00550012121514800041e2041c00300b03a015410191003100f0203010741038941024039000d40301e80e40402002d0708020580c070041040114040608000740214500548445c00c0024942c440480d01294282c1108000c2415544000351250a0740e074880d041c8142c4107000c042d8034840c00e2904240c1c2045220400070030403421f005402c4c2c40011403050b02c10a8460303105d0940201661180ca040a040251954600e00412854040190071007820300340f1690380403455440311071240d40d0001028844003e07007070000f088540e0380590403000803000007c110b21044900119154141d0b1202e2980c07060b001d01c030103591000540c1c0300325000384a21031000050150000400c06440c0102e036165a11a10070086100f501c0040c80640d0b4400c0e900d00d400352505041130300140b41070586000d294081c052030b88000d04180122100a12126003150130103854109001c09401944130701102228543d0103400903501c1c20380106d84c900d541540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 421996196 1250 421994946 421994977
    0x1302030601030c1b02040225050a1a040f0f0c03021f18030309260114011e08030a030e0a1505190501030b010603020c01091202060718030b040809190e1605 68
    0x119401b0000650014110245c0401070910100b2020200c0409001c14a2061001d002d00c2e09141c189400000407000800505944210800c00056003800090b0070655010f49103501003980f6041910080845400080d049400301c260b00041c8148090360101000316a5100304500c802010150744076401d03880028041446032205110b80c50a14120000c0c00825100743c01c524098041d2040c00d488060820800044171540180310340d03a0003822070301c00c14070450209030007103160250750350740c5c1d125040f5980100350703a51041040000c828040880c1c1c0c282c0000c06000555041c49000000784810b5502001c5500b80300002d203a0704080b07029017030480360070141c85451030f8071303000d41640a0f5000c042158902e5690301c90000016a5828043c006006203a000f07100500e48108007400420300820300b60409c940720384003000011a1035051681c000e511150443e254a134443c080303001d038600c4400e019000000e411010070444050b021041c421812241d26000c0780d081d4600a81d058418004800008207 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 421997446 1250 421996196 421996247
    0x316020616080403081b0c0102071a160b070201050f0408030103171c050a050123040b01170114010206070c030806010f02030d020c06011a040b03130203010b1302030601030c 76
    0x540040507144840454415010111096076281e14662080e00704850303041001c200c86508611002d950804030881d94001c00c41c01c2d0700000081d5444e1007500c580c100b001d4407071000c15140e030100c005460b821f602d03d161001c542c009030700e0f00c022100803c034dd4050040d841e010002e04603201441d0024013494101801c2840c43c2d00f1510784240c0c04400c0e00c8105444030080000660b0042d40041c1002148000034000400d401e000d0f90020580d00180c3c0180300500c11400306100081d4868004840c29000b01c0780051404191300040e620705803845007840c0201040c000008a00358400310780408054240d0954030b1a0341d4443c1c050755140c094140c06400900e840c1c0000d070f510750040004141c408041e004480c104043c07900e4050690f0301511406046820140040141c50108441000081c02c548400c40c01d1600300920100b42d40801447c02004280901a40043d500c003940b018260075005055074907420b0740c98040002950084d44c200d8002440c02010302e0402e48a01c1c49400003107142c600301e80b91403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 421998696 1250 421997446 421997449
    0x60b100f0c1202070b030a05060102011104050a1404060807030b07020706050f0f03250207080c060c0309060d0b04181a010806070c060212090d09090507080420030d03050117031602 79
    0x101042e00500c4107502c01c542022a030b040742c1402461207031512400200c0c41e40307030480009080d44c00314129500380d1801440240140e984103001c9800b078030306214005120701400c90019025000661180d18603025010b000300034030040c802c0052051545030225000d066440e2002c440c0341c81035041307090200c201806084070b20341003a001160081c084c880c43d0303201c2d4001c40d03402c5138038050321400c039001503481075604210200d400c0c8022112880100d5500d0b091160207110341d500c038032400c50881d2181100080c0e01d005244a07a00100090402402c01c00482d0100d144450300c9074010001550070342414010404c00b5810046040d051b1a9034401400040d1035201080e1030185151034105c1c3c02c0794090003d00d2213a03207a5981e06114064210007403490403003c40001d041d078081c903000300341d0302d5080001b08042e40d50408010358101d83e105840195884803001c1400324601c50020066041c01036401e181501d40d41508068140c1d56024048a0031700c00d0b00f034050703a40c3d2180b0280ca9061820188200703015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 421999946 1250 421998696 421998713
    0x303050c16120803190e0705031014060f0303070c0801020324010c170403080309060a150e0c090a0b03090105060a05040603030c0602180a031406242b060b100f0c 71
    0x2090b101d481009514800417a00000c0c0d0f0454640ca220343ea2000000b000305203020408505190a014000c110240c20068540300d1858002c000b0b5000c1c1201c030523003101c103440410440f006d007900140f05006054403081514080c2d0700c1914031200403d0442201c10491030000c0340c05054150503190911641d856954140c2d402e0003080e89040650b41c144400800305038042c0007503205d081c100dc041c12031031500021550071218401480100050b426000744401b545800c81c264200d000004400d4507545904006a4101070941001c100d1081c08424031105c800d05400c80d90003400112104802c003034485041c0400c4880901c00034001440701e10794500420101e50081035202c08811110500ba050a40411101181507000b200c20103180740c0b1003500c1c0d18080c00080d4220b00070074403501c8015041c051122040c152030860341e00c40c84400c110031406082c3e8910b0400780c0313a9841382400e0040d4050518000525417000514010702c0c000700c1f8200b0b110311450b0b43c02004092520380c2c6022a480c0d45480c0213 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 422001196 1250 421999946 421999951
    0x60311101d12030a030920030d0c0510090f0201170915100503070e04030801081b06090102070503060114030f01112205130b180402130c0c0c0303050c16120803 70
    0x10010030300c407254402400b080c802400c2101c00760720007042245143c50142610b000403ca55410851000e4804910f0341d00400c80307100606c00c61401d45030724616400c04500300400c070722880d031106113818512800c0105824442ca152030003621a4a452900c2d002c044000d000201c8480e2100e030024042d05030004480040180c2107010039400383c1d0b9407500d41b404a40340004d50382141010b40640c0040000301a4803900050240c0100806010131310300020142c1d80e51502c45074050302c40c150128040780700ea4801c2180500034000201101d510b941c2d2054044a40071002001600902800c946c201107003505004400c25510b448002900c0c2c81a502c2c1c0740c0fa01110f003e0307071000f203031004500006426580d4141d1303070720701c000100000a05203c0100c1000b003641413591840c3d0030351100c1820030000da079644200d25605226000c01094207284030101711100207109c2c02c0101000c2010102009143d84a0080c1101e240b649040711203081d000c1c410018030462910418151601641500c400511403501464 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 422002446 1250 422001196 422001199
    0x23060121140a0905011b021c050c0106091b0e090f040213060b09040c090e0f10091a0406061121070503040b030717041e03030216051006060315050409110310060311101d 74
    0x180ac1c0f08064041c50f0a4074200e0340a401c60a45a04003100e4001d10304406141c04000d5013414014800c41d60041162400020300041d85c0d100f1040002d4195290500400030110300700404015064071030344486056002001c4a034021340c50a0180810380d4001c000349019141000340c41d00c090b49d645940700d408a58020002c9082881030440041c15801501800a100c0389105a107400d00e0080014041100d507107603c0f030400c0220203000b0011a000c00b2552586690401c4000c40d01e50804460700035580c825088003c003244000a000280c00d95400017443c040c062666404800c00441d04075110102d00580d80070b072020035281c8901c8580b6203a40341c0014200d01c40d003409420b005d603d003411601405d81c0c1c81c0c2076800d500240b048507100400d6229000c01b40c9a642800c02040c02c45a0410302642114061301e070247e80d55001503000c0c011503116003a2034680c01011a0a13a0003103000401c0600740e20300c0210796140c0000300605091410058030030740c03615140d8a40000c1100c91007144080003981d0f681c207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 422003696 1250 422002446 422002457
    0x20d0b04060212090a030e09071b080903030c060a05090a150207052d1606020307080d11070f05060703020406050306060a1403090123060121140a0905011b021c 70
    0xd83c0300820500c0d0310b82c0f149508201500000d112810081c005103c1c5405983c0f0807c09002089420b54000480001d00f641c00d4000112110962410410510912800c2a4148004541088400070018050b41706030300c000c00902c140e441d610721080c0c4e10001e562004020640202941d004c1c0314160307010b03007546405213085900001e05681480c00c2001001c1c6032120f510b8031483c80052003402000380d01407011401592a03091450600025140c0c0030703001c4000e109202c00501e00507200c0d4541c1040c2e2165411030001580d0b16110301d0001040b01d84100c00316101e006500010b00301170300a01c00e56085440b5a25524555034070348040007203a600012804c020f120080d42440b15514010300070714442d503c0040006141180c000441402e10041113510102c0c0c000003080052590380040c4154000d46400d41d05140398041040039030113001c401c00c02a000ca0a104200000142180c1054075440d0060303000700503120004100f0b941242c018000c080259020007500d80d48004491011343e000e503030900d0407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422004946 1250 422003696 422003707
    0xf0c01050724020a020d0c2012010e010506130203012303010207051e070f05280e1f060302090121020403080f0403030e06030106021203190207050a0b0c07020d0b040602 74
    0x2c0040b0070004100708680541e001c9508070301140c0410420005022074105a507410b03e807542c0f0100000d14452200014034085100c0950b95114642080d4050101200901c000c080c2c8500480c002c01c0d0031101c0d640b190280100000140d04544203c81c103a40d13810a02c25410402a0300c42e4184000800320a80c05640c05c000c1040898800d128102d00b040d4004580c80c15405000486c40ca0039a01da00880000c180200c01000140e4410304c451001030515412b4080c1e8408613620000844d003030b5405041103420300c0040104c410380d00003850040d02c4800300941c20150b1564000c030200c0c041c08105601203046c88000c02500c050000100c0080d0001081c0986043d4a030354407144590040e040101c58902e01103000e204042d0080500700710800e0070b03100c841c01c0d9850100000d60300c2194060600040c0360010100b18031903a220045030907003081e9041907581d9002c41ca0115a103800303c150540d440340101c000b203800114500c04640801c0e130000c0401c030814424bc0c85070012070030050300840c1d2880c3c1c20040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 422006196 1250 422004946 422004983
    0xd03090b0a090f0b040506070f050109240f020a020303040f06060b0714060606030403050d0c03150e090c0f0f1c0209100e06010201020304020105030423030d0c0e030f0c010507 77
    0x10101c4001e03035925103500d20f00c0c125030580c400308070f03400c00ca200340e6061105201c00c0c0c681c01c080c0c998240d00700c84c80084405117824481d00411400e10081d2403205003101a2030704032030301c1003000b903c2510110108410f06400740d0303400c102d009405600005805c1040490b000c90390540320780d410580030f84000038550340c3c0c50718013154a070711050041b69220462005041b40107402c1c405283c0c402000c5e0781c158918a4180c1d070061061003240890401c0b140d035042000c84203446640107040000d01e1502e2420202e4843c02c0d8008c6440342103801044070320518600740c141d800d001d01800406940982102c05040541e000c0040000030900c004141c1645100c00e031015945082245001e049644502880c05003482850820060000c0003d81560b0040051100607684102141d40c40390700601c940c00326806800d20340074020070340006001c091001246211031844140c1c410355180031252121804401c0c07083c14980c5550f0140c002c1c80d41900020480d043d00e5014000914941d840380c8042c521104c001e91 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 422007446 1250 422006196 422006219
    0x80a060e130212150403110307121205102105190f050601060203070c0b071103010c09090e0708100213090c08041101170721020c15060a0e060d0309 65
    0xe0700284224164440d24041d0300300a10ba8500082e10000901100020581c2c480c0150401600060030040544108400c02d1000c1c0151001079601c210315018907c0f2034107000341a8001c040401e2806442c1c0b50208401d640b40700c1d9040d0440f0707109040040c1b4040111034440d1f1014030b009050300c240c0a03000e151b004007140c81d2121035009102e540c00c0c90050925041035480c049058010f070066501c2004400041809109040e0403204401c60b0399a0340c5001e85441d5004000c45d81466400d582015280104650065900340a031004400f0070028042c14403841961040c1780d114001954000d0502208144125001065080b40a800443c03d40360b032104074004850302c01100340c000500400500042201c0081c001424a1091900000d82e0080091a003883d40018120700e00303222816005480d4810100010429128038038811900c80c8080c0701c04a456079030608680500b64030395400200036150480396074003620f070300221800250307a44206111402c01c2406081d410300c0f082c4640010050341d00c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 422008696 1250 422007446 422007451
    0x240a0504050c19140304081b03030a0504050c030304031109040218180c010e1309030210180b010815040609081c1a040b03030a0c06090503030f0f0703091101080a060e 73
    0x10004507680f00d03059000010081030f1080c20000308000502c2c091007104041043e00c0c0c005802400059036400b21040a081c4103554182c0090540008020008120f01507803080e4801c81c022400e480c08140300c0410544c46c4c0c407640c000240040c94100c20004c41d030608800107940184040d01c4100c1d201c107a1184101c0ca04c0080702d50700d4280d95800907004030000706110b00d0004801c2802c01c2036412403a4400560126080c18000c0301003540c070308250043c0340c0300708040581045104001c00c54501c072151f1070b41c0c0c0c4d40c2d91072000341c0b40c0722200400081c01010002e00c4201d80342c50108500d410351140d0780c900010706010320051b2044241409a50007040700001c489507090400100010f84007140700e41120712000852145100710b01d8000507132100c0d00c0210032142d500700070786031000822806240007401050441c80140503884040100090004580141800750700044107442441e0f68141c0210142c904e4418001c0458801001680545d4003070180d00e07400c0301c0c3c00c0001042560315001d0810090008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 422009946 1250 422008696 422008711
    0x10b010f1209050a0b040302070501090b090d061116020906090c030121062310061e090f060314010b0304050304090b0d150b0a080304152102130e0609240a050405 71
    0x417013052204258041265600500003030820101e105d20344550010180076414580b40603441852a40b41000090b44c000c060808042000a80b140b00c800c0380601e0780c0d842a0000c0740110b40440110b4030610307000614a101e1513081c42043d02c1d40c0c0c00c080c0c0c3c924541c1040201c031964034550b000e40c080024502e0155804070340b540e2145007540c022240703202d0445940905280040810014103200c0158080f01904813800c00c40036803840400c00300c00c04c49040d40f4540c0540c0c0604100c070804508140e00d5003140c0203010440d10074003461303600d03260b901d0304520003a43c008000b503204000070003061196810207021040003e110403c40341080d120001c01c080b141c01d009c1c1d240307503950321000128600038480340f018000c1e9030021800d103030404c810f901150110000500030300c000c11118020102840c0d603003420300c81009906648459a590401c0c50b203c001d80250b0000070040000240503023070402c00144a29800b803542059046100340c417040188401d0310203a003000c009440401e8507111170040780d009668 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 422011196 1250 422009946 422009963
    0x40b030f0d211a060a0e090a02040602010501051002073c05121b150412030207050405061005090d03050c0106060504031202030712081017030a0e03010b010f1209050a 73
    0x2c0400d1965500c0103040e1400282c500c0d12441e00400704160b04040c900720b01c00d407101c0d642c0b600e9141c41594a01d9131010400d51110030302040010ba0f402030f4000d041114220340081c051a40c83c0e00810412444001c1401d005071301a000070010480d05c0751070581070f17503040c6080c0c00c240031220300c0902600c0c0d581c4500220034010100c0400160403d05050301e480032145000d40303001903145805c02c2c25103404015051052461150107401c41d0078110403207005158451421f1414461803402a49030803451013254840d03454500069480c0c02c16843d04041250b45030344841c82e0035481c0c0e0821410644808041d03040141c28451089140d209214160160103542c4542d61960700c1c40c42d011030001c410b080c0c0c20007150001c1c886080000c0848000c0c01604410382015080355460928242c0c02041c25408909183c001c0520b1080c518004001484043c21310740e2185074101d1190149400e980011034054001090040c4402c1101d01c6400901c0e501400f81c44003040350007564941c1443c10031040404e640010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 422012446 1250 422011196 422011217
    0x10219062705070504020f0f070203030c010513110307030b04080a0c060612171305120109020301021305030d030923010f0906060518010501050d02030c0909070207051305090a02040b030f0d 83
    0xb030100400001403404503010361030b0608800c0f0b03203005402610001c4185102c0400c1071021980e00380151040d190301440200158900301941c018000c11f04481903501ca100d03880c6c0d08083d801c0c0807413a43c064075080420140720b510f40340da0b10340c903550003034004008002c0303001a020b001030b005014400060060030b914480c6c085180c1001c88138900c0c3d45103500410001006820411060882c4000480d80708a0742c1401d11101c40696502401101d040203506501c0015021b19000101c03444005a1710141c040329280c0085080690444445200190003107030004160b00301c04006400220a04100d03100214103c80f0585001c1e0540c2c50406084031556201d210900050900c0d04c02c280204181200c01c400652400c0b00180c81c2e446441c101c510f507150004000b0b2400315110b4100c2d0021071000c3e042418514080700000d4541702036000c1c242c855112280c400c80c1480e20303030240c140600c802c40060400051280c1c200002440041012074040c0507861480c080302c1801c1c841c490940c0e0541d01d8129000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 422013696 1250 422012446 422012453
    0x1407020d180503070311010909020c011e0b210705180108010c2307030c0803090606120328200f100507020c1302190327020102190627 59
    0x2250407000528805103aaa001c00c003943d0001031107021641c21904000451154000485145c0c4480e00402810b500000700012010070550101d00300300603075059201610440c440750000e0703030f11a02c0e40c554498134200305040711440c104001c5040810500c2110f0a940c0e544012440c054254006540241410801080800030a000700031729041a803030a0364202e40840303d40c440465a40c05004c24001c404603410040500640c4401c242540000320b040d268074202c13001a9590b08200e40c1c150007400c0c01c18010242000000594588910030004808855a80e8924040c0001800003032801c1041400c83c08000b0300c0c030801e0212100300c42c1070161414189101070246003013401c0c444004d026162008012000343d0100350034405500454403000c00b10b8511022902038024841000c80300810444a0080300386c06610070000c2c0f04810fa01820f241101025101c0390182c0200c0c00f030b0258008801c0c103107110b1400c503201550144a00c0e0002a260100708000104400c0c480207155a820000981020b2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 422014946 1250 422013696 422013707
    0x71707140904050703030503070504030c1403010b040219050c0309040203070c03020c0604060806060903100f0f15030b1303030e01090c03141f0903110a030905090c09030a14011407020d 81
    0x12001e9801452900346035880a642d000c41d40b00107001c101010000c03d030214481e004a400450f0081f512600c06074864141c04c0800c0340c0c504409100398a0188625030b41d085c540281c85044960402d0480544403006040d00c1d642c0c485040940680400c100303c500e5540d807480a58090340d1241c0e00c03404840c207a403401130318082010560341c1c8030345010301c020051141e016200651152003a83d640c2d4542549002003890b11010040c0800c07000d0800351524034030182944680b040c100303840e8051028074866030b84980d050360302c0d00010b0a0700b0002c3c0006074141e020400042d4030f1512904e070001f50040440405806c55901c0c1d40c3c102d03804103d695081080c0020005500348402541d005407450301b1158950801c0d00d40c8544d4076600440c1c880001d10107060050318000c03c6005203405031500e00c03503a490020003010751802034034400e8540c0000300303402074101e0082d105240b40150007400c031650301d51111038940d84d2441c045251503481ba095401c50388543c80d0010300460032034009101003042c64001512 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 422016196 1250 422014946 422014979
    0x24090b1812070b220204141603090203030306040902060d0509010606080a05100512030c010509010501030c1a370e100215131b0b04060305010501080609040b0702071707 74
    0xc40c0d0140102c1c40400d89403420f16400c03d402c82d06020700c040c1c4c0c07500c89121300d01d00c601000c1d41c8580b44c4810b040c01c002d885902180b2030001a00d12038555074008405504480e40c3c4035028ad0564424000250541416482810700030700090800d4102190301443e4070651707100720b91441c07169442d21420072045403c0641c454100098900900c02407600344504880d1100345d216080c42500c00c0300c10368410034010f000b11007083c0d40c00707402800f00d4a40420b00340c0c040c0c2000e00c002c8401c0c02c0031403070001307040f2080714202e201e03502034880183c03504082004400c100886c45260108030040c120454074140008041c10400100c1034560b032032140541001c20040280c5c9030b0b070b010203541141150001440c80d107480324dd40010842d40c49142d000c40c6040c803040e061916030000c01014403c043c04110b0908000c00b80c41180c82c15139080c031481c0e807940011161403000340c0d4043c0d00140b1140202d40028122007685601c810380c0d1048645059503409403540704844010300c009240c00000c402e100012040e010b200307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 422017446 1250 422016196 422016223
    0x1501020f2b0306080c1e04021602090105060f040905071b030c0b090f071a04080f0a0605070e09010b0702120303010611011104060e09041b031a1324090b18 68
    0x30f09240918041d141c02d008917000740b1403100d895480c8115084880048801100600115154685c0d4110031201266285007a4413070300c00c201c0001828900501201c08151342018813604162801c400d1001404010304005d01380081c00ca50a059030000e600441040c5c3d00a0391f4690000d556402d00b0001c20300c0c0505280c0040c1c02000481005c504005803001c102c400003145910780184a21100d141800356030044252800368141c200c1c4d420100080100b1554010300e030401036500c51000581d08854024603030f0381c002c12840300401410768003201500201c3c2c005440c00c0b0700f02d581d9642c51410355009802003004079401c041c265400410901c5162807125520002c6407405003030130401b50616500c8504240301d00300071400601040740745482030510032030503c0030800c1d440d1289072030300b603540744141c010710034000302c3c80091018101000b00024007904118054a896014099078000c102a00c501c85c0303c2d1515150b101000900c8050314034407036000991078040381000524a5810604503039a4013 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 422018696 1250 422017446 422017451
    0x50c0a08071e2f1209011707031b0503100605070201020a060609020c010608030306062a0303070302030a27151d03220b0409050402210606010f090e1501020f2b03 71
    0xf03003146a0014400e01510200c84a0075110048900100c0f00c0b044510440b8954469080500c000550160000f1105078501450b0a044042d40c4204891034001100c10804081c04482c04125036405031004040481c018415540c0200d4503071224021303180f040d44003107015075001803403e60002080c030941000d441000003940ca9400d03c1400602c0e54000c102945c0c40c250f1262540d404a003403441c1200c040004c040c01684c0d12071500c01c80150007908111140c3c1086801d1400031501d131001c16200050f0903d4444008088003c1600d480619407014021402115034a50528138100c2c1c40c05116460080d0b030800541d502c0c0c0702c0b00340c02c170540082102010080305403803c00b400100c025006950582d540c07650002460355450001079959003040e0540064201401a03016009001240b41c40c4034410a03280d020b4031118070700003140c500baa0740c8242d44402005001003405482038207034102d0041c0c014411030703500c0700d080030383c040c1010b02d43d4060040a564000032621801c040b0320710b014500c101d030b0504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 422019946 1250 422018696 422018777
    0x1120c26011a0a090c2a05060a060603111c0507030b1203040504270f05151509010e06030a08210f090705011b021c15020703080a050c0a08071e 63
    0x90300500410106454086c81d09010145c80740d201c00300d1501785500401128282e041c680c88000c010244c2d801403d00003814001c2410081056400310781b09891200b03060203449003044110ba00809000d0601e004154451403403007003903526150300c420f2280ea1030000e1950b0314504801c1000303d5444026045c880c01c2c118104000c8962221040f60541d40c1040000e030800440c0c0c6070280c01d00d103a20800044007910351082c03200d00d01c500d2a00c08541101a030348038180d640c0f91158040141e00403103649906921441d080030001d0020005021180b003050803041d0b4160300c1151008907050308846141e001c10184040000c0380c14100311900040800b070074009800d114105003000941001701010f40a0f039400e0095010141142c91031910068100d185e0040f154800341590020b5030000c11700360000750b00c5e1404039140c60010311a842c00340b883c50050a00e021031140c0d06a500b618003c000134184420140c0800d5420349088175070030b444055544900d424541b0040c2c002082d801203c0307662089a9181c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 422021196 1250 422019946 422019971
    0x50108090d1407050708070608010302010e0315061201140f10060c05070501081f0b0c101a0907050708130302091503060109020d020d060305060603010501120c26011a0a09 75
    0x5a1038000707020740e442c1a0368154a080c0309103410b138642c1c03291110344101e03400000c038a03034002d440a060320b100340c2e2400300c5001e11508140da40c61907801c66140d07400d014404a1264076044542c03d080c0241800045205030780144201c2c01100200d44070200300f00c20a0070800702c4481c20010401401c0941801401240291105c60f07880a044c040c440c18000040d01203207105a60147d601c40c8113606c205900083d80e291012103ca50300180b02c444038912880021802a0006002c2c5150b1054400d01c0719035019002420010b0f1424040c00d1182031141c1003003c440410381180061900d8a007802811100b5459841401443d400c010f050095517000503480c01c0c040d41d404600715044070900c00700541c40d000d41c00c000d00001e1245040041400c2e251040000401c80301240b1a40300399801c070000c03c1184c1e40c866030300c0702c03c05141800801d24540d407242072081c6411900020058640c24401c12040f581c8569800d0851b41c18180740c04414100c01140d8140746030048020000d40907090301070051442280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 422022446 1250 422021196 422021207
    0xa050601090b0409051f0c1b0f060905031206210a0204050417070303051f0605040303030e1908031b2d090324010f03020114130f090204050108090d 65
    0x1400da01c15848040c55601a80c2d5a000318810b51313040b00035251203550f0100310b924200720b05030204000506004989007010300409035030480100080c42c00c80d610400d131391001182540e43c801182c0c1103649030105000304a00f0409000b892034607030034940c01401c01ca800c01c440d03503240860a21500ca80d40d44000110300d03000c01c10000f200e40c140d4011800c0d4640781f1748070310000c0c4054400c250340b0f10003107441d009260f4181c000c54003e81095a090590030703c2c0f00c4500203e00c04038000d1401040003000f040001074407903840035a81c004440296003447c07038440c60344c034080d90003c40300f5210a8030203c1404911084107542e080c44055030640c051034000d5590fa0b09220078080041480352088411240400c2e14900045071400d08004007602c10080c0361880b6003030140622071030140403032407c8001203040e048000000c000e50781c058603060249060103801440b164003c865480c0ea40d180d10000103500845209079001602c8042e00250b166410940018840c2000a1a0102d071b1b600003c14500c44d40c1d04803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 422023696 1250 422022446 422022449
    0x9060e0705161a0c07110409052d030304060e0d0903020a09020708040e07050301030b090c130f180501240f030f021f180605190305060d0615090e0a050601 68
    0x1910800c0009905041c02d03c0c1610015244081d51400f600030405810407000c01403807040e1148007980803145092051108079290700c1d0300148141e10141c03007c916101c0c0550a02c40110207400a010300c0d4842080316811030f0402e8604451040d2070301011419081b081c170011010035018a0040c03880752450f0009030850081d403048c041901c1e400034000c2d040c000c207142114003500068a00b203800d030802d01401000307940248810341c0d5010f5a4404034081d004040344400d2121300050910300e01a44008250300103251894080020a550300308038002d803803115040100e600d000d0b8000081080c25180030f52000311202a4440205c08000018800c0c0e854040060084d241c211041e098824254404038a800388082c10b444410a411404c410409500503030320b00e81c048185954000c03e03551b480b41030f0340c0d40c05001049015440041030162220348260b218990180005005903100c0919440c1e000450340000e56811144c0400b940034860740000e80220811aa02c5030000c1c010075a03d5100e168864006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 422024946 1250 422023696 422023717
    0x216091407030b0103152301020f120a0c140109060f060501023007080703120920190311030601050a0509070c031206090b0306060a050109050105030615030c0409060e0705 75
    0x50b80f0722400709910130751044a42e1101e01000c41e888540703032801d11101d02080c603144030b2418060a03d203400c65101040c070140a092040042c45080103001c102d0300d15401c011400000c209055005001042203000c21510075004003000080d80c5031142804010303185203401a4801d00e00304001000281d03400a103484180c10701600a2409241000401040c00fa20889650030703a00d0110b90102481030340001400303118031a4441d15254081c06840c6021b0300c400c0d0001414240c4080030b460300d04000501e01c2c040d401001040c011140f071102d1a03202808030550070070b03030340408003410400c0031b806c0800516004d4041240e03282042c0345400001041510b00404400c10000c0c400c0e10740c01098054540604c0d581d608034828460581c84100b00380081c000d5003402440303842428003045450900b003514a0581d4010394850b40348505060054459070701c0a0299074102c29000ba0403580c66038480080d50080c20100d106035921440d00c62400300313a03001a08010203004000050000498100040b15490b027103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 422026196 1250 422024946 422024951
    0x1020c0d061505060f0a0e0f0603240301110a020615060406050c071203080402030c040506090a1d0304030308010f08012c2e060f08060c0304080d0c021609140703 71
    0x10910204207841c00b00c3e074801c5400010108440c20044084005811001d0803690380d880100c0c00441040104c0025244540d0009800c0022503040c120f0210f0380c152002020300f580400c1c50001c000b0138215502030030340940e07103480814035828a42d03050200c1900b0040308602a040c641340200094402e12481c0704220505c880000c1c50300d40c0c48001c1c01800010510b0404158100c90790f8200640342c01d00c2114101e00c2405a405d02c1d40c0b01c1d2400e44240d500483c1c0151042c0d0040c6d0781c0c040a00c0c001d000044103000003054112107886480d13400c00080001c1c5100b41e94078062540342070104c203034003030554100d01e415904100481c1031503502c0384859800c00d550308080342071041582c200203060040e03624140c6601c689017201607000708030780280c500d45030012030310800c1400d5032071800780d500c031425003e0480c01c0d0b0040000724100c25403120180d0f401034000d03071945240c00744050083c3c04441015a468001d6040340d440e0f00a00d0240b120024000c0c00341c68014001c1c1451408078034280c90000700550189030303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 422027446 1250 422026196 422026211
    0xf18020703141207030608010e07050603090c090108100506030a0515040305090409031e0c0302061f051909050f0717070201020c03161e15020c010f11030f010501020c0d06 75
    0x5120700c90226040b601c11880300c0d0380f03141291019803801c1d411624007000c2030500f0800580540d051042c04a641c0024020702061402c203000c0142c958030107040c0507054810414148501d6951881c2d060007018000d009242c0085400710308829034400800151013030704500051400308102148540183c2c00660300d0280a68030303031a0641e00c0d03000b40301400381c10602d0b0100314410180c020301e41903002b0802e02d020002c11076803003404844101c460040240143c1016001c9640305d2805e5002c1c034004803460354042006601d91021490700d52624141034056080441e08200003541485070a0700b0142ca4900c2503401e14052202524151701041b9034440ba5200342c0002e0020340c401e6058542045100f0150380e61800f036042c00d10503604440006942201102d08041107060056450350106a40181c4059012034003807403400c02074010708516a001d540340c6d8a030b0889038599104010f500d0018201c001d84a0900005881100303805800a60642d0302c02440c10510383d0302d080c035808001c4e5000c8404034402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 422028696 1250 422027446 422027453
    0x1f0219030e0a08030d06050f0a0e0402041b20030f07060209060d0e0318041a0906010c120e030f0303042f04021911070e01170106081c0807021612020102011b0e0a0f180207 75
    0x40c005401140e044035000340c0072150307154fc400b800006641c8805918006d0000c40209180c99115042d0000c1c44142d00b004071000144654010f40404800209264148449642c0f07007416181801400d000765040040c181c02c19400c25400c01c0b90490041c0c3d8100712070000001c0100101c0c0c001a0003070310070311141c00000c0f80c40c0c0c0b26013248181203500c4510340c2c000e540000405403144240d00d201e58424094852081100c041c0002581d11450300000d05c0200d0b034092008202c41c5008040d403c1401c40000d000c5942191540d000500c10310ba140608003184244042c4000c1600c218111084080d0300807050400101c0c600322030050658002407006c031078001e10410814014000c551000905010381400040f0200c01d01500541e0f022840c0c517000119600c4400480c0c542a002d9180085880305110901132403031249030403642c0300e1040c000000c000c40403100790307002d0f0450300c0c140c0e40005201030070510240c10f01c4e0700c80900600e4814080e001160070a50b610700700f0203850544142c03460b0701140c1901032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 422029946 1250 422028696 422028701
    0x80a060e01091b0f050409200105160c050103050a024003050f010b03030a17040317100602010c031806021806070807021f0219030e0a08030d06050f0a0e040204 70
    0x59029891800b034015406280c11419654811580102d503101000117035414075004450107640d00104101d000e42c8501e00391800004190447c5040200034050020301403a00004031450714000c40603e041586010001000c3e00d03002060200c055006100c410070701601c54184100140700007420110410400e2030040704c80c109504819003800d000c44d4000280300c004601015041d107000002d01c6501141e00500d130b0369100710140c280009103541956002c089a003c070441c0c00511034500400c0c0c44050385c2c04501008002d84242c80c1c074515030601040382603024420b205480c505403d0902c1020000d1900d032209900d0200b0181c11180c000810b40b03a51000c000102102007030082c042611600303242800101e5422042040380904030880000d0442d50303031300d544420044180c2e4014035120355030b41c00490500c02100d00c02c03014000619015105551600301490250400b0001503841d91071203034a0b4030984606038004d40c020301c4e215050b0310981c0c44403000c4130242d40e900250180140c0b92880480c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 422031196 1250 422029946 422029961
    0x7090b0a120219030912030905061b120a050601200c011b050f031206060711060a0908060711013e040e010303050712140a1209150603120504080a060e01 67
    0x88400400c0f0000250030b0b0160f110b0584240626802c0d01110388112050301261055076006d42141d000740000b40390000500b000744074010002941e00d0034580001c42040c0000c80644446a003039440340d0401555503480a080000d072140040c3c188a80081e040300107444400385c00915040182e0340022044e001940300c035041034103604c0000c07140450b0001c109261660007082c0b42500c21a2103001042951030f0003000d4451a50b000481069403004030001c1090590010142c0c005020701c400340000c200000303004440c8a91015282c01541c00303500c81000e4211051040d00704840c21203030303180d0002c0300528040c00c10084644018031021015412500e5030902440e4440300b40099a43c00100c01c00d03138004d01800141d44501c1c119080304802640039100100354070054500254140000000f040c42410810010760300f2200000d808083c80d02d46400b81030300c03122610b441e503854410400030420b1045c05481d2044c564900030b4109418030350400d45032008404041c040c01d07103694140e08120001c2d400a42c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 422032446 1250 422031196 422031217
    0x9020307051e0a080c030606040b0d06050c0901030f060e0f0402010c0501060602070f051f051809040501020a18060206010909060209190501090503030f070813210b07090b0a1202 78
    0xb681007210502402e402c0b61000d2041e0094400100000d2819400907403403910352401030280c2080d0342c600041c440100020702c121035002c05102c00042c0030a480b4402d90740518540168a540c2c0c220001c0090140c1d0060b106416445140200820030001340c00c191310b4000a00c10310b03030045900e5500040b501d80e075145034064203a52a0003000a64030760000341000031100d0b60f100000d1881e649104001121015462440380d000c1070854880115200e44c0c0109204450240c41d03c002c1c0c542a008180e41c02d000b15000c0360680e50000315840d03c41d40001d110240c600b003100000031240e0401d54000e4550a061213005c0d14940c4500c00c0500308941601944c04103038014007503920716101c40c00400340c186107504c20f150201d410201d01103400d04000c0308803183c1600b582c18442c40c11041da90f2b0f82106038001d40da01ca000383e014110100301005400547c00d000400c8241404c01013200b410060071680740909502c0612400785810011342001a05443e20b0304442c4c208461054240011600644180d41c03268 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 422033696 1250 422032446 422032459
    0x307140301080604150509100e030d020a03200304020102070e100306090b100807080a110604081e100612030c0c080d090303080609071b03050d05040809030d1805040902030705 77
    0x41002c03080091024815030090b442a0581c03c80060640e0880700e040e00e903015603401860f060400300303002d80c0000024012110480e03180240e0250a01d040b03030030080c172410000b5140d00c40b040f09901e250424205409045203120b14504180e40082d503624801c1c2300d6250660250310000d80740d90003510011000359080b0100384191131369031800300c1d14908110340200f0b01d0310144001041106c8001811001d54220360001c1041e035405807516840740c4c15000020364131032001c0101241c00f1405000103120710baa40402d5540200c0e003200c00c00d0078401890240f14070b60349400010082210760f102c0303507200c00c1d0305030600e42494011350400d002d440040c0d0704021070310304c02c141d200d403009030740211240c007101d0007503071649010707160801040030841041e15180006100e149801c0c80907118103c103101041d00c44c2c10284c2c900b00c0b5590380318007a544119425204100042021186801c0038400c0352005912840c03c0c42c5140010014880d00c0c44075402118001c0c6d07900d6420400b192010070003040a44002045d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 422034946 1250 422033696 422033699
    0x14010f090308040f060f090e060f0301060b040602011b0e0109170309120d031a03030912070806010306020a03050906070903060b0a03050102120601020c1f030c14120403030c0905060904020307140301 87
    0x5056481303585108040010b100240b018040c0c511603045082034503910b15141a090710788004000004c07200201c1d09030b140d5a0303844001051001c000040006040c0c54001141c0060070346010b00c000c000c440c03042820702c584400080b4a582e801452101541c010220300c254000550310404e00c0d5010711070607240c008141c0c040c606100000050104801c801075902030080800441d121003086160f071482e0358265100344408032140c54694495281a0640800c503885540e0380ca0707247c0e00d424400e034001e40721150b0020355101803d0f0315009050f840000c2d18010159070800a070014000442484041c00d0940c0e181480c400719902c94840100958000e0003d6495190b400822a81c0c45030030b4034400d02500c2000480e060318200038030700c9541d00c131510302e11912440d0b66840a40c050500d0100250130040e0403884c02500d03a65040107414a0042c0504070b03490742c649490301a0803076a00d480ca450034040440000c000d5030781c0c1c02c0c08841400506403809030700d079182c03c80250b4080a50f82410100310030003200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 422036196 1250 422034946 422034959
    0x5090d0312090f0b0c0703051b03130b0304020102060708070f111603060204243c03050a0c03020f0f07110a0824060a03200a060905030708010614010f09030804 70
    0x245050103038018500001c8a444035a800c440320b01ca0306c200140400c00903c542903460080f0001e00c3e44038180042074a01d0581c07245034a20812035640c010100402c008401d000075943e040188503071003d414184180e240c1130281c400350410404c4140101040300340100a004144180200360a00c2d000d2090300813001e403a480c00001039045400b07119900d0300c4002401e1400c001e07500f80000e0452a40d1140302e50440c0c001c00304443d0b003480b503008034108412080c00c00306881c07080300782d103401c280d4541c1d000039182001c1021a0a48940c0d1390041c00b05401440714403d02c2140c00c0c01c440703540c000900e94560391466032a09901c850004d084c003076070081800c040000c1c10000481d04500040c2c01e4003c0d08103c10043c00045032102080e510a504000c03041c1e42400040c0e144030700403007001c2c8208510794a007040140012031021498100c0130010708810400c1046042c00c1000c1009440c20000070302c0301c030341006410082a41c210160904012201040d0b4400d1070041019401444e000a0016511600c851 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 422037446 1250 422036196 422036213
    0x702010f151701050f0c0f093616050703021c0507051603080301050f060c0f0c040c0c02100f0908010207030e1302090a09020d1103090705030f0d05090d031209 70
    0x41503080d0b100444020040007003061040da031040c941c0e007030100b0841d200d28800d681700d0f0b001180c00c064105810407038214a45e1360204c548900540c4000303911814100280810140106036001c50200781220050103468a01d01001501d00e160a203032040d1501e4071410203d05e84000b2803030380001c003259400840d010560000080c0140c5024604643e17030180b07406003c0c41400668031000d0306003001440148010310b01030a001d0513100c0300500603070400700c802010605201c05420300d50996400b501c07040c00503003054050700c9581c4c4602e0500078510845600414642c07592200240104004481c02018040c056030002d80a4401180219200e00841c6805044400c440405038840c840003a1800c4000d00302e80203d4170070200140ca0070342030074500540320019402c807400203034140c0c3e221146103850b0711140c0095449180d2100041c00002d2524041c141080042c5086440c02d8010b51012401603401c0700446002000c141c03120610380d521810100c40d0824507101b840c0000e824848900144020350 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 422038696 1250 422037446 422037449
    0xa06060b07021002030a020c0609010507061814073c090608060f0402030307061104092a110a030809070302180a060605040f03060f0f020a0809121e030702010f15 71
    0x2a50801c0b00d81103c00001e90b900e004020309000180d014040200720340c28000050030400d00c060400a0911503150307124025070303105a03c2c96880034402c00303591060050008641140074800e40c0984121424500c00b02025001c99007041915242d5260541d480110011001d20016601d0000c018460700c903182140079025902c1007018030720a00022444805000340c0c440d02541c0d005004501e04045a503952000e80b4110341400d1016000f400300180d0610903004910340c01c0081c0f1003500d6000c40e241c20300d001c012415850101080000d0728017810040340000c56240c4181c060502d40310556a140f1614942401a01300075008a0340701c044602800018040d031b40980d8940c0428440300c0d850b580c3c2100d080c0030714460150494000070003040407480d90750003444551520a0003085082c400080e45051740d004000c0f0b4000585240200501d0a0040c8060700455013201ca00901e001c1c184000d0703c460f11031040d0300c148020800004240800e0007540b06070500c07084448240a0020791410960904400303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 422039946 1250 422038696 422038699
    0xd02031f1e060806010c060510050a0f0306050907140909030c1507110a050706201507090b0906071401020705100e210a03050402060d0e030711100206180a06060b0702 73
    0x12200041030302c5001c1c01c2c00c580b20302c106035181260b015407500d9000150070003408034640441d0055020410f511004079820140c04503030010200c842c610300e03160044070002054800b040c0c00800040c0100d5004520981c0303900d0741201c90541a0b00e074406080d04502c0391000d000c00314480c22408111560b40c031440540301e900b454603062036010a0300400c0c1e884010f02070b0024001d1300f000c40e05000f100d0240c050361500070ba015554274070304041f2880c00c0d4900601c00710f403407070a020b07000c1c01c200200350302498007805003e04610307130f034100160038010a4060040381c0008080010709048042104000d6042c1c8141c103402900300d802000d00b050410b0000e060107030341c01019020395010407002d44100300380e01220f814800119803512803034050403002850301030812640003104124201d0031070242e000b240c0984074040003a69841202c0c0c034107440301200304a5440d00600c00018058003c43e00403c56503400021400c0052010044028107814130500e40070081549117440700c003250300980343c005800c000b0720 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 422041196 1250 422039946 422039999
    0x1050c0303250305070818070506030c0322050c0103090809130515030d02070302040b0109031202030301061803020d020405070504050303070b040209060a0f15020106030c090905070b0306060d02031f 87
    0x304004200c064910458400300458400c86c08603d40085203802c491203440e06c0720680c1c01075512030300010300e0784d8000d0f140c0c3c1c048250701109112100b8180310400c00303240840890603d45044556030b05032030381c10b40240a03043c140ea500c43c40044c001c0306d00c00c84418000c001d00042c0811160205903000306019a1480c20b08014100c20501c64200020090580c11540d0020002545503a0802c000383c412180800d041102801c0d0001c00941070709840440100c0b150080c40d160343c10410b0041c40d881401c4030007590344540020400160b1101c400d140340d2550140c5001c110b5a84007802a01c06118035807040380c15100000b410400c1c45503041d07400c0d000b503208841d06c1002d51101d00030005a8a010b000b00d0900300d0030070408000042c4012024030031444940004a49107980792200c1110610f154441c1d005a52900728042c1080010701c006409444403050050460038240d020601c0340c0110b40b0002c489944c00400324507524032040a1460203d03401d0f000c110010385a484601d0700c1d04044075200300c0c0c801c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 422042446 1250 422041196 422041261
    0x9060b030303010b1b12130602011b050406050d0908040603020a1710330e090609040c0501030b0a080f0c13090b1302040b0301060e060102120313020f01050c0303 71
    0x50301008490494045921441c181513100c58622107802602203800054403801450511081d00300d17000c0d0006801c4003101500407480c00002a003900c084038005010650102c1c0c03113180d815004400d03901500c3d064600a611040305100d0803000b04924100607042c1800803c00250a0354181c004283c00941980c03100d0501c07a0110241c40310900a8400d1010300140700030520101051100901d0100500141e0302c41c00a60200b0010701003070680c01c110005545244443e01c81d0030a20802d6411940c2603c004085280c691610355101c40700c1d0244504064a41800c3c8401d507440d48000c0018280e02401c8d9000201e0b9440c12940d40c01080488030301641074405001000e50052203081901e94105e42c405244d5a5188048660307500c1611b4100c0c2d110756106a4a00310352001d10900f4090008206040040d05224002a1601000803000c08110780104100300000000060350350415030706441001203180003200588003401000b43e0312105100110801c107591340e8080d4001c0c42c010000c60400f0224 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 422043696 1250 422042446 422042449
    0x3041e0b09100f0b1e150705010b04060b070b0a050714180f01021209010806040615020a02041b0e06070317070e2b0b04110303160b0f0108370609060b 66
    0x1580b0103141250b0100b40c40d0700c00101c0c0380302c40340748034a0900300800d01c101c000c480b0b03003c21b0f4450300220f00039140b6039074138810164103040611130480a0404040c515042034025640d100040030000c00074001780d510f40c404103007141d01030141da0300b44040c0100c1c030b151503d4926500071410b01c0d060316640c0c0718006291182c1f0040d400403c940e1080c90110644130f203000074120041d940307148040c00d00340e0440d03a15000000d2044000b5501c1c914070b0001e5000e4200030300d9500410040da4202c22040c00d01c89442d01516a03203541045403403074140d00c281d03481901c48485040076140180542030011211100e501007000c680c2c4e00420300180d1700011900314141c21209843c1450107a00c3e00d280b017110300d000e0070340d21000c640f00d403104e1640144251040c004010802c40070901b16000401c8020140c081422900300704000021802d030b1100000f9500e5401c0e42c581500c1caa914450350400d0018200c1301042081481c1404803604c200d80b2901c500514480100d00c1c0100040002c007c00352225441c0442c481072a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 422044946 1250 422043696 422043701
    0x30f032802060c09060d020f070215031009090f0c15080f070e19030203100f050a090b07110a05011b030e01111b0309030d031b030203010b03041e0b09100f 68
    0x140d0405a0041000d036a400000390b1090780503000140e40108280900d41c2c203034100d40010500354813094051a00e80d1001d10601074550880d02c0c400c00750010034401c000801c0783c041340d500111a41c0c141301207400a9903060140f9036040038039014084071950000440c02110324000c0c03803028220756a58400076540c80103120b41102c4c040d550400020101d850b06195490302201100174501840140e081d10f0340d40e5800245000520ba2a6441c000e40740c0200c02410b1107144234156124042617401e0010081ca41c2e942104188024032001c2402892108000a008104144034000d40e000d002000f0742c620084102d1942240980e681c0002070414403250241c28060140d03491031302c2580f1500741807100c28403108020000642c0c1081e024031052103041c40954081090103006a040d480000e1034511141840aa83c1440e03140201854010001048045942001c0f2944285c01c4600c84e42d40c9130300b01030408055100c8200181c0403440d00000e00c803045001055000000c2c03803100c0d08003c91820620030105 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 422046196 1250 422044946 422045017
    0x302070605130e15030a060e0d03060b0405040527030415030b090403051c1b020c030d0801030b060a05040c020c040b0d0302060a050406020c0d1110020423030c030f03 73
    0xc1e80314540348100706548840240c1d68101c0c130304c14aa15103076001c070070100f80391408000040d60311644424000d640c501c028000008039286502c0c0c02d1280d942010f00850b40ca20a602c2a24000c0303698400041c404040c4001400d160000074103952454040000c84603500d0304107014417800048810080f206180c0240305000744848090300901c0a07a880d520142c44075004040c0c180c411040070181000401098450107a01820030188030548803201d800007403070005a1451240650700c4454184006a000f0180c0d5044980c801c80c504104d54451001c52955003142d800160400c8c14110354030f05058020620300314911060794100104440e02003085680f60040c180a009038104902140c1407043c02e400403030303205000300d0025144c40da014903072501d002400c1c0c605e08000346845640340c8001c01c0621230050000d0802c50207504090034a06201400049006080860411100c0c5103c040c2c0b0207010902400d2001400d440c040b0701040d080399242d601c8001da160818114070582c0b890126640180341 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 422047446 1250 422046196 422046217
    0x6050d0b040609050c030d020703050d020304180203090109020933010f050c190c090e03040f0b0901090b0a0917030403050c090a1e0608010b030c130b06041806030302070605 76
    0x2140780c4032500c40c000200002c10090740d040c0203100c10103074252030800810103c25520340c014040281355040550070001030f01c403c80115001000200300075003c17088658500408160010307903a0b150325203400d0062880c008001c0d00460000c040005200d841400c800241c003564440882111030704028230414951807101c903006c905807100f21000c5610840240000c52071250423100c1e071607014100c801848403102400c840100c400007080c01405940c0c000c1c000060f2070513000714102401c24110488121260103410790500d000f0510880603032044202e00020001c110750309907100c4404800070215522401380c00100300089850803040840002120101da401038003800007807007000e082100410014219503242a107907100200f01c200d40c19030000408400c01c40006249140c41801760a60b181d051686120307421020120740345440300342204a1030040c1c2e1400003804a2038400052903800781b50011300740c00c10200c2500d0002d42d00d40e40400e0549001ea0211059140d503010100c9851240401c0e69 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 422048696 1250 422047446 422047463
    0xa03020615040906020f0a02100b0306010506220b0919080d08130606060c02010923060a0201060f2303190204150e1e160203041502010207050a120306050d 68
    0x5020007841c079002081a400c01400881e80782455110b1905980010785588446100042c1c1c1c0c00502d50104156504020800824800728940c1c1c0002921101e0522a545c016100044c961500940b040c401442500282607000c80060300c504006034150030010480340119039665260407022100142c0b00121600440104900c1d05001030480d1811006404000c0000d61203089200150050244d20b01610041d82c4041c102d1695000042c642c00c04ca42c0703c0c80d103c410365100c03501000680131f400740b02240196140e0341e80d0550707200202e00501d110340c4090a4090300c0d6030003040b04c8146040200d4202070000d10782101220f40010161194010f158019254038911044001400c0a40121401140046a01891582d0340115503000102141c0700c2c0481e410003409094001582d00c2641d402c114039400c42d64000600e00742c0655640301c0c4c3c0c043c00b484c00d2442c3c401010810310075012519600d07400b81c00e4072248025440c0039170324100390111031008a0708003000441d46060001444480540003141e5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 422049946 1250 422048696 422048701
    0x905070314011a0d02030c060a1206090c02030702151909091505090414030f0a0305090d0306120618050d0f0206160c110a030b011e12020102070320030105010b0406020607020a030206 80
    0x300905902803134401c030b8050103440803451003030340d510014110303a00d42e640700e542c02a849298002c1c101d814a40090324a189407107500c034407241d030000590b481503074142c6610611211007203550791a805a091140000d9010030845030155a02c441c1c03140464901c0d00c828040b640340030807800d001e61410b004494101002c1000100070079030012034500703440075040036030b03103051041800007116502844e9980c3c0070030b4441052050280d402c02241030708403d41d02d0300300172482c20400d849400954003400a400c06c0d4440503003c05410000000581050340310341100d1030295450b2010b403558101c060254090f0060000060b03d4082c02c1e51003c180074625034401340c2021440c1d0300e40c01110784000c92550441106030010000804529045d8007a041c1b0002d45010121040001203000817150400301300800354001100c01070340c00090b03c2040c1ca03449041003c091586044c0d034584c3c0c0e0001d2232019490342c00c10700006402c4403240b0003001541d080c6d500741c0744903a50300a016a903d03080c4000081c0140c0c0150300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 422051196 1250 422049946 422049949
    0x6061c02100507060f1a011d040b03010b04020d0b0102061b0301120302010e0615040b1e0603190906050708130f06020c03040504110406020124030809130905070314011a 74
    0x4051405141c5081140c1031004584444080790000981c07041e0190360b075820310100b403110400d00b1781d00b04424600011240d45616a500c695100e0343e09940c000c54031000c035042595405c2d003000d0740d0345601410840d20340c4600344031680986039042d520fa0142c0118400324000050340c02d04001d6841030f440d00e0600e183d103020a900c1070758801c2071042e011550384180d44101614280441d40c022221940484031156400d030402088403140c003040c2e0300c14031540d615405014150030200d550786900b00c800d26103999070b50130210300e4952000807900b0b01c20b04c0d0828034400c2042c5a0700140c0620482c0c1d48158030ba80e80c803400d00e00140b41d1140068400036a01d80c7c80400203d44d03070014000d1110000031f4900782a51000440d0680d8081c45aa14604070082010b01480d54244541005a21701b681001140d1402400c0340c18407645901010382030580004440c5810780f51440c0402e469100c05004010381c000a0800c42d445401500048030004480d0204800098050142003281390041100d45000c001150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 422052446 1250 422051196 422051209
    0x31504051b1c1d07150207050108190b0a03080d051003030503040609020f0307092f160602040f230f01050d0e19050607030e030f0d150512070806061c02 67
    0x801d03001807540c456050f80864848030781d00d4001d80c901e403001800400d003000c801130314460700c0c96000e804540c000201004140c1c1e210007441e4101140d000c030040214940f900300809008010648c0e45c0010a131b0300c0000030400303004014604000108000c201c95107c0342e2001d84140c1c150303c005400102d050011a01042d042c1d40410300491008060007000c011000119080031800d60001e40039594846080004807150b072040c5c1030440319111803030140b042010184c0c0c0b09008902000c684d1108400c1034100300300036603040340c01a2040074480500d07141c0e92504464046014282d40d03c100c03c03607003401c84031400c0130503084a900304141c650350b04044114141c400145103500010f09c4c98801c030752491034106078511094281038003500141c0107500d4440d0300a801d441a20900c450b080e0700070031500350100b0418040e038003134501e180008a004110b29081d182c5000c441d81100b07a00c240c181c41c00705100080050f40b10b0403108910241c88590b600c41c010001060240e41d0804c00c00d444500000c4014648030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 422053696 1250 422052446 422052487
    0x306141b0306120f03181009180209030a0c0503151023090f0717041a06031c11010b0d080d0b0619090501121b030b0402040b031504051b 60
    0xa8040d0080d00424007186281075241425140a500000f4100d00c4104004540251b03152013556503041d800410040148851860b11601c0f01600e0904c83c0307062004ca054040390310b840401030031203580071407604000c10040d103580b003464480d100d102d28448070041c50400f4213100b400c507003000c018401e1624a010b44a0301c05050700c1e0071400d0f000e02440480c1c1d6991001c0078085c0d66031035a41c40c850f2800d00300c068140080400310603030342c114802c100000a803105940c1745030200101900c0c2201d45074040800d10b4501d004000b43d10380780d03d00c845540e065510810008100c0d269100070700c6001d6521080c8405040400b8001e4044a0100241c000c0801c036508042407805014280758076040720480a04000c40d020800070b00054408201000b0070760380b0040c00c52a61509036410080d03047d04501000014000882e20000d1541300e2090f88681c0c0c1c0c541c2e040c0c1d0010703c0780d10407541d66441c0c04c040514680b1403910300e031f0303120742d2820012902d485e00c40d92413105170300300540d040c9103800b4a81500000c4503021 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 422054946 1250 422053696 422053699
    0x6181504111210030b01060203250201110303180c0a0503100b0613080109051b01050a030903020708070602100c020f100513020604090209011205071b1403030f010306141b0306 77
    0x1001841002035902407071510840f00e03140581c1e165800c61400c0f00c00b402060b4440070841d8070510646e50b01558005403244d843d001500348590095644c4010f80d104202c241c0b4a04042c00f001c0208000100c0b084000303941105c1d000d0656414217562000c11041c04040d0013138030b4142d40048403465006100e90701a00485a00600c02401c1440c4174003050404a49500100e21a0f515203010303008004013080b00d060741c131620000c2003902500d0780c0002402405401c00007020551601d002d281031600910480c000750403d5800e5504644c0c4450000c0c0d038445003c059179102c40e180038241e140351031000c590b0162100750701c8040c0101d0311502ea03002d03000d8071002e0a1502c43d08020408000140d41d0000184000d000c456800350300c0704140c20001d0080d000300d000c1c0740c006609000800214aa03c001071541e00311101c808520340d56038600b0b2074804400c80082034021444004280030002e280030b07050504880c4039641c180b2510746045c4880780c00c0c650545400c107003400b40000313031100c11070804003541e0311010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 422056196 1250 422054946 422054981
    0x10c0207060819050c0d1a061909081b0a0b0406090e1506041701050601080f0a0c0c060203070804020a090905030f03150d0318090e0a0318091406181504 67
    0xc0c141c0781c0700407a4026218040741342c2d400148280b03948071b18040c0e0031010180200c542d0b425103010340820a1803044458a030300b4410300482e000003980c000e5070144040e041c0d8008980308486141280412591a40441031140c45050301c009a40750001007110161081551100101c030310380904180106000307807041218404c0c03000440540d88405001d00001d01c00d00b00f01c0c030107040e003a0030010308482020741481d04009991082014a240c0031541030341000c120400014540c010350350884511810440007410340d8000800e104d02e80358400d403498010390007151001001030f513480054007206c4502c5c0e0010001c0d08107120b17445c46101080c01440c0c2c007000ba0000345450541100000c4d103502c00c0f01d0402c60204a1000601484149181080000e488150340030804109610312207a921440e8143c001c08000d101480ea100410000754100007c1140140510035201941c14000c4030399421240180500e00ea000580702444212103040e0141c022913074100c40c00042c0a0500002d804400c0d910140030301e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 422057446 1250 422056196 422056231
    0x1903200604081b12070506010f05011b3906030e030703080a0504031b1505010510020307060b0609030601090501030b060f0d030c02150d050a060909031d041e140702010c02070608 78
    0x2c1d107880052204c0d504c1400588130540c1882c49105c0d500c50142c0144d410414000010481c242e4443c890080d0700e0703042144c01821145229105074051641c801e37a89041e49460300141e1080d009948039070640340705803030601503035a2540703103190f60340a40c1c80003400058644012a400c8030880d88000d4125010f0b01c0c1c1104001c000311040308040015090486074040c00000340403121140c0d1240602503c41250b4000700c28940e100001c2d601d00401c000a8111941c3d0214000540d461f40c08441d540d08001d010341e070742580e5076440c5c10001c0c42c0c00d02c810b81d0002e92002c0000e4252811014206025000404182ca01c2070385840854410040200881e080842500020811315103000908803980040d0b070085032520780b4080080c192100c6501c10035030141840022030000350025503082031404440e8440155041d90780008000d06103001c000941a2171401024520031140d40100c00010308003035a90080e80c485c05401c074221002032602d040141c02551061100310300c16039400741c02c01c402989103c1e188 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 422058696 1250 422057446 422057473
    0x50301110f0c0a2004060501050a23040503010c110607030b0603010e090114090d170405150405031e07060e0606030601120f050d0905181006030c021903200604081b 72
    0x40c0b001944105804c2d001c0b040200f2500d003d00a110141c01c080c45c0c43e0341007804651010344901b10a100c00105c00c199005c06014003943da81c00e0303c0040000a00a100c080503242000e42001c1541060507464002c0000003014140a40242581000c02a02c05480c0d6860500c4c045c07200c800141900026540b030319000c0188900c1320034918050f200442c054414440342c0b8201801c4400389082401058499200700b00c0820404035109800004900003503c4a41d218038020703080d48200940c000c400c1d0520010401c41800b07200c041c0240904c01d010400240208140340e41d41ca940495103039500da486100180200901144c146211900c1620041180111aa941401d052030040607400181da003880801c541e2403c0d130602820030a0410050729141400a42034401e03d403640505800e054407810282c48007803003002a10b01b401d2041a41042e0354000c0e1a00428000081080040800103240310304100140440c4042c040d90b8000605071801c500c064910080300380420020489001d112502c41c0d94 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 422059946 1250 422058696 422058713
    0x319080319060f051302071b080705040902030c270718140d1e080304121407050607050310030b070c150e071e0302100819141b13080f0601050301110f0c0a 68
    0x1031060301d0008e5010b41c2041d80891904070103a110a03c41ca0402d080c10b4096107012804112446d425189585022029620f1840340307243e51140b50b801403290803c03c103180760b12203daa0018100c441e4200c2c4903d503103d1074510015504001d0581c0102420844000640903c000c0b181c0400410110b82140006890303003c00c0ba0811241942c6000107401410611548145440740808048031507908080168494650310b10000340700400303101c400004208810f904410f1000216400944001c80745001c0d0710050051a01b00300440d11020f04401030000200386000d40500b05003020010101146091006646804010003020715103240c1580032001da265a5026007041c034003a10381c1c0304130b4206500030038038a00000842448035403400010809600c41c5514403500301040c4c502800c1005401d0f1841c480030b20460b111406074002c48071000600d0343c404143d66101c21416400c1d40c3d038603a6204181400d03190604001426114208801100100c161002e06115001c50701200c1071441550341c2c6000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 422061196 1250 422059946 422059973
    0x3030b0901050a030c03080f090a090b09090318040b120102040602073006050a0b03071d0f01081e0a020306190b0102010e0d0507020319080319060f05130207 69
    0x2a16148060100d003400e200480c01440181c1c0c000746000c3c51a268640f1103012404018641800024030a506218240a881c00d140b0300a18015600340d44001c0354000707080810006008582e030030006a10401e021050720f1034805003920380100b00c5648420040206544115540d03c4100a070444900720002d01c054405056a50010034100341401c9100901c120f41446949610307110840b03a0742880402007000400a61000380410162514502c44024186901216416101710403000038001501c40010715890080385400c10107455400760440b080c9400d0040200e40d50166039185158400c1608a120849264084d500790b50070a0340024106601500e00305c0701d560740c00c810368450712405d20070390782106000d00007081980c580d03802c1c081e1201030740b05100d0248800440c0c05000d644040c400001c183c0c10f80c1803d1000348640f440d00040c2900140c1e080c8820283d0310203130815840942c03240d0750544502c3c85030034080c00d19050810180170207817440d12500540030302200f40050019000d003207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 422062446 1250 422061196 422061203
    0x1b03100c09030c060923060d020304020103090605040b0a0b09010806011703040b0412030f030507023f070c051c1b0803130602061f1701090227130b07030f0608030403 73
    0x3000b10b103800710700011b1031040d0f0107000266a04908100c43c554450302204c11340d41203040003680f00d0b501d500068000340b485910141146040100300300c100a00400b0091141c45141c0c010080d44144c1824803241ea1424003400100b5402000148500010351590703401040704103003120f1400351101400c4009820070390042003000d24040c0300100309500f00c80800101002403a00f00413910784000002d40d40e550422000c0c00c00340b401500348592052001052400c54100c68407042d0301c241e200c64004072640100c1701950500b45d000c001003054906a00314030040042034071450005009034940903003903620118a1040e140034640001680070080c40034210b2441117800c80c05000b468050007a00700358000708100c0c86603004007400d8420f030700588403020a5440c402d089003000b0004002d140c1c010031081902035440580d130801a07089100c048911038000d42800c494000603180d0f25004254114082c400070159035103100080c8201b440f81c2c1c07014105e941c07070703000c0032500e10f0790340b03100c2401c41e80b1a0304203a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 422063696 1250 422062446 422062457
    0x506012a0519173f061203030f06060f0703021605040c090911040e0c07060c05040b07030c060f050c040f06030504020d1b15030f061e0308030709030213020702031b03100c09030c06 79
    0x20000510f2141380c5580103505590f88000325050780a400c0d03c81c84002d15200007404654040f58440e1101015111499140304840c0d984e11181e04002c0e550f84108081c1d01d82c02c1d078a42201250608181c044c0d000c1040c9543c031100b240350b003003a48840c083d110f0680d000c41001c07800d12000401515110b961401070021308121542c6090a0a002d03090b90003400a0320103103c0200030420010041e001140d0080d60036107000303800c0c40584d240450103400710131910a02a410001403003620041c1c2c2c0001d00031504420950074103e60303a103406400380c503002c4901941c010314125040012654611224105241e0142c1407104aa01c4d080c113074a2001a0045c0361001903990742c10b1500244080c41603e0150900c01859400020481e01c002d9203000d00c3c0c08001d107020800300c08150803e00803051500595801409085126640072102c4000d4020301d00682c0b191103203c1100601842c5074901c98200100500a000b120f00f10002040207050080c5c40f9004215800340b0010119001e24600b60281c20341c1e5030352 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 422064946 1250 422063696 422063797
    0x301030f05010b03010902010f210609060f061409010311090405090f070e0f040602070813090207030801140a0e280b01020c030303010e07030506012a051917 69
    0xe0382c02c41e80c1032030f003442c0268903112100700541e80000c0e02401d540d000d8545201c12000038440c10b1282d04072031088022141c28040c02195000d03142c0c20002c00e640710080380820315955103c003113500d030680191078203d484081000e0b4017194070a0b0031182180703405c460803905e4180c8403004241100c00454001c9420380200c001185100c0780ad000341c20040c800b003a03032540207062400d0f0500d5040c42c0030304005c05c55540061881c082200600c265065980c1000503560150348c0d50702280e020b5803064408800245002c000420131040c8601007200c0100b02611014a0604090f189003850f00c020b4080c1c11145642e0300700003c155013422402c1e07482280a032002c0303980d00e92140003905d001004041c1c88d201790004c0c001401003000c050340c0e190b0302c41c0e482c0c90042001e1b25000c2c0142c03402481d1020140301d0312000d941c00d00015003483c20b403980c030038031134000c490100c5072983c6451507001000e0340040c0942110781d07401103015502c20141040951044040350002003001c0d8800700344d4090304047e00345d000113849 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 422066196 1250 422064946 422064953
    0x201050a0b0a030b19140c030a06060504060203220911041404290409121701060503091504150212010609060c020a060f0212030a062301050a1409060301030f 69
    0x15028229505650007030740c40c1c0c00c544c2c6001207410001c00035503ca1460042076102d00301182c0112003e00680450700425080440140d4610b40c0106d40140d0682d04040d00025040d102d10304031400c9811560241d81003005c1c00400e0f00c42c004101c83c100e01c030001c8507000032507903900320f1184980c090110500556140c0c40c04c60b1112101d01a10a0342d4487e03460300381a48140481003110074155103802c40c07401c03103040380b40300000c004000d00c8001900340e101c20000494000d4100c43c211216040306009202507030ba80302411a02848115007911064014105454500102c0e42003550000c1c86170000840c0d000180e103a01040360811502d441c1940c004100400009421208a201900103132501031220a2660041100e069aa00c10413003000031a603400442c9620a2146580e4190700841c1103940b42800000d940c003420803030090012130b0481c41c4214004988104024070201c0c01038660605181c403000e01600c070154500504040c102080140c00386658482c401540a18804c0d074101d02001560f05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 422067446 1250 422066196 422066201
    0x9140901120f150f0209120a0209010e0405160b0c0f010b0f100203370305010303170402060724061d010b0a020708010c02031911120318060108011a0a06170c0403050307030201050a 79
    0x4407003610323040803210b0809038585030f0015041d540c801c25501f5907031b15145440352800302d070150341c00000d03040c0c07183c0443c07050742c100e00510024294608451135800c40792105800c075540182510340c0300b030142b0303046040c81c200001c1c0f000200000b40140c90030210005011420a0109040590381c545203004441110345680c900c62081216442c9c100055811030381c01138030300c86c599a44000644079001c0090b0442d0380396030440b40d03030a40c4050190114080101c03401420020307594030760354844c24100045203448000c51481c0038044007a60304800c1e41d2030070703c0c11805035124405080450050b20300121752400d09024200311000340e94010b568070303211004030044654110030a4002c200d80781210942d0140d00094219100c1a80701020f56607448007000303c00c06603600d03505880039000300c60000807113020640c84202c4061141c02040384402c0001c0030410a180c99000d80c0010400140c3c40301c0700150301c00301c003561024000340854a00b50700d9413100c0303142d9004510308400507911001040310203003c0d030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 422068696 1250 422067446 422067469
    0x90708120a0207030f020a05130b040606020d0c080315090c03040501110403020f09060109050d0614360a0b01090b120c0a0902030c04030c030309140901120f150f0209 73
    0x100320090604005240c025102d00140c80080c12914554410105554884110500038038000701002d00784002e40303100402411012030154410303860400c00080e05030011485038140042c5a5803800102e0bc50742c1c4600d215040602199004036030103030f8000050b03e511854a0003800c040804030b0b12403174103141003400d440614040c01c404403014841000180c1b620480424151030840b580d030507031f40c0c078400100c0b00041c0b40d81c030440e8060356012400040c0f00d8954060a401d015215918600c2d503103a901010051480020300c035041a181100e41d140c4c10100600450006d0010003690044089034440081800f8203800c0604280e43c6c80e10903003150320304540480b8030754100c2d5024001c0142000001014055507200b901d415a400000255502101000300c0b000f4540c03142c1550403070f50722400c00800710411800b8581c0c284540024055092800b14000c604035030085580b45c2400c0880e0750b4412070351703070b004404a986841e14105107101c440c0c07034020075032822826640141c5485501e0100400c181d01d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 422069946 1250 422068696 422068723
    0x804140d0c0c060f080c030a1e0b04060e071b060e06070e0939070c15082203030905012a020d030204030c06080c070f0303020d0e0102031003030f030212090708 70
    0x582c11345407401c0341c104090581c0410900342554a9945803400750016210301d00c4800c08020180071001843e288a074042c000f42c1e0b40070b40f400c0040355120450602040025540340010034600d01c546160003039000003521241c2c1c894407002c581440d42c01c0c1c05500d055029100c0001080814185603010300341070322003e60100d6805800700ea000d603140f50321800c0d003181000d120911481501942540d840020481c0c01c0c1c070364032039810414140c0d00d000c0c0780c403800010b0b180c000014861402054039036800d40240300f001d00a9052502d010443c0350b4054005040d910012140c5540303c203c074030007001c0707000e890508401d2842c101e00200d5054043c02414508018056404c0c54810303c02030000c0b07182c4040d05c2068901c941849600d60311001110455405400001030034400390410362003c043c2e140c0c0281c001042c0403803040c040d40b8046140103090707010881d0440c50304a144001040403d1191b41c07000b4250b5031a0500600d4205d0045520010500888680e50b80394400a02000070100400c5103910f444074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 422071196 1250 422069946 422069957
    0x4090b04020304150b0a0305100203041208221a0424021201140d0c0305070807150507030807030b060d050105090c0c0616021c020f010614030d0804140d0c0c06 70
    0x5181c0e1303800f0464520414031450300b035a9441045003548460b80c014006c1c542101c103ca80c100940c005541c0654800c42d030840b10303104104d282c4461240a070041d540100110a10400c07a0b4560042c40030050715a0102034400e0300300011180d07041d0300800c4642d8040ea00a84000c16201c4c1ca030510254260080f40d48442c29910402ca50185204c8854056064902648014818403010340010b68111381c0341c040070f840c03100007130f00000402100040d4001241c0c0080290761440d0ba0702c88000c60300c845000940400b1460402070100024030507240c480d8402c0c510f0400180d00d42c00c000c00308034a600712000f18a035450b42c8100501251400b900015800401880102d140c1f031801c6030745945481c0302805840c0103c0910360203080441c024030140701c145402e50300320082c42d030342c5d050001d598020194428456500e03107400414031540c0081038081c401d4001c1e004100a130841c5001f00c840d0000104180e0b81d050756404000304000c010310038160340030b00310358903601000c0c80c03410300f40d1050302d095110505024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 422072446 1250 422071196 422071201
    0x6040e0a181104240308030612061006030506030c09070503060a0f09151e0608090c10200a03021b040209060a050a17070e15070605040305030717010f150207080304030804090b040203 80
    0x7135407800d001541c0c0d201501584a8407500041980404451001d01581c00340320200188420460000d004850140e0750a2011340c50b0101410384480c6071b100801d4108098200050206004100030b41d08404060b0141d014107a840ca00200c4407200c42e00716010454035000e000c038860394a070903804042e003503061104151408045445604010600c0b41c1800d00c40c0543c0021441002400351a170703602c5d0003410340049216184001020f0b01075100302c0c2c40c000b11101305006103004c1300280c46074405034140c00a000340c100c8030454003010600d0206c1e0782d0b03015400700403002c0e01d44c1390103003d45520f44554441b140c4400c801500034100300c8154481c450a00303118020443c0c000d5000108109039201030300c00c0443d03498074413007001040c41100d1019194170f003400140701c101540300001394818041d90f034071200729101051000b00404428071a002e40400e541360144400740c2000c5501030702024900485d14120381e0b550318507045410960050f10743c4400403d00700300c2c0e403030540103a10400c0000c440852651 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 422073696 1250 422072446 422072501
    0x1e02211f06110a1e06020f030414161a09120c0111030712050319020a08060f01030c0c14031b060703060905160c0203070503030412050f060606040e0a181104 69
    0xf42c503002805080b031030b201e0310038540400f031005034040042e030405d00940d40c0b035030005400c08003035100340e504840c6403603400e540084030362002c079071100c061101400410246191280040e0002c04512403400701410800c8907000030b036034809526000070789a0014010580e09540090600d01188181c0b49440d0020801640050082c407a51100100c9a00b0070b540c03241c44210f424a520126810300c081400c0c80000c20003085a00300c0e12091143c00f0440700850717180380072001101902c0ba1001904081289244064001244410070311407031600c820449080510901d0180c2514140c1b0342c00050036000310050100f0141d1600a20300a4203016505100a040c05905503203001d0601d280d2204114501171400304550301440340500829004048039165500d40640980075480754904550510482c103003413803940000b02e006445103038014102c5040c0340c50420700710b0007140b0083c030343c51200b60360740c0440e00e41d0300304c107035018034003601036a05c078481c1c006030306c0c14071044580600e1203218684040d609c0215a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 422074946 1250 422073696 422073703
    0x1415060a050d020904020705010b040b0a12110d0c061110110904330501030e07120201080727060206090c060f07240209131e02211f0611 60
    0x3020164900305075110050301400c80280076a40d6042d90007030000604009001c4150001c04000c1002c480400450050f10100584828284222240340358040300805c0070904400c1201212070000d8942c0007030605643d1050740ca05c085400401c0480c01d6160b0421505008010440e85246c1410080100b41d5807548441036130b0050003009072045850b031460070314a860720701841089c1d1800c10404410038031440d4100c10004200c1c0074050000340741685910701c0368800600d61040750060010714030880120b40044942c13200051540040c4861001402c01454115200b10818074a040c641c1034141d0801074000e040c0000a009244280e020142d85ca050350744910031943d04440c0d000060380c0e910401e1420758085042000070f41540490031404500e103425540040c180d20a00b100c01c001c019a18043c500229a40410607003c182c8456210f82c60048203a4002c00c2c0d4464283d244103202c4402094031190003e0840e05003200c85054050788902c80c441d0807880000c0d0045081624104002407141c0c2d58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 422076196 1250 422074946 422074957
    0x20702060301050d05030c0a030201050613020f0706020306010908190317070206010b0d090b010801150608070512040f080a120c0f020a08031806040c0509062d04020d0e01141506 78
    0x10130003040442d1001c100c810402c4405d0800e2480076200c01c901d10b810013034028441200c00c01e01400130344055050200081c400c480115800a41c060308001c5180c40d010001d410040c20319042c022061408114803408210320341190b640d907880c0d001c05c044585401070103010b00200c040040e003001002e0040150b000b198890641d80400c1c1d01da074480003071810303903800b60810540140c09001d01e100080781d01c0f00107420010b10003110f56000d400040da01c8404507400d8404940104c00030360244813592081104003443c0390840e0050351004801401a110076055500080c40360b008a00c88440c42c8040f40078900816503154418202400c012240000283d11222417850051a0050020000d103100ea07040400094118407181218020b00d014a46140700c104640110343c8640400c00c0003812600d0004035088800d0140e10002d581e100080708540341004403645d040341e002da0203000c3c1040108042c41080310310007030000013003038440c0200c2d42a004014007030481002c1480301140c0e00065111001181d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 422077446 1250 422076196 422076199
    0x6060503010b0d09050c0d300207140a09060605030411060405031b0d1b1e0b0d1a3a0b0c0d110706050f0702010915020d1e0603051002070206030105 65
    0x118004c80780382c00340c20304440d942c0480d8007030302242c40c900501100a80074001c111802c1180c3c00340105401c96450000c14106081c001030340100c90038450055003c00f241c5000c0c8000e13042112145e01c42d070542d42039030010b8000c000055408800c003c10b004882d02007844030385042d1006440e0a0601c00401d03203071404c2c050f801d03c414510703400c5403d076902c4040d046240c090b04800030707050010201900b00394041a5104150200d203170201000d0120f00703824000303070440360240f151502c0d207160780e070407200500301124600f401c28000034035140d000d0300d441400141c060130300398040e40b214101c0c502442e0f02e914403421721640c490f8100e00c0440050301d919412908000c44401031600c501404200001a02201440d600d80340b0001c01c019040000e03e400090144180c8034807003e00d42c1d81c00004908075130880001614004005a1202c510b001c158010802c0c0c51400002003030301301c030a11100c540e04000c120ba28101c0c071740e504400c01c20300c40c0c280886480c80706031080079490000a82c00080c4503000600406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 422078696 1250 422077446 422077451
    0x180b09100f0f0e1c05010504200a050f06071a01090c02071211030a0512070303050f0403090b1c050405030c0706021b130f290f010c1502040b0403110406060503010b0d 73
    0x221859880d2400c4c12402050000340702520030080c50602d01030007059030222031065144002c1000e0300d500209851183c0400f030030702e0000c03501d0581008110300b00d2010080c0c00c00350030401e6001085018490542e002403002c441c400d1540f401520200300e84404446104541000c0800e014986102c800404216004031200040306120800079051a03c0140e006113103202d4420701c2d075540c03c182c001400c0e0150294804010550320880145002c5004840003000074030401418040d505e04000a00500000070301802900407040441030111502a00c054032554004a180012108104000c0c4060010b5202900483c807040b003038190051b030000300951040b8060640d24007170604076030024401104101d0188088641840003102018901c076201000450280c095482410726042d101c07000c0344113035a000c4e00a005a100d02d06210b082d0801080b686408100c005140342c25900070300302841c0a0380e104040420190b08210031280e03590310001c18071809200401c0440d600381c0a031401101c285802 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 422079946 1250 422078696 422078717
    0x504260d0e1507090e060a05090601030504060b1c05120f0318030909040812010501030507020d05071b030b0a0c081306020c0703061e0b0f1f180b09100f0f 68
    0x80c500700000b0340030880982c0c0303410007081101030b80007250400700ca8440350306915503102c200c10b10142c2c0d0700c14007515400900c0900811104e52080d4002030703020b4051100000c10121400000345c0115120080c1d4109054040c0803105001d4148058084038001ca4045032a0603800c0e04081c60a020003406501c500c4034401500b0003000301401118a1034200618000a92410f450700300015000b03002e118191110300710010546500030301c6218000c0d074264008007444c80d01c0c0d520440301503011600c12100f5842000010f52311003d40502000034521401038815945040315040007201c1d1040344150801c401c0f281400200c580240c031103043d05412040141c3d0baa20180d94031844c01c0790544c00100240d18180700d204400d1601e1180001070105e140d4180f0540c0c0c007820400c190450f210750060b602000d242c010100244d02c03c89a80c0a40c1d109080040347d0415480c08140c0342000d50340910744166001403011a03e00d08091001ea83c046e00741800310348001801001000440a88058418480000d04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 422081196 1250 422079946 422079971
    0x1106070806060c1c050408011a0312090d020603040b0f100b1b011508011a01050909012105010f09031407030f050307050705031b0d0507080f16060905010504260d 71
    0x81c82c0110307a0911520042064130382c0c0002c10300e9000d841400290f51800180160310441070314203103605e1500030010032100030402d151855a62290b68259803280b07112100c500162181805588900c0c001e800000b19407030036620b01040800014110161005204d60a103c859007004c241c481b45280c2c000010201d850b06460140106021004031012680c0128005040041500030503045020a0084d000c642441801501c4601a843e20554000000801481754040c08400700046c4203070410b65940080e0561685804c4500b610080420107844500c000103154008c0c00034540d2900200803189804041c5d10014505000f030008441004800408079440300c0c890004c0c0c86c0c500b9003000580c0d075524460301003c0300c8442c155240e949140036540007040b199000320203813400d00341c2104d52a4a49101301d45ca8080710361140138803401014090380c21601140851180d0030400d446800001810708081c10701c401d801d00d030003560040340e010321660911000050000d07070f00b0350303841e0800114140941700c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 422082446 1250 422081196 422081203
    0x30a0204091b11030a090302121906020705010b06120f060415060809070f06020a06180b15040f021305041104090e030d0e0109082505010606030c1106070806060c 71
    0x500001100d42800700002c0102840b2500c41498001511080101c01203618480c1c3c0f80d004031038401000c50b00c003080801c0513050a8061300e0141e030361703081030b0b0b1290b203c245001540a400d0040903640030382d0110705c0004000d001d215040306010212641424850820703080740c111400105206103d19544000c02c009842e2130b04802c0c1c0301d109100802c0071450300d44000074615102203c4205040c45800000a040d084021600d000e6603050741c003901080701291100d50140400141d03985621042c5090080460324040d0564002c510882c5091500280081044165507220040b01080380c0704109a08a515814598008480c4103072004281095065a400c16500441e80100a450305040701c0f408020030120041c0580850b100c410042c42d07851031100da007200c51403500209030010402050354180700094051108400f105040b208030442540d600b4252621603009401184d112300c0d0310910319400510540d0b280860b03a004021915001c40c0c01411800050182405064006100900b072641071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 422083696 1250 422082446 422082449
    0x21b03010b0f130f0e0c0901140a15110102131e06091a19020102030108070f0b070803180d030e0d08093a0801050a0e0f0105010f02010906050a050f0f040309030602030a0204 76
    0x3401080144c0342c0d0301040761a030308907a0030a40701f005011700115000201a4642c40d860708041e000240c00c504202c2c955940000070440c0d40184030600d80a0064488240003c055901802443d071100924007040746000c41c0c0340311400c0340c1c1c03a00310305400d02446a00c00300b03000481e4518915048040f0f0745500b854654856443c3e400d451005c1030325403405594054004604940000c01115142035071a50380001c003064500500c1600c1c10204940800b2990b444069508511540e083c0031001002c0702c152460629a0a850408240c17500031007100c4003024050800b80000508100f4440d2907c14483c54580c0c01e2030912241484000c40d8810100542d5a480081c0f140310790703070704d0309004810480039046600034422188200203561010440c032a21104043c00742e00005075428040c1d007060700548004000c100440c086640e2400d030b17400820fa0030701605000d540c45034000640e5051100c81103140c507000610302c5d01c2d2050500c040c400000d0748400e02a049a4121a0058590b00d032015110043d1059 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 422084946 1250 422083696 422083721
    0xc0a0504180605030c09190c1b0605040b15060f070f0f08090901060f0f08150a0308180301061a1312050c040f051017011b021b03010b0f13 61
    0xc000158a6103095000800360350044080f20f0220003520b0401080600843d00310311f034000d104940444803d8a90044543c82c40d00d400d1045280210040c030501c50400c07001c065179220380705c500f407006211035104101d0b009805015220750070700d03086010407030750720941c049240340355800102e02c1c003488000340c0d401c8540b640c002d01c12480c0056500300a1100d0300000341041c801c00c0c070f8400020f02c01d401803450302c01411103512410303650002258140ca4041c0001c0560000841a00ba207841c213581d100b070300d80050b40c13040d013180340c0350100c8003028841000c10f0180319020740c2c9803100a005420084400c075402103210b00010b507651b038071030503072610a06541d03010990060441c0c6a40082040100d01810040c1040d03404110f034101c0080d00000782e80065900070003c001043d0b06000d9101d0000b4100180c1119100108107200b25406020062041101100041c2c00143c038404030050003100000b840c4004500a0128a2010b80018480050b40209601c08c82d105082c0701c070b101c00c90750090018a0f18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 422086196 1250 422084946 422084969
    0x40c0c030804060f02071406060a051507060b04110c1e121e1902011802060405040e0f0a0c080f0a08180d0203010903050409140f0a02070206040f0b090103060803120c0a0504 76
    0x1000d107440384108060b47e040c6146800740e40b0008402e4100000e003801180d80040201c0c1ca4280c4100d0448000c1e404048103450317480c3c0b141c540440a4803180a080205c2e90201c0b10035545801c0741c004a403c0c42c540b000200141c180880c524500c0000000700000540d658207981583c45000f00035600c2e090151324100002010046280c3d0b11055000d01441034401c51600240300013030001820034003240301451b009600070818070062099083c1035000e02c1e070b6003110324101d43c00401407000140c80c2680300e000454035030540a0040c0f0030308900703220010040a1000040c510312680b66100c0403140614ac009440e04a49031421064030f6588440f0035015540240003006451660b090080250744079008007042903007014060012114501141da11500c10b4400d1891f40d0745404ca0100b000c0e6002607030036a807003002404003082c0390a0400c40306004048204500b0b070354180ca01c0c000b400740e82030f5a115107280e400502408164148aa861a0b80300761400c4c50b241da113620050080d6410b0280e03410105203840c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 422087446 1250 422086196 422086207
    0xa0506070f09090207051002220806010918080a1409061902010506030a0317041a0702071509031101080a0f0e07050325170705090a1a040c0c030804060f02 68
    0x64025460100c1c042265450120340703a03d82c16210706a1244000080140e8003a0030703104100d03607803a80079160164005a01451142400d00400c42521590300003070055040300c8010880601d4600c103800304081d42410b030010005864407580bd9501584035000140115040320121890303a2000301d602c1c100300284655220405030803040500041c8000c07100140d031900e0b02095280c90001102d00176607070300d075440000c407514010006001900140080703400d600943d081815a240c01d04610b446607055034010001c2c64130700400c41c02c046060a020005214514a0910200d250340802d60300441080c28055140e4451051490003400702c4642d50a03c18542606e11a01c3d42d0017240c40001c50b00d080b4122103088a414901e401100d0b110400e07000000407400c42040b036451610340801400c151002600c02075640c0c5d4000c10100c400440c5e181c00ca03075540704036820aa81000c08070291451096404009440b4030001c090400c605101000d4240601c80e0005401c202e0a0f8100070702607000d0441c19508c0303030b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 422088696 1250 422087446 422087461
    0x41040204050d0f02030d0e0607150e0307030203250f0b06010c06060f08060606040605030726010303050a030e0601030804181506020303040c0b0c030304240510150809060f07020a0506 80
    0x300903e0000320b00c2805042d42002400d4403441c0300c2c4452240c018400c13450035605985510b81102080314281010303886140f10b0b54040300034006402100d00075009565602040d802841c7c0c503880c030502610301c60b0701410710000800ea0b081c0018141c0ba0740483c507900191501d800683c0d4003001190700030803c5040074000728402103660032800c21103800380c0c01c646030303501d0301005c024440c0500c0c05008001001840012030091050320044c2d5034200226018415030728001c840d13245424260402e4010a000141c84219035078517125890f00d000180c1c018188650650b505c0310b0240c81284941c0200e5815481c02c0c0d000c011442d4000300304010b42c4081c03080e5142d52400041d4590300308440695020f10103400010355044030608548400c80039101440c5143d40d19512164098000311244554001d40d03040709801c141c8a2150034040c84004009450705860b000e86080b0440c0680304010420843c2014080040000200c0da03400001660140e0610342e905201240303001030105014105110b0a000d10014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 422089946 1250 422088696 422088713
    0x180d0507090b01030203090a062a0f140a020a0303020a03020c07121403030f040206163912110607080d0203040201030c080103081909170741040204050d 67
    0x441d503a80e0710511180b40306600640882c003007110810401d8103c40002da00103142940071348030524035005d20690304a112004803510440e8045d101022030400a40c45201d141c100c19450303907007001407500750715140415500035112980741000409160300030584050580c001d03010b40d022031455004950545076201d80b15883d100c4100c009990340b0070f8111002c035012001000301d91040d0651078003518651519401c0c00b45561081d00321442a40c0814010400a84c00344404482c030140b034441580c0326550f40c5500940d0140c20800c0000c0107400c49820040300c20703540032800039103403c5030340314078181c1f440d50200b0b070188200d0400800c22400001c0c1c1e0f8100a00c2c0d940514059030003070360204825045440b040ea060f1400f070001904411007409030080c102030b41c1c400e41040094500c2c10448180d51210240c1c1c00400100e038035211504040c5090101c2440200c0540712804401c03043c01554200710200134506100e806640700c00f80c1a05035001a5480f150100c83c02407901504407511180341d070415560 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 422091196 1250 422089946 422089949
    0x3020f13090b06040b03011203021006060806010816210b0402070b011706010b09060a020106051203070b0f1614070f031101050f060f0f010309120c03081b0708180d0507 74
    0x2810b14082e12904075051800984081d9207011a03401d15590030811460411100b1600440440c805c01c0d102d90b8001c141c90150300c00406140c1c595a115052000c005000324200412000402024010440c500d90f8000622264a800340b0f130900301410300d2440203c043c2c0554000766030080e00005140c0c04104162210504a55900345d000b0002c04181d004561185400e100382c810080c000e0040300d01c10328241c0010400000725000000b001d43e507480200e403e60382d8820203516140c1010854100303010b4250b505560100a1944035085c618101040b800383d01d040201542c104282c3d0800607849402d06012140c0c036a0f003100360300c20310344203504e0010400c0f070b500340750600385500f4140481c4003109000d0310907000b00f0004187d42555005202440508102c0c3c107250350400d030301c40c0c5466012400a2800003641e01301c0340d99605000040e400c000d0038203080075180002a12094040320038200c40c03182950f507915070054046668511415102c04102c0240580f254801c510600b034004101c0c0014002d070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 422092446 1250 422091196 422091209
    0x3120c080106081005060f0f09040e010f0b01021621050111090a050d03120209060d0608010902030601120c09050421020c010305010b090108040212150f0402010311030c071203020f13 80
    0x83d05644005400c0200728151151540060041c840030140b944050007404661400c0420340c2e060010103030005090702c03442d02d880c0c040c03039550785815001240d250143c009120720130b0006144039064241342c00940740d100d1240442c0b144040c0e50168440b50041151585580c10000030321160201c070081921552161004030306c030710486480007944d4248001034030121501501c410b09400420300c28440a540913a80c2c13a81d00034801c00c005444100745204010140004c8000022402518414540f8028042c2c100881e111410340c81c00c4002800280340303006a440004000c20380e1b44441c80e01c2070102108050150b2814808072400c0c1610382d0009129102c1002641d0901042e40d075002401014451148000d0000308800005005814000d024806202d0540300310740f103480400c50802c4c00018180e0341c1e81d202a1090b024082503603071501510aa03010a02143d81c913508000346040e426100c0d500c40140307140d0440440c4c03030080c0d01950540c0d141009101c00e85030354048640605201d01854010301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 422093696 1250 422092446 422092457
    0xb06010c0206213612210606090d08090406090617011a0d02060f0903060f0f062b03020f03030c041806032a1d041e03020c0d03120c080106 61
    0x10700c00300302c01580022a240001419150710307010003150700520601e0b101308541c1380700d003110404070101224000c00108030402e0240d800545107501e601742820b40074020701e110380300c144030303d10360f607550364285001d10390380140456900c80c1c48a0201d800340c0440d03803115030f0b15842c050000450400355480903420450030300003000f00c106141541d80c0c3d52120204d40c0798102c415208124014280000105234654108403903d05020b02c0200107440c241c8200c1b1802d1507480c080c4140455141910351454014034111a030305001d4500503c05050007142c20741c08851940b000703a00340c1c1410300030312008864868040a50751b50f4500122921003503032052050100360071001850300e403c07850314032880c01a2540035019500e080540c001d203142d56102c0f5130001c090800010000034160000e410080c02103003401100b40120700e01030400d80309118010420004c6003403044140c20001c0d60100c3c61800b007c03811a20340c100700045040031a5501000b0000018070307032030140c1809903540c0000c207007030403540c07580e880 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 422094946 1250 422093696 422093701
    0x10c170601082206060b0318160b1204060212090303090d08060d06020f1b100e010209090115091809050105010b0408060f0a0b0d0605010f1a070b06010c020621 70
    0x1152504022070768900c0f869120304095502d50400e00154000714020f039004249039444106505066106a89010142c88074007020801c550f424440214010b030000e046040d06031070320088811500c9908181307442001c11800140401c001981903810b01c0300552059089840d010203020b0b5a984252083c030003034443c600100b0302e01c500c101d15091103054080d1400f403504c1310301d03620030700a50440004100c03811001d210244c14001d05031038101003640410000c000300e01d0314140010440303940007401c1e0541c0e40108429162900c6141c105070441b032001d94174410078070510303c0c00c580c6080250407560038040d03900101c08026074503400481d1a14050070080040da669080d20603414441c0784188005900003a001605603034400841071390104580c407010407881c0b24400050290b231078030b06044603000c0e45e500050068031004008040500302c60103403280a04000148948507020341d402c02009404024001450380e440340383ca82c1000c581c09045982c4500294800c001012010b490803046034030b60600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 422096196 1250 422094946 422094949
    0xc0e0903070302030f09120f0a060507051914130f0302030705010905010c080904140103030c0506011e0311180405071a0a08040204150f06090501080a0b06090d0f05010c1706 76
    0x45034000766043e0015843d09551409207003040d0440aa0700340c1c8090201210744031410244480c002504400d400340c8205000c0340752650864101800c1c2034100202440203aa00f60603d0260300c10140440c14502c445069000c1c401c80b5038032401d01d51a09540d80f00e50b0010701d41214000c8032041c1c030b10031030030f49040c0c0d500c402c0119002d030038902ca40350005010b007012030081403503580100030501c4060300200719903c0544005044c400203031300481c001110542c040d024040144101809410f041c81e150b8030b2001c0e118a40881d001c0c43d400b014184603040450600c4940e1000084641c0f50308c5c00019a603149824100b05441d0041842203841d100e050a041a250003103402c22900f00044685a8088984440d000c1c0001003490340c50120302d0000c80c0c0008031348029040156802000e031a81c43c1566075040c24001003040c00302a11941c00942850449001542d80c0015101001c1d03040e01c101414100c9418800c50500c00d040c0082c2480d440e01b00c0369400f6652080d8951000f5194080c4900d0503140d400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 422097446 1250 422096196 422096203
    0x615050111060906060909101109030c010908060c0c030c060a0c0809010c0c0605060607150b040b0f0a0306020a051b0304030c0b070515060409050115030b0108060f070302090d0f0c0e09 81
    0x310002c3e40744e0803040019560345060009640c00c000c09030221042d43e4982d0003800b003241c0c0c50074003d060055000c510481585020060346010239801e1034030480281c075120019603038002c06481c0708001030002c10034189640b004c0080d01c0340d040802c0111004c908040e20644000e008503140e20002030700c039400042a04005002d11000c21800d80d54142114245440e03c4006090280241d07a000004002c03400105403100c1c48904a025209c82c00240d8030030030740422045407c440c2901e070181540c071540c010b01e95140401002200c0d081a40540d550f045a2400c840902c034040113070b0799800040c40025048000003000e481030b03074801c00e00b04884607100c1ea05400c55000c0c28170010420313401a482c645042422003c4140c000d138004d40301003461240c554441c0d0a588240c81c0000e4404000002007017440745034080b150040c00050007414043c00e020700300814141d0010316000605400041c10030440d00e5640b400021250407102d1691100210b107800c0b0680e071068811103c40c00e11b2040480c0c003d10011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 422098696 1250 422097446 422097451
    0xa1a090c031807080c010c14010504030e0a060f0507080a18060305150d050d030c0509040617010b010c0506040b04022d0f040213030620030c07291f03061505011106 72
    0x1c200614400d095000115440007c0400c2200c055081c0c0f00d0102d00c09400b40200e600403031080e124240069018030038807082c4029a484541041718003002c12030231301d4000048900142d0409052540d03500a11000d41d00c0e40080700200040e454003050004d580760780740e80b05c00d005140d8004c1c080800c0f00c041041108201c3c24006c090010342064802441082c006c0d8012080c088081c04d081f820480130a00007411284540c3c02000b11034500030f103400701004c081c46440707444002400d040316042d070745813561a92580f008000501c445d10b1500460155038842d24000852150b110071041d0000b4904140181ea499060700d441c044e09012a042c40e82c1e2500d8000d50391604100318203103401a24549a090140c050740340074220303c460345e852003020a94503a0041d840f0700700c59501555940c2036407400014000300614052050407504844190300306502c0c0c0542e8202d129030b04543c1c41181c0c0d10194818494266000420192a204400d03420616440360b1608030b40b8241ca510762441515260513441d401c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 422099946 1250 422098696 422098709
    0x190503040501050a050412031a030f0304210b04080304050c090c090108060a05011d190b03010509070c1205030720010507020705180721050f0109051e0a1a090c031807 73
    0x11f00d2940912184a64841c044050128600a00101e005004241841c004080ca00c0c40703500001420301000c001c0107040401c810920000c40100403060700c544d4400040a0f0004042c1d0900002280512008000f90641e44034000c0280c155402c3c0801040c5181d440001818042841800094100e1030407411050448006848041d84100007407a2989240f003c0e204040d032244a80720303000c0202da0039940300b1010b4807050740444e507a5410703c020800c100c0401891071041100b049042ca00041301d41c14650410101410843d4481d01ca004007034420941c3d04080003c0454501000d441801c1e05422080c000d000707640070382d40000c2e243d8003805010008000704d855085550004120380b107208900c840d40403007201682416a519007201141941c8007542c48545544c000401440751413103900c549604403c08101410690709046030b00700c80c498000f4401d003c029559408044c4a60b030031103008251150040075002640f5140c528218a5001580c0041c28003054040140000b0000100207065401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 422101196 1250 422099946 422099963
    0x30512120604020c0a06051b07061a220c120f1509020f180f0a06080105090a0c08190209040204032906011707090f0e06030d0504060e040908190503040501050a0504 72
    0x1441d4442c40007a20001d0301ca44421412180d0b07107002004050080e11005109007404140701d41034180e03102e5001103101c040f51003a0300f1148a4244032820500358293305500c6900801c0400c2250000c2e210b695001458190312410100212449a55984800103030160b60381c2ca4400716440d800d03071004038000e041d02070154200410440306018164142207048100060080840c80301031008191482590f40c08103004c9600000140f240d4030f070064030a5070003000c1400030803c410381e0030340082540f03401802425074112080c1c0240110384040e0101c500c0c01401030000d542e01c598a1502c281003450b10302c040c00076a4450b0112440c111f180140240c0607080507034601c42c29050002c419034040724090222018130899450029040a140c1006c000801c00f54950108034175000c4281428040d241da01030707081150800c020300880da00701859401100d4143e40002e00300d41e0f18a00401a8070500c0e51510039203100726100028036070320000031882148613000a10290b1101d808000039100e064034010034500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 422102446 1250 422101196 422101213
    0x115090506030603010615080a050c03160e01200d0306052e0c020a0f06021e030a031503140706090b04080a02060d02070b011806083004030512120604020c 68
    0x80c103180650f070440310003400095101e6440e0324408204040701d08042c0400c2d807040400007000458410150312000711030911f07107140750907230f03004440d40389030790800040c07001014148007240d202d12541d100810441005500b101d14156090346e03102e00710801100000d051040c007280034104150210b640c4200800d000d01c40c1c043d500c00d901e8034254018203c0741001101c05121002d42e88440b12036004010a000403580281040d800038100020202400c4080364400c64052130030000004845ca4030801c0d150018824040c10034650300304010780e00c080d140c900305841031100307045c01040040840307445403600d20030103a480c20001440d00652044c207060341c10901c1010098100030000b8000c842060400604e00030b141e569069081000381c02803502082010547c5040e50b201c1e03c1440043d00c03411004040d00104041804125070154200c0c400c0010101c80d108039004410b000d940103140d0110540b03c14030001d5030303610841d40041495a1401d8141c03008150301e030400c0d200302c90300304000754041c01c07a05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 422103696 1250 422102446 422102449
    0x501080c0a150309020d0804030c0501081f03060e0307050106030b0708090d020a080a0e090a1e0204030c1403070e0108100b0d080904150b070b100509010b030112060f0f090b01150905 80
    0x4008544d020b9821208010300c09000810900081c03014603c500761480c14141404001800c200c00204800c80c84100c11700c08202801203583c03450100c84d070020001c9a03c06603000b4850071405408002030103503003400404800c010b8040f0030544100a580d5800c0c034555070b4401c071190b9644600403da00580c022020100200d01404010188a442c0d41011858101144040b488400003218400500c5944103c1440030600303022602000d8094150154105803e40d02d56111031296803041c4910441c3e035001048403901c041c40041c001341120781034088a90781d40c8501945460040002703480355483d000d540d540e6880c009040c3e8200c0d58000e20a20704019030035041c040203010340041102030420041000803400b48503002029041c1c4202845842814041200d5138140b5498110920400c0d0620061003040201d1081d40d0454021362103841081e20142400401844ca145828a029050200da5002403800c0d8010001c8144502904a65a0f986520726000211010010400100c6144080019 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 422104946 1250 422103696 422103701
    0xa0302090403032a020a060605220f0b18040c0b070c050904030c06020c030a0809030405100c111c05100c12020901021911100201200c0f0a03030501080c0a1503 70
    0x9140d9003091448001004c118141d0305a844988030301c2c010703400444440108010741c015000113020954a0343c4598196400c900d03400e000c078044502a060351004c2040000c2007a81000780c7d5040c0c0a04002c0400c2c1281401c5000c1e0074049034180c402ca03404120003d42c0e90215000c44008030340015052060b10306001c10441c50440140058080182098611300428040c0c8000c00020b6003910080d40c7c0c414071000054020180100100c0303281d0410300c0304110f030b030302c0d825101c460046040c9000144280a854440b4503208422210707600325140080a11241342d429201107800b60145049400c0d4521054091064039050240c80740025a40d02060b1015030094000c2e103900d84050040e9403180000d40b20546843c00d42c448262031400310b1003131141140c20000c440c0d030751122403403000744840b4440b483c9122040ca00350508640003c1c00241d20099100f040c000790a03800d0b01d50080e03854000c614103000b006031800303005140c1c07140a1445440f91078900b4240b84000c40b045190402c4000801c400c00760700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 422106196 1250 422104946 422104961
    0x60f090c010c150f02130f0b090d081c02030714031b03060d05120a0306150203090d0212010507020c100309020306060603180313140a0e0a0506030c03010207060f05060a030209040303 80
    0x401e243c504001c0b1000845a0041940708030000e000107841c1c43c81001054105510740d0300015280103803002c18814801008120756003803400380d6451200c100310f45040d0310305106681401444601550030300c2e11020071600194050000c5070340e10400707150422000c0c3c0303041c1b00a8891401c4101e10300751109200d01518080c50b84001c0c001d0080c2041c400903280c66051021004000109840004007804451703054401e03003001d8404004e2460400611a601030350b01c0c8280301070144201001c0315118119a11481212011940000203100f40e0402d10030181d80e4030440342d44148503074034548500c91601e2080c40396800003a00100182420f0700e030b60041c01940e50001c7d000c0c5c410546d001c94507841194007040100b038080c05051030688002c6c0340c48125800159071241c0c8a2241000b9103040048145e0581d0281c3c1002c02c1400001305ca40b14040002e152422184c50942c055001250100c2801142c5d408280803540c1c1d01401e0103160fa41c0c808100c01c074200c2e408004d504c10300c4100800c0219109034003165 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 422107446 1250 422106196 422106203
    0xf0402090406091d0303040b0a2c1608010b06040506030604020912030301060906090e04060b0f09101701020c0d0503090718050117010c142506050108060f090c010c 72
    0x5291410300e10129081c0d0341039411912225440d00070300c0d240605004000490b04034040d02540c1142000c1d59100c2d403222000e014500003640390844c0c001208401c8a103103401b4100040120200d800301004c054403842c000c1c8805042a8072110001401d40c810302546900c04d500801c96840e140c144802c00c00c031a0405045203070450750a003d40c41468a4101d244030700c1c2500d41008540365807510380c3c010440501e44d0030503000c108607070b1420070001c22401c00d400c3d046540654040750b00215180400d101116041c4001c1d0301c480160140454414243d05400944d80c01000303245501c403200141d20300340d00c202042590b280d4400c01c01075164901c58000780d9007000070401541c59190790303075134a101d001c000b80d503202e940903079940300400240300c14042d91720500f21b80c1700081c4088404004007501d90034480d50846091a000103000152254000c0c0002d030b00001199002800300860826000901090086c41001d2040c00081032441e42c404103021301c01c511882c000d00c60301020400441d2003601d14038084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 422108696 1250 422107446 422107451
    0xa0513080f07151503170a142107030606110111070221011e051e0106110f0a0809040605061201030611040503030a0c030e10230c030a09061d0f0f04 65
    0x40158020080c00820040705800341505500b0090440d44603a0300116030071b102040102d40d40ca40240c84040f0b0184404516130712024450581003d80043d5490b402c51100d003a0f04100300141c03d80e1114094030080c1d0b031050810300e00488428203e440e61144d6002a19082c04103100611340910110100b0019100500d240002018614255050380d110000c1c5410b40b10000e680040052040e032758080702140070b60b02004000108a15080018001c01c401c00240c00706030300c200c1c0c0080105088092340401141c4030b220780d03030415030010340107003c54078850346c01d1035000a074500d8402d0030760b00c980803038901600c5643d280d5603030035000740086005684200000e0000107115034060001c2d0030180c9658964401140e40b510b001000c0c1c1c01c070000c805100c0c80c600c26498806980c8541d030344500030b003115104100d841e2040c20015850080302d06100092000144054449600100c91401ca507030035218000a04060022407240382c140c94201e9411028029910b150340ca0400112158154081d100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 422109946 1250 422108696 422108723
    0x615050a1d1b0c01050103150b01050a0e0109120311060f220609061109031c0c2022050c0313020d0201030b0a090207050c090426120f0a0513080f07 65
    0x10705407180c1200107003083e00d95660004005102070100c260760512010032040044c0ea031020300292075402681e504404108007002c1c1d0307040b0307a40950042c0c800f401340609040c541d40d6492400920450030001150005c0c05000041140b0f0810080c1c280c3c000d82407004e07801103034080c03002c208101030900003080c0d4a0b01d480e00c003550041102072007004420b26450b401c407640c0d00014021f044c9003c914525003000c0c4206900c1e045000c961080d808101903600660074000845854880c4545442084d92030341d10102c0e0026049000b4101000c4c0b044c0714a08035420300181e81c84044092890004a604c8035036440a004080014903103000c04807001e620506000800c5d035000008904000282d402c14040d09038001100c0052002c100400d61050400f02e40c0301c1c5d45071400750348488018041c21400c41d03840f141000003409001402043c2c0341221071440725020360746841072540381040000c4d1181020310340f81101003840c03c900c881418071900d03041403044d031800900031404502c69001442c242d845a00300d150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 422111196 1250 422109946 422109991
    0x317130e0403022109010e0a0b0a030b030f01050a1d0703050d030c1205070f14130b131d040c0608040c0b0a050c1515010503011d061305040615050a1d 66
    0x408501d440b03136284800d071154510b80c005031030400660403c6210750303400c98082248040410455820300305629000c14070500d2503000c01c0ca056001d078000283d40d402d00e070404c803882a507030307200180c40a0071a1900900c8040c400c1071503100c00721800058a607070401090041414000d0308a40c0c0c20030362610340482d22a00e0101c00004540050b60108009180f19100d01082c5500121004541c64408030b01d5180c012080742e41c007101d10071441180410304012401e410b95070a051400001000011900e6240080003603910101c044110703000c56502d07001c6d03807011901502c685010351140307903c9182d0078500c50522100c0d030001c5d0803039100076040140070072100c8100c080620a245803150244800c51507400d06d1640b003e5610270b01202d07241080b00034001088170b21030004401c01024421482c030140d586489000c10200410030340c1043e0901d081400340000c0041d590711804a8840c1c038021129a00c0d03d80080018103800c504c59440c00d6143c44003000380280c24050300da500b143d500340002807259104103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 422112446 1250 422111196 422111233
    0x91109040506060102010c32070218040204050703020c1e010e2b0e061b03070b04050d0801081f050c040e07050a020106050109050109090527070317130e040302 70
    0x15001c44041e04403100303009141d602400ba4507441d051605200d00d80c0c500c289032035180c0e0b14804d0034061304d00d044118424015002d40741160242c980190000d646070301700040800c40080c064902301c0c0240d1500380020141440391080d95030000d80e0300007400c0760340d140d40ca032481c10f400405441e5005542c2c40041c464180c000300105811001450020358005016603810b608412072000400144030280c0018486035440ea400c4404000010204050785400c0301c00742440e41c01054801429855900180000e10000040103d801050796a414404d40e03200c0440c2e5481e03c441401c4a002007464260200d02c0d0603064000c143e000d01d5042e074807401c16a40350350752400110140c9140003c40c0c0000303031a0424550a00a003406030a00f030030102c50461070000020182032072480346c180d40b80c1c0c4d10b6021810b008510810a88654141d82e22181c4500c15000ca0507158403182c417040761000252010b070301124140380c0903180c032a04041103001d00e00f85050762080f24030b08020011030440c09400317604a081a40720 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 422113696 1250 422112446 422112451
    0x303020c1c020f061006020c060a091e23010503011401030f020d060e0c070209010e0703090203100b0301150806040f0213050f0711160915081906060b0a050a03091109 73
    0x2a40185a5144407128850801c4e90180c440c14104001030401c0c401150002601d00100600b510701e50754840c8600030031a0900210b4000302c00300705071f00740b20f0845254038044440c1910850004c04c1d10064600c841300301c0d521604100e01e03010074000d0004020181284200d00d40080042c1408603400c051040c8520881e4020320804e458a603942d1810b1080340c08441100e41d0250303c10306043c0c81c2502c00d030000350b001c0e04140305268032422000000365109201c7d81009030b09640c0a01110f5185400c000c24001905111410300d000790320701b003000d102c54221102810708a6a140010b06115200d176150130001440314001030740c000a410501e0140301d880d42c0309051107000c0c004103004290404500061244011342c00c4640d103036022040c03048031001c00c04a503204aa0141d4000182d0480d2031880c00d00070380c003e03440103030301d40500803141114040c10f010324a44c45108031810040c25481c0c05031850140601d1a0071781c00035130180480088140245c0c0944000c0e8016101ca8100e1101c800000301082400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 422114946 1250 422113696 422113753
    0x1104030b1905070f020c061e0307030501031e1e0602130b0301050406054009050c03060c070f0f0615030302030a030b01110c06031905010e15040501060c0303020c 71
    0xa90840700700d141c4061203100e41001092410150040040c24003d566400280000f442013600042d800b03910325070408585052405901c1300c603280d1a0040018000300024801624030001c0074030748c15105c102c0010440a039640c4015115621040440040103140481d1411170b06180d007044144203110084400100601940080569070360500b4103000c10380f1f1003544003600034000030f0f400044101c07042c5109491183c2c2c0440c41260100783d00076641c60b01c1a2800403d070384a00c1c000414043c03007804075640c0f010000035412942d05481d14109840c0078440c8600c0130f821148031144c1c40000583c000c50888107140200d101040300000c50503605075900c0c00d5407086015a100081078000d0303039014051551502030034280104189403280714203840d201ba5074a91446080000005103603a040303840f013906d8220f100030040001e5a1a1141c031103220f44250b48200d035421004030540710314a803c0c01a02d0590340d02d030755021501c86050b038096001c1d4214519a500b80d001c0e00c000418010510201018030198 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 422116196 1250 422114946 422114971
    0x80709271407090c08061207210203060c09010818030f19080703060524130602010c110f0312060303090d06061a030103050d110f070618081f1104030b 66
    0x203002009140c0070643e40680400c40c182043d0008064002e0880c0d64018002d440c01d00c1c0294540900a00b00806604000200d40481661b255004504180d180750203200f030303003120a641c4841200342124003c15003c0c5000516203000500038001c000d0700607844006a0003101d060800b400c8601d039140c6c10a12a180760320305c035220142c0510741c1c4803501541002150a04100a5040002164240c55030f2581c4400c9400c0301b0b28124446204a01103c0307988241c1c25180050a45410b0024003038442509140d00055103102044000c60300420300c40035200800000350703d07180000d1841801d000e00105055810301041c00a203000b40c40349480040c03240c2c0318000001c2c000b42054540d21026100a281000c2e101062005000280000900c411501d0490514000e00364000b20403915000300255515081c4c00384680014401ea04081d410400400b1000d1400605861303407555503456030040c911150301008000a000d604240b03500016000c85c52040302440c094a0385c56030452703031a050314890802c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 422117446 1250 422116196 422116223
    0x6070f17071a130b190207080301080c01020d0c030f050c060a0b120a080f030c1306021b060c1f060b040b1903020c0706081003020a0b0304050f0708070927 68
    0x1c4140404840442c0e0380c00311020b2402c01c0303211200421120030005002d0f41104000c0762480600340c4004108403110003055503038944610381f001c82504284100d05040c41090140c0c503840d170010501100c07040707060707840000c0040b8507201140c505c01c0c81c80e0008107002c000c10070003407008024055039100f1025000c0100700c1500403403d02070fa480011030030717110300e80000707040760006003054048a0b615452103115503102c2d00c0f038404040d583c1c820301840141c8900d00707460008000f900030850a042e601c0012900e102c41100c0020b01c04140701e915110b000603000611002403c1c039085440e1341340100036000001e000f0303071030380d4103803e080d403050304000140140810450001000c206240e4082d046500d010343c24450618900d03552120a03029000600001c01700082c1207e20120030a8011038004143d10030702a0b4880748604160300940d0706407524010200860030502d80044c0000489400000801c0d40c01d2600b900c490042c1415050000c8400c450406218800002e12211200d24010401890b012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 422118696 1250 422117446 422117453
    0x70503070209010b0a051803160e1005010e100f0e09101e080705060d0e1f0b0a0501120209010e03070308040f0e0105060708090d06321506070f1707 65
    0x88205038130544144000b0040d0104032513000c0306480c4841c81040c14500c420380032400180c10034800c1d207200c00036410705150000d03900d44621410f90181008288072072001740c89034011203402149981e0345030083c4484074640301040c45401082801d105529144020040e03a0b40016400c18003035404d80b0701106030141c148164502c1c4000c8000e1000d0514040683c14500550540c80340600d202e61481190003081c0c200580102d07400c0310700d182001c507080e074200c51084124140c140d00e0384d0703100c107141c103140410901d454282034002d40180c610507140e9110310980d4500380b4001e5071010140a042001803100d4080644003006172074041c40c4101c1440e41c6550800d002c4965018107a4021541c01960000403c1140c840c0c404840380301c0d80110b9142d6480d080d45c00898401c52178500018181e40c0b824501d05180e1006050620f083c00030618014410f080ba0110504c801c001501e4895044681c41c1130b120b400d10707009000b00440b5104203218a04280f4684031001d03092001001401021000100b69041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 422119946 1250 422118696 422118709
    0xa0e09270303240a1e08010504050615011d091503120703080907230105071a01060905030106030309092f0a080f19090303020405060c07090606030605150d0b060705030702 75
    0x2201284460012218000002411090300e41c800c0d10b4400c5405845174980014000d1288040c0c2465002880681881d02d415590ac4408507800011404c41c00c051001c03640c030035140c145c0da0540350740b081400c59000c40104144072001905e44000b02c050810003030500d450038441844005c4180c841d02c0e844141e141006010f40d0801072550300e05420420040c0401c00d010000e5065860042807000a251140c5006035118840c00a005d04024114002d90440d0000c0b43d210300d050719590b544159001d50366809060a80340c040c000180880e580e480c041c0600c58980d80701501c8556496020396169103004800881c40b81c0800c10034141d11000211401119001034030b0b00c0e00701045181c950300c10b240c2244c19080b01000550980c110545880208041c944643c05982c040e010052040e6611075000b000340b95505080e124900d4800d0415000103503941c020312608080726000303860301c3c0030f1400010300d110311a445030441c009419034a41c1e403500c0b1900c600019020a40c41000250796070b0810f170042190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 422121196 1250 422119946 422119981
    0x1c0b0406090603050a0305090117010905180d05040605160606120308100e0711150c040e01080c030a03050a050708070b04060f0603020f1e0303030907060909020a0e09270303 76
    0x2609410880b041000480010320140360035014a0704680b0307010107000403904402c102c036808c2e041481c4000042541141c542c411030182c0e49440080442404555002d038641000f06003070000300d20107101c05c11440d4010070040400d02d0703604100751003481069541c1021140705410440c00c045007440e80b481015001411203400c102502c8222500c1403500c148825502c01c0105522300700708400100300c40c2d8000400401b014156203901402d65443c0a41d1203100c01c2d0000d00c12106429134100c00081c42100c080703452115698060040c007000c000c10b44040d6035581c0241d602d441009004c21808000c280408003a0902a2003010303140040d007080d0030481c0c00e03035480004000c0c800d4500b07a020001079481e03040c0c00360205800c2d02c84010390f81c0301c1d44403a001d0b0b60b0614503031130f014000042048032202c004a804030549510752100c01c1a0b645440d2041d04a0013580c080c00081690351807a40c0c0e00785442d00960b0342c4070b404012844030030b03140c5c1c030300242c01d81c4901c05102d09036a0004c403e011405031b0000c140075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 422122302 1106 422121196 422121209
    0x3020a0c0203010e0c01022b110f030408010606030c050a080a05060f1f181a0318160e2a070206120702070302090c090d171c0b0406 58
    0x54940300c9417060680140150200b9260b40502c1c022001c05032006800e01443c078440410003640c0c92280003d805c40c8034890442801c012000c10001000601000300000c9441c074a03004014003550360030503810090201c14483e0303090980d440f5000e980d0001c0f048902003100e03200c9034041031000046007105038204140000c5802060141d81c081304070319419955103d0640009910070881c6081404ac0300c000c18141c00808803001154030245411649000c4d012070144d680b12031040c03800e0140d89070170001d540c0d40581000a82c150480c000d502010006a0015600d5520300c441c440d00498800d1302d8004002113000801d41d240c02c000e9480c10300c0512600242c900301240040c7d902c643c04e12040f4483c2822400140d03050142030150b80702d460000e0501800c20138950f032900040030070440c011010072000d105022003485071000c2096003000c0e03030700b0000c0d040f4002000d00c401c0c0c034030030340280 = true := by decide +kernel

theorem cover : BRFrame.Cov 421942446 422122302 := by
  have h0 := BRFrame.cov_init 421942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 421942446 ≤ n) (h2 : n < 422122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
